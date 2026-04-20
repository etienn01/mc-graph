require('dotenv').config();
const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const mqtt = require('mqtt');
const path = require('path');
const fs = require('fs');
const { MeshCoreDecoder, Utils } = require('meshcore-decoder');
const channelSecrets = (process.env.CHANNEL_SECRETS || '').split(',').filter(Boolean);
const keyStore = MeshCoreDecoder.createKeyStore({ channelSecrets });
const decryptOpts = { keyStore, attemptDecryption: true };

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static(path.join(__dirname, 'public')));

// ── Persistence ───────────────────────────────────────────────────────────────
const STATE_FILE = path.join(__dirname, 'data', 'graph-state.json');
const SAVE_INTERVAL_MS  = 5 * 60 * 1000; // 5 minutes
const PRUNE_INTERVAL_MS = 60 * 60 * 1000; // 1 hour

function loadState() {
  try {
    const raw = fs.readFileSync(STATE_FILE, 'utf8');
    const { nodes: ns, edges: es } = JSON.parse(raw);
    ns.forEach(n => nodes.set(n.id, { firstSeen: n.lastSeen, ...n }));
    const fallback = Date.now() - 5 * 24 * 60 * 60 * 1000;
    es.forEach(e => {
      const edgeFallback = Math.min(
        nodes.get(e.a)?.lastSeen ?? fallback,
        nodes.get(e.b)?.lastSeen ?? fallback,
      );
      edges.set(`${e.a}:${e.b}`, { lastSeen: edgeFallback, ...e });
    });
    console.log(`State loaded: ${nodes.size} nodes, ${edges.size} edges`);
  } catch {
    // No state file yet — start fresh
  }
}

function saveState() {
  fs.writeFileSync(STATE_FILE, JSON.stringify(getGraphSnapshot()), 'utf8');
}

// ── Graph state ───────────────────────────────────────────────────────────────
const nodes = new Map(); // id -> node object
// Edges are undirected (keyed by sorted pair a:b where a < b lexicographically).
// snrAB = SNR measured at B when A transmitted (A→B direction)
// snrBA = SNR measured at A when B transmitted (B→A direction)
// (RSSI is not tracked — SNR is sufficient for link quality)
const edges = new Map();

function normaliseId(id) { return id.toUpperCase(); }
function nodeShortId(id) { return id.slice(0, 8); }

// Returns true if a meaningful field changed (new node, name, mode, status, stats).
function updateNode(id, data) {
  id = normaliseId(id);
  const isNew = !nodes.has(id);
  const existing = nodes.get(id) || { id, shortId: nodeShortId(id), firstSeen: Date.now() };
  const clean = Object.fromEntries(Object.entries(data).filter(([k, v]) => v != null && k !== 'id' && k !== 'shortId'));
  nodes.set(id, { ...existing, ...clean, lastSeen: Date.now() });
  return isNew || Object.keys(clean).some(k => JSON.stringify(existing[k]) !== JSON.stringify(clean[k]));
}

// Record that `receiver` heard `sender` with the given SNR.
// Edges are stored undirected; SNR is stored per direction.
// Returns true if the edge was new or SNR values changed.
function recordLink(senderId, receiverId, snr) {
  senderId   = normaliseId(senderId);
  receiverId = normaliseId(receiverId);
  if (senderId === receiverId) return false;

  // Canonical key: lexicographically smaller ID first
  const [a, b] = senderId < receiverId ? [senderId, receiverId] : [receiverId, senderId];
  const key = `${a}:${b}`;
  const isNew = !edges.has(key);
  const existing = edges.get(key) || { a, b };

  const snrVal = snr != null ? parseFloat(snr) : null;

  // snrAB = SNR at B when A transmitted  (sender=A, receiver=B)
  // snrBA = SNR at A when B transmitted  (sender=B, receiver=A)
  const isAtoB = senderId === a;
  const updated = {
    ...existing,
    snrAB: isAtoB ? (snrVal ?? existing.snrAB) : existing.snrAB,
    snrBA: isAtoB ? existing.snrBA : (snrVal ?? existing.snrBA),
    lastSeen: Date.now(),
  };
  edges.set(key, updated);
  return isNew || updated.snrAB !== existing.snrAB || updated.snrBA !== existing.snrBA;
}

function getGraphSnapshot() {
  return {
    nodes: Array.from(nodes.values()),
    edges: Array.from(edges.values()),
  };
}

// Upgrade a node ID to the longest known node whose ID starts with it.
function upgradeTo(id) {
  id = normaliseId(id);
  for (const existingId of nodes.keys()) {
    if (existingId !== id && existingId.startsWith(id) && existingId.length > id.length) {
      return existingId;
    }
  }
  return id;
}

// Resolve a short hop hash to a full node ID by prefix match,
// or return the short hash itself as its own node ID.
function resolveHop(shortHash) {
  if (!shortHash || shortHash.length < 2) return null;
  const prefix = shortHash.toUpperCase();
  const matches = [];
  for (const [id, node] of nodes) {
    if (id.length > 6 && id.startsWith(prefix)) {
      const mode = node.mode?.toLowerCase();
      if (!mode || mode === 'repeater') matches.push(id);
    }
  }
  return matches.length === 1 ? matches[0] : null;
}

// ── Helpers ───────────────────────────────────────────────────────────────────
// Strip the flood/direct path and return a 0-hop packet the decoder can handle.
// The decoder treats pathLenByte as a raw byte count; we correct for the actual
// hop_count × bytes_per_hop encoding used by MeshCore firmware.
function stripPathForDecoder(rawHex) {
  const bytes = Buffer.from(rawHex, 'hex');
  const routeType  = bytes[0] & 0x03;
  // TRANSPORT_DIRECT (0x03) has 4 transport-code bytes before the path; DIRECT (0x02) doesn't
  const pathOffset = routeType === 0x03 ? 5 : 1;
  const pathLenByte  = bytes[pathOffset];
  const hopCount     = pathLenByte & 0x3F;
  const bytesPerHop  = (pathLenByte >> 6) + 1;
  const payloadStart = pathOffset + 1 + hopCount * bytesPerHop;
  // Preserve the full prefix (header + transport codes if any), zero out the path count
  return Buffer.concat([bytes.slice(0, pathOffset), Buffer.from([0x00]), bytes.slice(payloadStart)]).toString('hex');
}

// ── Trace path SNR parser ─────────────────────────────────────────────────────
// For TRACE packets the path bytes are signed int8 SNR values (units: 0.25 dB),
// one per hop. Returns an array of SNR values in dB, or [] if not applicable.
function parseTraceSNRs(rawHex) {
  if (!rawHex || rawHex.length < 4) return [];
  const bytes = Buffer.from(rawHex, 'hex');
  const routeType = bytes[0] & 0x03;
  // TRANSPORT_DIRECT (0x03) has 4 transport-code bytes before the path; DIRECT (0x02) doesn't
  const pathOffset = routeType === 0x03 ? 5 : 1;
  const pathLenByte = bytes[pathOffset];
  const hopCount    = pathLenByte & 0x3F;
  const bytesPerHop = (pathLenByte >> 6) + 1;
  if (hopCount === 0 || pathOffset + 1 + hopCount * bytesPerHop > bytes.length) return [];
  const snrs = [];
  for (let i = 0; i < hopCount; i++) {
    const offset = pathOffset + 1 + i * bytesPerHop;
    const raw    = bytes[offset];
    const signed = raw > 127 ? raw - 256 : raw;
    snrs.push(signed / 4.0);
  }
  return snrs;
}

// ── Flood path parser ─────────────────────────────────────────────────────────
// Correctly interprets pathLenByte: bits 0-5 = hop_count, bits 6-7 = bytes_per_hop - 1
// Returns array of uppercase hex hop IDs, or null if not a flood packet.
function parseFloodPath(rawHex) {
  if (!rawHex || rawHex.length < 4) return null;
  const bytes = Buffer.from(rawHex, 'hex');
  const routeType = bytes[0] & 0x03;
  // 0x00 = TRANSPORT_FLOOD (4 transport-code bytes before path), 0x01 = FLOOD
  if (routeType !== 0x01 && routeType !== 0x00) return null;
  const pathOffset = routeType === 0x00 ? 5 : 1;

  const pathLenByte = bytes[pathOffset];
  const hopCount    = pathLenByte & 0x3F;
  const bytesPerHop = (pathLenByte >> 6) + 1;
  const pathByteLen = hopCount * bytesPerHop;

  if (hopCount === 0) return [];
  if (pathOffset + 1 + pathByteLen > bytes.length) return null;

  const hops = [];
  for (let i = 0; i < hopCount; i++) {
    const offset = pathOffset + 1 + i * bytesPerHop;
    hops.push(bytes.slice(offset, offset + bytesPerHop).toString('hex').toUpperCase());
  }
  return hops;
}

// ── Merge short-hash node into full-key node when we learn the full key ───────
function mergeShortNode(fullId) {
  const shortIds = [...nodes.keys()].filter(id => id !== fullId && id.length < fullId.length && fullId.startsWith(id));
  for (const shortId of shortIds) {
    const shortNode = nodes.get(shortId);
    nodes.delete(shortId);
    for (const [key, edge] of edges) {
      const hasA = edge.a === shortId;
      const hasB = edge.b === shortId;
      if (!hasA && !hasB) continue;
      edges.delete(key);
      const newA = hasA ? fullId : edge.a;
      const newB = hasB ? fullId : edge.b;
      const [ca, cb] = newA < newB ? [newA, newB] : [newB, newA];
      // preserve direction when renaming
      const flipped = (hasA && edge.a !== ca) || (hasB && edge.b !== ca);
      edges.set(`${ca}:${cb}`, {
        ...edge,
        a: ca, b: cb,
        snrAB: flipped ? edge.snrBA : edge.snrAB,
        snrBA: flipped ? edge.snrAB : edge.snrBA,
      });
    }
    updateNode(fullId, shortNode);
  }
}

const STALE_MS        = 7 * 24 * 60 * 60 * 1000; // 7 days
const NO_ADVERT_MS    = 24 * 60 * 60 * 1000;      // 24 hours

function pruneStale() {
  const cutoff = Date.now() - STALE_MS;
  for (const [id, node] of nodes) {
    if ((node.lastSeen || 0) < cutoff) {
      nodes.delete(id);
      for (const [key, e] of edges) {
        if (e.a === id || e.b === id) edges.delete(key);
      }
    }
  }
  for (const [key, edge] of edges) {
    if ((edge.lastSeen || 0) < cutoff) edges.delete(key);
  }
  const connectedIds = new Set(Array.from(edges.values()).flatMap(e => [e.a, e.b]));
  for (const id of nodes.keys()) {
    if (!connectedIds.has(id)) nodes.delete(id);
  }
  const advertCutoff = Date.now() - NO_ADVERT_MS;
  for (const [id, node] of nodes) {
    if (!node.name && !node.mode && (node.firstSeen || 0) < advertCutoff) nodes.delete(id);
  }
}

// Load persisted state before starting
loadState();
pruneStale();
setInterval(saveState, SAVE_INTERVAL_MS);
setInterval(pruneStale, PRUNE_INTERVAL_MS);
process.on('SIGINT',  () => { saveState(); process.exit(); });
process.on('SIGTERM', () => { saveState(); process.exit(); });

// ── MQTT ──────────────────────────────────────────────────────────────────────
const mqttClient = mqtt.connect(process.env.MQTT_URL, {
  username: process.env.MQTT_USERNAME,
  password: process.env.MQTT_PASSWORD,
});

mqttClient.on('connect', () => {
  console.log('MQTT connected');
  mqttClient.subscribe('meshcore/#');
});

mqttClient.on('message', (topic, payload) => {
  let data;
  try { data = JSON.parse(payload.toString()); } catch { return; }

  const parts   = topic.split('/');
  if (parts.length < 4) return;
  const msgType = parts[parts.length - 1];
  if (!data.origin_id) return;
  const originId = upgradeTo(data.origin_id);

  if (msgType === 'status') {
    const changed = updateNode(originId, {
      name: data.origin, model: data.model,
      firmware: data.firmware_version, radio: data.radio,
      status: data.status, stats: data.stats,
    });
    if (changed) io.emit('graph', getGraphSnapshot());
    return;
  }

  if (msgType !== 'packets') return;

  let changed = updateNode(originId, { name: data.origin });

  const snr  = data.SNR !== 'Unknown' ? data.SNR : null;
  const packetType = data.packet_type;

  // ── Decode raw packet ────────────────────────────────────────────────────
  if (data.raw) {
    if (packetType === '9') {
      // ── TRACE PATH: path bytes are per-hop SNR values; node IDs are in payload ──
      try {
        const decoded    = MeshCoreDecoder.decode(stripPathForDecoder(data.raw), decryptOpts);
        const trace      = decoded?.payload?.decoded;
        const snrValues  = parseTraceSNRs(data.raw);

        if (trace?.isValid && trace.pathHashes?.length > 0) {
          // flags bits 0-1 = path_sz; bytesPerHop = 1 << path_sz (firmware spec v1.11+)
          const bph = 1 << (trace.flags & 0x03);
          const groupedHashes = [];
          for (let i = 0; i + bph <= trace.pathHashes.length; i += bph) {
            groupedHashes.push(trace.pathHashes.slice(i, i + bph).join(''));
          }
          const resolvedHops = groupedHashes.map(h => resolveHop(h));

          const routeType = Buffer.from(data.raw, 'hex')[0] & 0x03;
          const isDirect  = routeType === 0x02 || routeType === 0x03;

          const chain = isDirect
            ? [originId, ...resolvedHops, originId]
            : [...resolvedHops, originId];

          for (let i = 0; i < chain.length - 1; i++) {
            const isFirst = i === 0;
            const isLast  = i === chain.length - 2;
            // For DIRECT traces, skip the endpoint hops (originId ↔ first/last relay).
            // Any node that overhears the final relay's broadcast gets the fully-accumulated
            // packet and looks like the true initiator. Those links are captured by FLOOD.
            if (isDirect && (isFirst || isLast)) continue;
            if (!chain[i] || !chain[i + 1]) continue;
            const edgeSnr = isLast ? (snr ?? snrValues[i] ?? null) : (snrValues[i] ?? null);
            if (edgeSnr != null) {
              changed = updateNode(chain[i], {}) || changed;
              changed = updateNode(chain[i + 1], {}) || changed;
              changed = recordLink(chain[i], chain[i + 1], edgeSnr) || changed;
            }
          }
        }
      } catch {}
    } else {
      // ── FLOOD / TRANSPORT_FLOOD: path bytes are hop IDs ──────────────────────
      const hops = parseFloodPath(data.raw);
      const resolved = hops && hops.length > 0
        ? hops.map(h => resolveHop(h)).filter(Boolean)
        : [];
      if (resolved.length > 0) {
        resolved.forEach(h => { changed = updateNode(h, {}) || changed; });
        for (let i = 0; i < resolved.length - 1; i++) {
          changed = recordLink(resolved[i], resolved[i + 1], null) || changed;
        }
        // Last hop → observer: proven direct RF link with SNR
        changed = recordLink(resolved[resolved.length - 1], originId, snr) || changed;
      }

      // ADVERT: use meshcore-decoder for name/mode/location.
      if (packetType === '4') {
        let senderId = null;

        try {
          const decoded = MeshCoreDecoder.decode(stripPathForDecoder(data.raw), decryptOpts);
          const adv     = decoded?.payload?.decoded;

          if (adv?.isValid) {
            senderId = adv.publicKey?.toUpperCase() || null;
            if (senderId) {
              mergeShortNode(senderId);
              changed = updateNode(senderId, {
                name: adv.appData?.name,
                mode: adv.appData?.deviceRole != null ? Utils.getDeviceRoleName(adv.appData.deviceRole) : undefined,
                lat:  adv.appData?.location?.latitude,
                lon:  adv.appData?.location?.longitude,
              }) || changed;
            }
          }
        } catch {}

        // Link originator to the rest of the path
        if (senderId) {
          // Re-resolve hops after mergeShortNode — a hop may have been merged into senderId
          const firstHop = hops && hops.length > 0
            ? hops.map(h => resolveHop(h)).find(h => h && h !== senderId)
            : null;
          changed = recordLink(senderId, firstHop ?? originId, firstHop ? null : snr) || changed;
        }
      }
    }
  }

  if (changed) io.emit('graph', getGraphSnapshot());
});

mqttClient.on('error', err => console.error('MQTT error:', err.message));

// ── HTTP ──────────────────────────────────────────────────────────────────────
app.get('/api/graph', (_req, res) => res.json(getGraphSnapshot()));
io.on('connection', socket => socket.emit('graph', getGraphSnapshot()));

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => console.log(`Listening on port ${PORT}`));
