FROM node:24-alpine

WORKDIR /app

COPY package*.json ./
RUN npm ci --omit=dev

COPY server.js ./
COPY public/ ./public/

RUN mkdir -p data

EXPOSE 3000

CMD ["node", "server.js"]
