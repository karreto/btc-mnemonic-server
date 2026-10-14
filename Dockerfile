FROM node:20-alpine
WORKDIR /app
COPY package.json .
COPY index.js .
COPY public ./public
RUN echo "[]" > /app/found.json
ENV PORT=3000
EXPOSE 3000
CMD ["node", "index.js"]
