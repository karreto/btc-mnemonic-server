'use strict';
const express  = require('express');
const https    = require('https');
const fs       = require('fs');
const path     = require('path');
const crypto   = require('crypto');
const { Worker, isMainThread, parentPort, workerData } = require('worker_threads');

// ─── WORKER THREAD (corre en thread separado, no bloquea Express) ─────────────
if (!isMainThread) {
  // Este bloque corre solo cuando se lanza como Worker
  const C = workerData;

  const P  = BigInt('0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F');
  const N  = BigInt('0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141');
  const Gx = BigInt('0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798');
  const Gy = BigInt('0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8');

  function mod(a,m){m=m||P;return((a%m)+m)%m;}
  function modInv(a,m){m=m||P;let r=a,nr=m,s=1n,ns=0n;while(nr!==0n){const q=r/nr;[r,nr]=[nr,r-q*nr];[s,ns]=[ns,s-q*ns];}return mod(s,m);}
  function pointAdd(p1,p2){if(!p1)return p2;if(!p2)return p1;const[x1,y1]=p1,[x2,y2]=p2;if(x1===x2&&y1===y2){const s=mod(3n*x1*x1*modInv(2n*y1));const x3=mod(s*s-2n*x1);return[x3,mod(s*(x1-x3)-y1)];}if(x1===x2)return null;const s=mod((y2-y1)*modInv(mod(x2-x1)));const x3=mod(s*s-x1-x2);return[x3,mod(s*(x1-x3)-y1)];}
  function pointMul(k,point){let r=null,a=point;k=mod(k,N);while(k>0n){if(k&1n)r=pointAdd(r,a);a=pointAdd(a,a);k>>=1n;}return r;}
  function hexToBytes(h){const b=new Uint8Array(h.length/2);for(let i=0;i<h.length;i+=2)b[i/2]=parseInt(h.substr(i,2),16);return b;}
  function privToPub(priv){let k=0n;for(const b of priv)k=(k<<8n)|BigInt(b);const pt=pointMul(k,[Gx,Gy]);const xH=pt[0].toString(16).padStart(64,'0');return hexToBytes((pt[1]%2n===0n?'02':'03')+xH);}
  function sha256(data){return crypto.createHash('sha256').update(data).digest();}
  function hmac512(key,data){return crypto.createHmac('sha512',Buffer.from(key)).update(Buffer.from(data)).digest();}
  function hash160(data){return crypto.createHash('ripemd160').update(sha256(data)).digest();}
  function generateMnemonic(wordlist){const e=crypto.randomBytes(16),h=sha256(e);let bits='';for(const b of e)bits+=b.toString(2).padStart(8,'0');bits+=h[0].toString(2).padStart(8,'0').slice(0,4);const w=[];for(let i=0;i<bits.length;i+=11)w.push(wordlist[parseInt(bits.slice(i,i+11),2)]);return w.join(' ');}
  function mnemonicToSeed(m){return crypto.pbkdf2Sync(m,'mnemonic',2048,64,'sha512');}
  function deriveBIP32(seed,path){let I=hmac512(Buffer.from('Bitcoin seed'),seed),key=I.slice(0,32),chain=I.slice(32,64);for(const seg of path.replace('m/','').split('/')){const hard=seg.endsWith("'");let idx=parseInt(seg.replace("'",''),10);if(hard)idx+=0x80000000;const data=Buffer.alloc(37);if(hard){data[0]=0;Buffer.from(key).copy(data,1);}else{Buffer.from(privToPub(key)).copy(data,0);}data[33]=(idx>>>24)&0xff;data[34]=(idx>>>16)&0xff;data[35]=(idx>>>8)&0xff;data[36]=idx&0xff;const I2=hmac512(chain,data),IL=I2.slice(0,32),IR=I2.slice(32,64);let pk=0n;for(const b of key)pk=(pk<<8n)|BigInt(b);let ck=0n;for(const b of IL)ck=(ck<<8n)|BigInt(b);ck=(pk+ck)%N;key=hexToBytes(ck.toString(16).padStart(64,'0'));chain=IR;}return key;}
  const B58='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
  function base58Check(payload,ver){const v=Buffer.alloc(1+payload.length);v[0]=ver;Buffer.from(payload).copy(v,1);const cs=sha256(sha256(v)).slice(0,4),full=Buffer.concat([v,cs]);let n=0n;for(const b of full)n=n*256n+BigInt(b);let s='';while(n>0n){s=B58[Number(n%58n)]+s;n/=58n;}for(const b of full){if(b!==0)break;s='1'+s;}return s;}
  const B32C='qpzry9x8gf2tvdw0s3jn54khce6mua7l';
  function b32poly(v){const G=[0x3b6a57b2,0x26508e6d,0x1ea119fa,0x3d4233dd,0x2a1462b3];let c=1;for(const x of v){const b=c>>>25;c=((c&0x1ffffff)<<5)^x;for(let i=0;i<5;i++)if((b>>>i)&1)c^=G[i];}return c;}
  function b32hrp(h){const r=[];for(let i=0;i<h.length;i++)r.push(h.charCodeAt(i)>>5);r.push(0);for(let i=0;i<h.length;i++)r.push(h.charCodeAt(i)&31);return r;}
  function b32cs(hrp,data,xor){const p=b32poly(b32hrp(hrp).concat(data).concat([0,0,0,0,0,0]))^xor;const r=[];for(let i=0;i<6;i++)r.push((p>>>(5*(5-i)))&31);return r;}
  function cvtBits(data,from,to,pad){let acc=0,bits=0;const r=[],maxv=(1<<to)-1;for(const d of data){acc=(acc<<from)|d;bits+=from;while(bits>=to){bits-=to;r.push((acc>>>bits)&maxv);}}if(pad&&bits>0)r.push((acc<<(to-bits))&maxv);return r;}
  function segwit(h160){const w=[0].concat(cvtBits(Array.from(h160),8,5,true)),c=w.concat(b32cs('bc',w,1));let s='bc1';for(const d of c)s+=B32C[d];return s;}
  function taproot(pub){const x=Array.from(pub.slice(1,33)),w=[1].concat(cvtBits(x,8,5,true)),c=w.concat(b32cs('bc',w,0x2bc830a3));let s='bc1';for(const d of c)s+=B32C[d];return s;}
  function p2sh(h160){const rs=Buffer.alloc(22);rs[0]=0x00;rs[1]=0x14;Buffer.from(h160).copy(rs,2);return base58Check(hash160(rs),0x05);}
  function deriveAddresses(mnemonic){const seed=mnemonicToSeed(mnemonic),list=[],configs=[{bip:84,fn:(h,p)=>segwit(h),type:'P2WPKH'},{bip:44,fn:(h,p)=>base58Check(Buffer.from(h),0x00),type:'P2PKH'},{bip:49,fn:(h,p)=>p2sh(h),type:'P2SH'},{bip:86,fn:(h,p)=>taproot(p),type:'P2TR'}];for(const cfg of configs)for(const change of[0,1])for(let i=0;i<3;i++){const p="m/"+cfg.bip+"'/0'/0'/"+change+"/"+i;try{const priv=deriveBIP32(seed,p),pub=privToPub(priv),h160=hash160(Buffer.from(pub));list.push({address:cfg.fn(h160,pub),path:p,type:cfg.type});}catch(_){}}return list;}

  // Loop infinito en el worker thread
  const wordlist = C.wordlist;
  while (true) {
    try {
      const mnemonic   = generateMnemonic(wordlist);
      const addresses  = deriveAddresses(mnemonic);
      parentPort.postMessage({ mnemonic, addresses });
    } catch(e) {
      // ignorar errores individuales
    }
  }
}

// ─── MAIN THREAD ──────────────────────────────────────────────────────────────
const app          = express();
const PORT         = process.env.PORT || 3000;
const FOUND_FILE   = path.join(__dirname, 'found.json');
const DASHBOARD    = path.join(__dirname, 'public', 'dashboard.html');
const WORDS_URL    = 'https://raw.githubusercontent.com/bitcoin/bips/master/bip-0039/english.txt';

let WORDLIST     = [];
let running      = false;
let findings     = [];
let lastMnemonic = '';
let lastAddress  = '';
let cooldownUntil = 0;
let workers      = [];
const stats = { generated: 0, checked: 0, withTx: 0, startedAt: null };

if (fs.existsSync(FOUND_FILE)) {
  try { findings = JSON.parse(fs.readFileSync(FOUND_FILE, 'utf8')); } catch(_) {}
}

// ─── HTTPS GET helper ─────────────────────────────────────────────────────────
function httpsGet(url) {
  return new Promise((resolve, reject) => {
    const req = https.get(url, { headers: { 'User-Agent': 'Mozilla/5.0' } }, res => {
      let data = '';
      res.on('data', c => data += c);
      res.on('end', () => {
        if (res.statusCode === 429 || res.statusCode === 503) return reject(new Error('HTTP ' + res.statusCode));
        try { resolve(JSON.parse(data)); } catch(_) { reject(new Error('JSON error')); }
      });
    });
    req.setTimeout(15000, () => { req.destroy(); reject(new Error('timeout')); });
    req.on('error', reject);
  });
}

// ─── Verificar batch ──────────────────────────────────────────────────────────
async function checkBatch(addresses) {
  const batch  = addresses.slice(0, 20).join('|');
  const reqId  = Date.now() + '-' + Math.random().toString(36).substr(2, 6);
  const url    = 'https://blockchain.info/balance?active=' + batch + '&cors=true&_r=' + reqId;
  const data   = await httpsGet(url);
  for (const [addr, info] of Object.entries(data)) {
    if (info && (info.n_tx > 0 || info.final_balance > 0)) {
      return { found: true, address: addr, balance: info.final_balance || 0, received: info.total_received || 0, tx_count: info.n_tx || 0 };
    }
  }
  return { found: false };
}

// ─── Recibir resultado de worker thread y verificar ───────────────────────────
async function handleWorkerResult(mnemonic, addresses) {
  if (!running || Date.now() < cooldownUntil) return;
  lastMnemonic = mnemonic;
  lastAddress  = addresses[0] ? addresses[0].address : '';
  stats.generated++;
  try {
    const result = await checkBatch(addresses.map(a => a.address));
    stats.checked++;
    if (result.found) {
      const hit = {
        mnemonic, address: result.address,
        balance:  (result.balance  / 1e8).toFixed(8) + ' BTC',
        received: (result.received / 1e8).toFixed(8) + ' BTC',
        tx_count: result.tx_count,
        path:     (addresses.find(a => a.address === result.address) || {}).path || '?',
        type:     (addresses.find(a => a.address === result.address) || {}).type || '?',
        foundAt:  new Date().toISOString(),
      };
      findings.unshift(hit);
      fs.writeFileSync(FOUND_FILE, JSON.stringify(findings, null, 2));
      stats.withTx++;
      console.log('HIT! ' + hit.address + ' | ' + hit.balance);
    }
  } catch(err) {
    if (err.message.includes('429') || err.message.includes('503')) {
      cooldownUntil = Date.now() + 3 * 60 * 1000;
      console.log('Rate limit cooldown 3min');
    }
  }
}

// ─── Iniciar / Detener ────────────────────────────────────────────────────────
function startSearch() {
  if (running || WORDLIST.length === 0) return;
  running = true;
  stats.startedAt = new Date().toISOString();
  // Lanzar 2 worker threads — cada uno corre cripto en su propio thread
  for (let i = 0; i < 2; i++) {
    const w = new Worker(__filename, { workerData: { wordlist: WORDLIST } });
    w.on('message', ({ mnemonic, addresses }) => handleWorkerResult(mnemonic, addresses));
    w.on('error', err => console.error('Worker error:', err.message));
    workers.push(w);
  }
  console.log('Busqueda iniciada con ' + workers.length + ' workers');
}

function stopSearch() {
  running = false;
  workers.forEach(w => w.terminate());
  workers = [];
  console.log('Busqueda detenida');
}

// ─── Express routes ───────────────────────────────────────────────────────────
app.use((req, res, next) => { res.setHeader('Access-Control-Allow-Origin', '*'); next(); });
app.get('/api/status',  (req, res) => res.json({ running, stats, lastMnemonic, lastAddress, findings: findings.slice(0, 100), cooldownUntil, uptime: process.uptime() }));
app.get('/api/start',   (req, res) => { startSearch(); res.json({ ok: true, running }); });
app.get('/api/stop',    (req, res) => { stopSearch();  res.json({ ok: true, running }); });
app.get('/api/clear',   (req, res) => { findings = []; fs.writeFileSync(FOUND_FILE, '[]'); res.json({ ok: true }); });
app.get('/',            (req, res) => res.sendFile(DASHBOARD));
app.get('/dashboard',   (req, res) => res.sendFile(DASHBOARD));

// ─── Arrancar servidor ────────────────────────────────────────────────────────
app.listen(PORT, '0.0.0.0', () => {
  console.log('Server listening on port ' + PORT);
  // Cargar wordlist y arrancar búsqueda
  https.get(WORDS_URL, { headers: { 'User-Agent': 'Node.js' } }, r => {
    let txt = '';
    r.on('data', c => txt += c);
    r.on('end', () => {
      WORDLIST = txt.trim().split('\n').map(w => w.trim());
      console.log('Wordlist: ' + WORDLIST.length + ' palabras');
      startSearch();
    });
  }).on('error', err => console.error('Error wordlist:', err.message));
});

process.on('uncaughtException',  err => console.error('Uncaught:',  err.message));
process.on('unhandledRejection', err => console.error('Unhandled:', err && err.message));
