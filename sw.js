// Service worker GEP : l'appli s'ouvre même sans réseau, et les cartes déjà vues restent en mémoire.
const APP = 'gep-app-v6';
const TILES = 'gep-tuiles-v1';
const SHELL = ['./', 'index.html', 'style.css?v=6', 'app.js?v=6', 'manifest.webmanifest', 'vendor/leaflet.js', 'vendor/leaflet.css', 'vendor/qrcode.js', 'icons/icon.svg', 'icons/icon-192.png'];

self.addEventListener('install', (e) => { e.waitUntil(caches.open(APP).then((c) => c.addAll(SHELL))); self.skipWaiting(); });
self.addEventListener('activate', (e) => {
  e.waitUntil(caches.keys().then((ks) => Promise.all(ks.filter((k) => k !== APP && k !== TILES).map((k) => caches.delete(k)))));
  self.clients.claim();
});
self.addEventListener('fetch', (e) => {
  const req = e.request; if (req.method !== 'GET') return;
  const url = new URL(req.url);
  // fichiers de l'appli : réseau d'abord (mises à jour), mémoire si pas de réseau
  if (url.origin === location.origin) {
    e.respondWith(fetch(req).then((r) => { const c = r.clone(); caches.open(APP).then((x) => x.put(req, c)); return r; }).catch(() => caches.match(req).then((r) => r || caches.match('index.html'))));
    return;
  }
  // tuiles de carte IGN : mémoire d'abord, limitée à environ 3000 tuiles
  if (url.hostname === 'data.geopf.fr' && url.searchParams.get('REQUEST') === 'GetTile') {
    e.respondWith(caches.open(TILES).then(async (c) => {
      const hit = await c.match(req); if (hit) return hit;
      const r = await fetch(req); if (r.ok) { c.put(req, r.clone()); c.keys().then((ks) => { if (ks.length > 3000) ks.slice(0, 300).forEach((k) => c.delete(k)); }); }
      return r;
    }).catch(() => fetch(req)));
  }
});
