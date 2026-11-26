/* GEP Itinéraires — Guidage Expert Pilotage
 * Appli web (PWA) d'itinéraires pour convois exceptionnels.
 * Données publiques : Géoplateforme IGN (réseaux TE, franchissements, prescriptions,
 * itinéraire, altitude, géocodage), geo.api.gouv.fr (communes), OpenStreetMap (hauteurs/tonnages).
 * Tout est stocké sur l'appareil (localStorage). Aucun compte, aucun serveur à nous.
 */
'use strict';

// ---------------------------------------------------------------- constantes
const GPF = 'https://data.geopf.fr';
const WFS_URL = GPF + '/wfs/ows';
const OVERPASSES = ['https://overpass-api.de/api/interpreter', 'https://overpass.private.coffee/api/interpreter', 'https://maps.mail.ru/osm/tools/overpass/api/interpreter'];
const NETS = [
  { id: '1TE', label: '1TE (réseau historique 1re cat.)', layer: 'SECUROUTE.TE.1TE', style: 'RESEAU ROUTIER 1TE', color: '#2E7DD7' },
  { id: '2TE48', label: '2TE48 (2e cat. moins de 48 t)', layer: 'SECUROUTE.TE.2TE48', style: 'RESEAU ROUTIER 2TE48', color: '#1E8E3E' },
  { id: 'TE72', label: 'TE72 (moins de 72 t)', layer: 'SECUROUTE.TE.TE72', style: 'RESEAU ROUTIER TE72', color: '#C9A300' },
  { id: 'TE94', label: 'TE94 (moins de 94 t)', layer: 'SECUROUTE.TE.TE94', style: 'RESEAU ROUTIER TE94', color: '#E37400' },
  { id: 'TE120', label: 'TE120 (moins de 120 t)', layer: 'SECUROUTE.TE.TE120', style: 'RESEAU ROUTIER TE120', color: '#D93025' },
];
const CROSS_LAYERS = [
  { id: 'OA', label: 'Ouvrages d’art', layer: 'SECUROUTE.TE.OA', style: 'AUTRES FRANCHISSEMENTS' },
  { id: 'PN', label: 'Passages à niveau', layer: 'SECUROUTE.TE.PN', style: 'FRANCHISSEMENTS PASSAGE A NIVEAU' },
  { id: 'PND', label: 'Passages à niveau difficiles', layer: 'SECUROUTE.TE.PND', style: 'FRANCHISSEMENTS PASSAGE A NIVEAU DIFFICILE' },
];
// Vitesses maximales par catégorie (arrêté du 4 mai 2006, rappel DREAL Hauts-de-France)
const SPEEDS = {
  1: { autoroute: 80, route: 60, prioritaire: 70, agglo: 50 },
  2: { autoroute: 80, route: 60, prioritaire: 70, agglo: 40 },
  3: { autoroute: 60, route: 50, prioritaire: 50, agglo: 30 },
};
const TIME_RE = /heure|horaire|\b\d{1,2}\s?h\s?\d{0,2}\b|pointe|nuit|week-?end|samedi|dimanche|f[ée]ri[ée]|vendredi|matin|soir/i;

// ---------------------------------------------------------------- état
const DEFAULT = {
  profile: { longueur: 25, largeur: 3.5, hauteur: 4.2, poids: 60, essieux: 6, marge: 0.10, speedsOverride: null },
  settings: { base: 'plan', nets: ['TE72', 'TE94', 'TE120'], cross: ['OA', 'PND'], aimantNets: ['2TE48', 'TE72', 'TE94', 'TE120'], voice: true, osm: true },
  routes: [], folders: ['Général'], obstacles: [], restrictions: [], reports: [],
};
let DB = load();
let cur = newRoute();
let legs = [];            // résultat calculé de chaque tronçon entre deux points
let full = null;          // { coords, cum, steps, dist, dur }
let analysis = null;      // résultat de l'analyse le long du tracé
let drawMode = false;
let calcVersion = 0;
const legCache = new Map();
const wfsCache = new Map();

function load() {
  try {
    const d = JSON.parse(localStorage.getItem('gep.v1'));
    if (d) return Object.assign(structuredClone(DEFAULT), d, {
      profile: Object.assign({}, DEFAULT.profile, d.profile || {}),
      settings: Object.assign({}, DEFAULT.settings, d.settings || {}),
    });
  } catch (e) { /* données illisibles : on repart à zéro */ }
  return structuredClone(DEFAULT);
}
function save() {
  try { localStorage.setItem('gep.v1', JSON.stringify(DB)); }
  catch (e) { toast('Mémoire de l’appareil pleine : exportez une sauvegarde puis supprimez de vieux itinéraires.'); }
}
function newRoute() {
  return { id: 'r' + Date.now().toString(36), name: '', folder: 'Général', waypoints: [], modes: [], track: null, created: Date.now(), updated: Date.now() };
}

// ---------------------------------------------------------------- outils
const $ = (s, el = document) => el.querySelector(s);
const $$ = (s, el = document) => [...el.querySelectorAll(s)];
const esc = (s) => String(s ?? '').replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const R = 6371008.8;
const rad = (d) => d * Math.PI / 180;
function dist(a, b) { // a, b = [lat, lng] ; mètres
  const dLat = rad(b[0] - a[0]), dLng = rad(b[1] - a[1]);
  const h = Math.sin(dLat / 2) ** 2 + Math.cos(rad(a[0])) * Math.cos(rad(b[0])) * Math.sin(dLng / 2) ** 2;
  return 2 * R * Math.asin(Math.min(1, Math.sqrt(h)));
}
function bearing(a, b) {
  const y = Math.sin(rad(b[1] - a[1])) * Math.cos(rad(b[0]));
  const x = Math.cos(rad(a[0])) * Math.sin(rad(b[0])) - Math.sin(rad(a[0])) * Math.cos(rad(b[0])) * Math.cos(rad(b[1] - a[1]));
  return (Math.atan2(y, x) * 180 / Math.PI + 360) % 360;
}
// distance d'un point p au segment [a,b] (en mètres, approximation locale) + position t
function segDist(p, a, b) {
  const k = Math.cos(rad(p[0])) * 111320, m = 110540;
  const ax = (a[1] - p[1]) * k, ay = (a[0] - p[0]) * m, bx = (b[1] - p[1]) * k, by = (b[0] - p[0]) * m;
  const dx = bx - ax, dy = by - ay, L = dx * dx + dy * dy;
  let t = L ? -(ax * dx + ay * dy) / L : 0; t = Math.max(0, Math.min(1, t));
  const x = ax + t * dx, y = ay + t * dy;
  return { d: Math.hypot(x, y), t };
}
function cumul(coords) { const c = [0]; for (let i = 1; i < coords.length; i++) c.push(c[i - 1] + dist(coords[i - 1], coords[i])); return c; }
const km = (m) => (m / 1000).toLocaleString('fr-FR', { maximumFractionDigits: m < 10000 ? 1 : 0 }) + ' km';
const meters = (m) => m < 1000 ? Math.round(m / 10) * 10 + ' m' : km(m);
const hm = (s) => { const h = Math.floor(s / 3600), mn = Math.round((s % 3600) / 60); return h ? `${h} h ${String(mn).padStart(2, '0')}` : `${mn} min`; };
const num = (v) => { const n = parseFloat(String(v ?? '').replace(',', '.')); return isFinite(n) ? n : null; };
const fmtM = (v) => v == null ? '?' : v.toLocaleString('fr-FR', { minimumFractionDigits: 2, maximumFractionDigits: 2 }) + ' m';
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
async function pool(items, n, fn) {
  const out = new Array(items.length); let i = 0;
  await Promise.all(Array.from({ length: Math.min(n, items.length) }, async () => { while (i < items.length) { const k = i++; out[k] = await fn(items[k], k); } }));
  return out;
}
async function getJSON(url, opts = {}, tries = 2) {
  for (let t = 0; t <= tries; t++) {
    try {
      const ctl = new AbortController(); const timer = setTimeout(() => ctl.abort(), opts.timeout || 30000);
      const r = await fetch(url, { ...opts, signal: ctl.signal }); clearTimeout(timer);
      if (r.status === 429 || r.status >= 500) throw new Error('HTTP ' + r.status);
      if (!r.ok) { const tx = await r.text(); throw new Error('HTTP ' + r.status + ' ' + tx.slice(0, 200)); }
      return await r.json();
    } catch (e) { if (t === tries) throw e; await sleep(800 * (t + 1)); }
  }
}
let toastTimer;
function toast(msg, ms = 3500) { const t = $('#toast'); t.textContent = msg; t.hidden = false; clearTimeout(toastTimer); toastTimer = setTimeout(() => (t.hidden = true), ms); }

// ---------------------------------------------------------------- convoi
function category(p = DB.profile) {
  if (p.longueur > 25 || p.largeur > 4 || p.poids > 72) return 3;
  if (p.longueur > 20 || p.largeur > 3 || p.poids > 48) return 2;
  return 1;
}
function speeds() { return DB.profile.speedsOverride || SPEEDS[category()]; }
function isAutoroute(name) { return /^(A|AUTOROUTE)\s?\d|AUTOROUTE/i.test(name || ''); }

// ---------------------------------------------------------------- carte
const map = L.map('map', { zoomControl: false, preferCanvas: true, attributionControl: false }).setView([46.6, 2.4], 6);
L.control.zoom({ position: 'topright' }).addTo(map);
L.control.attribution({ position: 'topleft', prefix: false }).addTo(map);
if (window.innerWidth >= 760) L.control.scale({ imperial: false, position: 'bottomright' }).addTo(map);
function fitPad() { return window.innerWidth >= 760 ? { padding: [30, 30] } : { paddingTopLeft: [20, 20], paddingBottomRight: [20, $('#sheet').offsetHeight + 20] }; }
const wmts = (layer, style, fmt = 'image/png', tms = 'PM') =>
  `${GPF}/wmts?SERVICE=WMTS&REQUEST=GetTile&VERSION=1.0.0&LAYER=${layer}&STYLE=${encodeURIComponent(style)}&FORMAT=${fmt}&TILEMATRIXSET=${tms}&TILEMATRIX={z}&TILEROW={y}&TILECOL={x}`;
const ATTR = '© <a href="https://www.ign.fr">IGN</a> Géoplateforme · réseaux TE : Sécurité routière / IGN';
const bases = {
  plan: L.tileLayer(wmts('GEOGRAPHICALGRIDSYSTEMS.PLANIGNV2', 'normal'), { maxZoom: 19, maxNativeZoom: 19, attribution: ATTR }),
  photo: L.tileLayer(wmts('ORTHOIMAGERY.ORTHOPHOTOS', 'normal', 'image/jpeg'), { maxZoom: 19, maxNativeZoom: 19, attribution: ATTR }),
  osm: L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png', { maxZoom: 19, attribution: '© contributeurs OpenStreetMap' }),
};
const overlays = {};
for (const n of [...NETS, ...CROSS_LAYERS]) {
  overlays[n.id] = L.tileLayer(wmts(n.layer, n.style, 'image/png', 'PM_7_17'), { minZoom: 7, maxNativeZoom: 17, maxZoom: 19, opacity: 0.85, zIndex: 300 });
}
function applyLayers() {
  Object.entries(bases).forEach(([k, l]) => (k === DB.settings.base ? l.addTo(map) : map.removeLayer(l)));
  Object.entries(overlays).forEach(([k, l]) => ((DB.settings.nets.includes(k) || DB.settings.cross.includes(k)) ? l.addTo(map) : map.removeLayer(l)));
}
applyLayers();

const gRoute = L.layerGroup().addTo(map);     // tracé
const gOff = L.layerGroup().addTo(map);       // parties hors réseau TE
const gObs = L.layerGroup().addTo(map);       // ouvrages le long du tracé
const gMine = L.layerGroup().addTo(map);      // mes mesures et signalements
const gWp = L.layerGroup().addTo(map);        // points de passage
const gZones = L.layerGroup().addTo(map);     // villes avec restriction d'horaire
let meMarker = null;

// ---------------------------------------------------------------- points de passage
function wpIcon(i, n) {
  const cls = i === 0 ? 'start' : (i === n - 1 && n > 1 ? 'end' : '');
  return L.divIcon({ className: '', html: `<div class="wp ${cls}">${i === 0 ? 'D' : (i === n - 1 && n > 1 ? 'A' : i)}</div>`, iconSize: [26, 26], iconAnchor: [13, 13] });
}
function drawWaypoints() {
  gWp.clearLayers();
  const n = cur.waypoints.length;
  cur.waypoints.forEach((w, i) => {
    const m = L.marker([w[0], w[1]], { icon: wpIcon(i, n), draggable: true, autoPan: true }).addTo(gWp);
    m.on('dragend', () => { const p = m.getLatLng(); cur.waypoints[i] = [p.lat, p.lng]; changed(); });
    m.on('click', () => {
      if (!drawMode) return;
      cur.waypoints.splice(i, 1);
      if (cur.modes.length) cur.modes.splice(Math.max(0, i - 1), 1);
      changed();
    });
  });
}
function addWaypoint(latlng) {
  if (cur.track) { toast('Ce tracé est importé ou enregistré : effacez-le pour en dessiner un nouveau.'); return; }
  cur.waypoints.push([+latlng.lat.toFixed(6), +latlng.lng.toFixed(6)]);
  if (cur.waypoints.length > 1) cur.modes.push($('#leg-mode').value);
  changed();
}
map.on('click', (e) => { if (drawMode) addWaypoint(e.latlng); else inspectAt(e.latlng); });
map.on('contextmenu', (e) => addMineDialog(e.latlng));

function setDraw(on) {
  drawMode = on;
  $('#btn-draw').classList.toggle('active', on);
  $('#btn-draw').textContent = on ? '✅ Terminer' : '✏️ Tracer';
  $('#draw-hint').hidden = !on;
  if (on && window.innerWidth < 760) $('#sheet').classList.add('min');
}

let changeTimer;
function changed() {
  cur.updated = Date.now();
  drawWaypoints();
  clearTimeout(changeTimer);
  changeTimer = setTimeout(compute, 350);
}

// ---------------------------------------------------------------- calcul des tronçons
async function compute() {
  const v = ++calcVersion;
  analysis = null; gOff.clearLayers(); gObs.clearLayers();
  if (cur.track) {
    legs = [{ coords: cur.track, steps: [{ along: 0, text: 'Suivez le tracé enregistré', name: '' }], src: 'trace' }];
  } else {
    if (cur.waypoints.length < 2) { legs = []; full = null; renderRoute(); renderTab(); return; }
    setStats('Calcul du tracé…');
    const jobs = [];
    for (let i = 0; i < cur.waypoints.length - 1; i++) jobs.push([cur.waypoints[i], cur.waypoints[i + 1], cur.modes[i] || 'route']);
    try {
      legs = await pool(jobs, 3, ([a, b, mode]) => computeLeg(a, b, mode));
    } catch (e) { console.error(e); setStats('Erreur de calcul : ' + e.message); return; }
    if (v !== calcVersion) return;
  }
  buildFull();
  renderRoute();
  renderTab();
  analyse(v);
}
async function computeLeg(a, b, mode) {
  const key = mode + '|' + a.join(',') + '|' + b.join(',');
  if (legCache.has(key)) return legCache.get(key);
  let leg;
  if (mode === 'droit') leg = { coords: [a, b], steps: [{ along: 0, text: 'Ligne droite jusqu’au point suivant', name: '' }], src: 'droit' };
  else if (mode === 'aimant') leg = await legAimant(a, b);
  else leg = await legIGN(a, b);
  legCache.set(key, leg);
  return leg;
}

// Itinéraire IGN (graphe BD TOPO). Pas de profil poids lourd : c'est une liaison routière simple.
const MOD = { left: 'à gauche', right: 'à droite', 'slight left': 'légèrement à gauche', 'slight right': 'légèrement à droite', 'sharp left': 'franchement à gauche', 'sharp right': 'franchement à droite', straight: 'tout droit', uturn: 'demi-tour' };
function frInstr(ins, name) {
  const t = ins?.type, m = MOD[ins?.modifier] || '';
  const sur = name ? ` sur ${name}` : '';
  switch (t) {
    case 'depart': return `Partez${sur}`;
    case 'arrive': return 'Arrivée au point';
    case 'roundabout': case 'rotary': return `Au rond-point, ${ins.exit ? 'prenez la ' + ins.exit + (ins.exit === 1 ? 're' : 'e') + ' sortie' : 'continuez'}${sur}`;
    case 'merge': return `Insérez-vous${sur}`;
    case 'on ramp': return `Prenez la bretelle${m ? ' ' + m : ''}${sur}`;
    case 'off ramp': return `Sortez${m ? ' ' + m : ''}${sur}`;
    case 'fork': return `À l’embranchement, restez ${m || 'sur la voie'}${sur}`;
    case 'end of road': return `Au bout de la route, tournez ${m}${sur}`;
    case 'new name': case 'continue': return `Continuez${sur}`;
    default: return m ? `Tournez ${m}${sur}` : `Continuez${sur}`;
  }
}
async function legIGN(a, b) {
  const u = `${GPF}/navigation/itineraire?resource=bdtopo-osrm&profile=car&optimization=fastest&start=${a[1]},${a[0]}&end=${b[1]},${b[0]}&geometryFormat=geojson&getSteps=true&getBbox=false`;
  const j = await getJSON(u);
  const coords = j.geometry.coordinates.map((c) => [c[1], c[0]]);
  const steps = []; let along = 0;
  for (const p of j.portions || []) for (const s of p.steps || []) {
    const name = s.attributes?.name || '';
    steps.push({ along, text: frInstr(s.instruction, name), name, type: s.instruction?.type });
    along += s.distance || 0;
  }
  return { coords, steps, src: 'ign' };
}

// Aimant réseau TE : plus court chemin calculé sur les tronçons TE du Géoportail entre deux points proches.
async function wfs(type, cql, props, sortBy, max = 20000) {
  const key = type + '|' + cql + '|' + props;
  if (wfsCache.has(key)) return wfsCache.get(key);
  const count = 5000; let start = 0; const feats = [];
  while (start < max) {
    let u = `${WFS_URL}?SERVICE=WFS&VERSION=2.0.0&REQUEST=GetFeature&outputFormat=application/json&typeNames=SECUROUT.TE:${type}&count=${count}&startIndex=${start}&CQL_FILTER=${encodeURIComponent(cql)}`;
    if (props) u += '&propertyName=' + props;
    if (sortBy) u += '&sortBy=' + sortBy;
    const j = await getJSON(u, { timeout: 45000 });
    const got = (j.features || []).length; feats.push(...(j.features || []));
    const matched = typeof j.numberMatched === 'number' ? j.numberMatched : null;
    if (!got || (matched != null ? start + got >= matched : got < count)) break;
    start += got;
  }
  wfsCache.set(key, feats);
  return feats;
}
const bboxCql = (s, w, n, e) => `BBOX(geometrie,${w.toFixed(5)},${s.toFixed(5)},${e.toFixed(5)},${n.toFixed(5)},'EPSG:4326')`;
const lineCoords = (g) => (g.type === 'MultiLineString' ? g.coordinates : [g.coordinates]).map((l) => l.map((c) => [c[1], c[0]]));

async function legAimant(a, b) {
  const d = dist(a, b);
  if (d > 60000) { toast('Points éloignés de plus de 60 km : liaison par la route. Rapprochez vos points pour coller au réseau TE.', 5000); return legIGN(a, b); }
  const pad = Math.max(0.03, (d / 111000) * 0.3);
  const s = Math.min(a[0], b[0]) - pad, n = Math.max(a[0], b[0]) + pad;
  const padLng = pad / Math.cos(rad((a[0] + b[0]) / 2));
  const w = Math.min(a[1], b[1]) - padLng, e = Math.max(a[1], b[1]) + padLng;
  const nets = DB.settings.aimantNets.length ? DB.settings.aimantNets : NETS.map((x) => x.id);
  const cql = `reseau_te IN (${nets.map((x) => `'${x}'`).join(',')}) AND ${bboxCql(s, w, n, e)}`;
  let feats;
  try { feats = await wfs('troncon_te', cql, 'geometrie,identifiant_te,reseau_te,cpx_numero,nom_voie_ban_droite', 'identifiant_te', 40000); }
  catch (err) { toast('Réseau TE indisponible pour l’instant : liaison par la route.'); return legIGN(a, b); }
  // graphe : nœuds = extrémités des tronçons, + points intérieurs où un autre tronçon se raccorde (jonctions en T)
  const key = (c) => c[0].toFixed(6) + ',' + c[1].toFixed(6);
  const lines = []; const seen = new Set(); const endKeys = new Set();
  for (const f of feats) {
    const idf = f.properties.identifiant_te; if (seen.has(idf)) continue; seen.add(idf);
    const name = f.properties.cpx_numero || f.properties.nom_voie_ban_droite || '';
    for (const line of lineCoords(f.geometry)) if (line.length > 1) { lines.push({ line, name }); endKeys.add(key(line[0])); endKeys.add(key(line[line.length - 1])); }
  }
  const nodes = new Map(); const adj = []; const pts = [];
  const nodeId = (c) => { const k = key(c); let id = nodes.get(k); if (id === undefined) { id = adj.length; nodes.set(k, id); adj.push([]); pts[id] = c; } return id; };
  const addEdge = (line, name) => { const u = nodeId(line[0]), v = nodeId(line[line.length - 1]); const len = cumul(line).pop(); adj[u].push({ to: v, len, line, name }); adj[v].push({ to: u, len, line: line.slice().reverse(), name }); };
  for (const { line, name } of lines) {
    let st = 0;
    for (let i = 1; i < line.length - 1; i++) if (endKeys.has(key(line[i]))) { addEdge(line.slice(st, i + 1), name); st = i; }
    addEdge(line.slice(st), name);
  }
  if (!adj.length) { toast('Pas de réseau TE choisi dans cette zone : liaison par la route.'); return legIGN(a, b); }
  // composantes connexes : le réseau TE a des coupures. On autorise des « ponts » par la route
  // entre morceaux proches (moins de 3 km), pénalisés pour rester sur le réseau le plus possible.
  const comp = new Int32Array(adj.length).fill(-1); let nc = 0;
  for (let i = 0; i < adj.length; i++) { if (comp[i] >= 0) continue; const stack = [i]; comp[i] = nc; while (stack.length) { const x = stack.pop(); for (const ed of adj[x]) if (comp[ed.to] < 0) { comp[ed.to] = nc; stack.push(ed.to); } } nc++; }
  if (nc > 1) {
    // grille de 0,04° (~4 km) pour trouver vite les nœuds proches d'un autre morceau
    const G2 = 0.04, cells = new Map(); const ck = (c) => Math.floor(c[0] / G2) + ':' + Math.floor(c[1] / G2);
    pts.forEach((c, i) => { const k = ck(c); if (!cells.has(k)) cells.set(k, []); cells.get(k).push(i); });
    const done = new Set();
    for (let u = 0; u < adj.length; u++) {
      const [cx, cy] = ck(pts[u]).split(':').map(Number); const best = new Map();
      for (let x = cx - 1; x <= cx + 1; x++) for (let y = cy - 1; y <= cy + 1; y++) for (const v of cells.get(x + ':' + y) || []) {
        if (comp[v] === comp[u]) continue; const dd = dist(pts[u], pts[v]); if (dd > 4000) continue;
        const cur2 = best.get(comp[v]); if (!cur2 || dd < cur2.dd) best.set(comp[v], { v, dd });
      }
      for (const { v, dd } of best.values()) {
        const k2 = u < v ? u + '-' + v : v + '-' + u; if (done.has(k2)) continue; done.add(k2);
        const len = dd * 2.5 + 300; adj[u].push({ to: v, len, gap: true, line: [pts[u], pts[v]], name: '' }); adj[v].push({ to: u, len, gap: true, line: [pts[v], pts[u]], name: '' });
      }
    }
  }
  const nearest = (p) => { let best = -1, bd = Infinity; pts.forEach((q, i) => { const dd = dist(p, q); if (dd < bd) { bd = dd; best = i; } }); return [best, bd]; };
  const [na, da] = nearest(a), [nb, db] = nearest(b);
  if (da > 15000 || db > 15000) { toast('Point à plus de 15 km du réseau TE choisi : liaison par la route.'); return legIGN(a, b); }
  // Dijkstra (tas binaire)
  const N = adj.length, D = new Float64Array(N).fill(Infinity), prev = new Int32Array(N).fill(-1), prevE = new Array(N);
  const heap = [[0, na]]; D[na] = 0;
  const push = (x) => { heap.push(x); let i = heap.length - 1; while (i > 0) { const p = (i - 1) >> 1; if (heap[p][0] <= heap[i][0]) break; [heap[p], heap[i]] = [heap[i], heap[p]]; i = p; } };
  const pop = () => { const top = heap[0]; const last = heap.pop(); if (heap.length) { heap[0] = last; let i = 0; for (;;) { const l = 2 * i + 1, r = l + 1; let m = i; if (l < heap.length && heap[l][0] < heap[m][0]) m = l; if (r < heap.length && heap[r][0] < heap[m][0]) m = r; if (m === i) break; [heap[m], heap[i]] = [heap[i], heap[m]]; i = m; } } return top; };
  while (heap.length) {
    const [du, u] = pop(); if (du > D[u]) continue; if (u === nb) break;
    for (const ed of adj[u]) { const nd = du + ed.len; if (nd < D[ed.to]) { D[ed.to] = nd; prev[ed.to] = u; prevE[ed.to] = ed; push([nd, ed.to]); } }
  }
  if (!isFinite(D[nb])) { toast('Le réseau TE choisi n’est pas continu entre ces points : liaison par la route sur ce morceau.', 5000); return legIGN(a, b); }
  const chain = []; for (let v = nb; v !== na; v = prev[v]) chain.push(prevE[v]); chain.reverse();
  const gaps = chain.filter((e) => e.gap).length;
  if (gaps) toast(`Réseau TE coupé à ${gaps} endroit${gaps > 1 ? 's' : ''} : raccord${gaps > 1 ? 's' : ''} par la route (en rouge dans « Réseau »).`, 5000);
  // raccords : du point de départ vers le réseau, et du réseau vers l'arrivée
  let coords = [], steps = [];
  if (da > 60) { const c = await legIGN(a, pts[na]); coords = c.coords; steps = c.steps.filter((x) => x.type !== 'arrive'); }
  else coords = [a];
  let along = cumul(coords).pop(); let lastName = null, lastBear = null;
  for (const ed of chain) {
    if (ed.gap) { // morceau hors réseau : liaison routière IGN
      let c; try { c = await legIGN(ed.line[0], ed.line[1]); } catch (e) { c = { coords: ed.line, steps: [] }; }
      c.steps.filter((x) => x.type !== 'arrive').forEach((s2) => steps.push({ ...s2, along: along + s2.along }));
      coords.push(...c.coords.slice(1)); along += cumul(c.coords).pop(); lastName = null; const n2 = c.coords.length; if (n2 > 1) lastBear = bearing(c.coords[n2 - 2], c.coords[n2 - 1]);
      continue;
    }
    if (ed.name !== lastName) {
      let txt = lastName === null && !steps.length ? `Partez sur ${ed.name || 'le réseau TE'}` : `Continuez sur ${ed.name || 'le réseau TE'}`;
      if (lastBear != null && ed.line.length > 1) {
        const turn = ((bearing(ed.line[0], ed.line[1]) - lastBear + 540) % 360) - 180;
        if (turn > 35) txt = `Tournez à droite sur ${ed.name || 'la route'}`; else if (turn < -35) txt = `Tournez à gauche sur ${ed.name || 'la route'}`;
      }
      steps.push({ along, text: txt, name: ed.name }); lastName = ed.name;
    }
    coords.push(...ed.line.slice(1)); along += ed.len;
    const L2 = ed.line.length; if (L2 > 1) lastBear = bearing(ed.line[L2 - 2], ed.line[L2 - 1]);
  }
  if (db > 60) { const c = await legIGN(pts[nb], b); c.steps.forEach((s2) => steps.push({ ...s2, along: along + s2.along })); coords.push(...c.coords.slice(1)); }
  else coords.push(b);
  return { coords, steps, src: 'aimant' };
}

function buildFull() {
  const coords = [], steps = []; let offset = 0;
  legs.forEach((lg, i) => {
    const c = i === 0 ? lg.coords : lg.coords.slice(1);
    lg.steps.forEach((s) => { if (s.type === 'arrive' && i < legs.length - 1) return; steps.push({ ...s, along: s.along + offset }); });
    coords.push(...c);
    offset += cumul(lg.coords).pop() || 0;
  });
  const cum = cumul(coords);
  const total = cum[cum.length - 1] || 0;
  // durée estimée aux vitesses de la catégorie du convoi
  const sp = speeds(); let dur = 0;
  steps.forEach((s, i) => { const len = (steps[i + 1]?.along ?? total) - s.along; dur += len / ((isAutoroute(s.name) ? sp.autoroute : sp.route) / 3.6); });
  if (!steps.length) dur = total / (sp.route / 3.6);
  full = { coords, cum, steps, dist: total, dur };
}

function renderRoute() {
  gRoute.clearLayers();
  if (!full || full.coords.length < 2) { setStats(cur.waypoints.length ? 'Ajoutez au moins deux points.' : 'Touchez « Tracer » puis la carte pour poser vos points.'); return; }
  L.polyline(full.coords, { color: '#0E2A47', weight: 9, opacity: 0.35 }).addTo(gRoute);
  L.polyline(full.coords, { color: '#F28C28', weight: 5, opacity: 0.95 }).addTo(gRoute);
  setStats(`${km(full.dist)} · ${hm(full.dur)} à vitesse convoi · ${category()}e cat.`);
}
function setStats(t) { $('#route-stats').textContent = t; }

// ---------------------------------------------------------------- analyse le long du tracé
// Découpe le tracé en morceaux d'environ 12 km pour interroger les données par petites zones.
function chunks(coords, cum, size = 12000) {
  const out = []; let startI = 0;
  for (let i = 1; i < coords.length; i++) {
    if (cum[i] - cum[startI] >= size || i === coords.length - 1) {
      let s = 90, w = 180, n = -90, e = -180;
      for (let k = startI; k <= i; k++) { const c = coords[k]; s = Math.min(s, c[0]); n = Math.max(n, c[0]); w = Math.min(w, c[1]); e = Math.max(e, c[1]); }
      const p = 0.0015; out.push({ i0: startI, i1: i, s: s - p, w: w - p * 1.4, n: n + p, e: e + p * 1.4 });
      startI = i;
    }
  }
  return out;
}
// Position d'un point sur le tracé (distance depuis le départ) si à moins de maxD mètres.
function locate(p, maxD = 25, i0 = 0, i1 = null) {
  const C = full.coords; i1 = i1 ?? C.length - 1;
  let best = null;
  for (let i = Math.max(0, i0); i < Math.min(i1, C.length - 1); i++) {
    const a = C[i], b = C[i + 1];
    if (Math.abs(a[0] - p[0]) > 0.01 && Math.abs(b[0] - p[0]) > 0.01) continue;
    const r = segDist(p, a, b);
    if (r.d <= maxD && (!best || r.d < best.d)) best = { d: r.d, along: full.cum[i] + r.t * (full.cum[i + 1] - full.cum[i]), i };
  }
  return best;
}
function samples(step) { // points réguliers le long du tracé
  const out = []; const C = full.coords, cum = full.cum; let next = 0, i = 0;
  while (next <= full.dist && i < C.length - 1) {
    while (i < C.length - 2 && cum[i + 1] < next) i++;
    const seg = cum[i + 1] - cum[i] || 1, t = Math.max(0, Math.min(1, (next - cum[i]) / seg));
    out.push({ along: next, p: [C[i][0] + t * (C[i + 1][0] - C[i][0]), C[i][1] + t * (C[i + 1][1] - C[i][1])], i });
    next += step;
  }
  out.push({ along: full.dist, p: C[C.length - 1], i: C.length - 2 });
  return out;
}

async function analyse(v) {
  if (!full) return;
  const A = { ouvrages: [], prescriptions: [], reseau: null, profil: null, zones: [], busy: true, errors: [] };
  analysis = A; renderTab();
  const ch = chunks(full.coords, full.cum);
  const tasks = [
    analyseFranchissements(ch).then((r) => { A.ouvrages.push(...r); }).catch((e) => A.errors.push('ouvrages TE : ' + e.message)),
    analyseReseau(ch).then((r) => { A.reseau = r.reseau; A.prescriptions = r.prescriptions; }).catch((e) => A.errors.push('réseau / prescriptions : ' + e.message)),
    DB.settings.osm ? analyseOSM().then((r) => { A.ouvrages.push(...r); }).catch((e) => A.errors.push('OpenStreetMap : ' + e.message)) : null,
    analyseProfil().then((r) => { A.profil = r; }).catch((e) => A.errors.push('altitude : ' + e.message)),
  ].filter(Boolean);
  // mes mesures et signalements, et mes villes à horaires
  for (const o of DB.obstacles) { const loc = locate([o.lat, o.lng], 30); if (loc) A.ouvrages.push(mineToOuvrage(o, loc.along)); }
  for (const z of DB.restrictions) { const hit = zoneOnRoute(z); if (hit) A.zones.push({ z, along: hit.along }); }
  for (const t of tasks) { await t; if (v !== calcVersion) return; dedupeOuvrages(A); renderTab(); drawObstacles(); }
  A.busy = false; dedupeOuvrages(A);
  if (v !== calcVersion) return;
  renderTab(); drawObstacles();
  const nBad = A.ouvrages.filter((o) => o.level === 'bad').length;
  const off = A.reseau ? A.reseau.offKm : 0;
  let msg = `${km(full.dist)} · ${hm(full.dur)} · ${category()}e cat.`;
  if (nBad) msg += ` · ⛔ ${nBad} ouvrage${nBad > 1 ? 's' : ''} bloquant${nBad > 1 ? 's' : ''}`;
  if (off > 0.2) msg += ` · ${off.toFixed(1)} km hors réseau TE`;
  setStats(msg);
}

function judge(o) {
  const p = DB.profile; const reasons = []; let level = 'ok'; let unknown = true;
  const bump = (l) => { if (l === 'bad' || (l === 'warn' && level === 'ok')) level = l; };
  if (o.hauteur != null) { unknown = false; const need = p.hauteur + p.marge; if (need > o.hauteur) { bump('bad'); reasons.push(`hauteur ${fmtM(o.hauteur)} < convoi ${fmtM(p.hauteur)} + marge`); } else if (need > o.hauteur - 0.2) { bump('warn'); reasons.push(`hauteur juste : ${fmtM(o.hauteur)}`); } }
  if (o.largeur != null) { unknown = false; if (p.largeur > o.largeur) { bump('bad'); reasons.push(`largeur ${fmtM(o.largeur)} < convoi ${fmtM(p.largeur)}`); } }
  if (o.longueur != null) { unknown = false; if (p.longueur > o.longueur) { bump('bad'); reasons.push(`longueur max ${o.longueur} m`); } }
  if (o.tonnage != null) { unknown = false; if (p.poids > o.tonnage) { bump('bad'); reasons.push(`tonnage ${o.tonnage} t < convoi ${p.poids} t`); } }
  if (o.difficile) { bump('warn'); reasons.push('passage à niveau à franchissement difficile'); }
  if (o.vigilance) { bump('warn'); }
  o.level = unknown && level === 'ok' && !o.difficile ? 'unknown' : level; o.reasons = reasons; return o;
}

async function analyseFranchissements(ch) {
  const out = [];
  await pool(ch, 3, async (c) => {
    const f = await wfs('franchissement_te', bboxCql(c.s, c.w, c.n, c.e), null, 'identifiant_te', 5000);
    for (const x of f) {
      const g = x.geometry; if (!g) continue;
      const pt = g.type === 'Point' ? [g.coordinates[1], g.coordinates[0]] : [g.coordinates[0][1], g.coordinates[0][0]];
      const loc = locate(pt, 25, c.i0 - 2, c.i1 + 2); if (!loc) continue;
      const p = x.properties;
      out.push(judge({
        id: p.identifiant_te, src: 'Géoportail TE', lat: pt[0], lng: pt[1], along: loc.along,
        nom: p.nom_du_franchissement || p.nature, nature: p.nature, type: p.type_de_franchissement,
        commune: p.nom_commune, gestionnaire: p.gestionnaire_te || p.gestionnaire_du_franchissement,
        hauteur: num(p.restriction_de_hauteur_te), largeur: num(p.restriction_de_largeur_te), longueur: num(p.restriction_de_longueur_te), tonnage: num(p.restriction_de_tonnage_te),
        vigilance: p.vigilance, difficile: p.passage_a_niveau_difficile === true, voie: p.numero_de_la_voie || p.numero_de_la_voie_ferree,
      }));
    }
  });
  return out;
}

async function analyseReseau(ch) {
  // 1) tronçons TE autour du tracé, indexés dans une grille
  const segs = []; const grid = new Map(); const G = 0.002;
  const cell = (la, ln) => Math.floor(la / G) + ':' + Math.floor(ln / G);
  const feats = (await pool(ch, 3, (c) => wfs('troncon_te', bboxCql(c.s, c.w, c.n, c.e), 'geometrie,identifiant_te,reseau_te,cpx_numero,nom_voie_ban_droite,cpx_gestionnaire', 'identifiant_te', 20000))).flat();
  for (const f of feats) {
    for (const line of lineCoords(f.geometry)) for (let i = 0; i < line.length - 1; i++) {
      const a = line[i], b = line[i + 1]; const k = segs.length; segs.push({ a, b, net: f.properties.reseau_te, id: f.properties.identifiant_te, name: f.properties.cpx_numero || f.properties.nom_voie_ban_droite });
      const la0 = Math.floor(Math.min(a[0], b[0]) / G), la1 = Math.floor(Math.max(a[0], b[0]) / G), ln0 = Math.floor(Math.min(a[1], b[1]) / G), ln1 = Math.floor(Math.max(a[1], b[1]) / G);
      for (let x = la0; x <= la1; x++) for (let y = ln0; y <= ln1; y++) { const key = x + ':' + y; if (!grid.has(key)) grid.set(key, []); grid.get(key).push(k); }
    }
  }
  // 2) pour chaque point du tracé tous les 50 m : sur quels réseaux est-on ?
  const S = samples(50); const perNet = {}; NETS.forEach((n) => (perNet[n.id] = 0));
  const tronconAlong = new Map(); let offRuns = []; let run = null; let offM = 0;
  for (const s of S) {
    const nets = new Set();
    const [cx, cy] = cell(s.p[0], s.p[1]).split(':').map(Number);
    for (let x = cx - 1; x <= cx + 1; x++) for (let y = cy - 1; y <= cy + 1; y++) for (const k of grid.get(x + ':' + y) || []) {
      const sg = segs[k]; if (segDist(s.p, sg.a, sg.b).d <= 12) { nets.add(sg.net); if (!tronconAlong.has(sg.id)) tronconAlong.set(sg.id, s.along); }
    }
    nets.forEach((n) => (perNet[n] = (perNet[n] || 0) + 50));
    if (!nets.size) { offM += 50; if (!run) run = { from: s.along, to: s.along, pts: [] }; run.to = s.along; run.pts.push(s.p); }
    else if (run) { offRuns.push(run); run = null; }
  }
  if (run) offRuns.push(run);
  offRuns = offRuns.filter((r) => r.to - r.from >= 100);
  gOff.clearLayers();
  for (const r of offRuns) if (r.pts.length > 1) L.polyline(r.pts, { color: '#D93025', weight: 7, opacity: 0.9, dashArray: '8 6' }).bindPopup(`Hors réseau TE choisi<br>km ${km(r.from)} → ${km(r.to)}`).addTo(gOff);
  // 3) prescriptions liées aux tronçons parcourus
  const ids = [...tronconAlong.keys()];
  const batches = []; for (let i = 0; i < ids.length; i += 120) batches.push(ids.slice(i, i + 120));
  const links = (await pool(batches, 3, (b) => wfs('troncon_te_lien_prescription', `identifiant_troncon_te IN (${b.map((x) => `'${x}'`).join(',')})`, 'identifiant_troncon_te,identifiant_prescription_te', 'identifiant_prescription_te', 20000))).flat();
  const prAlong = new Map();
  for (const l of links) { const p = l.properties; const al = tronconAlong.get(p.identifiant_troncon_te) ?? 0; if (!prAlong.has(p.identifiant_prescription_te) || prAlong.get(p.identifiant_prescription_te) > al) prAlong.set(p.identifiant_prescription_te, al); }
  const prs = await loadPrescriptions([...prAlong.keys()]);
  const prescriptions = prs.map((p) => ({ ...p, along: prAlong.get(p.id) })).sort((a, b) => a.along - b.along);
  return { reseau: { perNet, offRuns, offKm: offM / 1000, total: full.dist }, prescriptions };
}
async function loadPrescriptions(ids) {
  const batches = []; for (let i = 0; i < ids.length; i += 100) batches.push(ids.slice(i, i + 100));
  const res = (await pool(batches, 3, (b) => wfs('prescritpion_te', `identifiant_prescription IN (${b.map((x) => `'${x}'`).join(',')})`,
    'identifiant_prescription,type_de_prescription,gestionnaire_te,numero,prescription,nom_du_fichier,largeur_prescription,hauteur_prescription,date_de_debut_de_validite,date_de_fin_de_validite', 'identifiant_prescription', 5000))).flat();
  return res.map((f) => {
    const p = f.properties;
    const txt = p.prescription || '';
    return {
      id: p.identifiant_prescription, type: p.type_de_prescription, gest: p.gestionnaire_te, numero: p.numero, texte: txt, fichier: p.nom_du_fichier,
      largeur: num(p.largeur_prescription), hauteur: num(p.hauteur_prescription), debut: p.date_de_debut_de_validite, fin: p.date_de_fin_de_validite,
      horaire: TIME_RE.test(txt), plages: parseRanges(txt), dept: (p.identifiant_prescription || '').slice(2, 5),
    };
  });
}
// "de 7h à 9h", "7h30-9h", "entre 16 h 30 et 19 h" → [["07:30","09:00"]]
function parseRanges(t) {
  const out = []; const re = /(\d{1,2})\s?h\s?(\d{2})?\s*(?:à|-|–|et|jusqu'à)\s*(\d{1,2})\s?h\s?(\d{2})?/gi; let m;
  while ((m = re.exec(t))) { const a = +m[1], b = +m[3]; if (a > 24 || b > 24) continue; out.push([`${String(a).padStart(2, '0')}:${m[2] || '00'}`, `${String(b).padStart(2, '0')}:${m[4] || '00'}`]); }
  return out;
}

function parseLen(v) { // valeurs OSM : "4.5", "4,5 m", "14'6\""
  if (!v) return null; const s = String(v).trim();
  const ft = s.match(/^(\d+)'\s*(\d+)?"?$/); if (ft) return +(ft[1] * 0.3048 + (ft[2] || 0) * 0.0254).toFixed(2);
  const n = parseFloat(s.replace(',', '.')); return isFinite(n) ? n : null;
}
async function analyseOSM() {
  const S = samples(150).map((s) => s.p);
  const batches = []; for (let i = 0; i < S.length; i += 220) batches.push(S.slice(Math.max(0, i - 1), i + 220));
  const out = [];
  await pool(batches, 2, async (pts) => {
    const poly = pts.map((p) => `${p[0].toFixed(5)},${p[1].toFixed(5)}`).join(',');
    const q = `[out:json][timeout:60];(way["highway"]["maxheight"](around:20,${poly});node["maxheight"](around:20,${poly});way["highway"]["maxweight"](around:20,${poly});way["highway"]["maxwidth"](around:20,${poly});node["maxwidth"](around:20,${poly});way["highway"]["tunnel"="yes"](around:15,${poly}););out tags geom;`;
    let j = null, lastErr;
    for (const srv of OVERPASSES) { try { j = await getJSON(srv, { method: 'POST', body: 'data=' + encodeURIComponent(q), headers: { 'Content-Type': 'application/x-www-form-urlencoded' }, timeout: 70000 }, 0); break; } catch (e) { lastErr = e; } }
    if (!j) throw lastErr;
    for (const el of j.elements || []) {
      const t = el.tags || {};
      let pt, along;
      if (el.type === 'node') { pt = [el.lat, el.lon]; const loc = locate(pt, 20); if (!loc) continue; along = loc.along; }
      else {
        const g = (el.geometry || []).map((c) => [c.lat, c.lon]); if (g.length < 2) continue;
        // la voie doit suivre le tracé (pas seulement le croiser) : on vérifie à 25 % et 75 % de sa longueur
        const cg = cumul(g), Lw = cg[cg.length - 1]; const at = (f) => { const target = Lw * f; let i = 0; while (i < g.length - 2 && cg[i + 1] < target) i++; const tt = (target - cg[i]) / ((cg[i + 1] - cg[i]) || 1); return [g[i][0] + tt * (g[i + 1][0] - g[i][0]), g[i][1] + tt * (g[i + 1][1] - g[i][1])]; };
        const l1 = locate(at(0.25), 15), l2 = locate(at(0.75), 15); if (!l1 || !l2) continue;
        pt = at(0.5); along = Math.min(l1.along, l2.along);
      }
      const tunnel = t.tunnel === 'yes';
      out.push(judge({
        id: 'osm' + el.type[0] + el.id, src: 'OpenStreetMap', lat: pt[0], lng: pt[1], along,
        nom: t.name || (tunnel ? 'Tunnel' : (t.bridge ? 'Pont' : 'Limitation')) + (t.ref ? ' · ' + t.ref : ''), nature: tunnel ? 'Tunnel' : (t.bridge ? 'Pont (voie portée)' : (el.type === 'node' ? 'Gabarit' : 'Passage limité')),
        hauteur: parseLen(t.maxheight || t['maxheight:physical']), largeur: parseLen(t.maxwidth), tonnage: parseLen(t.maxweight), commune: '',
      }));
    }
  });
  return out;
}
function mineToOuvrage(o, along) {
  return judge({ id: o.id, src: 'Ma mesure (' + (o.source || 'perso') + ', ' + new Date(o.date).toLocaleDateString('fr-FR') + ')', lat: o.lat, lng: o.lng, along, nom: o.nom || o.type, nature: o.type, hauteur: num(o.hauteur), largeur: num(o.largeur), tonnage: num(o.tonnage), note: o.note, mine: true });
}
function dedupeOuvrages(A) {
  A.ouvrages.sort((a, b) => a.along - b.along);
  const out = [];
  for (const o of A.ouvrages) {
    const twin = out.find((x) => Math.abs(x.along - o.along) < 40 && x.src !== o.src && (x.nature === o.nature || o.src === 'OpenStreetMap'));
    if (twin && o.src === 'OpenStreetMap') { // complète la fiche TE avec les cotes OSM manquantes
      ['hauteur', 'largeur', 'tonnage'].forEach((k) => { if (twin[k] == null && o[k] != null) { twin[k] = o[k]; twin.osmFill = true; } }); judge(twin); continue;
    }
    if (out.some((x) => x.id === o.id || (x.src === o.src && x.nom === o.nom && Math.abs(x.along - o.along) < 40))) continue;
    out.push(o);
  }
  A.ouvrages = out;
}
function obsEmoji(o) { return /tunnel/i.test(o.nature) ? '🚇' : /niveau/i.test(o.nature) ? '🚆' : /signal|travaux/i.test(o.nature) ? '⚠️' : '🌉'; }
function drawObstacles() {
  gObs.clearLayers(); if (!analysis) return;
  for (const o of analysis.ouvrages) {
    const cls = o.mine ? 'mine' : o.level === 'bad' ? 'bad' : o.level === 'warn' ? 'warn' : o.level === 'ok' ? 'ok' : '';
    L.marker([o.lat, o.lng], { icon: L.divIcon({ className: '', html: `<div class="obs ${cls}">${obsEmoji(o)}</div>`, iconSize: [24, 24], iconAnchor: [12, 12] }) })
      .bindPopup(ouvragePopup(o)).addTo(gObs);
  }
}
function ouvragePopup(o) {
  return `<h4>${esc(o.nom)}</h4>${esc(o.nature || '')}${o.type ? ' · ' + esc(o.type) : ''}<br>km ${km(o.along)}${o.commune ? ' · ' + esc(o.commune) : ''}
  <br>Hauteur : <b>${fmtM(o.hauteur)}</b> · Largeur : <b>${fmtM(o.largeur)}</b> · Tonnage : <b>${o.tonnage ?? '?'} t</b>
  ${o.reasons?.length ? '<br><b style="color:#D93025">' + esc(o.reasons.join(' · ')) + '</b>' : ''}
  ${o.vigilance ? '<br>Vigilance : ' + esc(o.vigilance) : ''}${o.note ? '<br>Note : ' + esc(o.note) : ''}
  <br><span class="small">Source : ${esc(o.src)}${o.osmFill ? ' + OpenStreetMap' : ''}</span>`;
}

async function analyseProfil() {
  const n = Math.min(200, Math.max(20, Math.round(full.dist / 250)));
  const step = full.dist / n; const S = samples(step);
  const batches = []; for (let i = 0; i < S.length; i += 100) batches.push(S.slice(i, i + 100));
  const zs = (await pool(batches, 2, async (b) => {
    const u = `${GPF}/altimetrie/1.0/calcul/alti/rest/elevation.json?lon=${b.map((s) => s.p[1].toFixed(5)).join('|')}&lat=${b.map((s) => s.p[0].toFixed(5)).join('|')}&resource=ign_rge_alti_wld&zonly=true`;
    const j = await getJSON(u); return j.elevations.map((e) => (typeof e === 'number' ? e : e.z));
  })).flat();
  const pts = S.map((s, i) => ({ along: s.along, z: zs[i] > -1000 ? zs[i] : null })).filter((p) => p.z != null);
  let up = 0, down = 0, maxUp = 0, maxDown = 0, maxUpAt = 0, maxDownAt = 0;
  for (let i = 1; i < pts.length; i++) {
    const dz = pts[i].z - pts[i - 1].z, dx = pts[i].along - pts[i - 1].along; if (dz > 0) up += dz; else down -= dz;
    if (dx > 50) { const g = dz / dx * 100; if (g > maxUp) { maxUp = g; maxUpAt = pts[i].along; } if (-g > maxDown) { maxDown = -g; maxDownAt = pts[i].along; } }
  }
  return { pts, up, down, maxUp, maxDown, maxUpAt, maxDownAt };
}

// ---------------------------------------------------------------- restrictions d'horaire (villes)
function inRing(p, ring) { let ins = false; for (let i = 0, j = ring.length - 1; i < ring.length; j = i++) { const xi = ring[i][0], yi = ring[i][1], xj = ring[j][0], yj = ring[j][1]; if (((yi > p[0]) !== (yj > p[0])) && (p[1] < (xj - xi) * (p[0] - yi) / (yj - yi) + xi)) ins = !ins; } return ins; }
function inGeom(p, g) { // p = [lat,lng], g = GeoJSON Polygon/MultiPolygon (lng,lat)
  if (!g) return false; const polys = g.type === 'Polygon' ? [g.coordinates] : g.coordinates;
  return polys.some((poly) => inRing(p, poly[0]) && !poly.slice(1).some((h) => inRing(p, h)));
}
function zoneOnRoute(z) { if (!full) return null; for (const s of samples(200)) if (inGeom(s.p, z.contour)) return { along: s.along }; return null; }
const DAYS = ['lun', 'mar', 'mer', 'jeu', 'ven', 'sam', 'dim'];
function zoneStatus(z, when = new Date()) { // 'active' | 'soon' (dans 30 min) | null
  const day = (when.getDay() + 6) % 7; if (z.days?.length && !z.days.includes(day)) return null;
  const mins = when.getHours() * 60 + when.getMinutes();
  for (const [a, b] of z.ranges || []) {
    const [ah, am] = a.split(':').map(Number), [bh, bm] = b.split(':').map(Number); const s = ah * 60 + am, e = bh * 60 + bm;
    if (mins >= s && mins < e) return { st: 'active', range: `${a}–${b}` };
    if (s - mins > 0 && s - mins <= 30) return { st: 'soon', range: `${a}–${b}` };
  }
  return null;
}
function drawZones() {
  gZones.clearLayers();
  for (const z of DB.restrictions) if (z.contour) L.geoJSON(z.contour, { style: { color: '#7B1FA2', weight: 2, fillOpacity: 0.08, dashArray: '4 4' } })
    .bindPopup(`<h4>🕒 ${esc(z.commune)}</h4>${esc(z.days?.length ? z.days.map((d) => DAYS[d]).join(', ') : 'tous les jours')}<br>${esc((z.ranges || []).map((r) => r.join('–')).join(' · ') || 'horaires non précisés')}${z.note ? '<br>' + esc(z.note) : ''}`).addTo(gZones);
}

// ---------------------------------------------------------------- onglets du panneau
let tab = 'ouvrages';
$$('#tabs button').forEach((b) => b.onclick = () => { tab = b.dataset.tab; $$('#tabs button').forEach((x) => x.classList.toggle('on', x === b)); renderTab(); });
function renderTab() {
  const el = $('#tab-body');
  if (!full) { el.innerHTML = '<p class="muted">Aucun itinéraire pour l’instant. Touchez « Tracer » puis posez vos points sur la carte, ou ouvrez un itinéraire enregistré.</p>'; return; }
  const A = analysis; const busy = A?.busy ? '<p class="muted">⏳ Analyse du tracé en cours (ponts, réseau, prescriptions, pente)…</p>' : '';
  const errs = A?.errors?.length ? `<p class="small" style="color:#D93025">Données non chargées : ${esc(A.errors.join(' ; '))}. Réessayez plus tard.</p>` : '';
  if (tab === 'ouvrages') {
    const list = A?.ouvrages || [];
    const bad = list.filter((o) => o.level === 'bad').length, warn = list.filter((o) => o.level === 'warn').length, unk = list.filter((o) => o.level === 'unknown').length;
    el.innerHTML = busy + errs + `<p class="small muted">${list.length} ouvrage(s) sur le tracé · ⛔ ${bad} bloquant(s) · ⚠️ ${warn} à vérifier · ${unk} sans cote connue. Convoi : ${fmtM(DB.profile.hauteur)} de haut, ${fmtM(DB.profile.largeur)} de large, ${DB.profile.poids} t.</p>` +
      list.map((o, i) => `<div class="item ${o.level === 'bad' ? 'bad' : o.level === 'warn' ? 'warn' : o.level === 'ok' ? 'ok' : ''}" data-i="${i}"><span class="km">km ${(o.along / 1000).toFixed(1)}</span>
      <h4>${obsEmoji(o)} ${esc(o.nom)}</h4><p>${esc(o.nature || '')}${o.voie ? ' · ' + esc(o.voie) : ''}${o.commune ? ' · ' + esc(o.commune) : ''}</p>
      <p>H ${fmtM(o.hauteur)} · L ${fmtM(o.largeur)} · ${o.tonnage ?? '?'} t</p>${o.reasons?.length ? `<p><b>${esc(o.reasons.join(' · '))}</b></p>` : ''}<p class="small muted">${esc(o.src)}</p></div>`).join('') +
      '<p class="small muted">Appui long (ou clic droit) sur la carte pour ajouter votre propre mesure d’un pont.</p>';
    $$('.item', el).forEach((it) => it.onclick = () => { const o = list[+it.dataset.i]; map.setView([o.lat, o.lng], 17); });
  } else if (tab === 'prescriptions') {
    const list = A?.prescriptions || [];
    const z = A?.zones || [];
    el.innerHTML = busy + errs + (z.length ? '<h4>🕒 Mes villes à horaires sur le trajet</h4>' + z.map(({ z: zz, along }) => `<div class="item warn"><span class="km">km ${(along / 1000).toFixed(1)}</span><h4>${esc(zz.commune)}</h4><p>${esc((zz.ranges || []).map((r) => r.join('–')).join(' · ') || 'horaires non précisés')} · ${esc(zz.days?.length ? zz.days.map((d) => DAYS[d]).join(', ') : 'tous les jours')}</p></div>`).join('') : '') +
      `<p class="small muted">${list.length} prescription(s) du Géoportail liées aux tronçons TE parcourus. 🕒 = mention d’horaire. Elles ne remplacent pas votre arrêté.</p>` +
      list.map((p, i) => `<div class="item ${p.horaire ? 'warn' : ''}"><span class="km">km ${((p.along || 0) / 1000).toFixed(1)}</span><h4>${p.horaire ? '🕒 ' : ''}${esc(p.gest || '')} <span class="pill">${esc(p.type || '')}${p.numero && p.numero !== '0' ? ' n°' + esc(p.numero) : ''}</span></h4>
      <p>${esc(p.texte).replace(/\n/g, '<br>')}</p>${p.largeur ? `<p>Largeur autorisée : ${fmtM(p.largeur)}</p>` : ''}${p.hauteur ? `<p>Hauteur : ${fmtM(p.hauteur)}</p>` : ''}
      <p class="small muted">${esc(p.fichier || '')} · <a href="https://www.geoportail.gouv.fr/depot/fiches/DSR/${esc(p.dept)}_Prescriptions.pdf" target="_blank" rel="noopener">fiche du département ${esc(p.dept)}</a></p>
      ${p.horaire ? `<button data-p="${i}" class="mkzone">🕒 Créer une alerte d’horaire pour cette ville</button>` : ''}</div>`).join('');
    $$('.mkzone', el).forEach((b) => b.onclick = () => { const p = list[+b.dataset.p]; restrictionDialog({ commune: p.gest, ranges: p.plages, note: p.texte.slice(0, 200) }); });
  } else if (tab === 'reseau') {
    const r = A?.reseau;
    if (!r) { el.innerHTML = busy + errs; return; }
    el.innerHTML = busy + errs + '<p class="small muted">Part du trajet sur chaque réseau TE du Géoportail (un tronçon peut appartenir à plusieurs réseaux).</p>' +
      NETS.map((n) => { const pc = Math.min(100, Math.round((r.perNet[n.id] || 0) / r.total * 100)); return `<div class="item"><h4><span class="swatch" style="background:${n.color}"></span> ${n.id} <span class="km">${pc} %</span></h4><div style="height:8px;background:#EEF2F6;border-radius:4px"><div style="height:8px;width:${pc}%;background:${n.color};border-radius:4px"></div></div></div>`; }).join('') +
      `<h4>Hors réseau TE : ${r.offKm.toFixed(1)} km</h4>` + (r.offRuns.length ? r.offRuns.map((o, i) => `<div class="item bad" data-i="${i}"><h4>km ${(o.from / 1000).toFixed(1)} → ${(o.to / 1000).toFixed(1)}</h4><p>${meters(o.to - o.from)} sans réseau TE autour du tracé. À vérifier avec votre arrêté.</p></div>`).join('') : '<p class="muted">Tout le tracé suit un réseau TE.</p>');
    $$('.item.bad', el).forEach((it) => it.onclick = () => { const o = r.offRuns[+it.dataset.i]; map.fitBounds(L.latLngBounds(o.pts), { ...fitPad(), maxZoom: 16 }); });
  } else if (tab === 'pente') {
    const p = A?.profil;
    if (!p) { el.innerHTML = busy + errs; return; }
    el.innerHTML = `<canvas id="profil" width="760" height="300"></canvas><div class="grid2"><p>Montée totale : <b>${Math.round(p.up)} m</b></p><p>Descente totale : <b>${Math.round(p.down)} m</b></p>
      <p>Pente max en montée : <b>${p.maxUp.toFixed(1)} %</b> (km ${(p.maxUpAt / 1000).toFixed(1)})</p><p>Pente max en descente : <b>${p.maxDown.toFixed(1)} %</b> (km ${(p.maxDownAt / 1000).toFixed(1)})</p></div><p class="small muted">Altitudes IGN (RGE ALTI), un point tous les ${Math.round(full.dist / p.pts.length)} m environ.</p>`;
    drawProfile($('#profil'), p);
  } else if (tab === 'etapes') {
    el.innerHTML = `<p class="small muted">Feuille de route : ${full.steps.length} indications.</p>` + full.steps.map((s) => `<div class="item"><span class="km">km ${(s.along / 1000).toFixed(1)}</span><p>${esc(s.text)}</p></div>`).join('') + '<div class="actions"><button id="btn-print">🖨️ Imprimer la feuille de route</button></div>';
    $('#btn-print').onclick = printRoadbook;
  }
}
function drawProfile(cv, p) {
  const ctx = cv.getContext('2d'); const W = cv.width, H = cv.height, padL = 46, padB = 26;
  const zs = p.pts.map((x) => x.z); const zmin = Math.min(...zs), zmax = Math.max(...zs) + 1; const D = p.pts[p.pts.length - 1].along || 1;
  const X = (a) => padL + (a / D) * (W - padL - 8), Y = (z) => H - padB - ((z - zmin) / (zmax - zmin)) * (H - padB - 10);
  ctx.clearRect(0, 0, W, H); ctx.font = '20px system-ui'; ctx.fillStyle = '#5D6B7A';
  ctx.fillText(Math.round(zmax) + ' m', 2, 22); ctx.fillText(Math.round(zmin) + ' m', 2, H - padB);
  ctx.fillText('0', padL, H - 4); ctx.fillText(km(D), W - 110, H - 4);
  ctx.beginPath(); ctx.moveTo(X(0), H - padB); p.pts.forEach((q) => ctx.lineTo(X(q.along), Y(q.z))); ctx.lineTo(X(D), H - padB); ctx.closePath();
  ctx.fillStyle = 'rgba(242,140,40,.25)'; ctx.fill();
  ctx.beginPath(); p.pts.forEach((q, i) => (i ? ctx.lineTo(X(q.along), Y(q.z)) : ctx.moveTo(X(q.along), Y(q.z)))); ctx.strokeStyle = '#F28C28'; ctx.lineWidth = 3; ctx.stroke();
}
function printRoadbook() {
  const w = window.open('', '_blank'); if (!w) return toast('Autorisez les fenêtres pour imprimer.');
  const P = DB.profile; const o = analysis?.ouvrages || [];
  w.document.write(`<html><head><meta charset="utf-8"><title>${esc(cur.name || 'Itinéraire')} – GEP</title><style>body{font-family:system-ui;margin:20px}td,th{border:1px solid #ccc;padding:4px 6px;font-size:12px}table{border-collapse:collapse;width:100%}h1{color:#0E2A47}</style></head><body>
  <h1>GEP · ${esc(cur.name || 'Itinéraire')}</h1><p>${km(full.dist)} · ${hm(full.dur)} · Convoi ${category()}e cat. : L ${P.longueur} m, l ${P.largeur} m, H ${P.hauteur} m, ${P.poids} t</p>
  <h2>Indications</h2><table><tr><th>km</th><th>Indication</th></tr>${full.steps.map((s) => `<tr><td>${(s.along / 1000).toFixed(1)}</td><td>${esc(s.text)}</td></tr>`).join('')}</table>
  <h2>Ouvrages</h2><table><tr><th>km</th><th>Ouvrage</th><th>H</th><th>L</th><th>t</th><th>Alerte</th></tr>${o.map((x) => `<tr><td>${(x.along / 1000).toFixed(1)}</td><td>${esc(x.nom)}</td><td>${fmtM(x.hauteur)}</td><td>${fmtM(x.largeur)}</td><td>${x.tonnage ?? '?'}</td><td>${esc(x.reasons?.join(' · ') || '')}</td></tr>`).join('')}</table>
  <p style="font-size:11px">Document d’aide à la préparation, sans valeur légale. L’arrêté d’autorisation et la reconnaissance du terrain font foi.</p></body></html>`);
  w.document.close(); w.print();
}

// ---------------------------------------------------------------- inspection au toucher (réseau + prescriptions)
async function inspectAt(ll) {
  if (!DB.settings.nets.length || map.getZoom() < 12) return;
  const d = 0.00025; const p = [ll.lat, ll.lng];
  try {
    const f = await wfs('troncon_te', bboxCql(ll.lat - d, ll.lng - d * 1.4, ll.lat + d, ll.lng + d * 1.4), 'geometrie,identifiant_te,reseau_te,cpx_numero,nom_voie_ban_droite,cpx_gestionnaire,largeur_de_chaussee', 'identifiant_te', 200);
    const near = f.filter((x) => lineCoords(x.geometry).some((l) => l.some((c, i) => i && segDist(p, l[i - 1], c).d < 20)));
    if (!near.length) return;
    const props = near[0].properties; const nets = [...new Set(near.map((x) => x.properties.reseau_te))];
    const ids = [...new Set(near.map((x) => x.properties.identifiant_te))];
    const pop = L.popup().setLatLng(ll).setContent(`<h4>${esc(props.cpx_numero || props.nom_voie_ban_droite || 'Tronçon TE')}</h4>${nets.map((n) => `<span class="pill te">${n}</span>`).join('')}<br>${esc(props.cpx_gestionnaire || '')}${props.largeur_de_chaussee ? ' · chaussée ' + props.largeur_de_chaussee + ' m' : ''}<br><span class="small">${esc(ids[0])}</span><br><i>Chargement des prescriptions…</i>`).openOn(map);
    const links = await wfs('troncon_te_lien_prescription', `identifiant_troncon_te IN (${ids.map((x) => `'${x}'`).join(',')})`, 'identifiant_troncon_te,identifiant_prescription_te', 'identifiant_prescription_te', 500);
    const prs = await loadPrescriptions([...new Set(links.map((l) => l.properties.identifiant_prescription_te))]);
    pop.setContent(`<h4>${esc(props.cpx_numero || props.nom_voie_ban_droite || 'Tronçon TE')}</h4>${nets.map((n) => `<span class="pill te">${n}</span>`).join('')}<br>${esc(props.cpx_gestionnaire || '')}${props.largeur_de_chaussee ? ' · chaussée ' + props.largeur_de_chaussee + ' m' : ''}<br><span class="small">${esc(ids[0])}</span>
      <div style="max-height:220px;overflow:auto;margin-top:6px">${prs.map((x) => `<p>${x.horaire ? '🕒 ' : ''}<b>${esc(x.gest || '')}</b> (${esc(x.type || '')}) : ${esc(x.texte.slice(0, 400))}${x.texte.length > 400 ? '…' : ''}${x.largeur ? ' · largeur ' + fmtM(x.largeur) : ''}</p>`).join('') || '<p>Aucune prescription particulière.</p>'}</div>`);
  } catch (e) { console.warn(e); }
}

// ---------------------------------------------------------------- fenêtres
function modal(title, html, onOpen) {
  $('#modal-title').textContent = title; $('#modal-body').innerHTML = html; $('#modal').hidden = false;
  if (onOpen) onOpen($('#modal-body'));
}
function closeModal() { $('#modal').hidden = true; }
$('#modal-close').onclick = closeModal;
$('#modal').addEventListener('click', (e) => { if (e.target.id === 'modal') closeModal(); });

$$('#topbar nav button').forEach((b) => b.onclick = () => ({ convoi: convoiDialog, calques: layersDialog, itineraires: routesDialog, horaires: restrictionsDialog, plus: plusDialog })[b.dataset.panel]());

function convoiDialog() {
  const P = DB.profile;
  const f = (k, l, step = '0.01') => `<div><label>${l}</label><input type="number" inputmode="decimal" step="${step}" data-k="${k}" value="${P[k]}"></div>`;
  modal('Mon convoi', `<div class="grid2">${f('longueur', 'Longueur (m)', '0.1')}${f('largeur', 'Largeur (m)')}${f('hauteur', 'Hauteur (m)')}${f('poids', 'Poids total (t)', '0.1')}${f('essieux', 'Nombre d’essieux', '1')}${f('marge', 'Marge sous les ponts (m)')}</div>
    <p>Catégorie : <span class="badge-cat" id="cat"></span></p><table class="spd" id="spd"></table>
    <p class="small muted">Catégorie et vitesses selon l’arrêté du 4 mai 2006. Votre arrêté d’autorisation peut imposer d’autres vitesses : il fait foi.</p>
    <div class="actions"><button class="primary" id="ok">Valider</button></div>`, (el) => {
    const upd = () => {
      $$('input', el).forEach((i) => (P[i.dataset.k] = num(i.value) ?? 0));
      const c = category(); $('#cat', el).textContent = c + (c === 1 ? 're' : 'e') + ' catégorie';
      const s = SPEEDS[c]; $('#spd', el).innerHTML = `<tr><th>Autoroute</th><th>Route</th><th>Route prioritaire</th><th>Agglomération</th></tr><tr><td>${s.autoroute}</td><td>${s.route}</td><td>${s.prioritaire}</td><td>${s.agglo}</td></tr>`;
    };
    $$('input', el).forEach((i) => i.oninput = upd); upd();
    $('#ok', el).onclick = () => { upd(); save(); closeModal(); if (full) { buildFull(); renderRoute(); if (analysis) { analysis.ouvrages.forEach(judge); renderTab(); drawObstacles(); } } };
  });
}

function layersDialog() {
  const S = DB.settings;
  const chk = (group, id, label, color) => `<label class="check"><input type="checkbox" data-g="${group}" value="${id}" ${S[group].includes(id) ? 'checked' : ''}>${color ? `<span class="swatch" style="background:${color}"></span>` : ''}${label}</label>`;
  modal('Calques de la carte', `<fieldset><legend>Fond de carte</legend>${['plan', 'photo', 'osm'].map((b) => `<label class="check"><input type="radio" name="base" value="${b}" ${S.base === b ? 'checked' : ''}>${{ plan: 'Plan IGN', photo: 'Photos aériennes IGN', osm: 'OpenStreetMap' }[b]}</label>`).join('')}</fieldset>
    <fieldset><legend>Réseaux TE affichés (Géoportail)</legend>${NETS.map((n) => chk('nets', n.id, n.label, n.color)).join('')}<p class="small muted">Visibles à partir du zoom départemental.</p></fieldset>
    <fieldset><legend>Franchissements</legend>${CROSS_LAYERS.map((n) => chk('cross', n.id, n.label)).join('')}</fieldset>
    <fieldset><legend>🧲 Réseaux suivis par l’aimant</legend>${NETS.map((n) => chk('aimantNets', n.id, n.id, n.color)).join('')}<button id="auto-nets">Choisir selon mon convoi (${DB.profile.poids} t)</button></fieldset>
    <fieldset><legend>Données complémentaires</legend><label class="check"><input type="checkbox" id="osm" ${S.osm ? 'checked' : ''}>Hauteurs et tonnages OpenStreetMap</label></fieldset>
    <div class="actions"><button class="primary" id="ok">Valider</button></div>`, (el) => {
    $('#auto-nets', el).onclick = () => {
      const p = DB.profile.poids; const sel = p <= 48 ? ['1TE', '2TE48', 'TE72', 'TE94', 'TE120'] : p <= 72 ? ['TE72', 'TE94', 'TE120'] : p <= 94 ? ['TE94', 'TE120'] : ['TE120'];
      $$('input[data-g="aimantNets"]', el).forEach((i) => (i.checked = sel.includes(i.value)));
    };
    $('#ok', el).onclick = () => {
      S.base = $('input[name=base]:checked', el).value;
      ['nets', 'cross', 'aimantNets'].forEach((g) => (S[g] = $$(`input[data-g="${g}"]:checked`, el).map((i) => i.value)));
      S.osm = $('#osm', el).checked; save(); applyLayers(); closeModal(); legCache.clear();
    };
  });
}

// ---------------------------------------------------------------- itinéraires enregistrés
function routesDialog() {
  const byFolder = {}; DB.folders.forEach((f) => (byFolder[f] = []));
  DB.routes.forEach((r) => (byFolder[r.folder] = byFolder[r.folder] || []).push(r));
  modal('Mes itinéraires', `<div class="actions" style="margin-top:0"><button class="primary" id="new">➕ Nouveau</button><button id="imp">📥 Importer un GPX</button><button id="fold">📁 Nouveau dossier</button></div>
    ${Object.entries(byFolder).map(([f, rs]) => `<fieldset><legend>📁 ${esc(f)} (${rs.length})</legend>${rs.sort((a, b) => b.updated - a.updated).map((r) => `<div class="item"><h4>${esc(r.name || 'Sans nom')}</h4><p class="small muted">${r.track ? 'Tracé enregistré' : r.waypoints.length + ' points'} · modifié le ${new Date(r.updated).toLocaleDateString('fr-FR')}</p>
    <div class="row"><button data-open="${r.id}">Ouvrir</button><button data-gpx="${r.id}">GPX</button><button data-move="${r.id}">Dossier</button><button class="danger" data-del="${r.id}">Supprimer</button></div></div>`).join('') || '<p class="muted small">Vide</p>'}</fieldset>`).join('')}`, (el) => {
    $('#new', el).onclick = () => { openRoute(newRoute()); closeModal(); setDraw(true); };
    $('#imp', el).onclick = () => $('#file-gpx').click();
    $('#fold', el).onclick = () => { const n = prompt('Nom du dossier (client, chantier…)'); if (n && !DB.folders.includes(n)) { DB.folders.push(n); save(); routesDialog(); } };
    $$('[data-open]', el).forEach((b) => b.onclick = () => { openRoute(structuredClone(DB.routes.find((r) => r.id === b.dataset.open))); closeModal(); });
    $$('[data-gpx]', el).forEach((b) => b.onclick = async () => { const r = DB.routes.find((x) => x.id === b.dataset.gpx); await openRoute(structuredClone(r)); exportGPX(); });
    $$('[data-move]', el).forEach((b) => b.onclick = () => { const r = DB.routes.find((x) => x.id === b.dataset.move); const n = prompt('Dossier : ' + DB.folders.join(', '), r.folder); if (n) { if (!DB.folders.includes(n)) DB.folders.push(n); r.folder = n; save(); routesDialog(); } });
    $$('[data-del]', el).forEach((b) => b.onclick = () => { const r = DB.routes.find((x) => x.id === b.dataset.del); if (confirm(`Supprimer « ${r.name || 'Sans nom'} » ?`)) { DB.routes = DB.routes.filter((x) => x !== r); save(); routesDialog(); } });
  });
}
async function openRoute(r) {
  cur = r; $('#route-name').value = r.name || ''; legs = []; full = null; analysis = null;
  drawWaypoints(); await compute();
  if (full) map.fitBounds(L.latLngBounds(full.coords), fitPad());
}
function saveRoute() {
  if (!full) return toast('Rien à enregistrer : tracez d’abord un itinéraire.');
  cur.name = $('#route-name').value.trim() || cur.name || `Itinéraire du ${new Date().toLocaleDateString('fr-FR')}`; $('#route-name').value = cur.name;
  cur.updated = Date.now();
  const i = DB.routes.findIndex((r) => r.id === cur.id); if (i >= 0) DB.routes[i] = structuredClone(cur); else DB.routes.push(structuredClone(cur));
  save(); toast('Itinéraire enregistré sur cet appareil.');
}

// GPX
function exportGPX() {
  if (!full) return toast('Aucun tracé à exporter.');
  const name = esc(cur.name || 'Itinéraire GEP');
  const wpts = (analysis?.ouvrages || []).filter((o) => o.level === 'bad' || o.level === 'warn').map((o) => `<wpt lat="${o.lat}" lon="${o.lng}"><name>${esc(o.nom)}</name><desc>${esc(o.reasons.join(' · '))}</desc></wpt>`).join('\n');
  const gpx = `<?xml version="1.0" encoding="UTF-8"?>\n<gpx version="1.1" creator="GEP Itinéraires" xmlns="http://www.topografix.com/GPX/1/1">\n<metadata><name>${name}</name></metadata>\n${wpts}\n<trk><name>${name}</name><trkseg>\n${full.coords.map((c) => `<trkpt lat="${c[0].toFixed(6)}" lon="${c[1].toFixed(6)}"/>`).join('\n')}\n</trkseg></trk>\n</gpx>`;
  download((cur.name || 'itineraire-gep').replace(/[^\w\-]+/g, '_') + '.gpx', gpx, 'application/gpx+xml');
}
function download(name, text, type) {
  const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([text], { type })); a.download = name; document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 1000);
}
$('#file-gpx').onchange = async (e) => {
  const f = e.target.files[0]; if (!f) return; e.target.value = '';
  const x = new DOMParser().parseFromString(await f.text(), 'application/xml');
  const pts = (sel) => [...x.getElementsByTagName(sel)].map((p) => [+p.getAttribute('lat'), +p.getAttribute('lon')]).filter((p) => isFinite(p[0]) && isFinite(p[1]));
  const trk = pts('trkpt'), rte = pts('rtept');
  const r = newRoute(); r.name = x.getElementsByTagName('name')[0]?.textContent || f.name.replace(/\.gpx$/i, '');
  if (trk.length > 1) r.track = trk.map((p) => [+p[0].toFixed(6), +p[1].toFixed(6)]);
  else if (rte.length > 1) { r.waypoints = rte; r.modes = rte.slice(1).map(() => 'route'); }
  else return toast('Aucun tracé trouvé dans ce fichier GPX.');
  closeModal(); await openRoute(r); toast('GPX importé. Pensez à l’enregistrer.');
};

// Partage par lien et QR code
function encodePolyline(coords) { let out = '', pl = 0, pg = 0; const enc = (v) => { v = v < 0 ? ~(v << 1) : v << 1; let s = ''; while (v >= 0x20) { s += String.fromCharCode((0x20 | (v & 0x1f)) + 63); v >>= 5; } return s + String.fromCharCode(v + 63); }; for (const [la, lg] of coords) { const a = Math.round(la * 1e5), b = Math.round(lg * 1e5); out += enc(a - pl) + enc(b - pg); pl = a; pg = b; } return out; }
function decodePolyline(s) { const out = []; let i = 0, la = 0, lg = 0; const dec = () => { let r = 0, sh = 0, b; do { b = s.charCodeAt(i++) - 63; r |= (b & 0x1f) << sh; sh += 5; } while (b >= 0x20); return r & 1 ? ~(r >> 1) : r >> 1; }; while (i < s.length) { la += dec(); lg += dec(); out.push([la / 1e5, lg / 1e5]); } return out; }
function shareRoute() {
  if (!full) return toast('Tracez d’abord un itinéraire.');
  const data = { n: $('#route-name').value || cur.name || '', ...(cur.track ? { t: encodePolyline(cur.track) } : { w: encodePolyline(cur.waypoints), m: cur.modes.map((m) => m[0]).join('') }) };
  const url = location.origin + location.pathname + '#r=' + encodeURIComponent(btoa(unescape(encodeURIComponent(JSON.stringify(data)))));
  let qr = '';
  if (url.length < 2300) { try { const q = qrcode(0, 'L'); q.addData(url); q.make(); qr = `<div class="qr">${q.createImgTag(5, 8)}</div>`; } catch (e) { qr = ''; } }
  modal('Partager l’itinéraire', `${qr || '<p class="muted">Tracé trop long pour un QR code : envoyez le lien.</p>'}<p class="small muted">Votre collègue ouvre le lien (ou scanne le code) et retrouve le même tracé dans son appli GEP. Les données restent sur vos appareils.</p>
    <input readonly value="${esc(url)}" id="url"><div class="actions"><button class="primary" id="cp">📋 Copier le lien</button>${navigator.share ? '<button id="sh">📤 Envoyer…</button>' : ''}<button id="gpx">⬇️ Fichier GPX</button></div>`, (el) => {
    $('#cp', el).onclick = async () => { try { await navigator.clipboard.writeText(url); toast('Lien copié.'); } catch (e) { $('#url', el).select(); document.execCommand('copy'); toast('Lien copié.'); } };
    if (navigator.share) $('#sh', el).onclick = () => navigator.share({ title: 'Itinéraire GEP', text: data.n, url }).catch(() => {});
    $('#gpx', el).onclick = exportGPX;
  });
}
function readShared() {
  const m = location.hash.match(/#r=(.+)$/); if (!m) return false;
  try {
    const d = JSON.parse(decodeURIComponent(escape(atob(decodeURIComponent(m[1])))));
    const r = newRoute(); r.name = d.n || 'Itinéraire partagé';
    if (d.t) r.track = decodePolyline(d.t);
    else { r.waypoints = decodePolyline(d.w); r.modes = (d.m || '').split('').map((c) => ({ a: 'aimant', r: 'route', d: 'droit' }[c] || 'route')); }
    history.replaceState(null, '', location.pathname);
    openRoute(r); toast('Itinéraire partagé ouvert. Enregistrez-le pour le garder.', 5000); return true;
  } catch (e) { toast('Lien d’itinéraire illisible.'); return false; }
}

// ---------------------------------------------------------------- recherche de lieu
function searchDialog() {
  modal('Chercher un lieu', `<input id="q" placeholder="Adresse, ville, zone industrielle…" autocomplete="off"><div id="res" style="margin-top:8px"></div>`, (el) => {
    let t; const q = $('#q', el); q.focus();
    q.oninput = () => { clearTimeout(t); t = setTimeout(async () => {
      if (q.value.trim().length < 3) return;
      try {
        const j = await getJSON(`${GPF}/geocodage/search?q=${encodeURIComponent(q.value)}&limit=6`);
        $('#res', el).innerHTML = (j.features || []).map((f, i) => `<div class="item" data-i="${i}"><h4>${esc(f.properties.label)}</h4><div class="row"><button data-go="${i}">Voir</button><button class="primary" data-add="${i}">➕ Ajouter au tracé</button></div></div>`).join('') || '<p class="muted">Aucun résultat.</p>';
        const go = (i) => { const c = j.features[i].geometry.coordinates; return { lat: c[1], lng: c[0] }; };
        $$('[data-go]', el).forEach((b) => b.onclick = () => { map.setView(go(+b.dataset.go), 15); closeModal(); });
        $$('[data-add]', el).forEach((b) => b.onclick = () => { const ll = go(+b.dataset.add); addWaypoint(ll); map.setView(ll, 13); closeModal(); });
      } catch (e) { $('#res', el).innerHTML = '<p class="muted">Recherche indisponible.</p>'; }
    }, 300); };
  });
}

// ---------------------------------------------------------------- mes mesures et signalements
function addMineDialog(ll) {
  modal('Ajouter à la carte', `<p class="small muted">Position : ${ll.lat.toFixed(5)}, ${ll.lng.toFixed(5)}</p>
    <label>Type</label><select id="type"><option>Pont</option><option>Tunnel</option><option>Passage étroit</option><option>Manœuvre difficile</option><option>Passage à niveau</option><option>Signalement : travaux</option><option>Signalement : barrière de dégel</option><option>Signalement : route coupée</option><option>Parking convoi</option></select>
    <label>Nom ou repère</label><input id="nom" placeholder="ex. Pont SNCF D2020">
    <div class="grid2"><div><label>Hauteur (m)</label><input id="h" type="number" step="0.01" inputmode="decimal"></div><div><label>Largeur (m)</label><input id="l" type="number" step="0.01" inputmode="decimal"></div>
    <div><label>Tonnage (t)</label><input id="t" type="number" step="0.1" inputmode="decimal"></div><div><label>Source de la mesure</label><select id="src"><option>pige</option><option>laser</option><option>panneau</option><option>document officiel</option></select></div></div>
    <label>Valable jusqu’au (signalements)</label><input id="fin" type="date"><label>Note</label><textarea id="note" rows="2" placeholder="Passage conseillé, contact…"></textarea>
    <div class="actions"><button class="primary" id="ok">Enregistrer</button></div>`, (el) => {
    $('#ok', el).onclick = () => {
      DB.obstacles.push({ id: 'm' + Date.now().toString(36), lat: ll.lat, lng: ll.lng, type: $('#type', el).value, nom: $('#nom', el).value, hauteur: $('#h', el).value, largeur: $('#l', el).value, tonnage: $('#t', el).value, source: $('#src', el).value, fin: $('#fin', el).value, note: $('#note', el).value, date: Date.now() });
      save(); drawMine(); closeModal(); toast('Ajouté. Il sera pris en compte dans vos prochains itinéraires.'); if (full) analyse(calcVersion);
    };
  });
}
function drawMine() {
  gMine.clearLayers();
  const today = new Date().toISOString().slice(0, 10);
  DB.obstacles = DB.obstacles.filter((o) => !o.fin || o.fin >= today);
  for (const o of DB.obstacles) {
    const m = L.marker([o.lat, o.lng], { icon: L.divIcon({ className: '', html: `<div class="obs mine">${/Signalement/.test(o.type) ? '⚠️' : /Parking/.test(o.type) ? '🅿️' : obsEmoji({ nature: o.type })}</div>`, iconSize: [24, 24], iconAnchor: [12, 12] }) }).addTo(gMine);
    m.bindPopup(`<h4>${esc(o.nom || o.type)}</h4>${esc(o.type)}<br>H ${esc(o.hauteur || '?')} m · L ${esc(o.largeur || '?')} m · ${esc(o.tonnage || '?')} t<br>Source : ${esc(o.source)} · ${new Date(o.date).toLocaleDateString('fr-FR')}${o.fin ? '<br>Jusqu’au ' + esc(o.fin) : ''}${o.note ? '<br>' + esc(o.note) : ''}<br><button data-delmine="${o.id}">Supprimer</button>`);
  }
}
document.addEventListener('click', (e) => { const id = e.target?.dataset?.delmine; if (id && confirm('Supprimer ce point ?')) { DB.obstacles = DB.obstacles.filter((o) => o.id !== id); save(); drawMine(); map.closePopup(); } });

// ---------------------------------------------------------------- restrictions d'horaire : écrans
function restrictionsDialog() {
  modal('Villes à restriction d’horaire', `<p class="small muted">Quand vous entrez dans une de ces villes pendant (ou 30 min avant) une plage interdite, l’appli vous alerte à la voix. Les prescriptions du Géoportail marquées 🕒 vous proposent aussi d’en créer une.</p>
    <div class="actions" style="margin-top:0"><button class="primary" id="add">➕ Ajouter une ville</button></div>
    ${DB.restrictions.map((z, i) => { const st = zoneStatus(z); return `<div class="item ${st?.st === 'active' ? 'bad' : st ? 'warn' : ''}"><h4>🕒 ${esc(z.commune)} <span class="small muted">(${esc(z.dept || '')})</span></h4><p>${esc(z.days?.length ? z.days.map((d) => DAYS[d]).join(', ') : 'tous les jours')} · ${esc((z.ranges || []).map((r) => r.join('–')).join(' · ') || 'horaires non précisés')}</p>${st ? `<p><b>${st.st === 'active' ? 'Interdit en ce moment' : 'Interdiction dans moins de 30 min'} (${st.range})</b></p>` : ''}${z.note ? `<p class="small">${esc(z.note)}</p>` : ''}<div class="row"><button data-edit="${i}">Modifier</button><button data-see="${i}">Voir</button><button class="danger" data-del="${i}">Supprimer</button></div></div>`; }).join('') || '<p class="muted">Aucune ville pour l’instant.</p>'}`, (el) => {
    $('#add', el).onclick = () => restrictionDialog({});
    $$('[data-edit]', el).forEach((b) => b.onclick = () => restrictionDialog(DB.restrictions[+b.dataset.edit], +b.dataset.edit));
    $$('[data-see]', el).forEach((b) => b.onclick = () => { const z = DB.restrictions[+b.dataset.see]; closeModal(); map.fitBounds(L.geoJSON(z.contour).getBounds()); });
    $$('[data-del]', el).forEach((b) => b.onclick = () => { if (confirm('Supprimer cette ville ?')) { DB.restrictions.splice(+b.dataset.del, 1); save(); drawZones(); restrictionsDialog(); } });
  });
}
function restrictionDialog(z = {}, idx = -1) {
  const ranges = z.ranges?.length ? z.ranges : [['07:00', '09:00'], ['16:30', '19:00']];
  const days = z.days?.length ? z.days : [0, 1, 2, 3, 4];
  modal(idx >= 0 ? 'Modifier la ville' : 'Ajouter une ville', `<label>Ville</label><input id="c" value="${esc(z.commune || '')}" placeholder="Nom de la commune" autocomplete="off"><div id="cres"></div>
    <label>Jours concernés</label><div class="row" style="flex-wrap:wrap">${DAYS.map((d, i) => `<label class="check" style="flex:0 0 auto"><input type="checkbox" class="day" value="${i}" ${days.includes(i) ? 'checked' : ''}>${d}</label>`).join('')}</div>
    <label>Plages interdites</label><div id="ranges">${ranges.map((r) => rangeRow(r)).join('')}</div><button id="addr">➕ Ajouter une plage</button>
    <label>Note (source, arrêté…)</label><textarea id="note" rows="2">${esc(z.note || '')}</textarea>
    <div class="actions"><button class="primary" id="ok">Enregistrer</button></div>`, (el) => {
    let picked = z.code ? { nom: z.commune, code: z.code, codeDepartement: z.dept } : null; let t;
    const search = async () => {
      const v = $('#c', el).value.trim(); if (v.length < 2) return;
      try {
        const j = await getJSON(`https://geo.api.gouv.fr/communes?nom=${encodeURIComponent(v)}&fields=nom,code,codeDepartement,codesPostaux&boost=population&limit=6`);
        $('#cres', el).innerHTML = j.map((c, i) => `<div class="item" data-i="${i}" style="cursor:pointer"><b>${esc(c.nom)}</b> <span class="small muted">${esc(c.codeDepartement)} · ${esc((c.codesPostaux || [])[0] || '')}</span></div>`).join('');
        $$('#cres .item', el).forEach((it) => it.onclick = () => { picked = j[+it.dataset.i]; $('#c', el).value = picked.nom; $('#cres', el).innerHTML = `<p class="small">✅ ${esc(picked.nom)} (${esc(picked.codeDepartement)})</p>`; });
      } catch (e) { $('#cres', el).innerHTML = '<p class="small muted">Recherche de commune indisponible.</p>'; }
    };
    $('#c', el).oninput = () => { picked = null; clearTimeout(t); t = setTimeout(search, 300); };
    if (!picked && z.commune) search();
    $('#addr', el).onclick = () => $('#ranges', el).insertAdjacentHTML('beforeend', rangeRow(['12:00', '14:00']));
    el.addEventListener('click', (e) => { if (e.target.classList.contains('delr')) e.target.closest('.row').remove(); });
    $('#ok', el).onclick = async () => {
      if (!picked) return toast('Choisissez la ville dans la liste.');
      let contour = z.code === picked.code ? z.contour : null;
      if (!contour) {
        try { const g = await getJSON(`https://geo.api.gouv.fr/communes/${picked.code}?fields=contour&format=geojson&geometry=contour`); contour = simplifyGeom(g.geometry); }
        catch (e) { return toast('Impossible de récupérer le contour de la ville. Réessayez avec du réseau.'); }
      }
      const rec = { id: z.id || 'z' + Date.now().toString(36), commune: picked.nom, code: picked.code, dept: picked.codeDepartement, contour,
        days: $$('.day:checked', el).map((i) => +i.value), ranges: $$('#ranges .row', el).map((r) => [$('.a', r).value, $('.b', r).value]).filter((r) => r[0] && r[1]), note: $('#note', el).value };
      if (idx >= 0) DB.restrictions[idx] = rec; else DB.restrictions.push(rec);
      save(); drawZones(); restrictionsDialog(); toast(`Alerte d’horaire enregistrée pour ${rec.commune}.`);
      if (full && analysis) { analysis.zones = DB.restrictions.map((zz) => ({ z: zz, hit: zoneOnRoute(zz) })).filter((x) => x.hit).map((x) => ({ z: x.z, along: x.hit.along })); renderTab(); }
    };
  });
}
const rangeRow = (r) => `<div class="row" style="align-items:center;margin-bottom:6px"><input type="time" class="a" value="${r[0]}"><span style="flex:0">à</span><input type="time" class="b" value="${r[1]}"><button class="delr" style="flex:0">✕</button></div>`;
function simplifyGeom(g) { // arrondit et allège le contour pour le stockage
  const ring = (r) => { const step = Math.max(1, Math.floor(r.length / 300)); const o = r.filter((_, i) => i % step === 0).map((c) => [+c[0].toFixed(5), +c[1].toFixed(5)]); o.push(o[0]); return o; };
  if (g.type === 'Polygon') return { type: 'Polygon', coordinates: g.coordinates.map(ring) };
  return { type: 'MultiPolygon', coordinates: g.coordinates.map((p) => p.map(ring)) };
}

// ---------------------------------------------------------------- menu Plus
function plusDialog() {
  modal('Plus', `<div class="actions" style="flex-direction:column">
    <button id="rec">⏺ Enregistrer un trajet en roulant</button>
    <button id="gpx">⬇️ Exporter l’itinéraire en GPX</button>
    <button id="print">🖨️ Feuille de route</button>
    <button id="bk">💾 Sauvegarder toutes mes données (fichier)</button>
    <button id="rs">📂 Restaurer une sauvegarde</button>
    <button id="inst">📲 Installer l’appli sur cet appareil</button>
    <button id="about">ℹ️ Sources et limites</button></div>
    <p class="small muted">Vos itinéraires restent sur cet appareil. Pour les retrouver sur la tablette, utilisez « Sauvegarder » puis « Restaurer », ou partagez un itinéraire par lien.</p>`, (el) => {
    $('#rec', el).onclick = () => { closeModal(); startNav({ recordOnly: true }); };
    $('#gpx', el).onclick = exportGPX;
    $('#print', el).onclick = () => (full ? printRoadbook() : toast('Aucun itinéraire.'));
    $('#bk', el).onclick = () => download(`gep-sauvegarde-${new Date().toISOString().slice(0, 10)}.json`, JSON.stringify(DB), 'application/json');
    $('#rs', el).onclick = () => $('#file-backup').click();
    $('#inst', el).onclick = installHelp;
    $('#about', el).onclick = aboutDialog;
  });
}
$('#file-backup').onchange = async (e) => {
  const f = e.target.files[0]; if (!f) return; e.target.value = '';
  try {
    const d = JSON.parse(await f.text()); if (!d.routes) throw new Error();
    if (!confirm(`Fusionner ${d.routes.length} itinéraire(s), ${d.restrictions?.length || 0} ville(s) et ${d.obstacles?.length || 0} mesure(s) avec celles de cet appareil ?`)) return;
    const merge = (a, b) => { const ids = new Set(a.map((x) => x.id)); return a.concat((b || []).filter((x) => !ids.has(x.id))); };
    DB.routes = merge(DB.routes, d.routes); DB.restrictions = merge(DB.restrictions, d.restrictions); DB.obstacles = merge(DB.obstacles, d.obstacles);
    DB.folders = [...new Set([...DB.folders, ...(d.folders || [])])]; if (d.profile) DB.profile = Object.assign(DB.profile, d.profile);
    save(); drawZones(); drawMine(); closeModal(); toast('Sauvegarde restaurée.');
  } catch (err) { toast('Fichier de sauvegarde illisible.'); }
};
let installEvt = null;
window.addEventListener('beforeinstallprompt', (e) => { e.preventDefault(); installEvt = e; });
function installHelp() {
  if (installEvt) { installEvt.prompt(); installEvt = null; return; }
  modal('Installer GEP', `<h4>Sur Android (téléphone ou tablette)</h4><p>Ouvrez cette page dans Chrome, touchez le menu ⋮ puis « Installer l’application » (ou « Ajouter à l’écran d’accueil »).</p>
    <h4>Sur iPhone ou iPad</h4><p>Ouvrez cette page dans Safari, touchez le bouton Partager ⬆️ puis « Sur l’écran d’accueil ».</p>
    <p class="small muted">L’icône GEP apparaît alors comme une appli. Le guidage fonctionne écran allumé (l’appli empêche la mise en veille pendant le guidage).</p>`);
}
function aboutDialog() {
  modal('Sources et limites', `<p><b>GEP Itinéraires</b> est un outil d’aide à la préparation et au guidage, sans valeur légale. Il ne remplace ni votre arrêté d’autorisation, ni la reconnaissance du terrain, ni votre vigilance.</p>
    <h4>Données utilisées (gratuites et publiques)</h4><ul class="small"><li>Réseaux TE 1TE, 2TE48, TE72, TE94, TE120, franchissements et prescriptions : Géoportail / IGN Géoplateforme (base TE de la Sécurité routière).</li>
    <li>Calcul de liaison routière, altitudes, recherche d’adresses : IGN Géoplateforme.</li><li>Contours des communes : geo.api.gouv.fr.</li><li>Hauteurs et tonnages complémentaires : contributeurs OpenStreetMap.</li>
    <li>Catégories et vitesses : arrêté du 4 mai 2006. Règles de franchissement des ouvrages : guides Cerema (ex-Sétra).</li></ul>
    <h4>Ce que l’appli ne sait pas</h4><ul class="small"><li>Les itinéraires imposés par votre arrêté et les autorisations individuelles.</li><li>Beaucoup de petits ponts n’ont pas de hauteur connue : ajoutez vos mesures (appui long sur la carte).</li><li>Travaux et barrières de dégel en direct : seulement vos propres signalements.</li><li>Les horaires interdits ne sont reconnus automatiquement que s’ils sont écrits dans les prescriptions : ajoutez vos villes dans « Horaires ».</li></ul>`);
}

// ---------------------------------------------------------------- guidage GPS
let nav = null;
const speak = (t) => { if (!DB.settings.voice || !('speechSynthesis' in window)) return; const u = new SpeechSynthesisUtterance(t); u.lang = 'fr-FR'; speechSynthesis.cancel(); speechSynthesis.speak(u); };
const sayM = (m) => (m >= 1000 ? (m / 1000).toFixed(1).replace('.', ',') + ' kilomètres' : Math.round(m / 10) * 10 + ' mètres');
const sayH = (h) => h == null ? '' : `${Math.floor(h)} mètres ${String(Math.round((h % 1) * 100)).padStart(2, '0')}`;

function startNavDialog() {
  if (!full) return toast('Tracez ou ouvrez d’abord un itinéraire.');
  modal('Démarrer le guidage', `<p>${esc(cur.name || 'Itinéraire')} · ${km(full.dist)} · ${hm(full.dur)}</p>${analysis?.busy ? '<p class="small" style="color:#E37400">L’analyse des ponts n’est pas terminée : les annonces seront incomplètes.</p>' : ''}
    <div class="actions" style="flex-direction:column"><button class="go" id="gps">▶ Guidage GPS</button><button id="sim">🧪 Simulation (pour tester, sans rouler)</button></div>
    <p class="small muted">Le guidage suit exactement votre tracé, sans jamais recalculer vers une autre route. Gardez l’écran allumé.</p>`, (el) => {
    $('#gps', el).onclick = () => { closeModal(); startNav({}); };
    $('#sim', el).onclick = () => { closeModal(); startNav({ sim: true }); };
  });
}
async function startNav(opt) {
  if (!opt.recordOnly && !full) return;
  nav = { opt, said: new Set(), lastI: 0, offCount: 0, rec: opt.recordOnly ? [] : null, zonesIn: new Set(), watch: null, sim: null, lock: null, lastPos: null };
  document.body.classList.add('navigating'); $('#nav').hidden = false; map.invalidateSize();
  $('#nav-rec').classList.toggle('on', !!nav.rec);
  if (opt.recordOnly) { $('#nav-instr').textContent = 'Enregistrement du trajet'; $('#nav-dist').textContent = ''; }
  try { if ('wakeLock' in navigator) nav.lock = await navigator.wakeLock.request('screen'); } catch (e) { /* non disponible */ }
  speak(opt.recordOnly ? 'Enregistrement du trajet démarré.' : 'Guidage GEP démarré. Bonne route.');
  if (opt.sim) {
    let s = 0; const v = 60 / 3.6 * 4; // 60 km/h accéléré 4 fois
    nav.sim = setInterval(() => { s += v; if (s > full.dist) s = full.dist; const p = pointAt(s); onFix({ coords: { latitude: p[0], longitude: p[1], speed: 60 / 3.6, accuracy: 5 } }); if (s >= full.dist) clearInterval(nav.sim); }, 1000);
  } else if ('geolocation' in navigator) {
    nav.watch = navigator.geolocation.watchPosition(onFix, (e) => toast('GPS indisponible : ' + e.message), { enableHighAccuracy: true, maximumAge: 1000, timeout: 20000 });
  } else toast('Pas de GPS sur cet appareil.');
}
function pointAt(s) { const C = full.coords, cum = full.cum; let i = 0; while (i < C.length - 2 && cum[i + 1] < s) i++; const t = (s - cum[i]) / ((cum[i + 1] - cum[i]) || 1); return [C[i][0] + t * (C[i + 1][0] - C[i][0]), C[i][1] + t * (C[i + 1][1] - C[i][1])]; }
function onFix(pos) {
  if (!nav) return;
  const p = [pos.coords.latitude, pos.coords.longitude];
  const kmh = pos.coords.speed != null && pos.coords.speed >= 0 ? pos.coords.speed * 3.6 : (nav.lastPos ? Math.min(150, dist(nav.lastPos.p, p) / Math.max(0.5, (Date.now() - nav.lastPos.t) / 1000) * 3.6) : 0);
  nav.lastPos = { p, t: Date.now() };
  if (!meMarker) meMarker = L.marker(p, { icon: L.divIcon({ className: '', html: '<div class="me"></div>', iconSize: [22, 22], iconAnchor: [11, 11] }), zIndexOffset: 1000 }).addTo(map);
  meMarker.setLatLng(p); map.setView(p, Math.max(map.getZoom(), 16), { animate: true });
  $('#nav-speed').textContent = Math.round(kmh);
  if (nav.rec && (!nav.rec.length || dist(nav.rec[nav.rec.length - 1], p) > 15)) nav.rec.push([+p[0].toFixed(6), +p[1].toFixed(6)]);
  checkZones(p);
  if (nav.opt.recordOnly || !full) { $('#nav-remain').textContent = nav.rec ? km(cumul(nav.rec).pop() || 0) + ' enregistrés' : ''; return; }
  // position sur le tracé : on cherche d'abord près de la dernière position connue
  let loc = locate(p, 80, nav.lastI - 20, nav.lastI + 400) || locate(p, 80);
  if (!loc) {
    nav.offCount++;
    if (nav.offCount === 3) { showAlert('Hors tracé : revenez sur votre itinéraire', 'bad'); speak('Attention, vous êtes hors de votre tracé.'); }
    return;
  }
  if (nav.offCount >= 3) hideAlert(); nav.offCount = 0; nav.lastI = loc.i;
  const s = loc.along, remain = full.dist - s;
  // indication suivante
  const st = full.steps.find((x) => x.along > s + 8);
  const curStep = [...full.steps].reverse().find((x) => x.along <= s + 8);
  if (st) {
    const d = st.along - s; $('#nav-instr').textContent = st.text; $('#nav-dist').textContent = meters(d);
    for (const [lim, key] of [[600, 'a'], [200, 'b'], [40, 'c']]) if (d <= lim && !nav.said.has(st.along + key)) { nav.said.add(st.along + key); speak((d > 60 ? 'Dans ' + sayM(d) + ', ' : '') + st.text); break; }
  } else { $('#nav-instr').textContent = 'Arrivée'; $('#nav-dist').textContent = meters(remain); }
  // vitesse maximale selon la catégorie
  const sp = speeds(); const auto = isAutoroute(curStep?.name);
  const lim = auto ? sp.autoroute : sp.route; $('#nav-limit').textContent = lim; $('#nav-limit-lbl').textContent = auto ? 'autoroute' : `route (agglo ${sp.agglo})`;
  $('.speed').classList.toggle('over', kmh > lim + 2);
  // ouvrages et prescriptions horaires à venir
  const obs = (analysis?.ouvrages || []).filter((o) => o.along > s - 10);
  const next = obs[0];
  $('#nav-remain').textContent = `${km(remain)} · arrivée ${new Date(Date.now() + remain / (lim / 3.6) * 1000).toLocaleTimeString('fr-FR', { hour: '2-digit', minute: '2-digit' })}`;
  $('#nav-next-obs').textContent = next ? `${obsEmoji(next)} ${next.nom} dans ${meters(next.along - s)} · H ${fmtM(next.hauteur)}` : 'Aucun ouvrage connu devant';
  for (const o of obs.filter((x) => x.along - s < 1100)) {
    const d = o.along - s;
    for (const [lm, key] of [[1000, '1'], [300, '3']]) if (d <= lm && d > 0 && !nav.said.has(o.id + key)) {
      nav.said.add(o.id + key);
      const what = /tunnel/i.test(o.nature) ? 'Tunnel' : /niveau/i.test(o.nature) ? 'Passage à niveau' : 'Pont';
      let txt = `${what} dans ${sayM(d)}`; if (o.hauteur != null) txt += `, hauteur ${sayH(o.hauteur)}`; if (o.tonnage != null && /portée|Pont \(/.test(o.nature || '')) txt += `, ${o.tonnage} tonnes`;
      if (o.level === 'bad') { txt = 'Danger. ' + txt + '. ' + o.reasons.join(', '); showAlert(`⛔ ${o.nom} dans ${meters(d)} : ${o.reasons.join(' · ')}`, 'bad'); }
      else if (o.level === 'warn') showAlert(`⚠️ ${o.nom} dans ${meters(d)} : ${o.reasons.join(' · ') || 'à vérifier'}`, 'warn');
      speak(txt); break;
    }
  }
  for (const pr of (analysis?.prescriptions || []).filter((x) => x.horaire && x.along != null && x.along - s < 1000 && x.along - s > -50)) {
    if (nav.said.has(pr.id)) continue; nav.said.add(pr.id);
    const st2 = pr.plages.length ? zoneStatus({ ranges: pr.plages }) : null;
    showAlert(`🕒 ${pr.gest} : ${pr.texte.slice(0, 140)}`, st2?.st === 'active' ? 'bad' : 'warn');
    speak(`Attention, restriction d'horaire à ${pr.gest}. ${st2?.st === 'active' ? 'Interdiction en cours.' : ''}`);
  }
  if (remain < 30 && !nav.said.has('end')) { nav.said.add('end'); speak('Vous êtes arrivé.'); }
}
function checkZones(p) {
  for (const z of DB.restrictions) {
    const inside = inGeom(p, z.contour);
    if (inside && !nav.zonesIn.has(z.id)) {
      nav.zonesIn.add(z.id); const st = zoneStatus(z);
      if (st?.st === 'active') { showAlert(`🕒 ${z.commune} : circulation interdite maintenant (${st.range})`, 'bad'); speak(`Attention, vous entrez dans ${z.commune}. Circulation interdite aux convois de ${st.range.replace('–', ' à ')}.`); }
      else if (st?.st === 'soon') { showAlert(`🕒 ${z.commune} : interdiction à partir de ${st.range.split('–')[0]}`, 'warn'); speak(`Vous entrez dans ${z.commune}. Interdiction aux convois à partir de ${st.range.split('–')[0].replace(':', ' heures ')}.`); }
      else toast(`Entrée dans ${z.commune} : restriction d’horaire ${(z.ranges || []).map((r) => r.join('–')).join(', ')}, pas en cours.`, 5000);
    } else if (!inside && nav.zonesIn.has(z.id)) nav.zonesIn.delete(z.id);
  }
  // prévenir à l'avance : villes sur le tracé dans les 2 km
  if (full && !nav.opt.recordOnly && analysis?.zones?.length && nav.lastI != null) {
    const s = full.cum[nav.lastI] || 0;
    for (const { z, along } of analysis.zones) {
      const d = along - s; if (d > 0 && d < 2000 && !nav.said.has('zone' + z.id)) {
        nav.said.add('zone' + z.id); const st = zoneStatus(z, new Date(Date.now() + d / 15 * 1000));
        if (st) { showAlert(`🕒 ${z.commune} dans ${meters(d)} : ${st.st === 'active' ? 'interdit' : 'interdiction proche'} (${st.range})`, st.st === 'active' ? 'bad' : 'warn'); speak(`Dans ${sayM(d)}, ${z.commune}. Restriction d'horaire de ${st.range.replace('–', ' à ')}.`); }
      }
    }
  }
}
let alertTimer;
function showAlert(t, cls) { const a = $('#nav-alert'); a.textContent = t; a.className = cls === 'warn' ? 'warn' : ''; a.hidden = false; clearTimeout(alertTimer); alertTimer = setTimeout(hideAlert, 15000); }
function hideAlert() { $('#nav-alert').hidden = true; }
function stopNav() {
  if (!nav) return;
  if (nav.watch != null) navigator.geolocation.clearWatch(nav.watch);
  if (nav.sim) clearInterval(nav.sim);
  try { nav.lock?.release(); } catch (e) { /* rien */ }
  speechSynthesis?.cancel?.();
  const rec = nav.rec; nav = null;
  document.body.classList.remove('navigating'); $('#nav').hidden = true; hideAlert(); map.invalidateSize();
  if (meMarker) { map.removeLayer(meMarker); meMarker = null; }
  if (rec && rec.length > 1) {
    modal('Trajet enregistré', `<p>${km(cumul(rec).pop())} enregistrés (${rec.length} points).</p><label>Nom</label><input id="n" value="Trajet du ${new Date().toLocaleDateString('fr-FR')}"><div class="actions"><button class="primary" id="ok">Garder comme itinéraire</button><button id="no">Ne pas garder</button></div>`, (el) => {
      $('#ok', el).onclick = async () => { const r = newRoute(); r.name = $('#n', el).value; r.track = rec; DB.routes.push(r); save(); closeModal(); await openRoute(structuredClone(r)); toast('Trajet enregistré dans vos itinéraires.'); };
      $('#no', el).onclick = closeModal;
    });
  }
}
$('#nav-stop').onclick = stopNav;
$('#nav-voice').onclick = () => { DB.settings.voice = !DB.settings.voice; save(); $('#nav-voice').textContent = DB.settings.voice ? '🔊' : '🔇'; };
$('#nav-rec').onclick = () => { if (!nav) return; nav.rec = nav.rec ? null : []; $('#nav-rec').classList.toggle('on', !!nav.rec); toast(nav.rec ? 'Enregistrement du trajet démarré.' : 'Enregistrement arrêté.'); };
$('#nav-report').onclick = () => { const p = nav?.lastPos?.p; if (!p) return toast('Position GPS inconnue.'); addMineDialog({ lat: p[0], lng: p[1] }); };
document.addEventListener('visibilitychange', async () => { if (nav && document.visibilityState === 'visible' && 'wakeLock' in navigator) { try { nav.lock = await navigator.wakeLock.request('screen'); } catch (e) { /* rien */ } } });

// ---------------------------------------------------------------- boutons du panneau
$('#btn-draw').onclick = () => setDraw(!drawMode);
$('#btn-undo').onclick = () => { if (cur.waypoints.length) { cur.waypoints.pop(); cur.modes.pop(); changed(); } };
$('#btn-clear').onclick = () => { if ((cur.waypoints.length || cur.track) && !confirm('Effacer le tracé en cours ?')) return; const keep = { id: cur.id, name: cur.name, folder: cur.folder, created: cur.created }; cur = Object.assign(newRoute(), keep); changed(); };
$('#btn-save').onclick = saveRoute;
$('#btn-share').onclick = shareRoute;
$('#btn-go').onclick = startNavDialog;
$('#btn-search').onclick = searchDialog;
$('#route-name').onchange = () => (cur.name = $('#route-name').value);
$('#leg-mode').onchange = () => toast({ aimant: 'Aimant : entre deux points proches, le tracé suit le réseau TE choisi (Calques).', route: 'Suivre la route : liaison routière la plus rapide, sans tenir compte des réseaux TE.', droit: 'Ligne droite : pour forcer un passage précis entre deux points très proches.' }[$('#leg-mode').value], 5000);
$('#grip').onclick = () => { const s = $('#sheet'); if (s.classList.contains('min')) s.classList.remove('min'); else if (s.classList.contains('max')) { s.classList.remove('max'); s.classList.add('min'); } else s.classList.add('max'); };
$('#btn-locate').onclick = () => navigator.geolocation?.getCurrentPosition((p) => { const ll = [p.coords.latitude, p.coords.longitude]; map.setView(ll, 14); if (!meMarker) meMarker = L.marker(ll, { icon: L.divIcon({ className: '', html: '<div class="me"></div>', iconSize: [22, 22], iconAnchor: [11, 11] }) }).addTo(map); else meMarker.setLatLng(ll); }, () => toast('Position indisponible.'), { enableHighAccuracy: true });

// ---------------------------------------------------------------- démarrage
drawZones(); drawMine();
if (!readShared()) renderTab();
if ('serviceWorker' in navigator && location.protocol.startsWith('http')) navigator.serviceWorker.register('sw.js').catch(() => {});
window.GEP = { DB, get full() { return full; }, get analysis() { return analysis; }, openRoute, compute, cur: () => cur }; // pour les tests
