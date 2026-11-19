'use strict';

/* ------------------------------------------------------------------ *
 *  荒岛余生 · The Last Shore
 *  单文件生存游戏 —— 世界、系统与渲染
 * ------------------------------------------------------------------ */

const canvas = document.getElementById('game');
const ctx = canvas.getContext('2d');
const nightCanvas = document.createElement('canvas');
const nctx = nightCanvas.getContext('2d');

const TILE = 32;
const MAP_W = 68;
const MAP_H = 46;
const WORLD_W = MAP_W * TILE;
const WORLD_H = MAP_H * TILE;
const RESCUE_TIME = 180;
const $ = id => document.getElementById(id);

const ISLANDS = [
  {
    key: 'wreck', name: '坠机岛', en: 'WRECK SHORE', seed: 20261103,
    sx: 1, sy: 1, pond: true, hill: false, wreck: true, site: null,
    boars: 4, snakes: 2,
    intro: '潮水把你推上南岸。机身断成两截，黑匣子的信号灯在雨里一明一灭。先活下去，再找到能出海的东西。'
  },
  {
    key: 'mist', name: '雾林岛', en: 'MISTWOOD', seed: 77123,
    sx: 0.92, sy: 1.07, pond: true, hill: false, wreck: false, site: 'camp',
    boars: 6, snakes: 3, tint: 'rgba(150,183,177,.06)', jungle: 0.13,
    intro: '这座岛被雾和藤蔓包着。树冠密得看不见天，林子里不断传来树枝被踩断的声音。西岸有一顶旧帆布帐篷。'
  },
  {
    key: 'reef', name: '环礁岛', en: 'THE REEF', seed: 99117,
    sx: 1.12, sy: 0.84, pond: false, hill: false, wreck: false, site: 'cave',
    boars: 3, snakes: 7, tint: 'rgba(216,172,108,.05)', sand: 0.045, rock: 0.035,
    intro: '环礁像一枚被咬缺的戒指。没有淡水，只有滚烫的礁石和退潮后露出的洞口。岩缝里有东西在动。'
  },
  {
    key: 'cove', name: '沉船湾', en: 'WRECK COVE', seed: 31415,
    sx: 1.16, sy: 0.9, pond: false, hill: false, wreck: false, site: 'fuel',
    boars: 5, snakes: 6, tint: 'rgba(91,132,145,.06)', sand: 0.05, rock: 0.02,
    intro: '半艘货轮搁浅在礁盘上，船壳锈得发红。货舱里也许还有柴油，但退潮后的浅滩上全是蛇。'
  },
  {
    key: 'ash', name: '火山岛', en: 'ASHFALL', seed: 27182,
    sx: 0.9, sy: 1.02, pond: false, hill: false, wreck: false, site: 'spark',
    boars: 7, snakes: 4, tint: 'rgba(191,91,61,.065)', rock: 0.12, sand: 0.015,
    intro: '黑色的火山灰没过脚踝，空气里有硫磺味。观测站的铁皮屋被落石砸开，里面也许还有点火模块。'
  },
  {
    key: 'signal', name: '信号岛', en: 'SIGNAL CAY', seed: 55031,
    sx: 0.86, sy: 1.05, pond: true, hill: true, wreck: false, site: null,
    boars: 5, snakes: 3, tint: 'rgba(91,122,148,.055)', rock: 0.065,
    intro: '北面的高地终于出现在海平线上。旧气象站只剩一圈石基，但这里能看见航道。把无线电架起来，点燃烽火。'
  }
];
const islandCache = new Map();

let VW = 960, VH = 600, DPR = 1;
let map = [];
let reachable = [];
let nodes = [];
let fires = [];
let shelters = [];
let wreck = null;
let hill = null;
let beacon = null;
let dock = null;
let storySites = [];
let enemies = [];
let seed = 20261103;
let tNow = 0;
let lastTime = performance.now();
let hudLast = 0;
let uiModal = null;
let storyCloseCallback = null;
let invDirty = true;
let currentPrompt = '';
let nodeId = 0;
const keys = new Set();
const camera = { x: 0, y: 0, tx: 0, ty: 0 };

// 界面模式与移动端输入
const MODE_ORDER = ['auto', 'mobile', 'desktop'];
let interfaceMode = 'auto';
try {
  const savedMode = localStorage.getItem('island_mode');
  if (MODE_ORDER.includes(savedMode)) interfaceMode = savedMode;
} catch (e) { /* file:// 或隐私模式下忽略 */ }
const touchInput = { x: 0, y: 0, active: false };
let touchSprint = false;
let joyPointerId = null;
let joystickReset = () => {};

function rand() {
  seed = (seed * 1664525 + 1013904223) >>> 0;
  return seed / 4294967296;
}
function clamp(v, a, b) { return Math.max(a, Math.min(b, v)); }
function dist(x1, y1, x2, y2) { return Math.hypot(x2 - x1, y2 - y1); }
function hash2(x, y) {
  const n = Math.sin(x * 127.1 + y * 311.7) * 43758.5453;
  return n - Math.floor(n);
}
function noise(x, y) {
  const xi = Math.floor(x), yi = Math.floor(y);
  const xf = x - xi, yf = y - yi;
  const u = xf * xf * (3 - 2 * xf);
  const v = yf * yf * (3 - 2 * yf);
  const a = hash2(xi, yi), b = hash2(xi + 1, yi);
  const c = hash2(xi, yi + 1), d = hash2(xi + 1, yi + 1);
  return (a + (b - a) * u) * (1 - v) + (c + (d - c) * u) * v;
}
function fbm(x, y) {
  return noise(x, y) * 0.55 + noise(x * 2.03 + 5, y * 2.03 + 9) * 0.3 + noise(x * 4.1 + 13, y * 4.1 + 3) * 0.15;
}

/* --------------------------- 状态数据 --------------------------- */

const state = {
  phase: 'menu',
  gameTime: 0,
  day: 1,
  clock: 8 * 60,
  weather: 'clear',
  weatherTimer: 95,
  flash: 0,
  player: { x: 0, y: 0, dir: -Math.PI / 2, moving: false, walk: 0 },
  stats: { health: 100, hunger: 88, thirst: 82, energy: 100, warmth: 100 },
  inv: { wood: 0, stone: 0, fiber: 0, coconut: 1, berries: 2, fish: 0, cookedFish: 0, meat: 0, cookedMeat: 0, herb: 0, water: 0, cleanWater: 0, blackbox: 0, coil: 0, battery: 0, fuel: 0, spark: 0 },
  tools: { axe: false, spear: false, waterskin: false },
  story: { blackbox: false, coil: false, battery: false, fuel: false, spark: false, camp: false, cave: false, radio: false },
  currentIsland: 0,
  visited: [true, false, false, false, false, false],
  totalWood: 0,
  sick: false,
  resting: false,
  hillFound: false,
  hurt: 0,
  invuln: 0,
  attackCd: 0,
  shake: 0,
  bleed: 0,
  nightWave: 0,
  beaconWave: 0,
  kills: 0,
  fishCd: 0,
  floats: [],
  warnings: {},
  rescued: false
};

const ITEMS = {
  wood:      { name: '木材', icon: '🪵', desc: '建造和生火的基础材料。' },
  stone:     { name: '石块', icon: '🪨', desc: '沉重、结实，可以垒灶或制作工具。' },
  fiber:     { name: '植物纤维', icon: '🌾', desc: '搓绳、绑扎和制作工具都用得上。' },
  coconut:   { name: '椰子', icon: '🥥', desc: '安全的水和食物。点击食用。' },
  berries:   { name: '浆果', icon: '🍓', desc: '补充少量饥饿。点击食用。' },
  fish:      { name: '生鱼', icon: '🐟', desc: '生吃可能致病。在燃烧的篝火旁点击可烤熟。' },
  cookedFish:{ name: '烤鱼', icon: '🍢', desc: '熟食。点击食用。' },
  meat:      { name: '野猪肉', icon: '🥩', desc: '生肉。在燃烧的篝火旁点击可烤熟。' },
  cookedMeat:{ name: '烤肉', icon: '🍖', desc: '厚实的熟肉，能填饱肚子并恢复少量生命。' },
  herb:      { name: '草药', icon: '🌿', desc: '可以止血、治疗肠胃炎，并回复少量生命。' },
  water:     { name: '生水', icon: '💧', desc: '直接喝可能致病。在燃烧的篝火旁点击可烧开。' },
  cleanWater:{ name: '净水', icon: '🫧', desc: '干净的水。点击饮用。' },
  blackbox:  { name: '黑匣子', icon: '🎙️', desc: '飞机驾驶舱录音器。上面刻着一串旧呼救频率。' },
  coil:      { name: '铜线圈', icon: '🧲', desc: '从废弃营地的旧电台里拆下来的线圈。' },
  battery:   { name: '蓄电池', icon: '🔋', desc: '海蚀洞里留下的铅酸蓄电池，还有一点电。' },
  fuel:      { name: '柴油', icon: '🛢️', desc: '沉船货舱里剩下的柴油。无线电烽火台需要它驱动发电机。' },
  spark:     { name: '点火模块', icon: '⚡', desc: '火山观测站里的点火模块。没有它，无线电发不出脉冲。' }
};

const FOOD = {
  coconut:   { hunger: 10, thirst: 20 },
  berries:   { hunger: 10, thirst: 2 },
  fish:      { hunger: 18, thirst: 0 },
  cookedFish:{ hunger: 34, thirst: 2 },
  meat:      { hunger: 20, thirst: 0 },
  cookedMeat:{ hunger: 42, thirst: 2 },
  water:     { hunger: 0, thirst: 27 },
  cleanWater:{ hunger: 0, thirst: 36 }
};

const NODE_DEFS = {
  palm:      { name: '椰子树', verb: '采摘', uses: 4, regrow: 120, energy: 4 },
  tree:      { name: '丛林树', verb: '砍伐', uses: 3, regrow: 160, energy: 5 },
  bush:      { name: '浆果丛', verb: '采摘', uses: 3, regrow: 95, energy: 2 },
  rock:      { name: '岩石', verb: '敲碎', uses: 4, regrow: 200, energy: 7 },
  driftwood: { name: '漂流木', verb: '拾取', uses: 1, regrow: 0, energy: 2 },
  herb:      { name: '草药', verb: '采集', uses: 1, regrow: 130, energy: 1 }
};

const RECIPES = [
  { id: 'axe', name: '石斧', icon: '🪓', kind: '工具', desc: '显著提高伐木收益，是荒岛上的第一件工具。', cost: { wood: 3, stone: 2, fiber: 1 }, once: true },
  { id: 'spear', name: '长矛', icon: '🔱', kind: '工具', desc: '削尖的木矛。站在水边时可以捕鱼。', cost: { wood: 2, stone: 1, fiber: 2 }, once: true },
  { id: 'waterskin', name: '水囊', icon: '🧴', kind: '容器', desc: '装下一份生水带回营地，可在篝火旁烧开。', cost: { fiber: 3, coconut: 2 }, once: true },
  { id: 'campfire', name: '篝火', icon: '🔥', kind: '建筑', desc: '取暖、照明、烤鱼和烧水。会持续消耗木柴。', cost: { wood: 5, stone: 3 } },
  { id: 'shelter', name: '庇护所', icon: '⛺', kind: '建筑', desc: '抵挡夜里的风寒，夜晚可以睡到清晨。', cost: { wood: 7, fiber: 4 } },
  { id: 'beacon', name: '无线电烽火台', icon: '🗼', kind: '求救', desc: '带回黑匣子、线圈和蓄电池，在北部信号高地组装无线电并点燃烽火。', cost: { wood: 9, stone: 5, fiber: 3 } }
];

const QUESTS = [
  { id: 'wreck', text: '搜索残骸，取回黑匣子', test: () => state.story.blackbox },
  { id: 'wood', text: '收集 5 份木材', test: () => state.totalWood >= 5 },
  { id: 'axe', text: '制作一把石斧', test: () => state.tools.axe },
  { id: 'fire', text: '点燃一堆篝火', test: () => fires.some(f => f.fuel > 0) },
  { id: 'camp', text: '在雾林岛调查旧营地', test: () => state.story.coil },
  { id: 'cave', text: '在环礁岛搜索海蚀洞', test: () => state.story.battery },
  { id: 'fuel', text: '在沉船湾货舱取柴油', test: () => state.story.fuel },
  { id: 'spark', text: '在火山岛取点火模块', test: () => state.story.spark },
  { id: 'radio', text: '在信号岛高地组装无线电', test: () => state.story.radio },
  { id: 'rescue', text: '守住烽火直到救援抵达', test: () => state.rescued }
];

const WEATHERS = {
  clear:  { name: '晴朗', icon: '☀' },
  cloudy: { name: '多云', icon: '☁' },
  rain:   { name: '降雨', icon: '🌧' },
  storm:  { name: '风暴', icon: '⛈' }
};

/* --------------------------- 世界生成 --------------------------- */

function generateWorld(islandIndex = 0) {
  const profile = ISLANDS[islandIndex] || ISLANDS[0];
  seed = profile.seed;
  map = [];
  nodes = [];
  fires = [];
  shelters = [];
  enemies = [];
  wreck = null;
  hill = null;
  beacon = null;
  dock = null;
  storySites = [];
  state.currentIsland = islandIndex;
  const cx = MAP_W / 2, cy = MAP_H / 2;
  const shapeX = profile.sx || 1;
  const shapeY = profile.sy || 1;

  for (let y = 0; y < MAP_H; y++) {
    const row = [];
    for (let x = 0; x < MAP_W; x++) {
      const nx = (x - cx) / (26.5 * shapeX);
      const ny = (y - cy) / (15.8 * shapeY);
      const ang = Math.atan2(ny, nx);
      const coast = 1 + 0.08 * Math.sin(3 * ang + 1.2) + 0.05 * Math.sin(5 * ang + 2.3) + 0.032 * Math.sin(8 * ang + 0.4);
      const d = Math.hypot(nx, ny) * (1 + 0.10 * (fbm(x * 0.21, y * 0.21) - 0.5));
      let type;
      const sandEdge = 0.085 + (profile.sand || 0);
      const rockBias = profile.rock || 0;
      if (d > coast + 0.13) type = 'deep';
      else if (d > coast) type = 'shallow';
      else if (d > coast - sandEdge) type = 'sand';
      else {
        const inland = 1 - d / coast;
        const n = fbm(x * 0.16 + 7.2, y * 0.16 + 13.7);
        if (inland > 0.70 - rockBias && n > 0.47 - rockBias * 0.7) type = 'rock';
        else if (inland > 0.34 - (profile.jungle || 0)) type = 'jungle';
        else type = 'grass';
      }
      const solid = type === 'deep' || type === 'shallow' || type === 'rock';
      row.push({ type, solid, v: hash2(x, y), hill: false });
    }
    map.push(row);
  }

  // 岛内淡水池塘（环礁岛没有淡水）
  if (profile.pond) {
    const pondX = cx + 7, pondY = cy - 2;
    for (let y = 0; y < MAP_H; y++) for (let x = 0; x < MAP_W; x++) {
      const t = map[y][x];
      if (t.solid || t.type === 'sand') continue;
      const dd = Math.pow((x - pondX) / 3.4, 2) + Math.pow((y - pondY) / 2.5, 2);
      if (dd < 1) {
        t.type = 'pond';
        t.solid = true;
        t.pond = true;
      }
    }
  }

  // 出生点：南部沙滩
  let spawnTile = null;
  for (let y = MAP_H - 3; y >= cy && !spawnTile; y--) {
    let best = null, bd = 99;
    for (let x = 2; x < MAP_W - 2; x++) {
      const t = map[y][x];
      if (!t.solid && (t.type === 'sand' || t.type === 'grass') && Math.abs(x - cx) < bd) {
        bd = Math.abs(x - cx);
        best = { x, y };
      }
    }
    if (best) spawnTile = best;
  }
  if (!spawnTile) spawnTile = { x: Math.floor(cx), y: Math.floor(cy) };
  const spawn = { tx: spawnTile.x, ty: spawnTile.y, x: (spawnTile.x + 0.5) * TILE, y: (spawnTile.y + 0.5) * TILE };

  // 连通区域
  reachable = [];
  const seen = new Set();
  const queue = [[spawn.tx, spawn.ty]];
  seen.add(spawn.tx + ',' + spawn.ty);
  while (queue.length) {
    const [x, y] = queue.shift();
    reachable.push({ x, y });
    for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const nx2 = x + dx, ny2 = y + dy;
      if (nx2 < 0 || ny2 < 0 || nx2 >= MAP_W || ny2 >= MAP_H) continue;
      const k = nx2 + ',' + ny2;
      if (seen.has(k) || map[ny2][nx2].solid) continue;
      seen.add(k);
      queue.push([nx2, ny2]);
    }
  }

  // 信号高地（只有最后的信号岛有）
  if (profile.hill) {
    const targetX = cx - 3, targetY = cy - 9;
    let bestHill = null, bestScore = Infinity;
    for (const r of reachable) {
      if (r.x < 5 || r.y < 5 || r.x > MAP_W - 6 || r.y > MAP_H - 6) continue;
      if (map[r.y][r.x].solid || map[r.y][r.x].type === 'pond') continue;
      const score = Math.hypot(r.x - targetX, r.y - targetY) + (r.y > cy ? 8 : 0);
      if (score < bestScore) { bestScore = score; bestHill = r; }
    }
    if (bestHill) {
      hill = { tx: bestHill.x, ty: bestHill.y, x: (bestHill.x + 0.5) * TILE, y: (bestHill.y + 0.5) * TILE };
      map[bestHill.y][bestHill.x].hill = true;
    }
  }

  const occupied = new Set();
  function addNode(type, tx, ty) {
    const key = tx + ',' + ty;
    if (occupied.has(key)) return false;
    if (tx < 0 || ty < 0 || tx >= MAP_W || ty >= MAP_H) return false;
    const t = map[ty][tx];
    if (t.solid) return false;
    const def = NODE_DEFS[type];
    nodes.push({
      id: ++nodeId, type, tx, ty,
      x: tx * TILE + TILE / 2 + (rand() - 0.5) * 14,
      y: ty * TILE + TILE / 2 + (rand() - 0.5) * 10,
      uses: def.uses, maxUses: def.uses, regrowAt: 0,
      phase: rand() * 6.28
    });
    occupied.add(key);
    return true;
  }

  for (const r of reachable) {
    const t = map[r.y][r.x];
    if (t.hill) continue;
    if (dist((r.x + 0.5) * TILE, (r.y + 0.5) * TILE, spawn.x, spawn.y) < 42) continue;
    const roll = rand();
    if (t.type === 'sand') {
      if (roll < 0.048) addNode('palm', r.x, r.y);
      else if (roll < 0.060) addNode('bush', r.x, r.y);
      else if (roll < 0.070) addNode('driftwood', r.x, r.y);
    } else if (t.type === 'grass') {
      if (roll < 0.018) addNode('palm', r.x, r.y);
      else if (roll < 0.075) addNode('bush', r.x, r.y);
      else if (roll < 0.092) addNode('herb', r.x, r.y);
      else if (roll < 0.108) addNode('rock', r.x, r.y);
    } else if (t.type === 'jungle') {
      if (roll < 0.115) addNode('tree', r.x, r.y);
      else if (roll < 0.152) addNode('bush', r.x, r.y);
      else if (roll < 0.176) addNode('herb', r.x, r.y);
      else if (roll < 0.190) addNode('rock', r.x, r.y);
    }
  }

  // 保证营地与高地附近有基础资源
  function ensureNear(type, ax, ay, rad, count) {
    for (let i = 0; i < count; i++) {
      const cands = reachable
        .filter(r => !occupied.has(r.x + ',' + r.y) && !map[r.y][r.x].hill && dist((r.x + 0.5) * TILE, (r.y + 0.5) * TILE, ax, ay) < rad * TILE)
        .sort(() => rand() - 0.5);
      if (cands[0]) addNode(type, cands[0].x, cands[0].y);
    }
  }
  ensureNear('palm', spawn.x, spawn.y, 7, 4);
  ensureNear('rock', spawn.x, spawn.y, 7, 2);
  ensureNear('bush', spawn.x, spawn.y, 6, 2);
  if (hill) {
    ensureNear('palm', hill.x, hill.y, 8, 5);
    ensureNear('rock', hill.x, hill.y, 8, 3);
    ensureNear('bush', hill.x, hill.y, 7, 2);
  }

  // 飞机残骸（只出现在坠机岛）
  if (profile.wreck) {
    let wreckTile = null, wd = Infinity;
    for (const r of reachable) {
      const d2 = Math.hypot(r.x - spawn.tx - 2.5, r.y - spawn.ty - 0.5);
      if (d2 < wd && dist((r.x + 0.5) * TILE, (r.y + 0.5) * TILE, spawn.x, spawn.y) < 130 && !map[r.y][r.x].solid) {
        wd = d2;
        wreckTile = r;
      }
    }
    if (wreckTile) {
      wreck = {
        x: (wreckTile.x + 0.5) * TILE,
        y: (wreckTile.y + 0.5) * TILE,
        looted: false
      };
    } else {
      wreck = { x: spawn.x + 70, y: spawn.y - 12, looted: false };
    }
  }

  // 主线地点：每个岛只放一个关键地点
  if (profile.site) {
    const side = (profile.site === 'camp' || profile.site === 'fuel') ? 'west' : 'east';
    const sitePool = reachable.filter(r => {
      const t = map[r.y][r.x];
      if (t.solid || t.type === 'pond') return false;
      if (r.x < 4 || r.y < 4 || r.x > MAP_W - 5 || r.y > MAP_H - 5) return false;
      const px = (r.x + 0.5) * TILE, py = (r.y + 0.5) * TILE;
      const d = dist(px, py, spawn.x, spawn.y);
      if (d < 220 || d > 1000) return false;
      if (side === 'west' && r.x > cx - 4) return false;
      if (side === 'east' && r.x < cx + 4) return false;
      if (hill && dist(px, py, hill.x, hill.y) < 190) return false;
      if (wreck && dist(px, py, wreck.x, wreck.y) < 180) return false;
      return true;
    });
    sitePool.sort((a, b) => side === 'west' ? a.x - b.x : b.x - a.x);
    let siteTile = sitePool[0] || null;
    if (!siteTile) {
      const fallback = reachable
        .filter(r => !map[r.y][r.x].solid && map[r.y][r.x].type !== 'pond')
        .filter(r => !hill || dist((r.x + 0.5) * TILE, (r.y + 0.5) * TILE, hill.x, hill.y) > 150)
        .filter(r => !wreck || dist((r.x + 0.5) * TILE, (r.y + 0.5) * TILE, wreck.x, wreck.y) > 140);
      siteTile = fallback.sort((a, b) => side === 'west' ? a.x - b.x : b.x - a.x)[0] || null;
    }
    if (siteTile) {
      storySites.push({
        id: profile.site,
        name: ({ camp: '西岸废弃营地', cave: '东侧海蚀洞', fuel: '沉船货舱', spark: '火山观测站' })[profile.site],
        kind: profile.site,
        x: (siteTile.x + 0.5) * TILE,
        y: (siteTile.y + 0.5) * TILE,
        found: false
      });
    }
  }

  // 每个岛南岸都有一只可以出海的木筏
  const dockCandidates = reachable.filter(r => {
    const t = map[r.y][r.x];
    if (t.solid || t.type === 'pond') return false;
    const px = (r.x + 0.5) * TILE, py = (r.y + 0.5) * TILE;
    const d = dist(px, py, spawn.x, spawn.y);
    if (d < 70 || d > 190) return false;
    if (storySites.some(s => dist(px, py, s.x, s.y) < 100)) return false;
    return true;
  });
  dockCandidates.sort((a, b) => {
    const ay = (a.y + 0.5) * TILE, by = (b.y + 0.5) * TILE;
    return (by - ay) || (Math.abs(a.x - spawn.tx) - Math.abs(b.x - spawn.tx));
  });
  if (dockCandidates[0]) {
    dock = {
      x: (dockCandidates[0].x + 0.5) * TILE,
      y: (dockCandidates[0].y + 0.5) * TILE
    };
  } else {
    dock = { x: spawn.x + 42, y: spawn.y };
  }

  spawnEnemies(spawn);

  state.player.x = spawn.x;
  state.player.y = spawn.y;
  camera.x = clamp(spawn.x - VW / 2, 0, Math.max(0, WORLD_W - VW));
  camera.y = clamp(spawn.y - VH / 2, 0, Math.max(0, WORLD_H - VH));
  camera.tx = camera.x;
  camera.ty = camera.y;
}

const ENEMY_DEFS = {
  boar:  { name: '野猪', hp: 4, speed: 86, aggro: 220, damage: 16, radius: 20 },
  snake: { name: '岛蛇', hp: 1, speed: 100, aggro: 130, damage: 9, radius: 11 }
};

function spawnEnemies(spawn) {
  enemies = [];
  const used = [];
  const pool = reachable.filter(r => {
    const t = map[r.y][r.x];
    if (t.solid || t.type === 'pond') return false;
    const px = (r.x + 0.5) * TILE, py = (r.y + 0.5) * TILE;
    const d = dist(px, py, spawn.x, spawn.y);
    if (d < 340 || d > 1250) return false;
    if (hill && dist(px, py, hill.x, hill.y) < 180) return false;
    if (wreck && dist(px, py, wreck.x, wreck.y) < 160) return false;
    return true;
  });
  const takeSpot = () => {
    for (let tries = 0; tries < 90; tries++) {
      if (!pool.length) return null;
      const r = pool[Math.floor(rand() * pool.length)];
      const px = (r.x + 0.5) * TILE, py = (r.y + 0.5) * TILE;
      if (!walkableAt(px, py)) continue;
      if (used.some(u => dist(px, py, u.x, u.y) < 95)) continue;
      used.push({ x: px, y: py });
      return { x: px, y: py };
    }
    return null;
  };
  const profile = ISLANDS[state.currentIsland] || ISLANDS[0];
  for (let i = 0; i < (profile.boars || 4); i++) {
    const s = takeSpot();
    if (s) addEnemy('boar', s.x, s.y);
  }
  for (let i = 0; i < (profile.snakes || 2); i++) {
    const s = takeSpot();
    if (s) addEnemy('snake', s.x, s.y);
  }
  // 旧营地与海蚀洞各有守卫，调查前要先清出空间
  storySites.forEach(site => {
    for (let i = 0; i < 12; i++) {
      const a = rand() * Math.PI * 2;
      const r = 92 + rand() * 34;
      const x = site.x + Math.cos(a) * r;
      const y = site.y + Math.sin(a) * r;
      if (!walkableAt(x, y)) continue;
      addEnemy(site.kind === 'camp' ? 'boar' : 'snake', x, y, true);
      break;
    }
  });
}

function addEnemy(type, x, y, guard = false) {
  const def = ENEMY_DEFS[type];
  enemies.push({
    type, name: def.name, x, y, hp: def.hp, maxHp: def.hp,
    speed: def.speed, aggro: def.aggro, damage: def.damage, radius: def.radius,
    dir: rand() * Math.PI * 2, phase: rand() * 6.28, wanderT: 0,
    attackCd: 0, stun: 0, hitFlash: 0, dead: false, guard
  });
}

function islandUnlocked(index) {
  if (index === 0) return true;
  if (index === 1) return state.story.blackbox;
  if (index === 2) return state.story.coil;
  if (index === 3) return state.story.battery;
  if (index === 4) return state.story.fuel;
  if (index === 5) return state.story.spark;
  return false;
}

function islandRequirement(index) {
  if (index === 1) return '需要黑匣子';
  if (index === 2) return '需要铜线圈';
  if (index === 3) return '需要蓄电池';
  if (index === 4) return '需要柴油';
  if (index === 5) return '需要点火模块';
  return '';
}

function saveCurrentIsland() {
  if (!map.length) return;
  islandCache.set(state.currentIsland, {
    map, reachable, nodes, fires, shelters, wreck, hill, beacon, dock,
    storySites, enemies,
    player: { x: state.player.x, y: state.player.y, dir: state.player.dir },
    camera: { x: camera.x, y: camera.y, tx: camera.tx, ty: camera.ty }
  });
}

function loadIsland(index) {
  const cached = islandCache.get(index);
  resetTouchInput(true);
  keys.clear();
  state.currentIsland = index;
  state.visited[index] = true;
  if (cached) {
    map = cached.map;
    reachable = cached.reachable;
    nodes = cached.nodes;
    fires = cached.fires;
    shelters = cached.shelters;
    wreck = cached.wreck;
    hill = cached.hill;
    beacon = cached.beacon;
    dock = cached.dock;
    storySites = cached.storySites;
    enemies = cached.enemies;
    state.player.x = cached.player.x;
    state.player.y = cached.player.y;
    state.player.dir = cached.player.dir;
    camera.x = cached.camera.x;
    camera.y = cached.camera.y;
    camera.tx = cached.camera.tx;
    camera.ty = cached.camera.ty;
  } else {
    generateWorld(index);
  }
  state.phase = 'playing';
  refreshQuests();
  updateHUD();
}

/* --------------------------- 输入与界面 --------------------------- */

function resize() {
  DPR = Math.min(window.devicePixelRatio || 1, 2);
  VW = window.innerWidth;
  VH = window.innerHeight;
  canvas.width = Math.floor(VW * DPR);
  canvas.height = Math.floor(VH * DPR);
  canvas.style.width = VW + 'px';
  canvas.style.height = VH + 'px';
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  nightCanvas.width = Math.floor(VW * DPR);
  nightCanvas.height = Math.floor(VH * DPR);
}
window.addEventListener('resize', () => {
  resize();
  if (interfaceMode === 'auto') applyInterfaceMode();
});
if (window.visualViewport) {
  window.visualViewport.addEventListener('resize', resize);
}

function prefersTouchLayout() {
  const coarse = window.matchMedia && window.matchMedia('(pointer: coarse)').matches;
  const noHover = window.matchMedia && window.matchMedia('(hover: none)').matches;
  const touch = (navigator.maxTouchPoints || 0) > 0;
  return (coarse && noHover) || (touch && window.innerWidth < 900) || window.innerWidth < 760;
}

function activeInterfaceMode() {
  if (interfaceMode === 'mobile') return 'mobile';
  if (interfaceMode === 'desktop') return 'desktop';
  return prefersTouchLayout() ? 'mobile' : 'desktop';
}

function resetTouchInput(stopSprint = false) {
  touchInput.x = 0;
  touchInput.y = 0;
  touchInput.active = false;
  if (stopSprint) {
    touchSprint = false;
    const sprintBtn = document.querySelector('[data-touch="sprint"]');
    if (sprintBtn) sprintBtn.classList.remove('active');
  }
  try { joystickReset(); } catch (e) { /* 忽略指针释放异常 */ }
}

function applyInterfaceMode() {
  const mode = activeInterfaceMode();
  const mobile = mode === 'mobile';
  document.body.classList.toggle('mode-mobile', mobile);
  document.body.classList.toggle('mode-desktop', !mobile);
  const labels = { auto: '自动', desktop: '桌面', mobile: '手机' };
  const btn = $('modeBtn');
  if (btn) {
    btn.textContent = labels[interfaceMode];
    btn.title = `界面模式：${labels[interfaceMode]}（当前为${mobile ? '手机布局' : '桌面布局'}）· 点击切换`;
    btn.setAttribute('aria-label', btn.title);
  }
  const startBtn = $('startModeBtn');
  if (startBtn) {
    startBtn.textContent = '界面：' + labels[interfaceMode];
    startBtn.title = `当前为${mobile ? '手机布局' : '桌面布局'}，点击切换`;
  }
  if (!mobile) {
    resetTouchInput(true);
    $('quest').classList.remove('mobile-open');
  }
}

function cycleInterfaceMode() {
  interfaceMode = MODE_ORDER[(MODE_ORDER.indexOf(interfaceMode) + 1) % MODE_ORDER.length];
  try { localStorage.setItem('island_mode', interfaceMode); } catch (e) { /* 忽略 */ }
  applyInterfaceMode();
  if (state.phase === 'playing') {
    const labels = { auto: '自动', desktop: '桌面', mobile: '手机' };
    log('界面已切换：' + labels[interfaceMode] + '布局', 'warn');
  }
}

function setupTouchControls() {
  const joy = $('joystick');
  const knob = $('joyKnob');
  if (!joy || !knob) return;

  const setFromEvent = e => {
    const r = joy.getBoundingClientRect();
    const cx = r.left + r.width / 2;
    const cy = r.top + r.height / 2;
    let dx = e.clientX - cx;
    let dy = e.clientY - cy;
    const maxR = r.width * 0.31;
    const len = Math.hypot(dx, dy);
    if (len > maxR) {
      dx = dx / len * maxR;
      dy = dy / len * maxR;
    }
    const strength = Math.min(1, len / maxR);
    if (strength < 0.14) {
      touchInput.x = 0;
      touchInput.y = 0;
      touchInput.active = false;
    } else {
      const n = Math.hypot(dx, dy) || 1;
      touchInput.x = dx / n * strength;
      touchInput.y = dy / n * strength;
      touchInput.active = true;
    }
    knob.style.transform = `translate(${dx}px, ${dy}px)`;
  };

  joystickReset = () => {
    if (joyPointerId !== null) {
      try { joy.releasePointerCapture(joyPointerId); } catch (e) { /* 已释放 */ }
      joyPointerId = null;
    }
    touchInput.x = 0;
    touchInput.y = 0;
    touchInput.active = false;
    knob.style.transform = 'translate(0, 0)';
    joy.classList.remove('active');
  };

  joy.addEventListener('pointerdown', e => {
    if (state.phase !== 'playing' || uiModal) return;
    e.preventDefault();
    joyPointerId = e.pointerId;
    joy.classList.add('active');
    try { joy.setPointerCapture(e.pointerId); } catch (err) { /* 忽略 */ }
    setFromEvent(e);
  });
  joy.addEventListener('pointermove', e => {
    if (e.pointerId !== joyPointerId) return;
    e.preventDefault();
    setFromEvent(e);
  });
  const end = e => {
    if (joyPointerId === null || e.pointerId !== joyPointerId) return;
    joyPointerId = null;
    touchInput.x = 0;
    touchInput.y = 0;
    touchInput.active = false;
    knob.style.transform = 'translate(0, 0)';
    joy.classList.remove('active');
  };
  joy.addEventListener('pointerup', end);
  joy.addEventListener('pointercancel', end);
  joy.addEventListener('lostpointercapture', end);

  document.querySelectorAll('[data-touch]').forEach(btn => {
    btn.addEventListener('pointerdown', e => {
      if (state.phase !== 'playing' || uiModal) return;
      e.preventDefault();
      e.stopPropagation();
      const action = btn.dataset.touch;
      if (action === 'interact') interact();
      else if (action === 'craft') openCraft();
      else if (action === 'rest') { toggleRest(); btn.classList.toggle('active', state.resting); }
      else if (action === 'sprint') {
        touchSprint = !touchSprint;
        btn.classList.toggle('active', touchSprint);
      }
      if (window.navigator && typeof navigator.vibrate === 'function') {
        try { navigator.vibrate(8); } catch (err) { /* 忽略 */ }
      }
    });
  });
  $('touchUI').addEventListener('contextmenu', e => e.preventDefault());
}

function log(message, kind = '') {
  const box = $('log');
  const el = document.createElement('div');
  el.className = 'toast ' + kind;
  el.textContent = message;
  box.prepend(el);
  while (box.children.length > 4) box.lastChild.remove();
  setTimeout(() => {
    el.style.transition = 'opacity .5s';
    el.style.opacity = '0';
    setTimeout(() => el.remove(), 520);
  }, 5200);
}

function floatText(x, y, text, color) {
  state.floats.push({ x, y, text, color: color || '#f4e3b8', life: 1.3, max: 1.3 });
}

function addItem(id, n) {
  if (!ITEMS[id] || n <= 0) return;
  state.inv[id] = (state.inv[id] || 0) + n;
  if (id === 'wood') state.totalWood += n;
  invDirty = true;
  const p = state.player;
  floatText(p.x, p.y - 32, '+' + n + ' ' + ITEMS[id].name);
}

function removeItem(id, n = 1) {
  if ((state.inv[id] || 0) < n) return false;
  state.inv[id] -= n;
  if (state.inv[id] <= 0) state.inv[id] = 0;
  invDirty = true;
  return true;
}

function canPay(cost) {
  return Object.keys(cost).every(k => (state.inv[k] || 0) >= cost[k]);
}
function pay(cost) {
  Object.keys(cost).forEach(k => { state.inv[k] -= cost[k]; });
  invDirty = true;
}
function costText(cost) {
  return Object.keys(cost).map(k => {
    const ok = (state.inv[k] || 0) >= cost[k];
    return `<span class="${ok ? 'have' : 'lack'}">${ITEMS[k].name} ${state.inv[k] || 0}/${cost[k]}</span>`;
  }).join('');
}
function missingText(cost) {
  return Object.keys(cost).filter(k => (state.inv[k] || 0) < cost[k])
    .map(k => `${ITEMS[k].name}×${cost[k] - (state.inv[k] || 0)}`).join('、');
}

function renderInventory() {
  const box = $('inventory');
  const entries = Object.keys(ITEMS).filter(k => state.inv[k] > 0);
  let html = '';
  entries.forEach(id => {
    const it = ITEMS[id];
    html += `<button class="slot" data-item="${id}" title="${it.name}：${it.desc}">
      <span>${it.icon}</span><b class="n">${state.inv[id]}</b></button>`;
  });
  for (let i = entries.length; i < 8; i++) html += '<div class="slot empty">·</div>';
  box.innerHTML = html;
  invDirty = false;

  const toolNames = { axe: '石斧', spear: '长矛', waterskin: '水囊' };
  const badges = Object.keys(state.tools).filter(k => state.tools[k]).map(k => `<span class="tool-badge">${toolNames[k]}</span>`).join('');
  $('tools').innerHTML = badges || '<span class="tool-badge" style="opacity:.45">暂无工具</span>';
}

function buildQuestList() {
  $('questList').innerHTML = QUESTS.map(q => `<li data-q="${q.id}">${q.text}</li>`).join('');
}

function refreshQuests() {
  if (state.phase !== 'playing') return;
  let firstIncomplete = true;
  let completed = 0;
  QUESTS.forEach(q => {
    const el = $('questList').querySelector(`[data-q="${q.id}"]`);
    if (!el) return;
    const done = !!q.test();
    const was = el.classList.contains('done');
    el.classList.toggle('done', done);
    el.classList.remove('active');
    if (!done && firstIncomplete) {
      el.classList.add('active');
      firstIncomplete = false;
    }
    if (done) completed++;
    if (done && !was) log('目标完成：' + q.text, 'good');
  });
  $('questCount').textContent = completed + '/' + QUESTS.length;
}

function updateHUD() {
  const s = state.stats;
  ['health', 'hunger', 'thirst', 'energy', 'warmth'].forEach(k => {
    const v = Math.round(clamp(s[k], 0, 100));
    $('v-' + k).textContent = v;
    $('b-' + k).style.width = v + '%';
  });
  const hh = Math.floor(state.clock / 60) % 24;
  const mm = Math.floor(state.clock % 60);
  $('dayText').textContent = '第 ' + state.day + ' 天';
  $('clockText').textContent = String(hh).padStart(2, '0') + ':' + String(mm).padStart(2, '0');
  const w = WEATHERS[state.weather];
  $('weatherIcon').textContent = w.icon;
  $('weatherText').textContent = w.name;
  $('phaseText').textContent = getPhaseName();

  let tags = '';
  if (state.sick) tags += '<span class="tag">肠胃炎</span>';
  if (state.bleed > 0) tags += '<span class="tag cold">流血</span>';
  if (s.warmth < 35) tags += '<span class="tag cold">失温</span>';
  if (s.energy <= 0) tags += '<span class="tag cold">力竭</span>';
  if (enemies.some(e => !e.dead && dist(state.player.x, state.player.y, e.x, e.y) < e.aggro)) {
    tags += '<span class="tag cold">野兽逼近</span>';
  }
  $('statusTags').innerHTML = tags;
  $('chapterText').textContent = storyChapter();

  let body = '状态良好';
  if (state.bleed > 0) body = '伤口在流血';
  else if (state.sick) body = '肠胃不适';
  else if (s.warmth < 30) body = '体温过低';
  else if (s.thirst < 20) body = '严重口渴';
  else if (s.hunger < 20) body = '饥肠辘辘';
  else if (s.energy < 20) body = '精疲力竭';
  $('bodyState').textContent = body;

  const target = storyTarget();
  if (target) {
    const dx = target.x - state.player.x;
    const dy = target.y - state.player.y;
    const d = Math.round(Math.hypot(dx, dy) / 16);
    $('compassArrow').style.transform = `rotate(${Math.atan2(dy, dx)}rad)`;
    $('compassLabel').textContent = target.label;
    $('compassDist').textContent = d + ' m';
    $('compassBar').style.width = clamp(100 - d / 11, 4, 100) + '%';
    $('mcArrow').style.transform = `rotate(${Math.atan2(dy, dx)}rad)`;
    $('mcLabel').textContent = target.label;
    $('mcDist').textContent = d + ' m';
  }
  $('compass').style.opacity = target ? '1' : '.35';

  const restTouch = document.querySelector('[data-touch="rest"]');
  if (restTouch) restTouch.classList.toggle('active', state.resting);
  const sprintTouch = document.querySelector('[data-touch="sprint"]');
  if (sprintTouch) sprintTouch.classList.toggle('active', touchSprint);

  if (beacon) {
    $('finale').classList.remove('hidden');
    $('rescueTime').textContent = Math.max(0, Math.ceil(RESCUE_TIME - beacon.progress));
    $('fuelBar').style.width = clamp(beacon.fuel / 100 * 100, 0, 100) + '%';
    $('fuelText').textContent = beacon.fuel > 0
      ? `烽火燃料 ${Math.ceil(beacon.fuel)} 秒 · 靠近按 E 添柴`
      : '烽火即将熄灭！快回到高地添柴！';
    $('fuelText').style.color = beacon.fuel > 0 ? '#a68c6b' : '#e89b84';
  } else {
    $('finale').classList.add('hidden');
  }

  const c = getContext();
  const prompt = $('prompt');
  if (c) {
    const label = c.label;
    if (label !== currentPrompt) {
      $('promptText').textContent = label;
      currentPrompt = label;
    }
    prompt.classList.remove('hidden');
  } else {
    prompt.classList.add('hidden');
    currentPrompt = '';
  }

  if (invDirty) renderInventory();
  refreshQuests();
}

/* --------------------------- 时间与天气 --------------------------- */

function getPhaseName() {
  const h = state.clock / 60;
  if (h >= 5 && h < 8) return '清晨';
  if (h >= 8 && h < 17) return '白昼';
  if (h >= 17 && h < 19) return '黄昏';
  return '夜晚';
}
function isNight() {
  const h = state.clock / 60;
  return h >= 19 || h < 6;
}
function darkness() {
  const h = state.clock / 60;
  if (h >= 20 || h < 5) return 0.60;
  if (h >= 17) return (h - 17) / 3 * 0.60;
  if (h < 7) return (1 - (h - 5) / 2) * 0.60;
  return 0;
}
function changeWeather() {
  const roll = Math.random();
  let next = 'clear';
  if (roll < 0.12) next = 'storm';
  else if (roll < 0.35) next = 'rain';
  else if (roll < 0.62) next = 'cloudy';
  state.weather = next;
  state.weatherTimer = 70 + Math.random() * 80;
  if (next === 'rain') log('云层压低，雨点落了下来。雨水让空气变得潮湿。', 'warn');
  else if (next === 'storm') log('风暴逼近。海面翻涌，体温流失得更快。', 'bad');
  else if (next === 'cloudy') log('云层遮住了太阳，天色暗了一些。');
  else log('云层散开，阳光重新照在岛上。', 'good');
}

/* --------------------------- 交互 --------------------------- */

function nearestNode(maxDist = 56) {
  let best = null, bd = maxDist;
  for (const n of nodes) {
    if (n.uses <= 0) continue;
    if (n.type === 'driftwood' && n.uses <= 0) continue;
    const d = dist(state.player.x, state.player.y, n.x, n.y);
    if (d < bd) { bd = d; best = n; }
  }
  return best;
}
function nearestFire(maxDist = 82) {
  let best = null, bd = maxDist;
  for (const f of fires) {
    const d = dist(state.player.x, state.player.y, f.x, f.y);
    if (d < bd) { bd = d; best = f; }
  }
  return best;
}
function litFireNear(maxDist = 132) {
  return fires.some(f => f.fuel > 0 && dist(state.player.x, state.player.y, f.x, f.y) < maxDist)
    || (beacon && beacon.fuel > 0 && dist(state.player.x, state.player.y, beacon.x, beacon.y) < 150);
}
function nearestShelter(maxDist = 80) {
  let best = null, bd = maxDist;
  for (const s of shelters) {
    const d = dist(state.player.x, state.player.y, s.x, s.y);
    if (d < bd) { bd = d; best = s; }
  }
  return best;
}
function nearHill(maxDist = 112) {
  return !!hill && dist(state.player.x, state.player.y, hill.x, hill.y) < maxDist;
}
function nearBeacon(maxDist = 105) {
  return !!beacon && dist(state.player.x, state.player.y, beacon.x, beacon.y) < maxDist;
}
function nearPond(maxDist = 76) {
  const ptx = Math.floor(state.player.x / TILE);
  const pty = Math.floor(state.player.y / TILE);
  for (let y = pty - 2; y <= pty + 2; y++) for (let x = ptx - 2; x <= ptx + 2; x++) {
    if (!map[y] || !map[y][x] || map[y][x].type !== 'pond') continue;
    const cx = (x + 0.5) * TILE, cy = (y + 0.5) * TILE;
    if (dist(state.player.x, state.player.y, cx, cy) < maxDist) return true;
  }
  return false;
}
function nearWater(maxDist = 80) {
  const fx = state.player.x + Math.cos(state.player.dir) * 42;
  const fy = state.player.y + Math.sin(state.player.dir) * 42;
  for (let y = 0; y < MAP_H; y++) {
    // only examine tiles within two tiles of the facing point
    const ty = Math.floor(fy / TILE), tx = Math.floor(fx / TILE);
    if (Math.abs(y - ty) > 2) continue;
    for (let x = Math.max(0, tx - 2); x <= Math.min(MAP_W - 1, tx + 2); x++) {
      const t = map[y][x];
      if (t.type !== 'shallow' && t.type !== 'deep') continue;
      if (dist(fx, fy, (x + 0.5) * TILE, (y + 0.5) * TILE) < maxDist) return true;
    }
  }
  return false;
}

function nearestEnemy(maxDist = 68) {
  let best = null, bd = maxDist;
  for (const e of enemies) {
    if (e.dead) continue;
    const d = dist(state.player.x, state.player.y, e.x, e.y);
    if (d < bd) { bd = d; best = e; }
  }
  return best;
}

function attackEnemy(e) {
  if (!e || e.dead || state.phase !== 'playing') return;
  if (state.attackCd > 0) return;
  const p = state.player;
  const spear = !!state.tools.spear;
  const damage = spear ? 2 : 1;
  state.attackCd = 0.45;
  state.stats.energy = clamp(state.stats.energy - 1.5, 0, 100);
  p.dir = Math.atan2(e.y - p.y, e.x - p.x);
  e.hp -= damage;
  e.hitFlash = 0.28;
  e.stun = 0.55;
  state.shake = Math.max(state.shake, 0.1);
  e.attackCd = Math.max(e.attackCd, 0.8);
  const a = Math.atan2(e.y - p.y, e.x - p.x);
  const nx = e.x + Math.cos(a) * 18;
  const ny = e.y + Math.sin(a) * 18;
  if (walkableAt(nx, e.y)) e.x = nx;
  if (walkableAt(e.x, ny)) e.y = ny;
  floatText(e.x, e.y - 24, spear ? '-2' : '-1', '#f0c078');
  if (e.hp <= 0) {
    e.dead = true;
    state.kills++;
    if (e.type === 'boar') {
      addItem('meat', 2);
      log('野猪轰然倒下。你割下两块还能吃的肉。', 'good');
    } else {
      addItem('herb', 1);
      log('岛蛇瘫软下去。你从它盘踞的岩缝边找到一株草药。', 'good');
    }
    refreshQuests();
    return;
  }
  if (spear) {
    log(`长矛刺中了${e.name}。它吃痛后退，但还没有倒下。`, 'warn');
  } else {
    log(`木棍打在${e.name}身上，几乎没造成伤害。你需要一根长矛。`, 'bad');
    hurtPlayer(4, e.name);
  }
}

function hurtPlayer(amount, source) {
  if (state.phase !== 'playing' || state.invuln > 0) return;
  state.invuln = 0.9;
  state.hurt = 0.65;
  state.shake = Math.max(state.shake, 0.28);
  state.stats.health = clamp(state.stats.health - amount, 0, 100);
  floatText(state.player.x, state.player.y - 34, `-${amount} 生命`, '#e58a72');
  log(`${source}伤到了你。快拉开距离！`, 'bad');
  if (amount >= 10) {
    state.bleed = Math.max(state.bleed, 5);
    log('伤口在流血。用草药止血，或者尽快离开这里。', 'bad');
  }
  if (source === '岛蛇' && Math.random() < 0.45) {
    state.sick = true;
    log('伤口一阵发麻。蛇毒让你恶心反胃。', 'bad');
  }
  if (state.stats.health <= 0) endGame(false);
}

function moveEnemy(e, dt, speed) {
  const step = speed * dt;
  const nx = e.x + Math.cos(e.dir) * step;
  const ny = e.y + Math.sin(e.dir) * step;
  let moved = false;
  if (walkableAt(nx, e.y)) { e.x = nx; moved = true; }
  if (walkableAt(e.x, ny)) { e.y = ny; moved = true; }
  if (!moved) {
    e.dir += Math.PI * (0.5 + rand() * 0.5);
    e.wanderT = 0.8;
  }
}

function updateEnemies(dt) {
  const p = state.player;
  const night = isNight();
  for (const e of enemies) {
    if (e.dead) continue;
    e.hitFlash = Math.max(0, e.hitFlash - dt);
    e.stun = Math.max(0, e.stun - dt);
    e.attackCd = Math.max(0, e.attackCd - dt);
    const d = dist(p.x, p.y, e.x, e.y);
    const aggroRange = e.aggro * (night ? 1.5 : 1);
    if (e.stun <= 0 && d < aggroRange) {
      e.dir = Math.atan2(p.y - e.y, p.x - e.x);
      moveEnemy(e, dt, e.speed * (night ? 1.18 : 1));
      if (d < e.radius + 20 && e.attackCd <= 0) {
        e.attackCd = e.type === 'boar' ? 1.35 : 1.7;
        hurtPlayer(e.damage, e.name);
        const a = Math.atan2(p.y - e.y, p.x - e.x);
        const nx = p.x + Math.cos(a) * 28;
        const ny = p.y + Math.sin(a) * 28;
        if (walkableAt(nx, p.y)) p.x = nx;
        if (walkableAt(p.x, ny)) p.y = ny;
      }
    } else {
      e.wanderT -= dt;
      if (e.wanderT <= 0) {
        e.dir = rand() * Math.PI * 2;
        e.wanderT = 1.4 + rand() * 2.2;
      }
      moveEnemy(e, dt, 18);
    }
  }
  enemies = enemies.filter(e => !e.dead);
}

function getContext() {
  if (state.phase !== 'playing' || uiModal) return null;
  const p = state.player;
  const enemy = nearestEnemy(66);
  if (enemy) {
    return {
      type: 'enemy', enemy,
      label: (state.tools.spear ? '用长矛攻击 ' : '用木棍攻击 ') + enemy.name + (state.tools.spear ? '' : '（危险）')
    };
  }
  const site = nearestStorySite();
  if (site) {
    return { type: 'story', site, label: (site.found ? '重读线索 · ' : '调查 · ') + site.name };
  }
  if (wreck && !wreck.looted && dist(p.x, p.y, wreck.x, wreck.y) < 68) {
    return { type: 'wreck', label: '搜索飞机残骸' };
  }
  if (dock && dist(p.x, p.y, dock.x, dock.y) < 72) {
    if (beacon) return { type: 'dock', label: '烽火燃烧中 · 不能离岛' };
    return { type: 'dock', label: state.story.blackbox ? '打开航海图' : '木筏还不能出海（先找到黑匣子）' };
  }
  if (beacon && nearBeacon()) {
    return { type: 'beacon', label: beacon.fuel > 0 ? '为烽火添柴（+25 秒）' : '重新点燃烽火（+25 秒）' };
  }
  if (!beacon && nearHill()) {
    const cost = RECIPES.find(r => r.id === 'beacon').cost;
    return { type: 'hill', label: canPay(cost) ? '在信号高地建造烽火台' : '查看烽火台材料（还缺材料）' };
  }
  const n = nearestNode();
  if (n) {
    const def = NODE_DEFS[n.type];
    return { type: 'node', node: n, label: `${def.verb} ${def.name}` };
  }
  const f = nearestFire();
  if (f) return { type: 'fire', fire: f, label: f.fuel > 0 ? '添一根木柴（+30 秒）' : '重新点燃篝火（消耗木材）' };
  const sh = nearestShelter();
  if (sh) return { type: 'shelter', shelter: sh, label: isNight() ? '在庇护所睡到清晨' : '庇护所 · 夜晚可以入睡' };
  if (nearPond()) {
    return { type: 'pond', label: state.tools.waterskin && state.inv.water < 3 ? '用水囊取一份生水' : '饮用池塘生水（可能致病）' };
  }
  if (nearWater()) {
    return { type: 'fish', label: state.tools.spear ? '用长矛捕鱼' : '需要一根长矛才能捕鱼' };
  }
  return null;
}

function interact() {
  const c = getContext();
  if (!c) return;
  if (c.type === 'enemy') attackEnemy(c.enemy);
  else if (c.type === 'story') inspectStorySite(c.site);
  else if (c.type === 'wreck') lootWreck();
  else if (c.type === 'dock') openMap();
  else if (c.type === 'hill') tryBuildBeacon();
  else if (c.type === 'beacon') addBeaconFuel();
  else if (c.type === 'node') gatherNode(c.node);
  else if (c.type === 'fire') addFireFuel(c.fire);
  else if (c.type === 'shelter') trySleep(c.shelter);
  else if (c.type === 'pond') drinkPond();
  else if (c.type === 'fish') fish();
}

function gatherNode(n) {
  if (n.uses <= 0) return;
  const p = state.player;
  p.dir = Math.atan2(n.y - p.y, n.x - p.x);
  let energy = NODE_DEFS[n.type].energy;
  if (state.tools.axe && (n.type === 'palm' || n.type === 'tree')) energy -= 2;
  state.stats.energy = clamp(state.stats.energy - energy, 0, 100);
  n.uses--;
  if (n.type === 'palm') {
    const amount = state.tools.axe ? 3 : 2;
    addItem('wood', amount);
    if (Math.random() < 0.38) addItem('coconut', 1);
    log(`你从椰子树上取下 ${amount} 份木材` + (state.inv.coconut > 0 ? '，还收获了一颗椰子。' : '。'));
  } else if (n.type === 'tree') {
    const amount = state.tools.axe ? 4 : 3;
    addItem('wood', amount);
    addItem('fiber', 1);
    log(`你砍下 ${amount} 份木材，剥下一些植物纤维。`);
  } else if (n.type === 'bush') {
    addItem('berries', 2);
    addItem('fiber', 1);
    log('你摘了两把浆果，顺手收集了纤维。');
  } else if (n.type === 'rock') {
    addItem('stone', state.tools.axe ? 2 : 2);
    log('你敲下两块可以用的石头。');
  } else if (n.type === 'driftwood') {
    addItem('wood', 3);
    addItem('fiber', 1);
    log('你从潮线边拖回一段干燥的漂流木。');
  } else if (n.type === 'herb') {
    addItem('herb', 1);
    log('你采到一株草药，气味苦涩但让人安心。');
  }
  if (n.uses <= 0) {
    if (NODE_DEFS[n.type].regrow > 0) n.regrowAt = state.gameTime + NODE_DEFS[n.type].regrow;
    else n.dead = true;
  }
}

function lootWreck() {
  if (!wreck || wreck.looted) return;
  wreck.looted = true;
  addItem('wood', 2);
  addItem('fiber', 3);
  addItem('berries', 2);
  addItem('herb', 1);
  addItem('blackbox', 1);
  state.story.blackbox = true;
  state.stats.health = clamp(state.stats.health + 6, 0, 100);
  log('你从扭曲的机舱里拖出木板、纤维和一株草药。急救箱已经进了海水，但还有点用。', 'good');
  refreshQuests();
  showStory('CHAPTER I · 飞机残骸', '黑匣子还在响', [
    '你撬开变形的驾驶舱隔板，在断裂的仪表台下面摸到一只冰冷的金属盒。外壳被海水泡得发白，指示灯却还在极慢地闪。',
    '黑匣子的电池快耗尽了。你把耳朵贴上去，只听见最后一段录音：',
    '<span class="story-quote">“……这里是海燕 704。货舱起火，准备迫降。北面有高地，旧气象站的中继器也许还能用。把线圈接上……重复，北面高地……”</span>',
    '录音在这里断了。你想起出发前货舱清单上的字样：<b>气象站补给 · 备用无线电组件</b>。这不是一架普通的航班。',
    '<span class="story-note">线索更新：黑匣子 · 旧气象站中继器</span>'
  ], () => {
    log('黑匣子指向北面的信号高地。去南岸木筏，找齐另外两件部件。', 'good');
  });
}

function addFireFuel(f) {
  if ((state.inv.wood || 0) < 1) { log('没有木柴了。先去砍些树。', 'bad'); return; }
  removeItem('wood', 1);
  f.fuel = Math.min(120, f.fuel + 30);
  log('你往火里添了一根木柴，火焰重新旺了起来。', 'good');
}
function addBeaconFuel() {
  if (!beacon) return;
  if ((state.inv.wood || 0) < 1) { log('烽火需要木柴。没有柴，救援船就看不到你。', 'bad'); return; }
  removeItem('wood', 1);
  beacon.fuel = Math.min(100, beacon.fuel + 25);
  beacon.emptyWarned = false;
  log('你往烽火里添了一根木柴。浓烟升得更高了。', 'good');
}

function trySleep() {
  if (!isNight()) { log('现在还不困。等天黑以后再睡。', 'warn'); return; }
  if (state.stats.hunger < 12 || state.stats.thirst < 12) { log('你太虚弱了，先吃点东西再睡。', 'bad'); return; }
  const beforeDay = state.day;
  if (state.clock >= 19 * 60) state.day++;
  state.clock = 6 * 60;
  state.stats.energy = 100;
  state.stats.health = clamp(state.stats.health + 10, 0, 100);
  state.stats.hunger = clamp(state.stats.hunger - 18, 0, 100);
  state.stats.thirst = clamp(state.stats.thirst - 23, 0, 100);
  state.stats.warmth = clamp(state.stats.warmth + 26, 0, 100);
  state.resting = false;
  log(`你在庇护所里熬过了一夜。第 ${beforeDay} 天结束，清晨的潮声把你叫醒。`, 'good');
}

function drinkPond() {
  if (state.tools.waterskin && state.inv.water < 3) {
    addItem('water', 1);
    log('你把水囊浸进池塘，灌了一份生水。生水最好烧开再喝。');
    return;
  }
  state.stats.thirst = clamp(state.stats.thirst + 27, 0, 100);
  floatText(state.player.x, state.player.y - 30, '+27 口渴', '#8dd5e4');
  if (Math.random() < 0.38) {
    state.sick = true;
    log('水有一股泥腥味。你的胃开始绞痛。', 'bad');
  } else {
    log('你喝了几口池塘水，暂时压住了口渴。');
  }
}

function fish() {
  if (!state.tools.spear) { log('徒手抓鱼太难了。先用木材和纤维做一根长矛。', 'warn'); return; }
  if (state.weather === 'storm') { log('风暴里水面太乱，根本看不清鱼。', 'bad'); return; }
  if (state.fishCd > 0) return;
  state.fishCd = 1.8;
  state.stats.energy = clamp(state.stats.energy - 6, 0, 100);
  state.player.dir = Math.atan2(0, 1);
  if (Math.random() < 0.72) {
    addItem('fish', 1);
    log('长矛刺入浅水，你叉到了一条鱼。记得烤熟再吃。', 'good');
  } else {
    log('鱼尾一摆，从矛尖下滑走了。', 'warn');
  }
}

function useItem(id) {
  if (state.phase !== 'playing' || uiModal) return;
  if (!state.inv[id]) return;
  const nearFire = litFireNear();

  if (id === 'blackbox' || id === 'coil' || id === 'battery' || id === 'fuel' || id === 'spark') {
    log(ITEMS[id].desc + ' 把它带到北部信号高地。');
    return;
  }
  if (id === 'meat' && nearFire) {
    removeItem('meat', 1); addItem('cookedMeat', 1);
    log('野猪肉在火边烤得滋滋作响。油脂滴进火里，香味让你想起很久以前的一顿饭。', 'good');
    return;
  }
  if (id === 'meat') {
    removeItem('meat', 1);
    state.stats.hunger = clamp(state.stats.hunger + 20, 0, 100);
    floatText(state.player.x, state.player.y - 30, '+20 饥饿', '#e0ad72');
    if (Math.random() < 0.4) {
      state.sick = true;
      log('生肉带着血腥味。你的胃开始翻腾。', 'bad');
    } else {
      log('你强忍着咽下几口生肉，勉强压住饥饿。');
    }
    return;
  }
  if (id === 'fish' && nearFire) {
    removeItem('fish', 1); addItem('cookedFish', 1);
    log('你把鱼架在火边烤熟，油脂滴进火里滋滋作响。', 'good');
    return;
  }
  if (id === 'water' && nearFire) {
    removeItem('water', 1); addItem('cleanWater', 1);
    log('生水在火边沸腾了几分钟。现在可以安全饮用了。', 'good');
    return;
  }
  if (id === 'fish') {
    removeItem('fish', 1);
    state.stats.hunger = clamp(state.stats.hunger + 18, 0, 100);
    floatText(state.player.x, state.player.y - 30, '+18 饥饿', '#e0ad72');
    if (Math.random() < 0.45) {
      state.sick = true;
      log('生鱼的腥味在嘴里散开。你的胃开始翻江倒海。', 'bad');
    } else {
      log('你生吃了一条鱼，勉强填了填肚子。');
    }
    return;
  }
  if (id === 'coconut' || id === 'berries' || id === 'cookedFish' || id === 'cookedMeat' || id === 'water' || id === 'cleanWater') {
    const f = FOOD[id];
    removeItem(id, 1);
    state.stats.hunger = clamp(state.stats.hunger + (f.hunger || 0), 0, 100);
    state.stats.thirst = clamp(state.stats.thirst + (f.thirst || 0), 0, 100);
    if (id === 'cookedFish') state.stats.health = clamp(state.stats.health + 5, 0, 100);
    if (id === 'cookedMeat') state.stats.health = clamp(state.stats.health + 8, 0, 100);
    floatText(state.player.x, state.player.y - 30,
      [f.hunger ? '+' + f.hunger + ' 饥饿' : '', f.thirst ? '+' + f.thirst + ' 口渴' : ''].filter(Boolean).join('  '),
      id === 'cookedFish' ? '#e8c27d' : '#9ad7d9');
    if (id === 'water' && Math.random() < 0.35) {
      state.sick = true;
      log('生水让你感到一阵恶心。下次最好烧开。', 'bad');
    } else {
      log('你吃掉了' + ITEMS[id].name + '。');
    }
    return;
  }
  if (id === 'herb') {
    removeItem('herb', 1);
    const hadBleed = state.bleed > 0;
    state.bleed = 0;
    state.stats.health = clamp(state.stats.health + 5, 0, 100);
    if (state.sick) {
      state.sick = false;
      log('你嚼碎草药咽下去。胃里的绞痛慢慢平息了，伤口也不再流血。', 'good');
    } else if (hadBleed) {
      log('你把草药敷在伤口上。血慢慢止住了。', 'good');
    } else {
      log('草药的苦味让你清醒了一点。');
    }
    return;
  }
  log(ITEMS[id].name + '：' + ITEMS[id].desc);
}

/* --------------------------- 制作与建造 --------------------------- */

function openCraft() {
  if (state.phase !== 'playing') return;
  resetTouchInput();
  $('quest').classList.remove('mobile-open');
  uiModal = 'craft';
  $('craftModal').classList.remove('hidden');
  renderCraft();
}
function closeCraft() {
  uiModal = null;
  $('craftModal').classList.add('hidden');
}
function openHelp() {
  if (state.phase !== 'playing') return;
  resetTouchInput();
  $('quest').classList.remove('mobile-open');
  uiModal = 'help';
  $('helpModal').classList.remove('hidden');
}
function closeHelp() {
  uiModal = null;
  $('helpModal').classList.add('hidden');
}

/* --------------------------- 新手指引 --------------------------- */

const GUIDE_KEY = 'island_guide_v1';
const GUIDE_STEPS = [
  {
    icon: '❤',
    heading: '先盯住五条状态',
    text: '左上角是你的生命、饥饿、口渴、体力和体温。任何一条见底，都会开始掉血。先学会看状态，再谈冒险。',
    tips: [
      '饥饿、口渴、体温归零会持续扣血。',
      '夜晚靠近燃烧的篝火取暖。',
      '流血或吃坏肚子时，点背包里的草药。'
    ]
  },
  {
    icon: '👣',
    heading: '先学会走路和伸手',
    text: '电脑用 WASD 移动、Shift 疾跑；手机用左下摇杆，右下是互动、制作、休息。靠近残骸、资源或木筏，按 E / 点“互动”。',
    tips: [
      '第一件事：搜飞机残骸，拿到黑匣子。',
      '<kbd>E</kbd> 也用于攻击野兽、上木筏、给篝火添柴。',
      '屏幕中央的提示会告诉你现在能做什么。'
    ]
  },
  {
    icon: '🪓',
    heading: '做一把石斧，再做长矛',
    text: '按 C 或点“制作”打开制作面板。先做石斧提高伐木收益，再做长矛捕鱼和防身。制作时游戏时间会暂停。',
    tips: [
      '石斧：木材 + 石块 + 纤维。',
      '长矛：木材 + 石块 + 纤维。',
      '水囊能装水带走，也能在火边烧开。'
    ]
  },
  {
    icon: '🔥',
    heading: '天黑前，把火生起来',
    text: '收集木材和石块，在营地建篝火。靠近火堆按 E 添柴；按 R 原地休息。体温太低会掉血，夜里野兽也更凶。',
    tips: [
      '火会吸引野兽，也会让它们不敢靠太近。',
      '庇护所可以睡到清晨。',
      '生水可能让你肠胃炎，椰子最安全。'
    ]
  },
  {
    icon: '📻',
    heading: '离开这里：六座岛与信号',
    text: '拿到黑匣子后，到南岸木筏按 E 打开航海图。依次找回线圈、蓄电池、柴油和点火模块，最后去信号高地组装无线电。',
    tips: [
      '五件部件会占背包，别丢。',
      '在信号高地建烽火台，守住 180 秒。',
      '第 60 / 125 秒各有一波野兽，记得按 E 添柴。'
    ]
  }
];
let guideIndex = 0;

function guideSeen() {
  try { return localStorage.getItem(GUIDE_KEY) === '1'; } catch (e) { return false; }
}

function markGuideSeen() {
  try { localStorage.setItem(GUIDE_KEY, '1'); } catch (e) { /* 忽略 */ }
}

function openGuide(index = 0) {
  if (state.phase !== 'playing' && state.phase !== 'menu') return;
  if (uiModal && uiModal !== 'guide') return;
  resetTouchInput();
  $('quest').classList.remove('mobile-open');
  guideIndex = Math.max(0, Math.min(GUIDE_STEPS.length - 1, Number(index) || 0));
  uiModal = 'guide';
  $('guideModal').classList.remove('hidden');
  renderGuide();
}

function renderGuide() {
  const step = GUIDE_STEPS[guideIndex];
  const total = GUIDE_STEPS.length;
  $('guideStepNo').textContent = String(guideIndex + 1).padStart(2, '0');
  $('guideKicker').textContent = `第 ${guideIndex + 1} / ${total} 步`;
  $('guideIcon').textContent = step.icon;
  $('guideHeading').textContent = step.heading;
  $('guideText').textContent = step.text;
  $('guideTips').innerHTML = step.tips.map(tip => `<li>${tip}</li>`).join('');
  $('guideProgress').innerHTML = GUIDE_STEPS.map((_, i) => `<i class="${i <= guideIndex ? 'on' : ''}"></i>`).join('');
  $('guidePrev').disabled = guideIndex === 0;
  $('guideNext').textContent = guideIndex === total - 1
    ? (state.phase === 'playing' ? '开始求生' : '开始探索')
    : '下一步 →';
}

function closeGuide(markSeen = true) {
  if (uiModal !== 'guide') return;
  $('guideModal').classList.add('hidden');
  uiModal = null;
  if (markSeen) markGuideSeen();
}

function nextGuide() {
  if (guideIndex >= GUIDE_STEPS.length - 1) {
    closeGuide();
    return;
  }
  guideIndex += 1;
  renderGuide();
}

function prevGuide() {
  if (guideIndex <= 0) return;
  guideIndex -= 1;
  renderGuide();
}

/* --------------------------- 主线剧情 --------------------------- */

function showStory(kicker, title, paragraphs, onClose = null) {
  uiModal = 'story';
  storyCloseCallback = onClose;
  resetTouchInput();
  $('quest').classList.remove('mobile-open');
  $('storyKicker').textContent = kicker;
  $('storyTitle').textContent = title;
  $('storyBody').innerHTML = paragraphs.map(p => `<p>${p}</p>`).join('');
  $('storyModal').classList.remove('hidden');
}

function closeStory() {
  if (uiModal !== 'story') return;
  $('storyModal').classList.add('hidden');
  uiModal = null;
  const cb = storyCloseCallback;
  storyCloseCallback = null;
  if (cb) cb();
}

function allStoryParts() {
  return state.story.blackbox && state.story.coil && state.story.battery && state.story.fuel && state.story.spark;
}

function storyPartsFound() {
  return [state.story.blackbox, state.story.coil, state.story.battery, state.story.fuel, state.story.spark].filter(Boolean).length;
}

function missingStoryParts() {
  const missing = [];
  if (!state.story.blackbox) missing.push('黑匣子');
  if (!state.story.coil) missing.push('铜线圈');
  if (!state.story.battery) missing.push('蓄电池');
  if (!state.story.fuel) missing.push('柴油');
  if (!state.story.spark) missing.push('点火模块');
  return missing;
}

function storyTarget() {
  if (beacon) return { x: beacon.x, y: beacon.y, label: '烽火台' };
  const dockTarget = label => dock ? { x: dock.x, y: dock.y, label } : null;
  if (!state.story.blackbox) {
    return wreck ? { x: wreck.x, y: wreck.y, label: '飞机残骸' } : dockTarget('码头');
  }
  if (!state.story.coil) {
    const camp = storySites.find(s => s.id === 'camp');
    return camp ? { x: camp.x, y: camp.y, label: '西岸营地' } : dockTarget('码头 · 前往雾林岛');
  }
  if (!state.story.battery) {
    const cave = storySites.find(s => s.id === 'cave');
    return cave ? { x: cave.x, y: cave.y, label: '东侧海蚀洞' } : dockTarget('码头 · 前往环礁岛');
  }
  if (!state.story.fuel) {
    const fuel = storySites.find(s => s.id === 'fuel');
    return fuel ? { x: fuel.x, y: fuel.y, label: '沉船货舱' } : dockTarget('码头 · 前往沉船湾');
  }
  if (!state.story.spark) {
    const spark = storySites.find(s => s.id === 'spark');
    return spark ? { x: spark.x, y: spark.y, label: '火山观测站' } : dockTarget('码头 · 前往火山岛');
  }
  if (state.currentIsland === 5 && hill) {
    return { x: hill.x, y: hill.y, label: '信号高地' };
  }
  return dockTarget('码头 · 前往信号岛');
}

function nearestStorySite(maxDist = 74) {
  let best = null, bd = maxDist;
  for (const site of storySites) {
    const d = dist(state.player.x, state.player.y, site.x, site.y);
    if (d < bd) { bd = d; best = site; }
  }
  return best;
}

function inspectStorySite(site) {
  if (site.id === 'camp') {
    const first = !state.story.coil;
    if (first) {
      state.story.coil = true;
      state.story.camp = true;
      site.found = true;
      addItem('coil', 1);
      refreshQuests();
    }
    showStory('CHAPTER II · 西岸旧营地', '潮线以上的帆布', [
      '你拨开藤蔓，找到一顶塌了半边的帆布帐篷。锅底积着雨水，旁边倒着一台被拆开的旧电台。',
      '电台的铜线圈还完好。压在上面的防水日志只剩最后一页能辨认：',
      '<span class="story-quote">“1987 年，补给船不会再来了。环礁岛东侧的海蚀洞里有备用蓄电池。如果有人看到这些字，把线圈和电池带回信号岛的高地。别在夜里点火，林子里的东西会被光吸引。”</span>',
      first ? '你把铜线圈缠好，塞进背包。日志的字迹被海雾泡得发软，但方向已经很清楚了。' : '你重新读了一遍那页日志。纸页脆得像干枯的叶子。',
      '<span class="story-note">线索更新：西岸营地 · 铜线圈</span>'
    ], () => {
      if (first) {
        log('获得铜线圈。回南岸木筏，去环礁岛找蓄电池。', 'good');
        if (allStoryParts()) log('五件无线电部件都齐了。去信号岛的信号高地。', 'good');
      }
    });
  } else if (site.id === 'cave') {
    const first = !state.story.battery;
    if (first) {
      state.story.battery = true;
      state.story.cave = true;
      site.found = true;
      addItem('battery', 1);
      refreshQuests();
    }
    showStory('CHAPTER III · 东侧海蚀洞', '潮水退去之后', [
      '退潮后，岩壁下露出一个半人高的洞口。里面没有宝藏，只有一只用木板垫高的铅酸蓄电池，和几根烧尽的信号棒。',
      '岩壁上刻着一排正字，最后一道只刻了一半。旁边歪歪扭扭地写着：',
      '<span class="story-quote">“电池还有电。线圈在营地。高地能看见航道。撑住。”</span>',
      first ? '你把蓄电池抱起来，比想象中沉。它还有电，足够让一台旧电台再响一次。' : '你摸了摸蓄电池的接线柱。微弱的电流刺了一下指尖。',
      '<span class="story-note">线索更新：东侧海蚀洞 · 蓄电池</span>'
    ], () => {
      if (first) {
        log('获得蓄电池。回南岸木筏，去沉船湾找柴油。', 'good');
        if (allStoryParts()) log('五件无线电部件都齐了。去信号岛的信号高地。', 'good');
      }
    });
  } else if (site.id === 'fuel') {
    const first = !state.story.fuel;
    if (first) {
      state.story.fuel = true;
      site.found = true;
      addItem('fuel', 1);
      refreshQuests();
    }
    showStory('CHAPTER IV · 沉船湾', '锈红的货舱', [
      '货轮侧躺在礁盘上，船腹被撕开一道口子。潮水在舱里来回撞，发出空洞的回声。',
      '你踩着倾斜的舱壁往下走，找到一只还封着的柴油桶。桶身印着 1987 年的补给编号，和营地日志上的字迹一样旧。',
      '<span class="story-quote">“发电机还能转。缺的是油和点火模块。火山岛的观测站里有备件。别走夜路，蛇会往热的地方聚。”</span>',
      first ? '你把柴油分装进水囊和铁壶。气味刺鼻，但这是信号高地唯一能用的燃料。' : '你检查了一遍油桶，确认没有更多能带走的柴油。',
      '<span class="story-note">线索更新：沉船湾 · 柴油</span>'
    ], () => {
      if (first) {
        log('获得柴油。回南岸木筏，去火山岛找点火模块。', 'good');
        if (allStoryParts()) log('五件无线电部件都齐了。去信号岛的信号高地。', 'good');
      }
    });
  } else if (site.id === 'spark') {
    const first = !state.story.spark;
    if (first) {
      state.story.spark = true;
      site.found = true;
      addItem('spark', 1);
      refreshQuests();
    }
    showStory('CHAPTER V · 火山岛', '灰烬里的备件箱', [
      '观测站的铁皮屋顶塌了一半，地上积着黑色的火山灰。每走一步，灰里都会扬起一股硫磺味。',
      '备件箱被压在倒塌的仪器架下面。你拖出箱子，里面躺着一枚用油纸包好的点火模块，还有半张航线图。',
      '<span class="story-quote">“如果信号塔还立着，就把模块接到配电盘上。别在雷暴里上高地。山会先响，然后才是闪电。”</span>',
      first ? '你把点火模块揣进内袋。金属外壳还是温的，像刚从火里拿出来。' : '你重新包好点火模块，确认它没有被火山灰弄湿。',
      '<span class="story-note">线索更新：火山岛 · 点火模块</span>'
    ], () => {
      if (first) {
        log('获得点火模块。回南岸木筏，去信号岛组装无线电。', 'good');
        if (allStoryParts()) log('五件无线电部件都齐了。去信号岛的信号高地。', 'good');
      }
    });
  }
}

function storyChapter() {
  const isl = ISLANDS[state.currentIsland] || ISLANDS[0];
  if (beacon) return '终章 · 烽火 · ' + isl.name;
  if (state.story.spark) return '第六章 · 信号 · ' + isl.name;
  if (state.story.fuel) return '第五章 · 火山 · ' + isl.name;
  if (state.story.battery) return '第四章 · 沉船 · ' + isl.name;
  if (state.story.coil) return '第三章 · 环礁 · ' + isl.name;
  if (state.story.blackbox) return '第二章 · 横渡 · ' + isl.name;
  return '第一章 · 残骸 · ' + isl.name;
}

function openMap() {
  if (state.phase !== 'playing' || uiModal) return;
  if (beacon) {
    log('烽火已经点燃。现在离开，救援船就看不到这座岛了。', 'warn');
    return;
  }
  if (!state.story.blackbox) {
    log('木筏还没有帆。先在坠机岛找到黑匣子，也许机舱里有能用的帆布。', 'warn');
    return;
  }
  resetTouchInput();
  $('quest').classList.remove('mobile-open');
  uiModal = 'map';
  renderMap();
  $('mapModal').classList.remove('hidden');
}

function closeMap() {
  uiModal = null;
  $('mapModal').classList.add('hidden');
}

function renderMap() {
  const grid = $('mapGrid');
  grid.innerHTML = ISLANDS.map((isl, i) => {
    const unlocked = islandUnlocked(i);
    const current = state.currentIsland === i;
    const visited = state.visited[i];
    return `<button class="island-card ${current ? 'current' : ''} ${unlocked ? '' : 'locked'}" data-island="${i}" ${unlocked ? '' : 'disabled'}>
      <span class="island-index">0${i + 1}</span>
      <span class="island-name">${isl.name}${current ? '<em>当前位置</em>' : ''}</span>
      <small>${isl.en}</small>
      <p>${unlocked ? isl.intro : islandRequirement(i) + '。沿着主线继续探索。'}</p>
      <span class="island-state">${current ? '停泊中' : visited ? '已探索 · 可再次前往' : unlocked ? '可航行' : '未解锁'}</span>
    </button>`;
  }).join('');
}

function travelTo(index) {
  if (index === state.currentIsland) { closeMap(); return; }
  if (beacon) {
    log('烽火燃烧中，你不能丢下它离岛。', 'warn');
    return;
  }
  if (!islandUnlocked(index)) {
    log(islandRequirement(index) + '，还不能前往' + ISLANDS[index].name + '。', 'warn');
    return;
  }
  saveCurrentIsland();
  const firstVisit = !state.visited[index];
  closeMap();
  state.clock = (state.clock + 55) % 1440;
  state.stats.energy = clamp(state.stats.energy - 5, 0, 100);
  state.stats.hunger = clamp(state.stats.hunger - 3, 0, 100);
  state.stats.thirst = clamp(state.stats.thirst - 5, 0, 100);
  loadIsland(index);
  const isl = ISLANDS[index];
  log(`你解开缆绳，木筏驶向${isl.name}。海面比你想象的更冷。`, 'warn');
  if (firstVisit) {
    setTimeout(() => {
      if (state.phase !== 'playing' || uiModal) return;
      showStory('NEW SHORE · ' + isl.en, isl.name, [isl.intro], () => {
        if (isl.key === 'signal') log('信号高地在岛的北面。把五件部件带上高地。', 'good');
        if (isl.key === 'mist') log('西岸有旧营地的帆布和烟。小心林子里的野猪。', 'warn');
        if (isl.key === 'reef') log('环礁没有淡水。海蚀洞在岛的东侧。', 'warn');
        if (isl.key === 'cove') log('货轮搁浅在西岸。涨潮前把柴油搬出来。', 'warn');
        if (isl.key === 'ash') log('观测站被落石砸开。火山灰里，蛇和野猪都不太怕人。', 'bad');
      });
    }, 420);
  }
}

function renderCraft() {
  const grid = $('craftGrid');
  grid.innerHTML = RECIPES.map(r => {
    let owned = false;
    if (r.once) owned = !!state.tools[r.id];
    if (r.id === 'beacon' && beacon) owned = true;
    const missingParts = r.id === 'beacon' ? missingStoryParts() : [];
    const can = canPay(r.cost) && !owned && missingParts.length === 0;
    const near = r.id !== 'beacon' || nearHill();
    let btn = owned ? '已拥有' : (r.id === 'beacon' ? '建造无线电烽火台' : (r.kind === '建筑' ? '建造' : '制作'));
    if (r.id === 'beacon' && !near && !owned) btn = '需靠近信号高地';
    if (r.id === 'beacon' && missingParts.length && !owned) btn = '缺少 ' + missingParts.join(' / ');
    return `<div class="craft-card ${can ? '' : 'locked'}">
      <div class="craft-top"><div class="craft-icon">${r.icon}</div><div><span class="craft-name">${r.name}</span><span class="craft-type">${r.kind}</span></div></div>
      <p class="craft-desc">${r.desc}${r.id === 'beacon' && !near ? '<br><span style="color:#d98b76">你必须在信号高地上才能建造。</span>' : ''}${r.id === 'beacon' && missingParts.length ? `<br><span style="color:#d98b76">还需部件：${missingParts.join('、')}</span>` : ''}</p>
      <div class="craft-cost">${costText(r.cost)}</div>
      <button class="craft-btn" data-craft="${r.id}" ${can && near ? '' : 'disabled'}>${btn}</button>
    </div>`;
  }).join('');
}

function craft(id) {
  const r = RECIPES.find(x => x.id === id);
  if (!r || state.phase !== 'playing') return;
  if (r.once && state.tools[id]) { log('你已经拥有这件工具了。'); return; }
  if (id === 'beacon' && beacon) { log('烽火台已经建好了。'); return; }
  if (id === 'beacon' && !nearHill()) { log('烽火台必须建在岛北部的信号高地。', 'warn'); return; }
  if (id === 'beacon' && missingStoryParts().length) {
    log('无线电还缺：' + missingStoryParts().join('、') + '。沿着雾林、环礁、沉船湾和火山岛找齐。', 'warn');
    return;
  }
  if (!canPay(r.cost)) { log('材料不足：还缺 ' + missingText(r.cost), 'bad'); return; }

  if (id === 'axe' || id === 'spear' || id === 'waterskin') {
    pay(r.cost);
    state.tools[id] = true;
    log(`你制作了${r.name}。${r.id === 'axe' ? '现在砍树会轻松很多。' : r.id === 'spear' ? '去水边试试叉鱼。' : '可以装水带走了。'}`, 'good');
    renderCraft();
    return;
  }

  if (id === 'beacon') {
    buildBeacon();
    return;
  }

  pay(r.cost);
  const spot = buildSpot();
  if (id === 'campfire') {
    fires.push({ x: spot.x, y: spot.y, fuel: 45 });
    log('你用石块垒起灶，点燃了篝火。靠近它按 E 可以添柴。', 'good');
  } else if (id === 'shelter') {
    shelters.push({ x: spot.x, y: spot.y });
    log('你用木料和棕榈叶搭起了一个简陋的庇护所。夜晚可以睡在里面。', 'good');
  }
  closeCraft();
}

function buildSpot() {
  const p = state.player;
  let x = p.x + Math.cos(p.dir) * 48;
  let y = p.y + Math.sin(p.dir) * 48;
  if (!walkableAt(x, y)) { x = p.x; y = p.y + 18; }
  return { x, y };
}

function tryBuildBeacon() {
  const cost = RECIPES.find(r => r.id === 'beacon').cost;
  if (!nearHill()) { log('你必须站在信号高地上才能建造烽火台。', 'warn'); return; }
  if (missingStoryParts().length) {
    log('无线电还缺：' + missingStoryParts().join('、') + '。去雾林、环礁、沉船湾和火山岛找。', 'warn');
    return;
  }
  if (!canPay(cost)) { log('材料不足：还缺 ' + missingText(cost), 'bad'); return; }
  buildBeacon();
}

function buildBeacon() {
  if (beacon) return;
  if (missingStoryParts().length) {
    log('无线电还缺：' + missingStoryParts().join('、') + '。', 'warn');
    return;
  }
  const cost = RECIPES.find(r => r.id === 'beacon').cost;
  pay(cost);
  removeItem('blackbox', 1);
  removeItem('coil', 1);
  removeItem('battery', 1);
  removeItem('fuel', 1);
  removeItem('spark', 1);
  state.story.radio = true;
  beacon = {
    x: hill.x, y: hill.y, fuel: 50, progress: 0,
    emptyWarned: false
  };
  state.hillFound = true;
  if (uiModal === 'craft') closeCraft();
  log('你把黑匣子的发射模块、铜线圈、蓄电池、柴油和点火模块接在一起。发电机咳嗽了两声，指示灯亮了。', 'good');
  log('烽火台立起来了。黑烟笔直地升向天空，救援倒计时开始。', 'good');
  log(`烽火会持续消耗燃料，坚持 ${RESCUE_TIME} 秒。靠近按 E 添柴，别让火熄灭。`, 'warn');
  spawnBeaconAttackers();
  refreshQuests();
}

function spawnAround(types, center, radius) {
  let spawned = 0;
  types.forEach((type, i) => {
    const angle = i * (Math.PI * 2 / types.length) + rand() * 0.7;
    for (let attempt = 0; attempt < 10; attempt++) {
      const a = angle + attempt * 0.42;
      const x = center.x + Math.cos(a) * radius;
      const y = center.y + Math.sin(a) * radius;
      if (walkableAt(x, y)) {
        addEnemy(type, x, y);
        spawned++;
        break;
      }
    }
  });
  return spawned;
}

function spawnBeaconAttackers() {
  if (!hill) return;
  const spawned = spawnAround(['boar', 'snake', 'boar', 'boar', 'snake'], hill, 190);
  if (spawned) log('火光和烟柱惊动了林子里的野兽。它们正朝高地围过来。', 'bad');
}

function spawnBeaconWave(types, radius = 230) {
  if (!hill) return;
  const spawned = spawnAround(types, hill, radius);
  if (spawned) log('又一批野兽被火光吸引，从林线里钻了出来。', 'bad');
}

function spawnNightHunt() {
  const spawned = spawnAround(['boar', 'snake'], state.player, 280);
  if (spawned) log('天黑之后，林子里的东西开始主动找你。', 'bad');
}

function toggleRest() {
  if (state.phase !== 'playing' || uiModal) return;
  if (state.resting) {
    state.resting = false;
    log('你站起来活动了一下。');
    return;
  }
  if (litFireNear() || nearestShelter(90)) {
    state.resting = true;
    log('你坐下来休息，让体力慢慢恢复。时间仍在流逝。');
  } else {
    log('在这里休息太冷了。靠近篝火或庇护所再休息。', 'warn');
  }
}

/* --------------------------- 移动与更新 --------------------------- */

function walkableAt(x, y) {
  if (x < 10 || y < 10 || x > WORLD_W - 10 || y > WORLD_H - 10) return false;
  const points = [[-8, -6], [8, -6], [-8, 6], [8, 6], [0, 0]];
  for (const [ox, oy] of points) {
    const tx = Math.floor((x + ox) / TILE);
    const ty = Math.floor((y + oy) / TILE);
    if (!map[ty] || !map[ty][tx] || map[ty][tx].solid) return false;
  }
  return true;
}

function updatePlayer(dt) {
  const p = state.player;
  let dx = 0, dy = 0;
  if (keys.has('KeyW') || keys.has('ArrowUp')) dy -= 1;
  if (keys.has('KeyS') || keys.has('ArrowDown')) dy += 1;
  if (keys.has('KeyA') || keys.has('ArrowLeft')) dx -= 1;
  if (keys.has('KeyD') || keys.has('ArrowRight')) dx += 1;
  if (touchInput.active) {
    dx += touchInput.x;
    dy += touchInput.y;
  }
  let len = Math.hypot(dx, dy);
  const moving = len > 0.08;
  if (moving && state.resting) state.resting = false;
  if (!moving) {
    p.moving = false;
    return;
  }
  if (len > 1) {
    dx /= len;
    dy /= len;
    len = 1;
  }
  dx /= Math.max(len, 0.0001);
  dy /= Math.max(len, 0.0001);
  let speed = 118 * Math.min(1, len);
  const sprint = (keys.has('ShiftLeft') || keys.has('ShiftRight') || touchSprint) && state.stats.energy > 2 && len > 0.5;
  if (sprint) speed = 178 * Math.min(1, len);
  if (state.stats.energy <= 0) speed *= 0.58;
  if (state.resting) speed *= 0.5;
  const nx = p.x + dx * speed * dt;
  if (walkableAt(nx, p.y)) p.x = nx;
  const ny = p.y + dy * speed * dt;
  if (walkableAt(p.x, ny)) p.y = ny;
  p.dir = Math.atan2(dy, dx);
  p.moving = true;
  p.walk += dt * (sprint ? 15 : 10);
  if (sprint) state.stats.energy = clamp(state.stats.energy - dt * 0.8, 0, 100);
}

function updateStats(dt) {
  const s = state.stats;
  const night = isNight();
  const rain = state.weather === 'rain' || state.weather === 'storm';
  const storm = state.weather === 'storm';
  let hungerRate = 0.26;
  let thirstRate = 0.37;
  if (rain) thirstRate *= 0.68;
  if (state.resting) { hungerRate *= 1.25; thirstRate *= 1.25; }
  s.hunger = clamp(s.hunger - hungerRate * dt, 0, 100);
  s.thirst = clamp(s.thirst - thirstRate * dt, 0, 100);

  if (state.resting) s.energy = clamp(s.energy + 8 * dt, 0, 100);
  else if (state.player.moving) s.energy = clamp(s.energy - dt * 0.23, 0, 100);
  else s.energy = clamp(s.energy - dt * 0.035, 0, 100);

  const shel = nearestShelter(110);
  if (litFireNear(150)) s.warmth = clamp(s.warmth + 11 * dt, 0, 100);
  else if (night) {
    let rate = shel ? 0.16 : 0.40;
    if (storm) rate += 0.17;
    s.warmth = clamp(s.warmth - rate * dt, 0, 100);
  } else {
    s.warmth = clamp(s.warmth + (rain ? 0.25 : 0.7) * dt, 0, 100);
  }

  if (s.warmth < 20) s.health -= (1.0 + (20 - s.warmth) * 0.025) * dt;
  if (s.warmth <= 0) s.health -= 0.9 * dt;
  if (s.hunger <= 0) s.health -= 0.75 * dt;
  if (s.thirst <= 0) s.health -= 1.15 * dt;
  if (s.energy <= 0) s.health -= 0.22 * dt;
  if (state.sick) { s.health -= 0.23 * dt; s.energy = clamp(s.energy - 0.07 * dt, 0, 100); }
  if (!state.sick && s.hunger > 55 && s.thirst > 55 && s.warmth > 55 && s.health < 100) s.health += 0.025 * dt;
  s.health = clamp(s.health, 0, 100);

  // 状态警告
  const warn = (key, condition, text) => {
    if (condition && !state.warnings[key] && state.phase === 'playing') {
      state.warnings[key] = true;
      log(text, 'bad');
    } else if (!condition) state.warnings[key] = false;
  };
  warn('hunger', s.hunger < 20, '你的胃在抽搐。再不吃东西，身体会撑不住。');
  warn('thirst', s.thirst < 20, '喉咙像被沙子磨过。必须找水。');
  warn('warmth', s.warmth < 25, '你开始控制不住地发抖。靠近火源取暖。');
  warn('health', s.health < 30, '视野开始发黑。你需要休息、食物，或者治疗。');
}

function update(dt) {
  state.gameTime += dt;
  state.clock += dt * 4.8;
  if (state.clock >= 1440) { state.clock -= 1440; state.day++; }
  state.fishCd = Math.max(0, state.fishCd - dt);

  if (state.weatherTimer > 0) state.weatherTimer -= dt;
  else changeWeather();
  state.flash = Math.max(0, state.flash - dt * 2.5);
  state.hurt = Math.max(0, state.hurt - dt * 1.7);
  state.invuln = Math.max(0, state.invuln - dt);
  state.attackCd = Math.max(0, state.attackCd - dt);
  state.shake = Math.max(0, state.shake - dt * 2.6);
  if (state.weather === 'storm' && Math.random() < dt * 0.35) state.flash = 1;

  if (state.bleed > 0) {
    state.bleed = Math.max(0, state.bleed - dt);
    state.stats.health = clamp(state.stats.health - dt * 0.85, 0, 100);
    if (state.stats.health <= 0) { endGame(false); return; }
  }

  updatePlayer(dt);
  updateEnemies(dt);
  updateStats(dt);
  if (isNight() && state.nightWave !== state.day) {
    state.nightWave = state.day;
    if (!(state.resting && nearestShelter(90))) spawnNightHunt();
  }

  fires.forEach(f => {
    if (f.fuel > 0) {
      f.fuel = Math.max(0, f.fuel - dt * (state.weather === 'rain' ? 1.35 : state.weather === 'storm' ? 1.6 : 1));
    }
  });

  nodes.forEach(n => {
    if (n.uses <= 0 && n.regrowAt > 0 && state.gameTime >= n.regrowAt) {
      n.uses = n.maxUses;
      n.regrowAt = 0;
    }
  });

  if (beacon) {
    if (beacon.fuel > 0) {
      beacon.fuel = Math.max(0, beacon.fuel - dt);
      beacon.progress = Math.min(RESCUE_TIME, beacon.progress + dt);
      beacon.emptyWarned = false;
      if (beacon.progress > 60 && state.beaconWave < 1) {
        state.beaconWave = 1;
        spawnBeaconWave(['boar', 'snake', 'boar']);
      } else if (beacon.progress > 125 && state.beaconWave < 2) {
        state.beaconWave = 2;
        spawnBeaconWave(['boar', 'boar', 'snake', 'snake'], 250);
      }
    } else if (!beacon.emptyWarned) {
      beacon.emptyWarned = true;
      log('烽火熄灭了。救援船正在失去信号——快添柴！', 'bad');
    }
    if (beacon.progress >= RESCUE_TIME && state.phase === 'playing') {
      winGame();
      return;
    }
  }

  if (!state.hillFound && hill && dist(state.player.x, state.player.y, hill.x, hill.y) < 190) {
    state.hillFound = true;
    log('你爬上了北面的高地。这里能看见整片海。就在这里点燃烽火。', 'good');
  }

  state.floats.forEach(f => { f.y -= 26 * dt; f.life -= dt; });
  state.floats = state.floats.filter(f => f.life > 0);

  camera.tx = clamp(state.player.x - VW / 2, 0, Math.max(0, WORLD_W - VW));
  camera.ty = clamp(state.player.y - VH / 2, 0, Math.max(0, WORLD_H - VH));
  camera.x += (camera.tx - camera.x) * Math.min(1, dt * 7);
  camera.y += (camera.ty - camera.y) * Math.min(1, dt * 7);

  if (state.stats.health <= 0 && state.phase === 'playing') endGame(false);
}

/* --------------------------- 绘制：世界 --------------------------- */

function drawTiles() {
  const x0 = Math.max(0, Math.floor(camera.x / TILE) - 1);
  const y0 = Math.max(0, Math.floor(camera.y / TILE) - 1);
  const x1 = Math.min(MAP_W - 1, Math.ceil((camera.x + VW) / TILE) + 1);
  const y1 = Math.min(MAP_H - 1, Math.ceil((camera.y + VH) / TILE) + 1);
  const hour = state.clock / 60;
  const daylight = hour >= 7 && hour < 17.5;

  for (let y = y0; y <= y1; y++) {
    for (let x = x0; x <= x1; x++) {
      const t = map[y][x];
      const px = x * TILE, py = y * TILE;
      const v = t.v;
      if (t.type === 'deep') {
        ctx.fillStyle = '#0b3d55';
        ctx.fillRect(px, py, TILE + 1, TILE + 1);
        ctx.strokeStyle = 'rgba(66,143,162,.18)';
        ctx.lineWidth = 1;
        const waveY = py + 8 + Math.sin(tNow * 0.9 + x * 0.7 + y * 0.4) * 4;
        ctx.beginPath();
        ctx.moveTo(px + 4 + v * 8, waveY);
        ctx.quadraticCurveTo(px + 16, waveY - 3, px + 27, waveY);
        ctx.stroke();
      } else if (t.type === 'shallow') {
        ctx.fillStyle = '#257e93';
        ctx.fillRect(px, py, TILE + 1, TILE + 1);
        const foam = 0.5 + 0.5 * Math.sin(tNow * 1.4 + x * 0.9 + y * 0.5);
        ctx.fillStyle = `rgba(190,232,230,${0.07 + foam * 0.08})`;
        ctx.fillRect(px + 3, py + 5 + v * 9, 20 + v * 7, 2);
        ctx.fillStyle = 'rgba(129,198,197,.12)';
        ctx.fillRect(px, py, TILE + 1, 2);
        if (daylight && v > 0.72) {
          ctx.fillStyle = `rgba(235,245,218,${0.05 + v * 0.06})`;
          ctx.fillRect(px + 7 + v * 12, py + 10 + hash2(x, y + 4) * 12, 5, 1);
        }
      } else if (t.type === 'sand') {
        const shade = 0.94 + v * 0.06;
        ctx.fillStyle = `rgb(${Math.floor(216 * shade)},${Math.floor(198 * shade)},${Math.floor(150 * shade)})`;
        ctx.fillRect(px, py, TILE + 1, TILE + 1);
        if (v > 0.45) {
          ctx.fillStyle = 'rgba(126,104,68,.18)';
          ctx.fillRect(px + 5 + v * 14, py + 8 + hash2(x, y + 2) * 18, 2, 1);
          ctx.fillRect(px + 20 - v * 9, py + 22 - v * 10, 1, 1);
        }
        if (v > 0.86) {
          ctx.strokeStyle = 'rgba(248,232,200,.55)';
          ctx.lineWidth = 1;
          ctx.beginPath();
          ctx.arc(px + 8 + v * 6, py + 24 - v * 9, 2.2, Math.PI, Math.PI * 1.9);
          ctx.stroke();
        }
        // 潮线泡沫
        const up = y > 0 ? map[y - 1][x] : null;
        if (up && (up.type === 'shallow' || up.type === 'deep')) {
          ctx.fillStyle = 'rgba(232,240,220,.22)';
          ctx.fillRect(px, py, TILE + 1, 2);
        }
      } else if (t.type === 'grass') {
        const shade = 0.92 + v * 0.12;
        ctx.fillStyle = `rgb(${Math.floor(100 * shade)},${Math.floor(141 * shade)},${Math.floor(78 * shade)})`;
        ctx.fillRect(px, py, TILE + 1, TILE + 1);
        ctx.strokeStyle = `rgba(46,78,42,${0.18 + v * 0.12})`;
        ctx.lineWidth = 1;
        const gx = px + 8 + v * 14, gy = py + 12 + hash2(y, x) * 12;
        ctx.beginPath(); ctx.moveTo(gx, gy + 5); ctx.lineTo(gx + 2, gy); ctx.moveTo(gx + 4, gy + 5); ctx.lineTo(gx + 6, gy + 1); ctx.stroke();
        if (v > 0.72) {
          ctx.fillStyle = v > 0.9 ? 'rgba(224,196,116,.5)' : 'rgba(214,224,170,.35)';
          ctx.beginPath(); ctx.arc(px + 22 - v * 5, py + 9 + hash2(y, x + 3) * 15, 1.2, 0, Math.PI * 2); ctx.fill();
        }
      } else if (t.type === 'jungle') {
        const shade = 0.82 + v * 0.14;
        ctx.fillStyle = `rgb(${Math.floor(57 * shade)},${Math.floor(94 * shade)},${Math.floor(57 * shade)})`;
        ctx.fillRect(px, py, TILE + 1, TILE + 1);
        ctx.fillStyle = 'rgba(23,51,31,.22)';
        ctx.beginPath();
        ctx.ellipse(px + 10 + v * 14, py + 12 + hash2(x, y) * 12, 7, 3, v * 3, 0, Math.PI * 2);
        ctx.fill();
        ctx.fillStyle = 'rgba(113,151,86,.22)';
        ctx.fillRect(px + 20, py + 6, 5, 2);
        if (v > 0.8) {
          ctx.strokeStyle = 'rgba(126,164,93,.32)'; ctx.lineWidth = 1;
          ctx.beginPath();
          ctx.moveTo(px + 5, py + 27); ctx.quadraticCurveTo(px + 10, py + 17, px + 15, py + 24);
          ctx.moveTo(px + 10, py + 24); ctx.quadraticCurveTo(px + 15, py + 14, px + 20, py + 22);
          ctx.stroke();
        }
      } else if (t.type === 'rock') {
        ctx.fillStyle = '#777b70';
        ctx.fillRect(px, py, TILE + 1, TILE + 1);
        ctx.fillStyle = 'rgba(48,54,50,.24)';
        ctx.beginPath();
        ctx.moveTo(px + 2, py + 20);
        ctx.lineTo(px + 12 + v * 8, py + 4);
        ctx.lineTo(px + 29, py + 13);
        ctx.lineTo(px + 22, py + 29);
        ctx.lineTo(px + 7, py + 28);
        ctx.closePath(); ctx.fill();
        ctx.strokeStyle = 'rgba(196,201,184,.2)';
        ctx.beginPath(); ctx.moveTo(px + 10, py + 8); ctx.lineTo(px + 20, py + 15); ctx.stroke();
      } else if (t.type === 'pond') {
        ctx.fillStyle = '#286d7d';
        ctx.fillRect(px, py, TILE + 1, TILE + 1);
        const shimmer = 0.5 + 0.5 * Math.sin(tNow * 1.6 + x + y * 0.7);
        ctx.strokeStyle = `rgba(164,225,222,${0.10 + shimmer * 0.13})`;
        ctx.beginPath();
        ctx.moveTo(px + 4, py + 12 + v * 8);
        ctx.quadraticCurveTo(px + 16, py + 9 + v * 8, px + 28, py + 12 + v * 8);
        ctx.stroke();
      }
    }
  }
}

function drawHillMarker() {
  if (!hill || beacon) return;
  const x = hill.x, y = hill.y;
  const pulse = 0.5 + 0.5 * Math.sin(tNow * 2);
  ctx.save();
  ctx.translate(x, y);
  ctx.strokeStyle = `rgba(228,163,83,${0.22 + pulse * 0.25})`;
  ctx.lineWidth = 1.5;
  ctx.beginPath(); ctx.ellipse(0, 2, 45 + pulse * 4, 28 + pulse * 3, 0, 0, Math.PI * 2); ctx.stroke();
  ctx.strokeStyle = 'rgba(228,163,83,.15)';
  ctx.beginPath(); ctx.ellipse(0, 2, 62, 39, 0, 0, Math.PI * 2); ctx.stroke();
  // 石堆
  ctx.fillStyle = '#5b5d52';
  for (const [ox, oy, r] of [[-9, 1, 6], [4, 0, 7], [11, 3, 5], [-2, -7, 5], [5, -8, 4]]) {
    ctx.beginPath(); ctx.ellipse(ox, oy, r, r * 0.7, 0, 0, Math.PI * 2); ctx.fill();
  }
  // 旗杆
  ctx.strokeStyle = '#7c6243';
  ctx.lineWidth = 3;
  ctx.beginPath(); ctx.moveTo(0, -4); ctx.lineTo(0, -58); ctx.stroke();
  ctx.fillStyle = '#c86845';
  ctx.beginPath();
  ctx.moveTo(1, -56);
  ctx.lineTo(28 + Math.sin(tNow * 2) * 3, -49);
  ctx.lineTo(1, -41);
  ctx.closePath(); ctx.fill();
  ctx.fillStyle = 'rgba(242,216,166,.86)';
  ctx.font = '8px "Microsoft YaHei",sans-serif';
  ctx.textAlign = 'center';
  ctx.fillText('信号高地', 0, 22);
  ctx.restore();
}

function drawNode(n) {
  const def = NODE_DEFS[n.type];
  const depleted = n.uses <= 0;
  if (n.type === 'driftwood' && depleted) return;
  const x = n.x, y = n.y;
  const sway = Math.sin(tNow * 1.2 + n.phase) * 1.6;
  ctx.save();
  ctx.translate(x, y);

  if (n.type === 'palm') {
    drawShadow(0, 2, 20, 7);
    if (depleted) { drawStump('#6f4d32'); ctx.restore(); return; }
    ctx.strokeStyle = '#785336';
    ctx.lineWidth = 5;
    ctx.beginPath();
    ctx.moveTo(0, 2);
    ctx.quadraticCurveTo(-9, -25, -4 + sway, -50);
    ctx.stroke();
    ctx.strokeStyle = '#9a6d43';
    ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-1, 0); ctx.quadraticCurveTo(-9, -24, -4 + sway, -48); ctx.stroke();
    const crownX = -4 + sway, crownY = -50;
    for (let i = 0; i < 7; i++) {
      const a = -Math.PI + i * (Math.PI * 2 / 7);
      ctx.strokeStyle = i % 2 ? '#3f7448' : '#4d8250';
      ctx.lineWidth = 5;
      ctx.beginPath();
      ctx.moveTo(crownX, crownY);
      const ex = crownX + Math.cos(a) * 28, ey = crownY + Math.sin(a) * 14 + 6;
      ctx.quadraticCurveTo(crownX + Math.cos(a) * 16, crownY + Math.sin(a) * 7 - 8, ex, ey);
      ctx.stroke();
    }
    ctx.fillStyle = '#3e5e33';
    ctx.beginPath(); ctx.arc(crownX, crownY, 5, 0, Math.PI * 2); ctx.fill();
    if (n.uses > 0) {
      ctx.fillStyle = '#5a4028';
      ctx.beginPath(); ctx.arc(crownX - 4, crownY + 5, 3.5, 0, Math.PI * 2); ctx.arc(crownX + 3, crownY + 7, 3, 0, Math.PI * 2); ctx.fill();
    }
  } else if (n.type === 'tree') {
    drawShadow(0, 3, 24, 8);
    if (depleted) { drawStump('#5d4631'); ctx.restore(); return; }
    ctx.strokeStyle = '#584330';
    ctx.lineWidth = 7;
    ctx.beginPath(); ctx.moveTo(0, 2); ctx.lineTo(sway, -27); ctx.stroke();
    const colors = ['#2e5739', '#376443', '#426f48'];
    for (let i = 0; i < 4; i++) {
      ctx.fillStyle = colors[i % 3];
      ctx.beginPath();
      ctx.arc(sway + [-13, 8, -2, 15][i], -42 + [4, 1, -9, 9][i], 16 - i * 1.5, 0, Math.PI * 2);
      ctx.fill();
    }
    ctx.fillStyle = 'rgba(150,184,116,.18)';
    ctx.beginPath(); ctx.arc(sway - 4, -48, 11, 0, Math.PI * 2); ctx.fill();
  } else if (n.type === 'bush') {
    drawShadow(0, 2, 15, 5);
    if (depleted) {
      ctx.strokeStyle = '#4d5f3a'; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.moveTo(-8, 0); ctx.lineTo(0, -9); ctx.lineTo(8, 0); ctx.stroke();
      ctx.restore(); return;
    }
    ctx.fillStyle = '#3f6a43';
    ctx.beginPath(); ctx.arc(-8, -4, 8, 0, Math.PI * 2); ctx.arc(5, -7, 9, 0, Math.PI * 2); ctx.arc(0, 1, 7, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#517b4b';
    ctx.beginPath(); ctx.arc(-4, -8, 5, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#c45f52';
    for (let i = 0; i < 5; i++) {
      ctx.beginPath();
      ctx.arc(-8 + i * 4, -8 + Math.sin(i * 2) * 5, 2, 0, Math.PI * 2);
      ctx.fill();
    }
  } else if (n.type === 'rock') {
    drawShadow(0, 3, 15, 5);
    const scale = depleted ? 0.6 : 1;
    ctx.scale(scale, scale);
    ctx.fillStyle = '#6f746d';
    ctx.beginPath();
    ctx.moveTo(-14, 2); ctx.lineTo(-9, -10); ctx.lineTo(3, -15); ctx.lineTo(14, -5); ctx.lineTo(11, 4); ctx.lineTo(-5, 6);
    ctx.closePath(); ctx.fill();
    ctx.fillStyle = '#91968a';
    ctx.beginPath(); ctx.moveTo(-9, -10); ctx.lineTo(3, -15); ctx.lineTo(7, -7); ctx.lineTo(-3, -4); ctx.closePath(); ctx.fill();
    ctx.strokeStyle = 'rgba(45,50,46,.45)';
    ctx.beginPath(); ctx.moveTo(4, -3); ctx.lineTo(1, 5); ctx.moveTo(-4, -3); ctx.lineTo(-9, 2); ctx.stroke();
  } else if (n.type === 'driftwood') {
    drawShadow(0, 2, 15, 4);
    ctx.strokeStyle = '#7b5c3e'; ctx.lineWidth = 5;
    ctx.beginPath(); ctx.moveTo(-14, 1); ctx.lineTo(12, -5); ctx.stroke();
    ctx.strokeStyle = '#a17a50'; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-13, -3); ctx.lineTo(10, -9); ctx.stroke();
    ctx.strokeStyle = '#63492f'; ctx.lineWidth = 3;
    ctx.beginPath(); ctx.moveTo(-5, 5); ctx.lineTo(8, 5); ctx.stroke();
  } else if (n.type === 'herb') {
    if (depleted) {
      ctx.strokeStyle = '#5b6e44'; ctx.lineWidth = 1.4;
      ctx.beginPath(); ctx.moveTo(-4, 1); ctx.lineTo(-2, -5); ctx.moveTo(3, 1); ctx.lineTo(4, -4); ctx.stroke();
      ctx.restore(); return;
    }
    ctx.strokeStyle = '#507b4b'; ctx.lineWidth = 1.5;
    for (let i = 0; i < 4; i++) {
      const ox = -5 + i * 3.5;
      ctx.beginPath(); ctx.moveTo(ox, 2); ctx.quadraticCurveTo(ox + (i % 2 ? 4 : -4), -8, ox + (i % 2 ? 1 : -1), -16); ctx.stroke();
      ctx.fillStyle = i % 2 ? '#6e9a5c' : '#7fa962';
      ctx.beginPath(); ctx.ellipse(ox + (i % 2 ? -3 : 3), -8, 3, 1.6, i, 0, Math.PI * 2); ctx.fill();
    }
    ctx.fillStyle = '#d7c270';
    ctx.beginPath(); ctx.arc(1, -17, 2.2, 0, Math.PI * 2); ctx.fill();
  }
  ctx.restore();
  if (depleted && n.regrowAt) {
    ctx.save();
    ctx.globalAlpha = 0.6;
    ctx.fillStyle = 'rgba(235,221,184,.5)';
    ctx.font = '8px "Microsoft YaHei",sans-serif';
    ctx.textAlign = 'center';
    ctx.fillText('恢复中', x, y - 18);
    ctx.restore();
  }
}

function drawStump(color) {
  ctx.fillStyle = color;
  ctx.fillRect(-5, -8, 10, 9);
  ctx.fillStyle = '#b09161';
  ctx.beginPath(); ctx.ellipse(0, -8, 5, 2.2, 0, 0, Math.PI * 2); ctx.fill();
  ctx.strokeStyle = '#7a5e3d'; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.ellipse(0, -8, 2.5, 1.2, 0, 0, Math.PI * 2); ctx.stroke();
}

function drawShadow(x, y, rx, ry, alpha = 0.24) {
  ctx.fillStyle = `rgba(11,25,20,${alpha})`;
  ctx.beginPath(); ctx.ellipse(x, y, rx, ry, 0, 0, Math.PI * 2); ctx.fill();
}

function drawFire(f, big = false) {
  const x = f.x, y = f.y;
  const lit = f.fuel > 0;
  drawShadow(0, 3, 18, 6);
  ctx.save();
  ctx.translate(x, y);
  ctx.fillStyle = '#5d5e52';
  for (let i = 0; i < 7; i++) {
    const a = i / 7 * Math.PI * 2;
    ctx.beginPath(); ctx.ellipse(Math.cos(a) * 15, Math.sin(a) * 8 + 1, 4, 3, a, 0, Math.PI * 2); ctx.fill();
  }
  ctx.strokeStyle = '#5b402b'; ctx.lineWidth = 4;
  ctx.beginPath(); ctx.moveTo(-9, 1); ctx.lineTo(9, -3); ctx.moveTo(-7, -4); ctx.lineTo(8, 2); ctx.stroke();
  if (lit) {
    const flick = Math.sin(tNow * 12 + x) * 2;
    const h = big ? 37 : 23;
    ctx.fillStyle = 'rgba(220,110,49,.95)';
    ctx.beginPath();
    ctx.moveTo(-8, 0);
    ctx.quadraticCurveTo(-4, -h * 0.35, -2 + flick, -h);
    ctx.quadraticCurveTo(6, -h * 0.42, 8, 0);
    ctx.closePath(); ctx.fill();
    ctx.fillStyle = '#f0b761';
    ctx.beginPath();
    ctx.moveTo(-4, -1);
    ctx.quadraticCurveTo(-1, -h * 0.32, 1 + flick * 0.5, -h * 0.7);
    ctx.quadraticCurveTo(5, -h * 0.3, 5, 0);
    ctx.closePath(); ctx.fill();
    ctx.fillStyle = '#ffe0a0';
    ctx.beginPath(); ctx.ellipse(1, -4, 3, 5 + flick * 0.2, 0, 0, Math.PI * 2); ctx.fill();
    // 烟
    ctx.globalAlpha = 0.13;
    ctx.fillStyle = '#dce2d2';
    for (let i = 0; i < 3; i++) {
      const sy = -h - 10 - i * 12 - (tNow * 7 + i * 8) % 12;
      ctx.beginPath(); ctx.arc(Math.sin(tNow + i) * 6, sy, 6 + i * 3, 0, Math.PI * 2); ctx.fill();
    }
    ctx.globalAlpha = 1;
  }
  ctx.restore();
}

function drawShelter(sh) {
  ctx.save();
  ctx.translate(sh.x, sh.y);
  drawShadow(0, 3, 29, 8);
  ctx.strokeStyle = '#6b4e34'; ctx.lineWidth = 4;
  ctx.beginPath(); ctx.moveTo(-20, 2); ctx.lineTo(-16, -33); ctx.moveTo(18, 2); ctx.lineTo(15, -25); ctx.stroke();
  ctx.fillStyle = '#4f7040';
  ctx.beginPath();
  ctx.moveTo(-25, -12); ctx.lineTo(-18, -42); ctx.lineTo(21, -31); ctx.lineTo(24, -8); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#658450';
  for (let i = 0; i < 4; i++) {
    ctx.beginPath();
    ctx.ellipse(-12 + i * 10, -24 - i * 2, 8, 2.4, 0.25 + i * 0.1, 0, Math.PI * 2);
    ctx.fill();
  }
  ctx.strokeStyle = '#b49b6d'; ctx.lineWidth = 1;
  ctx.beginPath(); ctx.moveTo(-18, -42); ctx.lineTo(21, -31); ctx.stroke();
  ctx.fillStyle = 'rgba(20,35,24,.22)';
  ctx.beginPath(); ctx.ellipse(0, -5, 14, 7, 0, 0, Math.PI * 2); ctx.fill();
  ctx.restore();
}

function drawStorySites() {
  for (const site of storySites) {
    if (site.x < camera.x - 120 || site.x > camera.x + VW + 120 || site.y < camera.y - 140 || site.y > camera.y + VH + 120) continue;
    const x = site.x, y = site.y;
    const pulse = 0.5 + 0.5 * Math.sin(tNow * 2.2 + (site.id === 'cave' ? 1.7 : 0));
    ctx.save();
    ctx.translate(x, y);
    drawShadow(0, 8, 28, 9, 0.28);
    if (site.kind === 'camp') {
      ctx.fillStyle = '#6d5738';
      ctx.beginPath(); ctx.moveTo(-26, 6); ctx.lineTo(0, -30); ctx.lineTo(26, 6); ctx.closePath(); ctx.fill();
      ctx.fillStyle = '#3d3325';
      ctx.beginPath(); ctx.moveTo(-10, 6); ctx.lineTo(0, -19); ctx.lineTo(11, 6); ctx.closePath(); ctx.fill();
      ctx.strokeStyle = '#8d744d'; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.moveTo(0, -30); ctx.lineTo(0, -40); ctx.stroke();
      ctx.fillStyle = '#4d4637'; ctx.fillRect(16, -1, 12, 9);
      ctx.fillStyle = '#2f5a58'; ctx.fillRect(18, -14, 12, 8);
      ctx.fillStyle = '#a98a5a'; ctx.fillRect(19, -13, 3, 3);
    } else if (site.kind === 'cave') {
      ctx.fillStyle = '#596055';
      ctx.beginPath(); ctx.ellipse(0, 0, 27, 20, 0, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = '#2b3734';
      ctx.beginPath(); ctx.ellipse(0, 2, 14, 15, 0, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = '#6b7062';
      ctx.beginPath(); ctx.ellipse(-20, -8, 9, 7, -0.4, 0, Math.PI * 2); ctx.fill();
      ctx.beginPath(); ctx.ellipse(19, -7, 8, 6, 0.5, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = '#3a4f45'; ctx.fillRect(-8, 7, 14, 7);
    } else if (site.kind === 'fuel') {
      ctx.fillStyle = '#5b4b3d';
      ctx.beginPath(); ctx.moveTo(-34, 2); ctx.lineTo(-25, -24); ctx.lineTo(24, -18); ctx.lineTo(34, 5); ctx.closePath(); ctx.fill();
      ctx.fillStyle = '#775842';
      ctx.beginPath(); ctx.moveTo(-24, -23); ctx.lineTo(21, -17); ctx.lineTo(14, -6); ctx.lineTo(-18, -8); ctx.closePath(); ctx.fill();
      ctx.strokeStyle = '#b46b45'; ctx.lineWidth = 2;
      ctx.beginPath(); ctx.moveTo(-18, -8); ctx.lineTo(15, -6); ctx.moveTo(-10, -22); ctx.lineTo(5, 4); ctx.stroke();
      ctx.fillStyle = '#3e5c63';
      ctx.beginPath(); ctx.ellipse(20, 1, 8, 12, 0, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = '#d0a25c';
      ctx.beginPath(); ctx.ellipse(20, -8, 7, 4, 0, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = '#a34f37'; ctx.fillRect(-21, -3, 9, 14);
      ctx.fillStyle = '#d7c07e'; ctx.font = 'bold 7px Georgia,serif'; ctx.textAlign = 'center';
      ctx.fillText('1987', -16.5, 6);
      ctx.fillStyle = 'rgba(20,28,28,.5)';
      ctx.beginPath(); ctx.arc(28, -20, 8, 0, Math.PI * 2); ctx.fill();
    } else if (site.kind === 'spark') {
      ctx.fillStyle = '#4a4a44';
      ctx.fillRect(-25, -22, 46, 28);
      ctx.fillStyle = '#69665a';
      ctx.beginPath(); ctx.moveTo(-28, -22); ctx.lineTo(-14, -32); ctx.lineTo(25, -26); ctx.lineTo(19, -20); ctx.closePath(); ctx.fill();
      ctx.fillStyle = '#2b2c28'; ctx.fillRect(-8, -12, 18, 18);
      ctx.fillStyle = '#9b7b4b'; ctx.fillRect(-24, 1, 43, 5);
      ctx.strokeStyle = '#c9a15e'; ctx.lineWidth = 1.5;
      ctx.beginPath(); ctx.moveTo(24, -26); ctx.lineTo(24, -43); ctx.stroke();
      ctx.fillStyle = (0.6 + 0.4 * Math.sin(tNow * 3)) > 0.75 ? '#ffcf6a' : '#985338';
      ctx.beginPath(); ctx.arc(24, -44, 2.4, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = 'rgba(255,154,74,.16)';
      ctx.beginPath(); ctx.ellipse(24, -44, 10, 10, 0, 0, Math.PI * 2); ctx.fill();
      ctx.fillStyle = '#2c2923';
      ctx.beginPath(); ctx.ellipse(-26, 7, 8, 3, 0.2, 0, Math.PI * 2); ctx.fill();
    }
    if (!site.found) {
      ctx.strokeStyle = `rgba(228,163,83,${0.22 + pulse * 0.3})`;
      ctx.lineWidth = 1.4;
      ctx.beginPath(); ctx.ellipse(0, 4, 42 + pulse * 4, 26 + pulse * 3, 0, 0, Math.PI * 2); ctx.stroke();
      ctx.fillStyle = `rgba(242,196,120,${0.8 + pulse * 0.2})`;
      ctx.font = 'bold 13px Georgia,serif'; ctx.textAlign = 'center';
      ctx.fillText('!', 0, -48 - pulse * 3);
    }
    ctx.fillStyle = site.found ? 'rgba(158,170,153,.55)' : 'rgba(242,224,182,.82)';
    ctx.font = '8px "Microsoft YaHei",sans-serif'; ctx.textAlign = 'center';
    ctx.fillText(site.name, 0, 28);
    ctx.restore();
  }
}

function drawEnemy(e) {
  if (e.dead) return;
  if (e.x < camera.x - 100 || e.x > camera.x + VW + 100 || e.y < camera.y - 120 || e.y > camera.y + VH + 100) return;
  const x = e.x, y = e.y;
  const aggro = dist(state.player.x, state.player.y, e.x, e.y) < e.aggro;
  const hit = e.hitFlash > 0;
  ctx.save();
  ctx.translate(x, y);
  if (e.type === 'boar') {
    const gait = Math.sin(tNow * (aggro ? 11 : 4.5) + e.x * 0.08);
    drawShadow(0, 9, 26 + Math.abs(gait) * 1.5, 9, 0.3);
    ctx.strokeStyle = '#3d3027'; ctx.lineWidth = 4; ctx.lineCap = 'round';
    [[-13, 6], [-5, 7], [7, 6], [14, 5]].forEach(([lx, ly], i) => {
      const stride = gait * (i % 2 ? 2.4 : -2.4);
      ctx.beginPath(); ctx.moveTo(lx, ly); ctx.lineTo(lx + (lx < 0 ? -2 : 2) + stride, ly + 9); ctx.stroke();
    });
    ctx.fillStyle = hit ? '#efdbc2' : '#584333';
    ctx.beginPath(); ctx.ellipse(-3, -3, 22, 13 + Math.sin(tNow * 2 + e.x) * 0.5, 0, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = hit ? '#f2e2ca' : '#6a5140';
    ctx.beginPath(); ctx.ellipse(18, -7, 11, 9, 0.15, 0, Math.PI * 2); ctx.fill();
    // 鬃毛
    ctx.strokeStyle = 'rgba(39,31,25,.55)'; ctx.lineWidth = 1.2;
    for (let i = 0; i < 5; i++) {
      ctx.beginPath(); ctx.moveTo(-16 + i * 6, -13); ctx.lineTo(-18 + i * 6, -17); ctx.stroke();
    }
    ctx.fillStyle = '#96745b';
    ctx.beginPath(); ctx.ellipse(27, -4, 6, 4, 0.15, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#4a3528';
    ctx.beginPath(); ctx.arc(29, -4, 1, 0, Math.PI * 2); ctx.arc(26, -3, 1, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#e8e0c8';
    ctx.beginPath(); ctx.moveTo(24, 0); ctx.quadraticCurveTo(30, 5, 31, 7); ctx.quadraticCurveTo(28, 4, 26, 1); ctx.closePath(); ctx.fill();
    ctx.fillStyle = aggro || isNight() ? '#f0b96a' : '#211d19';
    ctx.beginPath(); ctx.arc(18, -11, 1.8, 0, Math.PI * 2); ctx.fill();
    if (aggro || isNight()) {
      ctx.fillStyle = 'rgba(240,185,106,.15)';
      ctx.beginPath(); ctx.arc(18, -11, 5, 0, Math.PI * 2); ctx.fill();
    }
    ctx.fillStyle = '#3a2b21';
    ctx.beginPath(); ctx.moveTo(-12, -13); ctx.lineTo(-7, -23); ctx.lineTo(-2, -13); ctx.closePath(); ctx.fill();
    ctx.fillStyle = 'rgba(150,116,90,.35)';
    ctx.beginPath(); ctx.ellipse(-10, -7, 8, 3, -0.25, 0, Math.PI * 2); ctx.fill();
    if (aggro) {
      ctx.fillStyle = '#e08970'; ctx.font = 'bold 12px Georgia,serif'; ctx.textAlign = 'center';
      ctx.fillText('!', 0, -34);
    }
  } else {
    const slither = Math.sin(tNow * 8 + e.y * 0.06);
    drawShadow(0, 6, 18, 5, 0.25);
    ctx.strokeStyle = hit ? '#e8dcc6' : '#596d3e'; ctx.lineWidth = 5; ctx.lineCap = 'round';
    ctx.beginPath();
    ctx.moveTo(-18, 8);
    ctx.quadraticCurveTo(-8, -6 + slither * 2, 1, 3);
    ctx.quadraticCurveTo(9, 11 + slither * 2, 15, 0);
    ctx.stroke();
    ctx.strokeStyle = 'rgba(196,208,128,.24)'; ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(-14, 6); ctx.quadraticCurveTo(-6, -2, 0, 3);
    ctx.quadraticCurveTo(8, 8, 13, 1);
    ctx.stroke();
    ctx.fillStyle = hit ? '#f0e4ce' : '#6f8248';
    ctx.beginPath(); ctx.ellipse(16, -2, 6, 4, -0.4, 0, Math.PI * 2); ctx.fill();
    ctx.strokeStyle = '#d9866b'; ctx.lineWidth = 1.5;
    ctx.beginPath(); ctx.moveTo(21, -2); ctx.lineTo(27, -5 + slither); ctx.moveTo(21, -1); ctx.lineTo(27, 1 + slither); ctx.stroke();
    ctx.fillStyle = isNight() || aggro ? '#f0c06b' : '#201b15';
    ctx.beginPath(); ctx.arc(17.5, -3.5, 1.1, 0, Math.PI * 2); ctx.fill();
    if (aggro) {
      ctx.fillStyle = '#e08970'; ctx.font = 'bold 11px Georgia,serif'; ctx.textAlign = 'center';
      ctx.fillText('!', 6, -20);
    }
  }
  if (e.hp < e.maxHp || aggro) {
    const w = 34;
    ctx.fillStyle = 'rgba(0,0,0,.55)'; ctx.fillRect(-w / 2, -24, w, 3);
    ctx.fillStyle = '#c86b55'; ctx.fillRect(-w / 2, -24, w * (e.hp / e.maxHp), 3);
  }
  if (aggro) {
    ctx.fillStyle = 'rgba(240,215,176,.85)';
    ctx.font = '8px "Microsoft YaHei",sans-serif'; ctx.textAlign = 'center';
    ctx.fillText(e.name, 0, 22);
  }
  ctx.restore();
}

function drawDock() {
  if (!dock) return;
  if (dock.x < camera.x - 100 || dock.x > camera.x + VW + 100 || dock.y < camera.y - 120 || dock.y > camera.y + VH + 100) return;
  const x = dock.x, y = dock.y;
  ctx.save();
  ctx.translate(x, y);
  drawShadow(0, 8, 30, 9, 0.25);
  ctx.fillStyle = '#6f5538';
  for (let i = 0; i < 4; i++) {
    ctx.beginPath(); ctx.ellipse(0, i * 4 - 3, 25 - i * 2, 4, 0, 0, Math.PI * 2); ctx.fill();
  }
  ctx.strokeStyle = '#8d7048'; ctx.lineWidth = 3;
  ctx.beginPath(); ctx.moveTo(0, -3); ctx.lineTo(0, -44); ctx.stroke();
  ctx.fillStyle = state.story.blackbox ? '#c9b47e' : '#6f6a58';
  ctx.beginPath(); ctx.moveTo(1, -40); ctx.lineTo(18, -34); ctx.lineTo(1, -27); ctx.closePath(); ctx.fill();
  ctx.fillStyle = 'rgba(242,224,182,.82)';
  ctx.font = '8px "Microsoft YaHei",sans-serif'; ctx.textAlign = 'center';
  ctx.fillText(state.story.blackbox ? '木筏 · 出海' : '木筏', 0, 26);
  ctx.restore();
}

function drawWreck() {
  if (!wreck) return;
  const x = wreck.x, y = wreck.y;
  ctx.save();
  ctx.translate(x, y);
  ctx.rotate(-0.18);
  drawShadow(0, 7, 38, 10, 0.3);
  ctx.fillStyle = '#c6c8bd';
  ctx.beginPath();
  ctx.moveTo(-36, -6); ctx.lineTo(-14, -17); ctx.lineTo(36, -10); ctx.lineTo(28, 9); ctx.lineTo(-26, 8); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#9b9e94';
  ctx.beginPath(); ctx.moveTo(-26, 8); ctx.lineTo(28, 9); ctx.lineTo(22, 14); ctx.lineTo(-21, 13); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#a64f3b';
  ctx.fillRect(-31, -2, 58, 3);
  ctx.fillStyle = '#5f7377';
  for (let i = 0; i < 3; i++) {
    ctx.beginPath(); ctx.ellipse(-20 + i * 14, -8, 5, 3, 0, 0, Math.PI * 2); ctx.fill();
  }
  ctx.strokeStyle = '#888d82'; ctx.lineWidth = 4;
  ctx.beginPath(); ctx.moveTo(10, 2); ctx.lineTo(42, 24); ctx.stroke();
  ctx.fillStyle = '#d9d9cf';
  ctx.beginPath(); ctx.moveTo(-20, -16); ctx.lineTo(-2, -23); ctx.lineTo(12, -15); ctx.closePath(); ctx.fill();
  ctx.fillStyle = '#7f4435';
  ctx.font = 'bold 8px monospace'; ctx.textAlign = 'center';
  ctx.fillText('SOS', 0, -3);
  ctx.restore();
  if (!wreck.looted) {
    ctx.fillStyle = 'rgba(242,224,182,.72)';
    ctx.font = '8px "Microsoft YaHei",sans-serif'; ctx.textAlign = 'center';
    ctx.fillText('飞机残骸', x, y + 26);
  }
}

function drawBeacon() {
  if (!beacon) return;
  const x = beacon.x, y = beacon.y;
  const lit = beacon.fuel > 0;
  ctx.save();
  ctx.translate(x, y);
  drawShadow(0, 5, 26, 8);
  ctx.fillStyle = '#5d5d50';
  for (let i = 0; i < 9; i++) {
    const a = i / 9 * Math.PI * 2;
    ctx.beginPath(); ctx.ellipse(Math.cos(a) * 24, Math.sin(a) * 12 + 2, 5, 3.5, a, 0, Math.PI * 2); ctx.fill();
  }
  ctx.strokeStyle = '#684d34'; ctx.lineWidth = 5;
  ctx.beginPath();
  ctx.moveTo(-16, 2); ctx.lineTo(-5, -45);
  ctx.moveTo(16, 2); ctx.lineTo(5, -45);
  ctx.moveTo(-13, 2); ctx.lineTo(13, -41);
  ctx.stroke();
  ctx.fillStyle = '#7c5c3c';
  ctx.fillRect(-8, -46, 16, 5);
  ctx.fillStyle = '#4b4d44';
  ctx.beginPath(); ctx.ellipse(0, -50, 15, 5, 0, 0, Math.PI * 2); ctx.fill();
  if (lit) {
    const flick = Math.sin(tNow * 11) * 3;
    ctx.fillStyle = '#d56835';
    ctx.beginPath();
    ctx.moveTo(-12, -50);
    ctx.quadraticCurveTo(-8, -78, 1 + flick, -101);
    ctx.quadraticCurveTo(9, -74, 12, -50);
    ctx.closePath(); ctx.fill();
    ctx.fillStyle = '#f1b65e';
    ctx.beginPath();
    ctx.moveTo(-6, -51);
    ctx.quadraticCurveTo(-2, -74, 2 + flick, -88);
    ctx.quadraticCurveTo(7, -68, 7, -51);
    ctx.closePath(); ctx.fill();
    ctx.globalAlpha = 0.12;
    ctx.fillStyle = '#e5e5d2';
    for (let i = 0; i < 4; i++) {
      ctx.beginPath(); ctx.arc(Math.sin(tNow + i) * 10, -108 - i * 16 - (tNow * 10 + i * 13) % 16, 9 + i * 4, 0, Math.PI * 2); ctx.fill();
    }
    ctx.globalAlpha = 1;
    ctx.fillStyle = '#d8d2bd';
    ctx.font = '8px "Microsoft YaHei",sans-serif'; ctx.textAlign = 'center';
    ctx.fillText('烽火台', 0, 26);
  }
  ctx.restore();
}

function drawPlayer() {
  const p = state.player;
  const sit = state.resting;
  const bob = p.moving && !sit ? Math.sin(p.walk * 2) * 1.4 : 0;
  ctx.save();
  ctx.translate(p.x, p.y + bob);
  drawShadow(0, 5, 11, 5, 0.32);
  if (sit) {
    ctx.fillStyle = '#b55036';
    ctx.beginPath(); ctx.ellipse(0, -5, 9, 7, 0, 0, Math.PI * 2); ctx.fill();
    ctx.strokeStyle = '#332b24'; ctx.lineWidth = 4;
    ctx.beginPath(); ctx.moveTo(-4, -1); ctx.lineTo(-9, 5); ctx.moveTo(5, -1); ctx.lineTo(10, 5); ctx.stroke();
    ctx.fillStyle = '#d0a176';
    ctx.beginPath(); ctx.arc(0, -15, 6.5, 0, Math.PI * 2); ctx.fill();
    ctx.fillStyle = '#33251d';
    ctx.beginPath(); ctx.arc(0, -17, 6.3, Math.PI, Math.PI * 2); ctx.fill();
    ctx.restore();
    return;
  }
  const step = p.moving ? Math.sin(p.walk) * 3.5 : 0;
  const armSwing = p.moving ? Math.sin(p.walk) * 2.6 : Math.sin(tNow * 1.7) * 0.4;
  const breathe = Math.sin(tNow * 2.1 + p.walk * 0.2) * 0.35;
  ctx.strokeStyle = '#4b4337'; ctx.lineWidth = 4; ctx.lineCap = 'round';
  ctx.beginPath();
  ctx.moveTo(-3, -5); ctx.lineTo(-4 - step, 3);
  ctx.moveTo(3, -5); ctx.lineTo(4 + step, 3);
  ctx.stroke();
  ctx.fillStyle = '#2e332f';
  ctx.beginPath(); ctx.ellipse(-4 - step, 4, 4, 2, 0, 0, Math.PI * 2); ctx.ellipse(4 + step, 4, 4, 2, 0, 0, Math.PI * 2); ctx.fill();
  // 身体：暗部 + 高光
  ctx.fillStyle = '#a84430';
  ctx.beginPath(); ctx.ellipse(0, -12 + breathe, 8.5, 11.5, 0, 0, Math.PI * 2); ctx.fill();
  ctx.fillStyle = '#c05a3d';
  ctx.beginPath(); ctx.ellipse(-2.2, -13 + breathe, 5.2, 9.2, -0.08, 0, Math.PI * 2); ctx.fill();
  ctx.fillStyle = 'rgba(255,214,170,.13)';
  ctx.beginPath(); ctx.ellipse(-4, -15 + breathe, 2.2, 5.5, -0.2, 0, Math.PI * 2); ctx.fill();
  ctx.fillStyle = '#8f3f2c';
  ctx.beginPath(); ctx.ellipse(0, -7 + breathe, 7, 4, 0, 0, Math.PI * 2); ctx.fill();
  // 背包与肩带
  ctx.fillStyle = '#6d543a';
  ctx.beginPath(); ctx.ellipse(0, -13 + breathe, 6, 7, 0, 0, Math.PI * 2); ctx.fill();
  ctx.strokeStyle = '#4b3826'; ctx.lineWidth = 1.5;
  ctx.beginPath(); ctx.moveTo(-5, -15 + breathe); ctx.lineTo(5, -15 + breathe); ctx.stroke();
  ctx.strokeStyle = '#3e2f21'; ctx.lineWidth = 1.2;
  ctx.beginPath(); ctx.moveTo(-7, -16 + breathe); ctx.lineTo(-4, -8 + breathe); ctx.moveTo(7, -16 + breathe); ctx.lineTo(4, -8 + breathe); ctx.stroke();
  // 手臂随步伐摆动
  ctx.strokeStyle = '#d0a176'; ctx.lineWidth = 3.2;
  ctx.beginPath();
  ctx.moveTo(-7, -14 + breathe); ctx.lineTo(-10 - armSwing, -5);
  ctx.moveTo(7, -14 + breathe); ctx.lineTo(10 + armSwing, -6);
  ctx.stroke();
  // 头与发际
  ctx.fillStyle = '#d7a87c';
  ctx.beginPath(); ctx.arc(0, -24 + breathe * 0.5, 7.2, 0, Math.PI * 2); ctx.fill();
  ctx.fillStyle = 'rgba(105,63,43,.25)';
  ctx.beginPath(); ctx.arc(2, -22.5 + breathe * 0.5, 5.5, -0.6, 1.8); ctx.fill();
  ctx.fillStyle = '#34251c';
  ctx.beginPath(); ctx.arc(0, -26 + breathe * 0.5, 7.3, Math.PI, Math.PI * 2); ctx.fill();
  ctx.beginPath(); ctx.ellipse(-6.2, -23.5 + breathe * 0.5, 1.7, 4.1, 0.18, 0, Math.PI * 2); ctx.fill();
  ctx.beginPath(); ctx.ellipse(6.2, -23.5 + breathe * 0.5, 1.7, 4.1, -0.18, 0, Math.PI * 2); ctx.fill();
  ctx.fillStyle = 'rgba(215,168,124,.85)';
  ctx.beginPath(); ctx.ellipse(-7.3, -23 + breathe * 0.5, 1.2, 1.8, 0, 0, Math.PI * 2); ctx.fill();
  ctx.beginPath(); ctx.ellipse(7.3, -23 + breathe * 0.5, 1.2, 1.8, 0, 0, Math.PI * 2); ctx.fill();
  ctx.strokeStyle = 'rgba(91,51,37,.55)'; ctx.lineWidth = 0.8;
  ctx.beginPath(); ctx.moveTo(-1.8, -20.8 + breathe * 0.5); ctx.lineTo(1.8, -20.8 + breathe * 0.5); ctx.stroke();
  ctx.fillStyle = '#2c211a';
  ctx.beginPath(); ctx.arc(Math.cos(p.dir) * 3.8, -23 + breathe * 0.5 + Math.sin(p.dir) * 1.4, 1.1, 0, Math.PI * 2); ctx.fill();
  // 工具
  if (state.tools.spear) {
    ctx.strokeStyle = '#9b7a4e'; ctx.lineWidth = 2.3;
    ctx.beginPath(); ctx.moveTo(10, -20); ctx.lineTo(22, 2); ctx.stroke();
    ctx.fillStyle = '#c7c9bd';
    ctx.beginPath(); ctx.moveTo(22, 2); ctx.lineTo(25, 7); ctx.lineTo(20, 5); ctx.closePath(); ctx.fill();
  }
  if (state.tools.axe) {
    ctx.strokeStyle = '#9b7a4e'; ctx.lineWidth = 2;
    ctx.beginPath(); ctx.moveTo(-10, -13); ctx.lineTo(-16, -2); ctx.stroke();
    ctx.fillStyle = '#8f9388';
    ctx.beginPath(); ctx.moveTo(-16, -2); ctx.lineTo(-22, -5); ctx.lineTo(-20, 2); ctx.closePath(); ctx.fill();
  }
  ctx.restore();
}

/* --------------------------- 绘制：光照与天气 --------------------------- */

function worldToScreen(x, y) {
  return { x: x - camera.x, y: y - camera.y };
}

function drawNight() {
  const a = darkness();
  if (a <= 0.005) return;
  nctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  nctx.clearRect(0, 0, VW, VH);
  nctx.fillStyle = `rgba(3,10,23,${a})`;
  nctx.fillRect(0, 0, VW, VH);
  nctx.globalCompositeOperation = 'destination-out';
  const hole = (x, y, r, strength) => {
    const g = nctx.createRadialGradient(x, y, r * 0.12, x, y, r);
    g.addColorStop(0, `rgba(0,0,0,${strength})`);
    g.addColorStop(0.55, `rgba(0,0,0,${strength * 0.55})`);
    g.addColorStop(1, 'rgba(0,0,0,0)');
    nctx.fillStyle = g;
    nctx.fillRect(x - r, y - r, r * 2, r * 2);
  };
  const ps = worldToScreen(state.player.x, state.player.y);
  hole(ps.x, ps.y, 155, 0.92);
  fires.forEach(f => {
    if (f.fuel <= 0) return;
    const s = worldToScreen(f.x, f.y);
    hole(s.x, s.y, 175, 0.55);
  });
  if (beacon && beacon.fuel > 0) {
    const s = worldToScreen(beacon.x, beacon.y);
    hole(s.x, s.y, 245, 0.7);
  }
  nctx.globalCompositeOperation = 'source-over';
  ctx.drawImage(nightCanvas, 0, 0, VW, VH);

  ctx.save();
  ctx.globalCompositeOperation = 'lighter';
  const glow = (x, y, r, alpha) => {
    const g = ctx.createRadialGradient(x, y, 0, x, y, r);
    g.addColorStop(0, `rgba(243,160,73,${alpha})`);
    g.addColorStop(0.4, `rgba(216,117,55,${alpha * 0.4})`);
    g.addColorStop(1, 'rgba(216,117,55,0)');
    ctx.fillStyle = g;
    ctx.fillRect(x - r, y - r, r * 2, r * 2);
  };
  fires.forEach(f => {
    if (f.fuel <= 0) return;
    const s = worldToScreen(f.x, f.y);
    glow(s.x, s.y, 150, 0.13);
  });
  if (beacon && beacon.fuel > 0) {
    const s = worldToScreen(beacon.x, beacon.y);
    glow(s.x, s.y, 220, 0.15);
  }
  ctx.restore();
}

function drawRain() {
  if (state.weather !== 'rain' && state.weather !== 'storm') return;
  const heavy = state.weather === 'storm';
  const count = heavy ? 145 : 75;
  ctx.save();
  ctx.strokeStyle = `rgba(183,216,222,${heavy ? 0.24 : 0.17})`;
  ctx.lineWidth = 1;
  ctx.beginPath();
  for (let i = 0; i < count; i++) {
    const speed = 580 + (i % 7) * 50;
    const x = ((hash2(i, 3) * (VW + 200) + tNow * 90) % (VW + 200)) - 100;
    const y = ((hash2(i, 9) * VH + tNow * speed) % (VH + 60)) - 30;
    ctx.moveTo(x, y);
    ctx.lineTo(x - (heavy ? 9 : 6), y + (heavy ? 22 : 16));
  }
  ctx.stroke();
  // 地面溅水
  ctx.strokeStyle = `rgba(205,232,232,${heavy ? 0.2 : 0.12})`;
  for (let i = 0; i < (heavy ? 18 : 10); i++) {
    const x = (hash2(i, 21) * VW + tNow * 14) % VW;
    const y = (hash2(i, 27) * VH + tNow * 22) % VH;
    ctx.beginPath();
    ctx.arc(x, y, 2 + (i % 3), Math.PI * 0.15, Math.PI * 0.85);
    ctx.stroke();
  }
  ctx.restore();
}

function drawFloats() {
  ctx.save();
  state.floats.forEach(f => {
    const s = worldToScreen(f.x, f.y);
    ctx.globalAlpha = clamp(f.life / f.max * 1.4, 0, 1);
    ctx.font = 'bold 11px "Microsoft YaHei",sans-serif';
    ctx.textAlign = 'center';
    ctx.lineWidth = 3;
    ctx.strokeStyle = 'rgba(4,12,12,.7)';
    ctx.strokeText(f.text, s.x, s.y);
    ctx.fillStyle = f.color;
    ctx.fillText(f.text, s.x, s.y);
  });
  ctx.restore();
}

let grainPattern = null;

function drawAtmosphere() {
  const profile = ISLANDS[state.currentIsland] || ISLANDS[0];
  const h = state.clock / 60;
  ctx.save();

  // 日出 / 日落暖光
  let warm = 0;
  if (h >= 5 && h < 8) warm = (1 - Math.abs(h - 6.4) / 1.6) * 0.13;
  else if (h >= 16.5 && h < 19.5) warm = (1 - Math.abs(h - 17.8) / 1.7) * 0.16;
  if (warm > 0.004) {
    const g = ctx.createLinearGradient(0, 0, VW * 0.4, VH);
    g.addColorStop(0, `rgba(255,184,102,${warm})`);
    g.addColorStop(0.55, `rgba(226,123,73,${warm * 0.45})`);
    g.addColorStop(1, 'rgba(91,70,86,0)');
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, VW, VH);
  }

  // 白天斜射光
  if (h >= 8 && h < 17) {
    const light = ctx.createLinearGradient(0, 0, VW, VH);
    light.addColorStop(0, 'rgba(255,236,185,.055)');
    light.addColorStop(0.45, 'rgba(255,236,185,.012)');
    light.addColorStop(1, 'rgba(255,236,185,0)');
    ctx.fillStyle = light;
    ctx.fillRect(0, 0, VW, VH);
  }

  // 缓慢移动的云影
  ctx.globalAlpha = 0.055;
  for (let i = 0; i < 3; i++) {
    const cx = ((tNow * (5 + i * 2) + i * 410) % (VW + 520)) - 260;
    const cy = VH * (0.18 + i * 0.27) + Math.sin(tNow * 0.12 + i) * 30;
    const r = 190 + i * 90;
    const g = ctx.createRadialGradient(cx, cy, 10, cx, cy, r);
    g.addColorStop(0, 'rgba(4,16,20,.55)');
    g.addColorStop(1, 'rgba(4,16,20,0)');
    ctx.fillStyle = g;
    ctx.fillRect(cx - r, cy - r, r * 2, r * 2);
  }
  ctx.globalAlpha = 1;

  // 火山灰
  if (profile.key === 'ash') {
    ctx.fillStyle = 'rgba(29,25,23,.55)';
    for (let i = 0; i < 46; i++) {
      const x = ((hash2(i, 7) * VW + tNow * (12 + i % 5 * 4)) % VW);
      const y = ((hash2(i, 11) * VH + tNow * (18 + i % 7 * 5)) % VH);
      const s = 1 + hash2(i, 3) * 2.4;
      ctx.fillRect(x, y, s, s);
    }
    const heat = ctx.createLinearGradient(0, VH, 0, VH * 0.55);
    heat.addColorStop(0, 'rgba(211,83,39,.10)');
    heat.addColorStop(1, 'rgba(211,83,39,0)');
    ctx.fillStyle = heat;
    ctx.fillRect(0, VH * 0.55, VW, VH * 0.45);
  }
  ctx.restore();
}

function drawGrain() {
  if (!grainPattern) {
    const c = document.createElement('canvas');
    c.width = 96; c.height = 96;
    const g = c.getContext('2d');
    const img = g.createImageData(96, 96);
    for (let i = 0; i < img.data.length; i += 4) {
      const v = Math.random() * 255;
      img.data[i] = img.data[i + 1] = img.data[i + 2] = v;
      img.data[i + 3] = 255;
    }
    g.putImageData(img, 0, 0);
    grainPattern = ctx.createPattern(c, 'repeat');
  }
  ctx.save();
  ctx.globalAlpha = 0.036;
  ctx.fillStyle = grainPattern;
  ctx.fillRect(0, 0, VW, VH);
  ctx.restore();
}

function drawVignette() {
  const g = ctx.createRadialGradient(VW / 2, VH / 2, Math.min(VW, VH) * 0.35, VW / 2, VH / 2, Math.max(VW, VH) * 0.72);
  g.addColorStop(0, 'rgba(0,0,0,0)');
  g.addColorStop(1, 'rgba(1,7,8,.34)');
  ctx.fillStyle = g;
  ctx.fillRect(0, 0, VW, VH);
}

/* --------------------------- 主渲染 --------------------------- */

function render() {
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.clearRect(0, 0, VW, VH);
  // 背景海水
  ctx.fillStyle = '#092f43';
  ctx.fillRect(0, 0, VW, VH);

  if (!map.length) return;

  const shake = state.shake > 0 ? state.shake : 0;
  const shakeX = Math.sin(tNow * 74) * shake * 18;
  const shakeY = Math.cos(tNow * 61) * shake * 12;
  ctx.save();
  ctx.translate(-camera.x + shakeX, -camera.y + shakeY);
  drawTiles();
  drawHillMarker();
  drawStorySites();
  drawDock();
  drawWreck();

  const drawables = [];
  for (const n of nodes) {
    if (n.x < camera.x - 120 || n.x > camera.x + VW + 120 || n.y < camera.y - 160 || n.y > camera.y + VH + 120) continue;
    drawables.push({ y: n.y, fn: () => drawNode(n) });
  }
  fires.forEach(f => drawables.push({ y: f.y, fn: () => drawFire(f) }));
  shelters.forEach(s => drawables.push({ y: s.y, fn: () => drawShelter(s) }));
  enemies.forEach(e => drawables.push({ y: e.y, fn: () => drawEnemy(e) }));
  if (beacon) drawables.push({ y: beacon.y, fn: drawBeacon });
  drawables.push({ y: state.player.y, fn: drawPlayer });
  drawables.sort((a, b) => a.y - b.y);
  drawables.forEach(d => d.fn());

  // 岸边水光
  ctx.restore();

  drawNight();
  drawRain();
  drawAtmosphere();
  const islandProfile = ISLANDS[state.currentIsland] || ISLANDS[0];
  if (islandProfile.tint) {
    ctx.fillStyle = islandProfile.tint;
    ctx.fillRect(0, 0, VW, VH);
  }
  if (islandProfile.key === 'mist') {
    const fog = ctx.createRadialGradient(VW * 0.25, VH * 0.35, 20, VW * 0.25, VH * 0.35, VW * 0.7);
    fog.addColorStop(0, 'rgba(196,211,201,.055)');
    fog.addColorStop(1, 'rgba(196,211,201,0)');
    ctx.fillStyle = fog; ctx.fillRect(0, 0, VW, VH);
  }
  const threat = enemies.reduce((min, e) => {
    if (e.dead) return min;
    return Math.min(min, dist(state.player.x, state.player.y, e.x, e.y));
  }, Infinity);
  if (threat < 210) {
    const g = ctx.createRadialGradient(VW / 2, VH / 2, Math.min(VW, VH) * 0.28, VW / 2, VH / 2, Math.max(VW, VH) * 0.7);
    g.addColorStop(0, 'rgba(130,20,14,0)');
    g.addColorStop(1, `rgba(130,20,14,${0.10 + (1 - threat / 210) * 0.13})`);
    ctx.fillStyle = g; ctx.fillRect(0, 0, VW, VH);
  }
  if (state.hurt > 0) {
    ctx.fillStyle = `rgba(150,28,20,${state.hurt * 0.20})`;
    ctx.fillRect(0, 0, VW, VH);
  }
  if (state.flash > 0) {
    ctx.fillStyle = `rgba(218,236,236,${state.flash * 0.22})`;
    ctx.fillRect(0, 0, VW, VH);
  }
  drawFloats();
  drawVignette();
  drawGrain();
}

/* --------------------------- 流程与主循环 --------------------------- */

function startGame() {
  if (state.phase !== 'menu') return;
  state.phase = 'playing';
  $('start').classList.add('hidden');
  log('你咳出海水，在沙滩上醒来。飞机残骸就在不远处，黑匣子的信号灯还在闪。', 'warn');
  log('先搜索残骸。天黑前生一堆火，林子里的东西不欢迎你。', 'warn');
  setTimeout(() => {
    if (activeInterfaceMode() === 'mobile') log('提示：用右侧 C 键制作，点顶部“目标”查看任务。');
    else log('提示：按 C 打开制作面板。目标在右侧。');
  }, 1400);
  refreshQuests();
  updateHUD();
  if (!guideSeen()) {
    setTimeout(() => {
      if (state.phase === 'playing' && !uiModal) openGuide(0);
    }, 650);
  }
}

function endGame(won) {
  if (state.phase === 'end') return;
  state.phase = 'end';
  state.resting = false;
  uiModal = null;
  resetTouchInput(true);
  $('quest').classList.remove('mobile-open');
  $('finale').classList.add('hidden');
  $('end').classList.remove('hidden');
  $('endKicker').textContent = won ? 'RESCUED · 获救' : 'THE END · 长眠于此';
  $('endTitle').textContent = won ? '你获救了' : '你倒下了';
  $('endText').textContent = won
    ? '救援船的汽笛穿过晨雾。你带回了黑匣子、线圈、蓄电池、柴油和点火模块，也带回了那本 1987 年的日志。岛上还有人没能等到这一天——但这一次，信号传出去了。'
    : '海风还在吹，潮水照常涨落。下一次，记得在太阳落下之前把火生起来，也别忘了林子里的东西。';
  $('endStats').innerHTML = `<div><b>${state.day}</b><span>生存天数</span></div>
    <div><b>${fires.length}</b><span>点燃篝火</span></div>
    <div><b>${state.kills}</b><span>击退野兽</span></div>
    <div><b>${state.visited.filter(Boolean).length}/6</b><span>探索岛屿</span></div>
    <div><b>${storyPartsFound()}/5</b><span>无线电部件</span></div>`;
}

function winGame() {
  if (state.phase !== 'playing') return;
  state.rescued = true;
  endGame(true);
}

function closeModal() {
  if (uiModal === 'craft') closeCraft();
  else if (uiModal === 'help') closeHelp();
  else if (uiModal === 'guide') closeGuide();
  else if (uiModal === 'story') closeStory();
  else if (uiModal === 'map') closeMap();
}

/* --------------------------- 事件绑定 --------------------------- */

$('startBtn').addEventListener('click', startGame);
$('restartBtn').addEventListener('click', () => location.reload());
$('craftBtn').addEventListener('click', openCraft);
$('restBtn').addEventListener('click', toggleRest);
$('closeCraft').addEventListener('click', closeCraft);
$('helpBtn').addEventListener('click', openHelp);
$('closeHelp').addEventListener('click', closeHelp);
$('helpOk').addEventListener('click', closeHelp);
$('startGuideBtn').addEventListener('click', () => openGuide(0));
$('guideFromHelp').addEventListener('click', () => {
  closeHelp();
  openGuide(0);
});
$('closeGuide').addEventListener('click', () => closeGuide());
$('guideSkip').addEventListener('click', () => closeGuide());
$('guideNext').addEventListener('click', nextGuide);
$('guidePrev').addEventListener('click', prevGuide);
$('closeStory').addEventListener('click', closeStory);
$('storyOk').addEventListener('click', closeStory);
$('closeMap').addEventListener('click', closeMap);
$('mapGrid').addEventListener('click', e => {
  const card = e.target.closest('[data-island]');
  if (!card || card.disabled) return;
  travelTo(Number(card.dataset.island));
});
$('modeBtn').addEventListener('click', cycleInterfaceMode);
$('startModeBtn').addEventListener('click', cycleInterfaceMode);
$('mobileQuestBtn').addEventListener('click', () => {
  if (state.phase !== 'playing') return;
  $('quest').classList.toggle('mobile-open');
});
canvas.addEventListener('pointerdown', () => $('quest').classList.remove('mobile-open'));

$('craftGrid').addEventListener('click', e => {
  const btn = e.target.closest('[data-craft]');
  if (btn && !btn.disabled) craft(btn.dataset.craft);
});
$('inventory').addEventListener('click', e => {
  const slot = e.target.closest('[data-item]');
  if (!slot) return;
  useItem(slot.dataset.item);
  slot.classList.add('flash');
  setTimeout(() => slot.classList.remove('flash'), 420);
});

window.addEventListener('keydown', e => {
  if (['ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'Space'].includes(e.code)) e.preventDefault();
  if (uiModal === 'guide') {
    if (e.code === 'ArrowLeft') { prevGuide(); return; }
    if (e.code === 'Enter' || e.code === 'Space' || e.code === 'ArrowRight') { nextGuide(); return; }
    if (e.code === 'Escape') { closeGuide(); return; }
    return;
  }
  if (e.code === 'Enter') {
    if (uiModal === 'story') { closeStory(); return; }
    if (state.phase === 'menu' && !uiModal) startGame();
    else if (state.phase === 'end') location.reload();
    return;
  }
  if (state.phase !== 'playing') return;
  if (e.code === 'Escape') {
    if (uiModal) closeModal();
    return;
  }
  if (uiModal) {
    if (uiModal === 'story' && (e.code === 'KeyE' || e.code === 'Space')) { closeStory(); return; }
    if (e.code === 'KeyC' && uiModal === 'craft') closeCraft();
    return;
  }
  if (e.code === 'KeyC') { openCraft(); return; }
  if (e.code === 'KeyR') { toggleRest(); return; }
  if (e.code === 'KeyE') { if (!e.repeat) interact(); return; }
  if (e.code === 'KeyH') { openHelp(); return; }
  if (['KeyW', 'KeyA', 'KeyS', 'KeyD', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'ShiftLeft', 'ShiftRight'].includes(e.code)) {
    keys.add(e.code);
  }
});
window.addEventListener('keyup', e => { keys.delete(e.code); });
window.addEventListener('blur', () => { keys.clear(); resetTouchInput(); });

// 点击模态背景关闭
document.querySelectorAll('.modal').forEach(m => {
  m.addEventListener('mousedown', e => { if (e.target === m) closeModal(); });
});

/* --------------------------- 启动 --------------------------- */

function frame(now) {
  const dt = Math.min(0.05, Math.max(0, (now - lastTime) / 1000));
  lastTime = now;
  tNow += dt;
  if (state.phase === 'playing' && !uiModal) update(dt);
  render();
  if (now - hudLast > 110) {
    updateHUD();
    hudLast = now;
  }
  requestAnimationFrame(frame);
}

applyInterfaceMode();
resize();
generateWorld(0);
buildQuestList();
setupTouchControls();
updateHUD();
requestAnimationFrame(frame);

// 便于自动化验收：index.html?autostart=1 直接进入游戏
const debugParams = new URLSearchParams(location.search);
if (debugParams.has('autostart')) {
  setTimeout(startGame, 250);
}
if (debugParams.has('debug')) {
  window.__islandDebug = {
    state: () => ({
      phase: state.phase,
      x: state.player.x,
      y: state.player.y,
      island: state.currentIsland,
      islandName: (ISLANDS[state.currentIsland] || ISLANDS[0]).name,
      mode: activeInterfaceMode(),
      interfaceMode,
      touch: { x: touchInput.x, y: touchInput.y, active: touchInput.active },
      sprint: touchSprint,
      story: { ...state.story },
      dock: dock ? { x: dock.x, y: dock.y } : null,
      sites: storySites.map(s => ({ id: s.id, x: s.x, y: s.y, found: s.found })),
      enemies: enemies.length,
      hill: hill ? { x: hill.x, y: hill.y } : null
    }),
    start: startGame,
    travel: travelTo,
    teleport: (x, y) => { state.player.x = x; state.player.y = y; },
    grant: (id, n = 1) => addItem(id, n),
    unlockAll: () => {
      state.story.blackbox = state.story.coil = state.story.battery = state.story.fuel = state.story.spark = true;
      state.visited = [true, true, true, true, true, true];
    },
    inspectSite: () => {
      const s = storySites[0];
      if (s) inspectStorySite(s);
    },
    closeStory,
    openMap,
    closeMap,
    beacon: () => beacon ? { fuel: beacon.fuel, progress: beacon.progress } : null,
    setProgress: n => { if (beacon) beacon.progress = Number(n); },
    setStory: patch => { Object.assign(state.story, patch); refreshQuests(); },
    clearEnemies: () => { enemies = []; },
    heal: () => { state.stats.health = 100; state.bleed = 0; state.sick = false; }
  };
}
