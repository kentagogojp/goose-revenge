'use strict';
// Made with Claude Code (Sonnet 5.5)
// ガチョウの逆襲 — Canvas 2D による疑似3D(斜め見下ろし)ゲーム。
// ワールドの計算(移動・当たり判定・AI)はすべて2D。描画のときだけ y方向を圧縮して奥行きを出す。

// ---------- 定数 ----------
const W = 720, H = 720;            // フィールド画面(正方形)
const WORLD = 1320;               // ワールドの一辺(TILEの整数倍にすること)
const TILE = 120;                  // 地面の市松模様の1マス
const YS = 0.6;                    // 描画時の y方向の圧縮率(小さいほど平たく見える)
const GAME_TIME = 60;              // 制限時間(秒)
const DUCK_TARGET = 20;            // フィールド上のアヒル数
const GOOSE_SPEED = 340;           // ガチョウの速度(px/秒)
const SPEED_RATIO = 0.8;           // アヒルの逃走速度 = ガチョウの0.8倍(ガチョウ:アヒル = 1:0.8)
const DUCK_FLEE = GOOSE_SPEED * SPEED_RATIO;
const BIG_FLEE = DUCK_FLEE;
const DUCK_WALK = 70;              // アヒルの散歩速度
const DETECT = 330;                // この距離にガチョウが入ると群れが逃げ出す
const CALM = 600;                  // これ以上離れると落ち着く
const PECK_DUR = 0.26;             // つつき動作の長さ(秒)
const PECK_GAP = 0.04;             // つつき後の隙(秒)
const RADAR_RANGE = 700;           // レーダーの探知距離
const GOOSE_KEEPOUT = 62;          // アヒルの中心がガチョウに近づける限界 = これ + アヒルの半径(つつきが届く距離を確保)
const CURSOR_RADIUS = 200;         // 照準が動ける範囲(ガチョウを中心とした画面上の半径。目で追いやすいよう近くに留める)
const COUNT_STEP = 0.8;            // カウントダウン1つ分の長さ(秒)
const COUNT_FROM = 3;              // 3, 2, 1 → スタート!
const GO_FLASH = 0.7;              // 「スタート!」表示の長さ(秒)

const STORE_BEST = 'gooseGame.best';   // {name, score}
const STORE_NAME = 'gooseGame.name';
const STORE_MUTE = 'gooseGame.muted';
const DEFAULT_NAME = '名もないガチョウ';
const GAME_TITLE = 'ガチョウの逆襲';
const GAME_URL = 'https://kentagogojp.github.io/goose-revenge/';   // 公開ページ(ローカルで遊んでもこのURLを共有する)
const SHARE_URL = GAME_URL + '?v=3';   // 投稿に入れるURL。Xは一度読んだURLの結果(カードなし)を覚えるため、読み直されるよう末尾を付けている
const HASHTAG = '#GooseRevenge';

// ---------- 要素 ----------
const wrap = document.getElementById('wrap');
const canvas = document.getElementById('field');
const ctx = canvas.getContext('2d');
const radar = document.getElementById('radar');
const rctx = radar.getContext('2d');
const startEl = document.getElementById('start');
const nameInput = document.getElementById('nameInput');
const bestText = document.getElementById('bestText');
const startBtn = document.getElementById('startBtn');
const muteText = document.getElementById('muteText');
const shareBtn = document.getElementById('shareBtn');
const pName = document.getElementById('pName');
const pScore = document.getElementById('pScore');
const pKills = document.getElementById('pKills');

// ---------- 状態 ----------
let state = 'START';               // 'START' | 'PLAY' | 'RESULT'
let result = null, resultT = 0;    // 終了画面の内容と経過時間
let lastCountStep = -1;            // 直前に鳴らしたカウントダウンの数字(音の二重鳴り防止)
let countdown = 0, goFlash = 0;   // 開始前カウントダウンの残り時間 / 「スタート!」表示の残り時間
let hadLock = false;               // ポインターロックを一度でも取得できたか
let goose, ducks, obstacles, tufts, fence, particles, texts;
let timeLeft, score, kills, bigKills, spawnCount, nextGroup, clock;
let mouseDown = false;
const keys = {};
const cursor = { x: W / 2, y: H / 2 };

// ---------- 小道具 ----------
const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
const rand = (a, b) => a + Math.random() * (b - a);

function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function loadJSON(key) {
  try { return JSON.parse(localStorage.getItem(key)); } catch (e) { return null; }
}
function saveJSON(key, val) {
  try { localStorage.setItem(key, JSON.stringify(val)); } catch (e) { /* 保存できなくても遊べる */ }
}

// ---------- 効果音(Web Audio APIで合成。音声ファイルは使わない) ----------
let audio = null, master = null, lastQuack = 0;
let muted = loadJSON(STORE_MUTE) === true;

// ブラウザの仕様で、音は最初のキー/クリック操作の後でないと出せない(startGame から呼ぶ)
function initAudio() {
  if (!audio) {
    try {
      audio = new (window.AudioContext || window.webkitAudioContext)();
      master = audio.createGain();
      master.gain.value = 0.5;
      master.connect(audio.destination);
    } catch (e) { audio = null; }
  }
  if (audio && audio.state === 'suspended') audio.resume();
}

// 周波数が f0→f1 に変化する音を1つ鳴らす
function tone(f0, f1, dur, { type = 'sine', vol = 0.25, delay = 0, filter = 0 } = {}) {
  if (!audio || muted) return;
  const t = audio.currentTime + delay;
  const osc = audio.createOscillator(), g = audio.createGain();
  osc.type = type;
  osc.frequency.setValueAtTime(f0, t);
  osc.frequency.exponentialRampToValueAtTime(Math.max(1, f1), t + dur);
  g.gain.setValueAtTime(0.0001, t);
  g.gain.exponentialRampToValueAtTime(vol, t + 0.008);
  g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
  let node = osc;
  if (filter) {                                     // 鋭い波形をこもらせる(ガーガー声などに使う)
    const f = audio.createBiquadFilter();
    f.type = 'bandpass'; f.frequency.value = filter; f.Q.value = 2;
    osc.connect(f); node = f;
  }
  node.connect(g); g.connect(master);
  osc.start(t); osc.stop(t + dur + 0.02);
}

// ノイズ(ザッ、バキッ、ドスッ のような音)
function noise(dur, { vol = 0.3, freq = 1500, type = 'lowpass', delay = 0 } = {}) {
  if (!audio || muted) return;
  const t = audio.currentTime + delay;
  const buf = audio.createBuffer(1, Math.ceil(audio.sampleRate * dur), audio.sampleRate);
  const data = buf.getChannelData(0);
  for (let i = 0; i < data.length; i++) data[i] = Math.random() * 2 - 1;
  const src = audio.createBufferSource(); src.buffer = buf;
  const f = audio.createBiquadFilter(); f.type = type; f.frequency.value = freq;
  const g = audio.createGain();
  g.gain.setValueAtTime(vol, t);
  g.gain.exponentialRampToValueAtTime(0.0001, t + dur);
  src.connect(f); f.connect(g); g.connect(master);
  src.start(t);
}

const sfx = {
  swing()   { noise(0.12, { vol: 0.18, freq: 2500, type: 'bandpass' }); tone(500, 900, 0.1, { type: 'triangle', vol: 0.06 }); },
  hit(big)  { tone(big ? 160 : 260, 90, 0.12, { type: 'square', vol: 0.18 }); noise(0.06, { vol: 0.2, freq: 3000 }); },
  kill(big) {
    tone(big ? 220 : 330, big ? 110 : 160, 0.16, { type: 'sawtooth', vol: 0.2, filter: 700 });          // ガァ
    tone(big ? 330 : 520, big ? 160 : 260, 0.14, { type: 'sawtooth', vol: 0.18, filter: 900, delay: 0.1 });
    tone(880, 1320, 0.12, { type: 'triangle', vol: 0.12, delay: 0.06 });                               // ピコッ
    if (big) { tone(110, 50, 0.3, { type: 'sine', vol: 0.35 }); noise(0.2, { vol: 0.25, freq: 800, delay: 0.02 }); }
  },
  quack(big) {                                                                                         // 逃げ出すときのクワッ
    if (!audio || audio.currentTime - lastQuack < 0.25) return;
    lastQuack = audio.currentTime;
    const k = big ? 0.7 : 1;
    tone(520 * k, 330 * k, 0.1, { type: 'sawtooth', vol: 0.07, filter: 1000 });
  },
  crash(kind) {
    if (kind === 'tree') { noise(0.28, { vol: 0.4, freq: 1800 }); tone(180, 60, 0.2, { type: 'square', vol: 0.2 }); }
    else { noise(0.3, { vol: 0.45, freq: 900 }); tone(90, 40, 0.3, { type: 'sine', vol: 0.4 }); }
  },
  thud(kind) {
    if (kind === 'tree') noise(0.1, { vol: 0.3, freq: 1500 });
    else { noise(0.08, { vol: 0.3, freq: 1200, type: 'bandpass' }); tone(200, 120, 0.08, { type: 'square', vol: 0.15 }); }
  },
  tick()    { tone(660, 660, 0.14, { type: 'square', vol: 0.15 }); },
  go()      { tone(990, 990, 0.35, { type: 'square', vol: 0.18 }); tone(1320, 1320, 0.35, { type: 'triangle', vol: 0.15 }); },
  timeUp()  { tone(660, 660, 0.18, { type: 'square', vol: 0.18 }); tone(494, 494, 0.18, { type: 'square', vol: 0.18, delay: 0.18 }); tone(330, 330, 0.5, { type: 'square', vol: 0.18, delay: 0.36 }); },
  record()  { [523, 659, 784, 1047].forEach((f, i) => tone(f, f, 0.22, { type: 'triangle', vol: 0.22, delay: 0.95 + i * 0.12 })); },
};

// ---------- 最高得点(名前+得点) ----------
function showBest() {
  const best = loadJSON(STORE_BEST);
  bestText.textContent = best && best.score > 0 ? `${best.name}  ${best.score} アヒル` : 'まだ記録なし';
}

// ---------- ワールド生成 ----------
function buildWorld() {
  const rnd = mulberry32((Date.now() & 0xffffff) + 1);
  obstacles = [];
  tufts = [];
  fence = [];

  const place = (n, kind, r, hp) => {
    let placed = 0;
    for (let tries = 0; placed < n && tries < n * 30; tries++) {
      const x = 80 + rnd() * (WORLD - 160);
      const y = 80 + rnd() * (WORLD - 160);
      if (Math.hypot(x - WORLD / 2, y - WORLD / 2) < 160) continue;       // スタート地点は空ける
      if (obstacles.some(o => Math.hypot(o.x - x, o.y - y) < o.r + r + 30)) continue;
      obstacles.push({ x, y, r, kind, v: rnd(), hp, flash: 0, peckId: 0 });
      placed++;
    }
  };
  place(15, 'tree', 18, 1);      // 木は1回、岩は2回つつくと壊れる
  place(10, 'rock', 24, 2);
  for (let i = 0; i < 100; i++) tufts.push({ x: rnd() * WORLD, y: rnd() * WORLD, v: rnd() });

  const step = 66;               // WORLD を割り切れる値にすること
  for (let t = 0; t < WORLD; t += step) {
    fence.push({ x: t, y: 0, nx: t + step, ny: 0 });
    fence.push({ x: t, y: WORLD, nx: t + step, ny: WORLD });
    fence.push({ x: 0, y: t, nx: 0, ny: t + step });
    fence.push({ x: WORLD, y: t, nx: WORLD, ny: t + step });
  }
}

// 障害物とフェンスから押し出す(これで「滑る」動きになる)
function collide(e, r) {
  e.blocked = false;
  for (const o of obstacles) {
    const dx = e.x - o.x, dy = e.y - o.y, min = o.r + r;
    const d2 = dx * dx + dy * dy;
    if (d2 < min * min) {
      const d = Math.sqrt(d2) || 0.001;
      e.x = o.x + (dx / d) * min;
      e.y = o.y + (dy / d) * min;
      e.blocked = true;
    }
  }
  e.x = clamp(e.x, r + 12, WORLD - r - 12);
  e.y = clamp(e.y, r + 12, WORLD - r - 12);
}

function isOffscreen(x, y, margin) {
  return Math.abs(x - goose.x) > W / 2 + margin || Math.abs(y - goose.y) > H / (2 * YS) + margin;
}

// 障害物のない位置を探す。pred で追加条件(画面外など)を付けられる
function freePos(r, pred) {
  let p = null;
  for (let i = 0; i < 300; i++) {
    p = { x: rand(60, WORLD - 60), y: rand(60, WORLD - 60) };
    if (obstacles.some(o => Math.hypot(o.x - p.x, o.y - p.y) < o.r + r + 10)) continue;
    if (!pred || pred(p)) return p;
  }
  return p;
}

// ---------- アヒル ----------
function makeDuck(x, y, group) {
  const big = (spawnCount++ % 10) === 9;           // 10羽に1羽が大アヒル
  return {
    x, y, group, big,
    hp: big ? 5 : 1, maxHp: big ? 5 : 1,
    r: big ? 26 : 14,
    heading: rand(0, Math.PI * 2),
    fleeing: false, offset: 0,
    wTimer: 0, wAngle: 0, wMove: false,
    fleeSpeed: big ? BIG_FLEE : DUCK_FLEE,
    kx: 0, ky: 0, flash: 0, peckId: 0, moving: false,
    phase: rand(0, 10),
  };
}

function spawnInitialDucks() {
  let total = 0;
  while (total < DUCK_TARGET) {
    const size = Math.min(1 + Math.floor(Math.random() * 5), DUCK_TARGET - total);   // 1〜5羽の群れ
    const c = freePos(30, p => Math.hypot(p.x - goose.x, p.y - goose.y) > 350);
    const gid = nextGroup++;
    for (let i = 0; i < size; i++) {
      const d = makeDuck(c.x + rand(-60, 60), c.y + rand(-60, 60), gid);
      collide(d, d.r);
      ducks.push(d);
    }
    total += size;
  }
}

// 1羽やられたら、ガチョウから見えない場所に1羽補充する
function respawnOne() {
  const groups = {};
  for (const d of ducks) (groups[d.group] = groups[d.group] || []).push(d);
  const cands = Object.values(groups).filter(g => g.length < 5 && g.every(d => isOffscreen(d.x, d.y, 60)));
  if (cands.length && Math.random() < 0.6) {
    const g = cands[Math.floor(Math.random() * cands.length)];
    for (let i = 0; i < 20; i++) {
      const x = g[0].x + rand(-70, 70), y = g[0].y + rand(-70, 70);
      if (x < 40 || y < 40 || x > WORLD - 40 || y > WORLD - 40) continue;
      if (!isOffscreen(x, y, 40)) continue;
      if (obstacles.some(o => Math.hypot(o.x - x, o.y - y) < o.r + 30)) continue;
      ducks.push(makeDuck(x, y, g[0].group));
      return;
    }
  }
  const p = freePos(26, q => isOffscreen(q.x, q.y, 60));
  ducks.push(makeDuck(p.x, p.y, nextGroup++));
}

function updateDucks(dt) {
  const alarmed = {}, cent = {};
  for (const d of ducks) {
    const c = cent[d.group] || (cent[d.group] = { x: 0, y: 0, n: 0 });
    c.x += d.x; c.y += d.y; c.n++;
    if (Math.hypot(d.x - goose.x, d.y - goose.y) < DETECT) alarmed[d.group] = true;
  }

  for (const d of ducks) {
    const dx = d.x - goose.x, dy = d.y - goose.y, dist = Math.hypot(dx, dy) || 1;

    // 群れの誰かがガチョウに気づいたら全員逃げる。ただし逃げる方向は個体ごとにばらばら
    if (alarmed[d.group]) {
      if (!d.fleeing) {
        d.fleeing = true; d.offset = rand(-1.2, 1.2);
        if (Math.random() < 0.25) sfx.quack(d.big);
      }
    } else if (d.fleeing && dist > CALM) {
      d.fleeing = false;
    }

    let vx, vy, speed;
    if (d.fleeing) {
      const a = Math.atan2(dy, dx) + d.offset;
      vx = Math.cos(a); vy = Math.sin(a);
      // 壁際では内側へ、障害物からは遠ざかるように舵を切る
      const m = 170;
      vx += (Math.max(0, (m - d.x) / m) - Math.max(0, (m - (WORLD - d.x)) / m)) * 1.8;
      vy += (Math.max(0, (m - d.y) / m) - Math.max(0, (m - (WORLD - d.y)) / m)) * 1.8;
      for (const o of obstacles) {
        const ox = d.x - o.x, oy = d.y - o.y, range = o.r + d.r + 55;
        const od = Math.hypot(ox, oy);
        if (od < range && od > 0) {
          const k = (1 - od / range) * 2.4;
          vx += (ox / od) * k; vy += (oy / od) * k;
        }
      }
      const l = Math.hypot(vx, vy) || 1;
      vx /= l; vy /= l;
      speed = d.fleeSpeed;
    } else {
      d.wTimer -= dt;
      if (d.wTimer <= 0) {
        d.wTimer = rand(1.5, 4.5);
        d.wAngle = rand(0, Math.PI * 2);
        d.wMove = Math.random() < 0.6;
        const c = cent[d.group];
        if (Math.hypot(d.x - c.x / c.n, d.y - c.y / c.n) > 130) {   // 群れから離れすぎたら戻る
          d.wAngle = Math.atan2(c.y / c.n - d.y, c.x / c.n - d.x);
          d.wMove = true;
        }
      }
      vx = Math.cos(d.wAngle); vy = Math.sin(d.wAngle);
      speed = d.wMove ? DUCK_WALK : 0;
    }

    d.x += vx * speed * dt + d.kx * dt;
    d.y += vy * speed * dt + d.ky * dt;
    d.kx *= Math.max(0, 1 - 8 * dt); d.ky *= Math.max(0, 1 - 8 * dt);
    collide(d, d.r);
    // ガチョウの体に密着させない(近すぎるとつつきの先端が届かないため、押し出す)
    const gx = d.x - goose.x, gy = d.y - goose.y, gd = Math.hypot(gx, gy);
    const keep = GOOSE_KEEPOUT + d.r;
    if (gd < keep) {
      const a = gd > 0.01 ? Math.atan2(gy, gx) : Math.random() * Math.PI * 2;
      d.x = goose.x + Math.cos(a) * keep;
      d.y = goose.y + Math.sin(a) * keep;
      collide(d, d.r);
    }
    if (d.blocked && !d.fleeing) d.wTimer = 0;
    if (speed > 1) { d.heading = Math.atan2(vy, vx); d.moving = true; } else d.moving = false;
    d.flash = Math.max(0, d.flash - dt);
  }
}

// ---------- ガチョウ ----------
function tipDist(ext) { return 36 + ext * 110; }

function extension() {
  if (goose.peckT < 0) return 0;
  const p = goose.peckT / PECK_DUR;
  const e = p < 0.4 ? p / 0.4 : 1 - (p - 0.4) / 0.6;
  return Math.sin(clamp(e, 0, 1) * Math.PI / 2);
}

// 照準をガチョウ中心の円の内側に収める
function clampCursor() {
  const dx = cursor.x - W / 2, dy = cursor.y - H / 2, d = Math.hypot(dx, dy);
  if (d > CURSOR_RADIUS) {
    cursor.x = W / 2 + (dx / d) * CURSOR_RADIUS;
    cursor.y = H / 2 + (dy / d) * CURSOR_RADIUS;
  }
}

// マウス位置の方向を向く(画面は y が圧縮されているので戻して角度を出す)
function aimGoose() {
  const sdx = cursor.x - W / 2, sdy = cursor.y - H / 2;
  if (Math.hypot(sdx, sdy) > 4) goose.heading = Math.atan2(sdy / YS, sdx);
}

function updateGoose(dt) {
  aimGoose();

  const fx = Math.cos(goose.heading), fy = Math.sin(goose.heading);
  const lx = fy, ly = -fx;                                     // 左向きのベクトル
  const f = (keys.KeyW ? 1 : 0) - (keys.KeyS ? 0.7 : 0);       // 後退は少し遅い
  const s = ((keys.KeyA ? 1 : 0) - (keys.KeyD ? 1 : 0)) * 0.9;
  let vx = fx * f + lx * s, vy = fy * f + ly * s;
  const l = Math.hypot(vx, vy);
  if (l > 1) { vx /= l; vy /= l; }
  goose.moving = l > 0.05;
  goose.x += vx * GOOSE_SPEED * dt;
  goose.y += vy * GOOSE_SPEED * dt;
  collide(goose, 22);
  if (goose.moving) goose.walk += dt * 11;

  // つつき
  if (goose.peckT >= 0) {
    goose.peckT += dt;
    if (extension() >= 0.7) peckHit();
    if (goose.peckT >= PECK_DUR) { goose.peckT = -1; goose.gap = PECK_GAP; }
  } else {
    goose.gap = Math.max(0, goose.gap - dt);
    if (mouseDown && goose.gap <= 0) { goose.peckT = 0; goose.peckId++; sfx.swing(); }
  }
}

function peckHit() {
  const dist = tipDist(extension());
  const tx = goose.x + Math.cos(goose.heading) * dist;
  const ty = goose.y + Math.sin(goose.heading) * dist;
  const dead = [];
  for (const d of ducks) {
    if (d.peckId === goose.peckId) continue;
    if (Math.hypot(d.x - tx, d.y - ty) < 36 + d.r) {
      d.peckId = goose.peckId;
      d.hp--;
      d.flash = 0.15;
      if (d.hp > 0) sfx.hit(d.big);
      const a = Math.atan2(d.y - goose.y, d.x - goose.x);
      d.kx += Math.cos(a) * 360; d.ky += Math.sin(a) * 360;
      burst(d.x, d.y, d.big ? 8 : 5, d.big ? '#e0b060' : '#ffe27a');
      if (d.hp <= 0) dead.push(d);
    }
  }
  // 木や岩も壊せる(ポイントなし)
  for (let i = obstacles.length - 1; i >= 0; i--) {
    const o = obstacles[i];
    if (o.peckId === goose.peckId) continue;
    if (Math.hypot(o.x - tx, o.y - ty) < 36 + o.r) {
      o.peckId = goose.peckId;
      o.hp--;
      o.flash = 0.15;
      const chip = o.kind === 'tree' ? '#7a4f2a' : '#9aa0a6';
      if (o.hp <= 0) {
        sfx.crash(o.kind);
        burst(o.x, o.y, 22, chip);
        burst(o.x, o.y, o.kind === 'tree' ? 12 : 6, o.kind === 'tree' ? '#3a8f46' : '#ffffff');
        obstacles.splice(i, 1);
      } else {
        sfx.thud(o.kind);
        burst(o.x, o.y, 6, chip);
      }
    }
  }
  for (const d of dead) {
    ducks.splice(ducks.indexOf(d), 1);
    const pts = d.big ? 5 : 1;
    sfx.kill(d.big);
    score += pts; kills++; if (d.big) bigKills++;
    burst(d.x, d.y, d.big ? 24 : 14, '#ffffff');
    texts.push({ x: d.x, y: d.y, txt: `+${pts}`, life: 0.9, big: d.big });
    respawnOne();
  }
}

// ---------- 演出 ----------
function burst(x, y, n, color) {
  for (let i = 0; i < n; i++) {
    const a = rand(0, Math.PI * 2), sp = rand(60, 220);
    particles.push({ x, y, z: rand(8, 24), vx: Math.cos(a) * sp, vy: Math.sin(a) * sp, vz: rand(40, 160), life: rand(0.4, 0.8), color });
  }
}

function updateFx(dt) {
  for (const p of particles) {
    p.x += p.vx * dt; p.y += p.vy * dt; p.z += p.vz * dt; p.vz -= 400 * dt;
    p.vx *= 0.96; p.vy *= 0.96; p.life -= dt;
    if (p.z < 0) { p.z = 0; p.vz = 0; }
  }
  particles = particles.filter(p => p.life > 0);
  for (const o of obstacles) if (o.flash > 0) o.flash = Math.max(0, o.flash - dt);
  for (const t of texts) t.life -= dt;
  texts = texts.filter(t => t.life > 0);
}

// ---------- 描画 ----------
const px = x => W / 2 + (x - goose.x);
const py = y => H / 2 + (y - goose.y) * YS;

function ellipse(x, y, rx, ry, color) {
  ctx.fillStyle = color;
  ctx.beginPath(); ctx.ellipse(x, y, rx, ry, 0, 0, Math.PI * 2); ctx.fill();
}
function shadow(x, y, rx) { ellipse(x, y, rx, rx * 0.4, 'rgba(0,0,0,0.25)'); }

// つつかれた直後は左右に揺らす
const shake = o => (o.flash > 0 ? Math.sin(o.flash * 120) * 4 : 0);

function drawTree(sx, sy, o) {
  shadow(sx, sy, 34);
  sx += shake(o);
  ctx.fillStyle = '#6b4423'; ctx.fillRect(sx - 7, sy - 46, 14, 46);
  const k = 0.85 + o.v * 0.3;
  ellipse(sx, sy - 64, 40 * k, 34 * k, '#2d7438');
  ellipse(sx - 14, sy - 72, 26 * k, 22 * k, '#3a8f46');
  ellipse(sx + 12, sy - 82, 24 * k, 20 * k, '#48a554');
}

function drawRock(sx, sy, o) {
  shadow(sx, sy, 32);
  sx += shake(o);
  ellipse(sx, sy - 10, 27, 20, '#7d8288');
  ellipse(sx - 6, sy - 15, 17, 11, '#9aa0a6');
}

function drawFence(sx, sy, f) {
  const nx = px(f.nx), ny = py(f.ny);
  ctx.strokeStyle = '#8a5a2b'; ctx.lineWidth = 3;
  ctx.beginPath();
  ctx.moveTo(sx, sy - 6); ctx.lineTo(nx, ny - 6);
  ctx.moveTo(sx, sy - 20); ctx.lineTo(nx, ny - 20);
  ctx.stroke();
  ctx.lineWidth = 5;
  ctx.beginPath(); ctx.moveTo(sx, sy); ctx.lineTo(sx, sy - 26); ctx.stroke();
}

function drawDuck(sx, sy, d) {
  const k = d.big ? 1.9 : 1;
  const bob = d.moving ? Math.abs(Math.sin(clock * (d.fleeing ? 16 : 8) + d.phase)) * 3 : 0;
  const fx = Math.cos(d.heading), fy = Math.sin(d.heading) * YS;
  const bx = sx, by = sy - (11 + bob) * k;
  const body = d.flash > 0 ? (d.big ? '#ffd0c8' : '#ffffff') : (d.big ? '#fbfbf6' : '#ffd84a');
  const wing = d.flash > 0 ? '#eeeeee' : (d.big ? '#dfe3dc' : '#f0b92a');
  const headFirst = fy < 0;       // 奥を向いているときは頭を先に描く(体で隠れる)

  shadow(sx, sy, 17 * k);
  // 水かき
  ellipse(sx - 5 * k, sy - 1, 4 * k, 2 * k, '#f08a1c');
  ellipse(sx + 5 * k, sy - 1, 4 * k, 2 * k, '#f08a1c');

  const hx = bx + fx * 13 * k, hy = by + fy * 9 * k - 10 * k;
  const drawHead = () => {
    ellipse(hx, hy, 8 * k, 8 * k, body);
    ellipse(hx + fx * 8 * k, hy + fy * 5 * k + 1.5 * k, 5 * k, 2.8 * k, '#f08a1c');
    if (fy >= -0.3) {
      ellipse(hx + fx * 3 * k - 3.5 * k, hy - 2 * k, 1.4 * k, 1.4 * k, '#222');
      ellipse(hx + fx * 3 * k + 3.5 * k, hy - 2 * k, 1.4 * k, 1.4 * k, '#222');
    }
  };
  if (headFirst) drawHead();
  ellipse(bx, by, 16 * k, 12 * k, body);
  ellipse(bx - fx * 14 * k, by - fy * 6 * k - 3 * k, 6 * k, 4 * k, body);   // 尾
  ellipse(bx - fx * 2 * k, by - 1 * k, 9 * k, 6 * k, wing);
  if (!headFirst) drawHead();

  if (d.big && d.hp < d.maxHp) {
    const w = 46, x = sx - w / 2, y = sy - 62;
    ctx.fillStyle = 'rgba(0,0,0,0.5)'; ctx.fillRect(x - 1, y - 1, w + 2, 7);
    ctx.fillStyle = '#e8453c'; ctx.fillRect(x, y, w * d.hp / d.maxHp, 5);
  }
}

function drawGoose(sx, sy) {
  const fx = Math.cos(goose.heading), fy = Math.sin(goose.heading) * YS;
  const ext = extension();
  const bob = goose.moving ? Math.abs(Math.sin(goose.walk)) * 3 : 0;
  const bx = sx, by = sy - 20 - bob;
  const away = fy < 0;           // 奥向き(画面上向き)のときは首を体の後ろに描く

  shadow(sx, sy, 34);
  ellipse(sx - 9, sy - 1, 6, 3, '#f08a1c');
  ellipse(sx + 9, sy - 1, 6, 3, '#f08a1c');

  // 頭の位置: 休んでいるときは首を立て、つつくときは前へ伸ばす
  const dist = tipDist(ext);
  const hx = sx + fx * dist;
  const hy = sy + fy * dist - (36 - 24 * ext);
  const nbx = bx + fx * 14, nby = by - 6;               // 首の付け根

  const drawNeckHead = () => {
    const cx = (nbx + hx) / 2, cy = Math.min(nby, hy) - 22 * (1 - ext);
    ctx.lineCap = 'round';
    ctx.strokeStyle = '#9aa3a8'; ctx.lineWidth = 13;
    ctx.beginPath(); ctx.moveTo(nbx, nby); ctx.quadraticCurveTo(cx, cy, hx, hy); ctx.stroke();
    ctx.strokeStyle = '#ffffff'; ctx.lineWidth = 9;
    ctx.beginPath(); ctx.moveTo(nbx, nby); ctx.quadraticCurveTo(cx, cy, hx, hy); ctx.stroke();
    ellipse(hx, hy, 9, 9, '#ffffff');
    // くちばし
    ctx.fillStyle = '#f08a1c';
    ctx.beginPath();
    ctx.ellipse(hx + fx * 11, hy + fy * 7 + 1, 8, 4.2, Math.atan2(fy, fx), 0, Math.PI * 2);
    ctx.fill();
    if (!away) { ellipse(hx - 3.5, hy - 2.5, 1.8, 1.8, '#111'); ellipse(hx + 3.5, hy - 2.5, 1.8, 1.8, '#111'); }
  };

  if (away) drawNeckHead();
  ellipse(bx, by, 27, 18, '#e8ecee');
  ellipse(bx, by - 2, 25, 16, '#ffffff');
  ellipse(bx - fx * 24, by - fy * 10 - 2, 10, 6, '#f1f3f4');             // 尾
  ellipse(bx - fx * 3, by - 2, 16, 10, '#e3e8ea');                      // 翼
  if (!away) drawNeckHead();
}

function drawField() {
  const cx = goose.x, cy = goose.y;
  ctx.fillStyle = '#1f3320';
  ctx.fillRect(0, 0, W, H);

  // 地面(市松模様)
  const halfH = H / (2 * YS);
  const maxT = WORLD / TILE - 1;
  const x0 = Math.max(0, Math.floor((cx - W / 2) / TILE)), x1 = Math.min(maxT, Math.floor((cx + W / 2) / TILE));
  const y0 = Math.max(0, Math.floor((cy - halfH) / TILE)), y1 = Math.min(maxT, Math.floor((cy + halfH) / TILE));
  for (let ty = y0; ty <= y1; ty++) {
    for (let tx = x0; tx <= x1; tx++) {
      const shade = (tx * 7 + ty * 13) % 3;
      ctx.fillStyle = ((tx + ty) & 1) ? ['#6fae4e', '#72b151', '#6cab4b'][shade] : ['#68a648', '#6ba94b', '#65a345'][shade];
      ctx.fillRect(px(tx * TILE), py(ty * TILE), TILE + 1, TILE * YS + 1);
    }
  }

  // 草むら
  ctx.strokeStyle = '#4b8a38'; ctx.lineWidth = 2;
  for (const t of tufts) {
    const sx = px(t.x), sy = py(t.y);
    if (sx < -20 || sx > W + 20 || sy < -20 || sy > H + 20) continue;
    ctx.beginPath();
    ctx.moveTo(sx - 5, sy); ctx.lineTo(sx - 7, sy - 9 - t.v * 4);
    ctx.moveTo(sx, sy); ctx.lineTo(sx, sy - 12 - t.v * 5);
    ctx.moveTo(sx + 5, sy); ctx.lineTo(sx + 7, sy - 9 - t.v * 4);
    ctx.stroke();
  }

  // 手前・奥の前後関係を y座標順で表現(画家のアルゴリズム)
  const items = [];
  const vis = (sx, sy) => sx > -110 && sx < W + 110 && sy > -130 && sy < H + 110;
  for (const o of obstacles) {
    const sx = px(o.x), sy = py(o.y);
    if (vis(sx, sy)) items.push({ y: o.y, f: o.kind === 'tree' ? () => drawTree(sx, sy, o) : () => drawRock(sx, sy, o) });
  }
  for (const f of fence) {
    const sx = px(f.x), sy = py(f.y);
    if (vis(sx, sy)) items.push({ y: f.y, f: () => drawFence(sx, sy, f) });
  }
  for (const d of ducks) {
    const sx = px(d.x), sy = py(d.y);
    if (vis(sx, sy)) items.push({ y: d.y, f: () => drawDuck(sx, sy, d) });
  }
  items.push({ y: goose.y, f: () => drawGoose(W / 2, H / 2) });
  items.sort((a, b) => a.y - b.y);
  for (const it of items) it.f();

  // 羽根のパーティクル・得点表示
  for (const p of particles) {
    ctx.globalAlpha = clamp(p.life * 2, 0, 1);
    ellipse(px(p.x), py(p.y) - p.z, 3, 2, p.color);
  }
  ctx.globalAlpha = 1;
  ctx.textAlign = 'center';
  for (const t of texts) {
    ctx.globalAlpha = clamp(t.life * 2, 0, 1);
    ctx.font = `bold ${t.big ? 34 : 24}px "Segoe UI","Yu Gothic UI",sans-serif`;
    const y = py(t.y) - 40 - (0.9 - t.life) * 50;
    ctx.lineWidth = 4; ctx.strokeStyle = '#3b2a00'; ctx.strokeText(t.txt, px(t.x), y);
    ctx.fillStyle = '#ffd84a'; ctx.fillText(t.txt, px(t.x), y);
  }
  ctx.globalAlpha = 1;

  drawHud();
  if (state === 'PLAY') drawCursor();
}

// 開始前のカウントダウン(3, 2, 1)と、開始直後の「スタート!」
function drawCountdown() {
  let label, f, color;
  if (countdown > 0) {
    const e = COUNT_STEP * COUNT_FROM - countdown;                 // 経過時間
    const step = Math.min(COUNT_FROM - 1, Math.floor(e / COUNT_STEP));
    label = String(COUNT_FROM - step);
    f = (e - step * COUNT_STEP) / COUNT_STEP;                      // この数字の中での進み具合 0→1
    color = '#ffffff';
    ctx.fillStyle = 'rgba(8, 20, 12, 0.25)';
    ctx.fillRect(0, 0, W, H);
  } else if (goFlash > 0) {
    label = 'スタート!';
    f = 1 - goFlash / GO_FLASH;
    color = '#ffd84a';
  } else return;
  const scale = 1 + 0.6 * (1 - f) * (1 - f);                       // ポンと大きく出て縮む
  ctx.save();
  ctx.translate(W / 2, H / 2 - 120);
  ctx.scale(scale, scale);
  ctx.globalAlpha = countdown > 0 ? 1 : clamp((1 - f) * 2.5, 0, 1);
  ctx.textAlign = 'center';
  ctx.font = `bold ${countdown > 0 ? 150 : 96}px "Segoe UI","Yu Gothic UI",sans-serif`;
  ctx.lineJoin = 'round'; ctx.lineWidth = 14; ctx.strokeStyle = '#2b4a2e';
  ctx.strokeText(label, 0, 40);
  ctx.fillStyle = color; ctx.fillText(label, 0, 40);
  ctx.restore();
}

// 終了時: フィールドを暗くして得点を表示
function drawResult() {
  ctx.fillStyle = 'rgba(8, 20, 12, 0.72)';
  ctx.fillRect(0, 0, W, H);
  ctx.textAlign = 'center';
  const font = px => `bold ${px}px "Segoe UI","Yu Gothic UI",sans-serif`;
  const text = (t, y, size, color, stroke) => {
    ctx.font = font(size);
    if (stroke) { ctx.lineWidth = 8; ctx.strokeStyle = stroke; ctx.lineJoin = 'round'; ctx.strokeText(t, W / 2, y); }
    ctx.fillStyle = color; ctx.fillText(t, W / 2, y);
  };
  text('TIME UP!', 190, 64, '#ffffff', '#2b6a2f');
  text(`${result.name} の得点`, 260, 26, '#c9d8cd');
  text(`${result.score} アヒル`, 350, 88, '#ffd84a', '#5a3a00');
  if (result.isRecord) {
    const pulse = 1 + Math.sin(resultT * 8) * 0.06;
    ctx.save();
    ctx.translate(W / 2, 430); ctx.scale(pulse, pulse); ctx.translate(-W / 2, -430);
    text('最高得点更新!!', 430, 52, '#ff6a5a', '#ffffff');
    ctx.restore();
  }
  if (resultT > 0.6) {
    ctx.globalAlpha = 0.6 + 0.4 * Math.sin(resultT * 4);
    text('スペースキーを押すとスタート画面に戻ります', 560, 26, '#ffffff');
    ctx.globalAlpha = 1;
  }
}

function drawHud() {
  if (muted) {                                       // ミュート中は左上に小さく表示
    ctx.textAlign = 'left';
    ctx.font = '14px "Segoe UI","Yu Gothic UI",sans-serif';
    ctx.fillStyle = 'rgba(0,0,0,0.5)'; ctx.fillRect(12, 12, 118, 26);
    ctx.fillStyle = '#ffffff'; ctx.fillText('効果音 OFF (M)', 20, 31);
  }
  const sec = Math.max(0, Math.ceil(timeLeft));
  ctx.fillStyle = 'rgba(0,0,0,0.5)';
  ctx.beginPath(); ctx.roundRect(W - 168, 12, 156, 54, 10); ctx.fill();
  ctx.textAlign = 'right';
  ctx.font = '14px "Segoe UI","Yu Gothic UI",sans-serif';
  ctx.fillStyle = '#c9d8cd'; ctx.fillText('残り時間', W - 112, 44);
  ctx.font = 'bold 36px "Segoe UI","Yu Gothic UI",sans-serif';
  ctx.fillStyle = sec <= 10 ? '#ff6a5a' : '#ffffff';
  ctx.fillText(String(sec), W - 22, 52);
}

function drawCursor() {
  const { x, y } = cursor;
  // 照準の可動範囲をうっすら表示
  ctx.save();
  ctx.strokeStyle = 'rgba(255,255,255,0.28)'; ctx.lineWidth = 2; ctx.setLineDash([8, 10]);
  ctx.beginPath(); ctx.arc(W / 2, H / 2, CURSOR_RADIUS, 0, Math.PI * 2); ctx.stroke();
  ctx.restore();
  ctx.strokeStyle = '#ff3b30'; ctx.lineWidth = 2.5;
  ctx.beginPath(); ctx.arc(x, y, 11, 0, Math.PI * 2); ctx.stroke();
  ctx.beginPath();
  ctx.moveTo(x - 17, y); ctx.lineTo(x - 6, y);
  ctx.moveTo(x + 6, y); ctx.lineTo(x + 17, y);
  ctx.moveTo(x, y - 17); ctx.lineTo(x, y - 6);
  ctx.moveTo(x, y + 6); ctx.lineTo(x, y + 17);
  ctx.stroke();
}

function drawRadar() {
  const c = radar.width / 2, R = c - 6, sc = R / RADAR_RANGE;
  rctx.clearRect(0, 0, radar.width, radar.height);
  rctx.fillStyle = 'rgba(12,40,24,0.92)';
  rctx.beginPath(); rctx.arc(c, c, R, 0, Math.PI * 2); rctx.fill();
  rctx.strokeStyle = 'rgba(120,220,150,0.35)'; rctx.lineWidth = 1;
  for (const f of [0.33, 0.66, 1]) { rctx.beginPath(); rctx.arc(c, c, R * f, 0, Math.PI * 2); rctx.stroke(); }
  rctx.beginPath(); rctx.moveTo(c - R, c); rctx.lineTo(c + R, c); rctx.moveTo(c, c - R); rctx.lineTo(c, c + R); rctx.stroke();
  rctx.strokeStyle = 'rgba(255,255,255,0.35)';                                  // いま見えている範囲
  rctx.strokeRect(c - (W / 2) * sc, c - (H / (2 * YS)) * sc, W * sc, (H / YS) * sc);

  rctx.save();
  rctx.beginPath(); rctx.arc(c, c, R, 0, Math.PI * 2); rctx.clip();
  for (const d of ducks) {
    const rx = c + (d.x - goose.x) * sc, ry = c + (d.y - goose.y) * sc;
    rctx.fillStyle = d.big ? '#ff5a4a' : '#ffd84a';
    rctx.beginPath(); rctx.arc(rx, ry, d.big ? 6 : 3.5, 0, Math.PI * 2); rctx.fill();
  }
  rctx.restore();

  rctx.save();                                                                   // ガチョウ(向き付き)
  rctx.translate(c, c); rctx.rotate(goose.heading);
  rctx.fillStyle = '#ffffff';
  rctx.beginPath(); rctx.moveTo(9, 0); rctx.lineTo(-6, -6); rctx.lineTo(-6, 6); rctx.closePath(); rctx.fill();
  rctx.restore();
  rctx.strokeStyle = '#3d5a49'; rctx.lineWidth = 3;
  rctx.beginPath(); rctx.arc(c, c, R, 0, Math.PI * 2); rctx.stroke();
}

let lastScore = -1;
function updatePanel() {
  if (score === lastScore) return;
  lastScore = score;
  pScore.textContent = String(score);
  pKills.textContent = `通常 ${kills - bigKills} 羽 / 大アヒル ${bigKills} 羽`;
}

// ---------- 状態遷移 ----------
function startGame() {
  if (state !== 'START') return;
  const name = nameInput.value.trim() || DEFAULT_NAME;
  nameInput.value = name;
  saveJSON(STORE_NAME, name);

  buildWorld();
  goose = { x: WORLD / 2, y: WORLD / 2, heading: 0, moving: false, walk: 0, peckT: -1, gap: 0, peckId: 0, name };
  ducks = []; particles = []; texts = [];
  spawnCount = 0; nextGroup = 1; score = 0; kills = 0; bigKills = 0; lastScore = -1;
  timeLeft = GAME_TIME; clock = 0; mouseDown = false;
  cursor.x = W / 2 + 120; cursor.y = H / 2;
  countdown = COUNT_STEP * COUNT_FROM; goFlash = 0; lastCountStep = -1;
  initAudio();
  for (const k in keys) keys[k] = false;
  spawnInitialDucks();

  pName.textContent = name;
  updatePanel();
  startEl.hidden = true;
  startBtn.blur(); nameInput.blur();
  state = 'PLAY';
  document.body.classList.add('playing');

  // マウスカーソルをフィールド内に閉じ込める(ポインターロック)。使えない環境では通常のマウス座標で代用
  try {
    const p = canvas.requestPointerLock();
    if (p && p.catch) p.catch(() => {});
  } catch (e) { /* 代用モードで続行 */ }
}

function releaseInput() {
  hadLock = false;
  mouseDown = false;
  for (const k in keys) keys[k] = false;
  document.body.classList.remove('playing');
  if (document.pointerLockElement) document.exitPointerLock();
}

// ESC による途中終了: 記録は残さずスタート画面へ
function abortGame() {
  if (state !== 'PLAY') return;
  state = 'START';
  releaseInput();
  showBest();
  startEl.hidden = false;
}

// 時間切れ: 操作を止めて、フィールド上に得点を表示する(スペースでスタート画面へ)
function finishGame() {
  if (state !== 'PLAY') return;
  state = 'RESULT';
  releaseInput();
  goose.moving = false;
  goose.peckT = -1;
  const best = loadJSON(STORE_BEST);
  const isRecord = score > 0 && (!best || score > best.score);
  if (isRecord) saveJSON(STORE_BEST, { name: goose.name, score });
  result = { name: goose.name, score, isRecord };
  resultT = 0;
  sfx.timeUp();
  if (isRecord) sfx.record();
  shareBtn.hidden = false;
  showBest();
}

// X(旧Twitter)の投稿画面を新しいタブで開く。自動投稿はしない(最終的に投稿するかは本人が決める)
function shareText() {
  const lines = [
    `『${GAME_TITLE}』で ${result.name} が ${result.score} アヒルを駆逐!` + (result.isRecord ? ' 最高得点更新!!' : ''),
    SHARE_URL,
    HASHTAG,
  ];
  return lines.join('\n');
}

function shareResult() {
  if (state !== 'RESULT' || !result) return;
  const url = 'https://x.com/intent/post?text=' + encodeURIComponent(shareText());
  window.open(url, '_blank', 'noopener');
  shareBtn.blur();
}

function backToStart() {
  if (state !== 'RESULT') return;
  state = 'START';
  shareBtn.hidden = true;
  startEl.hidden = false;
}

// ---------- 入力 ----------
window.addEventListener('keydown', e => {
  // M キーで効果音のオン/オフ(名前入力中は文字として扱う)
  if (e.code === 'KeyM' && e.target !== nameInput && !e.repeat) {
    muted = !muted;
    saveJSON(STORE_MUTE, muted);
    updateMuteLabel();
    return;
  }
  if (state === 'RESULT') {
    if (e.code === 'KeyX' && !e.repeat) { shareResult(); return; }
    if (e.code === 'Space') { e.preventDefault(); if (resultT > 0.6 && !e.repeat) backToStart(); }
    return;                                           // 終了中はWASDなどを受け付けない
  }
  if (state === 'START') {
    if (e.target === nameInput) {
      if (e.code === 'Enter') nameInput.blur();     // 入力を確定
      return;
    }
    if (e.code === 'Space') { e.preventDefault(); startGame(); }
    return;
  }
  if (e.code === 'Escape') { abortGame(); return; }
  if (['KeyW', 'KeyA', 'KeyS', 'KeyD', 'Space'].includes(e.code)) e.preventDefault();
  keys[e.code] = true;
});
window.addEventListener('keyup', e => { keys[e.code] = false; });
window.addEventListener('blur', () => { for (const k in keys) keys[k] = false; mouseDown = false; });

window.addEventListener('mousemove', e => {
  if (state !== 'PLAY') return;
  const scale = fitScale || 1;
  if (document.pointerLockElement === canvas) {
    cursor.x += e.movementX / scale;
    cursor.y += e.movementY / scale;
  } else {
    const r = canvas.getBoundingClientRect();
    cursor.x = (e.clientX - r.left) / r.width * W;
    cursor.y = (e.clientY - r.top) / r.height * H;
  }
  clampCursor();
});
window.addEventListener('mousedown', e => {
  if (state !== 'PLAY' || e.button !== 0) return;
  mouseDown = true;
  e.preventDefault();
  // スペース押下時のロックに失敗していた場合、クリックで取り直す
  if (!document.pointerLockElement) {
    try { const p = canvas.requestPointerLock(); if (p && p.catch) p.catch(() => {}); } catch (err) { /* 代用モード */ }
  }
});
window.addEventListener('mouseup', e => { if (e.button === 0) mouseDown = false; });

// ポインターロックは ESC で解除されるので、ロック喪失=途中終了として扱う
document.addEventListener('pointerlockchange', () => {
  if (document.pointerLockElement === canvas) hadLock = true;
  else if (state === 'PLAY' && hadLock) abortGame();
});

startBtn.addEventListener('click', startGame);
shareBtn.addEventListener('click', shareResult);
nameInput.addEventListener('input', () => saveJSON(STORE_NAME, nameInput.value));

// ---------- 画面フィット(小さい画面では縮小して中央配置) ----------
let fitScale = 1;
function fit() {
  fitScale = Math.min(1, window.innerWidth / 1060, window.innerHeight / 720);
  wrap.style.transform = `scale(${fitScale})`;
  wrap.style.left = Math.max(0, (window.innerWidth - 1060 * fitScale) / 2) + 'px';
  wrap.style.top = Math.max(0, (window.innerHeight - 720 * fitScale) / 2) + 'px';
}
window.addEventListener('resize', fit);

// ---------- メインループ ----------
let lastTs = 0;
function loop(ts) {
  const dt = Math.min(0.05, (ts - lastTs) / 1000 || 0);
  lastTs = ts;
  if (state === 'PLAY' && countdown > 0) {
    // カウントダウン中: 時間も移動もつつきも止めて、向きだけ変えられる
    countdown -= dt;
    clock += dt;
    mouseDown = false;
    aimGoose();
    const step = Math.min(COUNT_FROM - 1, Math.floor((COUNT_STEP * COUNT_FROM - countdown) / COUNT_STEP));
    if (step !== lastCountStep) { lastCountStep = step; sfx.tick(); }
    drawField();
    drawCountdown();
    drawRadar();
    if (countdown <= 0) { countdown = 0; goFlash = GO_FLASH; sfx.go(); }
  } else if (state === 'PLAY') {
    clock += dt;
    timeLeft -= dt;
    goFlash = Math.max(0, goFlash - dt);
    updateGoose(dt);
    updateDucks(dt);
    updateFx(dt);
    drawField();
    drawCountdown();
    drawRadar();
    updatePanel();
    if (timeLeft <= 0) { timeLeft = 0; finishGame(); }
  } else if (state === 'RESULT') {
    resultT += dt;
    clock += dt;
    updateDucks(dt);
    updateFx(dt);
    drawField();
    drawResult();
    drawRadar();
  }
  requestAnimationFrame(loop);
}

function updateMuteLabel() {
  muteText.textContent = muted ? 'OFF' : 'ON';
}

// ---------- 起動 ----------
updateMuteLabel();
nameInput.value = loadJSON(STORE_NAME) || DEFAULT_NAME;
showBest();
fit();
requestAnimationFrame(loop);
