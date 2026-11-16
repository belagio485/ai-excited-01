// ai-excited-01: "Escape Velocity"
// A paper plane bursting away from a blazing black hole, drawn procedurally
// with the Node standard library only. Deterministic: same bytes every run.
const fs = require("node:fs");
const path = require("node:path");
const zlib = require("node:zlib");
const crypto = require("node:crypto");

const W = 1024;
const H = 1024;
const fb = new Float32Array(W * H * 3);

// Deterministic PRNG (mulberry32).
function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function clamp(v, lo, hi) {
  return v < lo ? lo : v > hi ? hi : v;
}
function lerp(a, b, t) {
  return a + (b - a) * t;
}
function smoothstep(a, b, x) {
  const t = clamp((x - a) / (b - a), 0, 1);
  return t * t * (3 - 2 * t);
}

// Additive glow stamp with a gaussian profile.
function stamp(cx, cy, sigma, r, g, b, peak) {
  const rad = Math.ceil(sigma * 3.2);
  const x0 = Math.max(0, Math.floor(cx - rad));
  const x1 = Math.min(W - 1, Math.ceil(cx + rad));
  const y0 = Math.max(0, Math.floor(cy - rad));
  const y1 = Math.min(H - 1, Math.ceil(cy + rad));
  const inv = 1 / (2 * sigma * sigma);
  for (let y = y0; y <= y1; y++) {
    const dy = y - cy;
    let idx = (y * W + x0) * 3;
    for (let x = x0; x <= x1; x++) {
      const dx = x - cx;
      const p = peak * Math.exp(-(dx * dx + dy * dy) * inv);
      fb[idx] += r * p;
      fb[idx + 1] += g * p;
      fb[idx + 2] += b * p;
      idx += 3;
    }
  }
}

// Anti-aliased line segment. Alpha fades along its length when fade > 0.
function drawLine(x0, y0, x1, y1, halfW, r, g, b, alpha, fade, additive) {
  const pad = halfW + 2;
  const minX = Math.max(0, Math.floor(Math.min(x0, x1) - pad));
  const maxX = Math.min(W - 1, Math.ceil(Math.max(x0, x1) + pad));
  const minY = Math.max(0, Math.floor(Math.min(y0, y1) - pad));
  const maxY = Math.min(H - 1, Math.ceil(Math.max(y0, y1) + pad));
  const vx = x1 - x0;
  const vy = y1 - y0;
  const len2 = vx * vx + vy * vy;
  const len = Math.sqrt(len2);
  for (let y = minY; y <= maxY; y++) {
    for (let x = minX; x <= maxX; x++) {
      const px = x + 0.5;
      const py = y + 0.5;
      let t = len2 === 0 ? 0 : ((px - x0) * vx + (py - y0) * vy) / len2;
      t = clamp(t, 0, 1);
      const qx = x0 + t * vx;
      const qy = y0 + t * vy;
      const d = Math.hypot(px - qx, py - qy);
      const cov = clamp((halfW - d) / 1.2 + 0.5, 0, 1);
      if (cov <= 0) continue;
      let a = alpha * cov;
      if (fade > 0) a *= Math.pow(1 - t, fade);
      const idx = (y * W + x) * 3;
      if (additive) {
        fb[idx] += r * a;
        fb[idx + 1] += g * a;
        fb[idx + 2] += b * a;
      } else {
        fb[idx] = fb[idx] * (1 - a) + r * a;
        fb[idx + 1] = fb[idx + 1] * (1 - a) + g * a;
        fb[idx + 2] = fb[idx + 2] * (1 - a) + b * a;
      }
    }
  }
}

// Filled triangle with per-vertex colours and anti-aliased edges (opaque).
function fillTri(ax, ay, bx, by, cx, cy, cA, cB, cC) {
  let area = (bx - ax) * (cy - ay) - (by - ay) * (cx - ax);
  if (area === 0) return;
  if (area < 0) {
    const tx = bx; const ty = by;
    bx = cx; by = cy; cx = tx; cy = ty;
    const tc = cB; cB = cC; cC = tc;
    area = -area;
  }
  const minX = Math.max(0, Math.floor(Math.min(ax, bx, cx) - 2));
  const maxX = Math.min(W - 1, Math.ceil(Math.max(ax, bx, cx) + 2));
  const minY = Math.max(0, Math.floor(Math.min(ay, by, cy) - 2));
  const maxY = Math.min(H - 1, Math.ceil(Math.max(ay, by, cy) + 2));
  const lenAB = Math.hypot(bx - ax, by - ay) || 1;
  const lenBC = Math.hypot(cx - bx, cy - by) || 1;
  const lenCA = Math.hypot(ax - cx, ay - cy) || 1;
  for (let y = minY; y <= maxY; y++) {
    for (let x = minX; x <= maxX; x++) {
      const px = x + 0.5;
      const py = y + 0.5;
      const e0 = (bx - ax) * (py - ay) - (by - ay) * (px - ax);
      const e1 = (cx - bx) * (py - by) - (cy - by) * (px - bx);
      const e2 = (ax - cx) * (py - cy) - (ay - cy) * (px - cx);
      const d0 = e0 / lenAB;
      const d1 = e1 / lenBC;
      const d2 = e2 / lenCA;
      const md = Math.min(d0, d1, d2);
      if (md < -1.6) continue;
      const cov = clamp(md / 1.4 + 0.5, 0, 1);
      if (cov <= 0) continue;
      const wC = e0 / area;
      const wA = e1 / area;
      const wB = e2 / area;
      const cr = wA * cA[0] + wB * cB[0] + wC * cC[0];
      const cg = wA * cA[1] + wB * cB[1] + wC * cC[1];
      const cb = wA * cA[2] + wB * cB[2] + wC * cC[2];
      const idx = (y * W + x) * 3;
      fb[idx] = fb[idx] * (1 - cov) + cr * cov;
      fb[idx + 1] = fb[idx + 1] * (1 - cov) + cg * cov;
      fb[idx + 2] = fb[idx + 2] * (1 - cov) + cb * cov;
    }
  }
}

// ---------------------------------------------------------------------------
// 1. Deep-space background: vertical gradient plus a faint lift near the hole.
// ---------------------------------------------------------------------------
function paintBackground() {
  const hx = 290;
  const hy = 285;
  for (let y = 0; y < H; y++) {
    const t = y / (H - 1);
    const baseR = lerp(0.008, 0.014, t);
    const baseG = lerp(0.008, 0.01, t);
    const baseB = lerp(0.022, 0.032, t);
    const dy = y - hy;
    let idx = y * W * 3;
    for (let x = 0; x < W; x++) {
      const dx = x - hx;
      const d2 = dx * dx + dy * dy;
      const lift = Math.exp(-d2 / (2 * 520 * 520));
      fb[idx] = baseR + 0.03 * lift;
      fb[idx + 1] = baseG + 0.016 * lift;
      fb[idx + 2] = baseB + 0.007 * lift;
      idx += 3;
    }
  }
  // Nebula blobs: large, soft, dim.
  const blobs = [
    [200, 180, 190, 0.16, 0.08, 0.30, 0.38],
    [830, 220, 170, 0.04, 0.20, 0.26, 0.34],
    [850, 850, 195, 0.22, 0.05, 0.20, 0.32],
    [150, 850, 160, 0.05, 0.10, 0.28, 0.34],
  ];
  for (const [bx, by, sig, r, g, b, a] of blobs) {
    stamp(bx, by, sig, r, g, b, a);
  }
}

// ---------------------------------------------------------------------------
// 2. Stars, a few with diffraction spikes.
// ---------------------------------------------------------------------------
function paintStars() {
  const rnd = mulberry32(0x5eed5eed);
  const spikes = [];
  for (let i = 0; i < 380; i++) {
    const x = rnd() * W;
    const y = rnd() * H;
    const bright = Math.pow(rnd(), 3) * 1.0 + 0.05;
    const kind = rnd();
    let r = 1.0;
    let g = 1.0;
    let b = 1.0;
    if (kind < 0.15) {
      r = 0.75; g = 0.85; b = 1.0;
    } else if (kind < 0.22) {
      r = 1.0; g = 0.85; b = 0.65;
    }
    const halo = 0.9 + Math.pow(rnd(), 4) * 2.4;
    stamp(x, y, halo, r, g, b, bright * 0.55);
    stamp(x, y, 0.55, r, g, b, bright * 1.15);
    if (bright > 0.85) spikes.push([x, y, bright, r, g, b]);
  }
  spikes.sort((a, b) => b[2] - a[2]);
  for (const [x, y, bright, r, g, b] of spikes.slice(0, 5)) {
    const len = 8 + bright * 14;
    const a = 0.3 * bright;
    drawLine(x - len, y, x + len, y, 0.8, r, g, b, a, 0, true);
    drawLine(x, y - len, x, y + len, 0.8, r, g, b, a, 0, true);
    drawLine(x - len * 0.45, y - len * 0.45, x + len * 0.45, y + len * 0.45, 0.6, r, g, b, a * 0.6, 0, true);
    drawLine(x - len * 0.45, y + len * 0.45, x + len * 0.45, y - len * 0.45, 0.6, r, g, b, a * 0.6, 0, true);
  }
}

// ---------------------------------------------------------------------------
// 3. The black hole: glow, tilted accretion ring, shadow, photon ring,
//    near-side ring pass, and the lensed arc over the top.
// ---------------------------------------------------------------------------
const HOLE = { x: 290, y: 285, horizon: 105 };
const TILT = (22 * Math.PI) / 180;
const SQUASH = 0.55;
const R_IN = 130;
const R_OUT = 330;

function ringField(x, y) {
  // Returns [brightness, r, angle] of the accretion ring at a pixel, or null.
  const dx = x - HOLE.x;
  const dy = y - HOLE.y;
  const cosT = Math.cos(TILT);
  const sinT = Math.sin(TILT);
  const xp = dx * cosT + dy * sinT;
  const yp = -dx * sinT + dy * cosT;
  const u = xp;
  const v = yp / SQUASH;
  const r = Math.hypot(u, v);
  if (r < R_IN - 16 || r > R_OUT + 14) return null;
  const ang = Math.atan2(v, u);
  let prof = Math.pow(R_IN / Math.max(r, R_IN), 2.6);
  prof *= smoothstep(R_IN - 14, R_IN + 8, r);
  prof *= 1 - smoothstep(R_OUT - 40, R_OUT + 12, r);
  // Doppler beaming: the side swinging toward us burns brighter.
  prof *= 1 + 0.5 * Math.cos(ang - 2.6);
  // Bright knots riding the ring.
  const knots = [
    [2.55, 175, 0.6],
    [0.5, 240, 0.55],
    [-1.9, 200, 0.6],
  ];
  for (const [ka, kr, kw] of knots) {
    let da = ang - ka;
    da = Math.atan2(Math.sin(da), Math.cos(da));
    const dr = (r - kr) / 30;
    prof += kw * Math.exp(-(da * da) / (2 * 0.36 * 0.36) - dr * dr);
  }
  return [prof, r, yp];
}

function ringColor(r) {
  const t = clamp((r - R_IN) / (R_OUT - R_IN), 0, 1);
  if (t < 0.35) {
    const k = t / 0.35;
    return [lerp(1.0, 1.0, k), lerp(0.95, 0.62, k), lerp(0.85, 0.22, k)];
  }
  const k = (t - 0.35) / 0.65;
  return [lerp(1.0, 0.72, k), lerp(0.62, 0.18, k), lerp(0.22, 0.06, k)];
}

function paintRingPass(nearOnly) {
  const pad = R_OUT + 30;
  const x0 = Math.max(0, Math.floor(HOLE.x - pad));
  const x1 = Math.min(W - 1, Math.ceil(HOLE.x + pad));
  const y0 = Math.max(0, Math.floor(HOLE.y - pad));
  const y1 = Math.min(H - 1, Math.ceil(HOLE.y + pad));
  for (let y = y0; y <= y1; y++) {
    for (let x = x0; x <= x1; x++) {
      const f = ringField(x + 0.5, y + 0.5);
      if (!f) continue;
      const [prof, r, yp] = f;
      if (nearOnly && yp <= 0) continue;
      if (prof <= 0) continue;
      const [cr, cg, cb] = ringColor(r);
      const idx = (y * W + x) * 3;
      const p = prof * 1.6;
      fb[idx] += cr * p;
      fb[idx + 1] += cg * p;
      fb[idx + 2] += cb * p;
    }
  }
}

function paintBlackHole() {
  // Wide glow.
  stamp(HOLE.x, HOLE.y, 200, 1.0, 0.45, 0.15, 0.35);
  stamp(HOLE.x, HOLE.y, 380, 0.6, 0.25, 0.1, 0.07);
  // Far side of the ring, then the shadow over it.
  paintRingPass(false);
  const rh = HOLE.horizon;
  const x0 = Math.max(0, Math.floor(HOLE.x - rh - 4));
  const x1 = Math.min(W - 1, Math.ceil(HOLE.x + rh + 4));
  const y0 = Math.max(0, Math.floor(HOLE.y - rh - 4));
  const y1 = Math.min(H - 1, Math.ceil(HOLE.y + rh + 4));
  for (let y = y0; y <= y1; y++) {
    for (let x = x0; x <= x1; x++) {
      const d = Math.hypot(x + 0.5 - HOLE.x, y + 0.5 - HOLE.y);
      const cov = clamp((rh - d) / 2 + 0.5, 0, 1);
      if (cov <= 0) continue;
      const idx = (y * W + x) * 3;
      fb[idx] = fb[idx] * (1 - cov) + 0.004 * cov;
      fb[idx + 1] = fb[idx + 1] * (1 - cov) + 0.004 * cov;
      fb[idx + 2] = fb[idx + 2] * (1 - cov) + 0.008 * cov;
    }
  }
  // Photon ring: a thin, brilliant rim hugging the shadow.
  for (let y = y0; y <= y1; y++) {
    for (let x = x0; x <= x1; x++) {
      const d = Math.hypot(x + 0.5 - HOLE.x, y + 0.5 - HOLE.y);
      const off = Math.abs(d - (rh + 1.5));
      if (off > 3.0) continue;
      const p = 1.5 * Math.max(0, 1 - off / 3.0);
      const idx = (y * W + x) * 3;
      fb[idx] += 1.0 * p;
      fb[idx + 1] += 0.9 * p;
      fb[idx + 2] += 0.68 * p;
    }
  }
  // Near side of the ring passes in front of the shadow.
  paintRingPass(true);
  // Lensed arc: the far ring bent over the top of the shadow.
  const ax0 = Math.max(0, Math.floor(HOLE.x - rh - 24));
  const ax1 = Math.min(W - 1, Math.ceil(HOLE.x + rh + 24));
  const ay0 = Math.max(0, Math.floor(HOLE.y - rh - 24));
  const ay1 = Math.min(H - 1, Math.ceil(HOLE.y));
  for (let y = ay0; y <= ay1; y++) {
    for (let x = ax0; x <= ax1; x++) {
      const px = x + 0.5;
      const py = y + 0.5;
      const d = Math.hypot(px - HOLE.x, py - HOLE.y);
      if (d < rh + 2 || d > rh + 26) continue;
      const up = clamp((HOLE.y - py) / rh, 0, 1);
      const fade = Math.pow(up, 1.2) * (1 - (d - rh - 2) / 24);
      if (fade <= 0) continue;
      const idx = (y * W + x) * 3;
      const p = fade * 1.05;
      fb[idx] += 1.0 * p;
      fb[idx + 1] += 0.85 * p;
      fb[idx + 2] += 0.6 * p;
    }
  }
}

// ---------------------------------------------------------------------------
// 4. The paper plane and its light trail.
// ---------------------------------------------------------------------------
const PLANE = { x: 730, y: 720, angle: (28 * Math.PI) / 180 };

function planePoint(lx, ly) {
  const c = Math.cos(PLANE.angle);
  const s = Math.sin(PLANE.angle);
  return [PLANE.x + lx * c - ly * s, PLANE.y + lx * s + ly * c];
}

function paintTrail() {
  const tail = planePoint(-225, 0);
  // Cubic Bezier from the ring's edge to the plane's tail.
  const p0 = [465, 425];
  const p1 = [445, 520];
  const p2 = [475, 590];
  const p3 = tail;
  function bez(t) {
    const mt = 1 - t;
    const x =
      mt * mt * mt * p0[0] +
      3 * mt * mt * t * p1[0] +
      3 * mt * t * t * p2[0] +
      t * t * t * p3[0];
    const y =
      mt * mt * mt * p0[1] +
      3 * mt * mt * t * p1[1] +
      3 * mt * t * t * p2[1] +
      t * t * t * p3[1];
    return [x, y];
  }
  // Wide soft glow along the curve.
  const N = 220;
  for (let i = 0; i <= N; i++) {
    const t = i / N;
    const [x, y] = bez(t);
    const sig = lerp(8, 3.2, Math.pow(t, 0.7));
    const r = lerp(1.0, 0.72, t);
    const g = lerp(0.78, 0.94, t);
    const b = lerp(0.4, 1.0, t);
    stamp(x, y, sig, r, g, b, lerp(0.28, 0.6, t));
  }
  // Bright core.
  for (let i = 0; i <= 300; i++) {
    const t = i / 300;
    const [x, y] = bez(t);
    stamp(x, y, 1.6, 1.0, 0.98, 0.94, 0.85);
  }
  // Sparks thrown off the trail.
  const rnd = mulberry32(0x7a111ce5);
  for (let i = 0; i < 130; i++) {
    const t = rnd();
    const [x, y] = bez(t);
    const spread = 48 * (1 - t * 0.5);
    const off = (rnd() + rnd() + rnd() - 1.5) * spread;
    const along = (rnd() - 0.5) * 26;
    // Perpendicular direction of the curve, approximated by the chord.
    const nx = 0.55;
    const ny = -0.83;
    const sx = x + nx * off + 0.83 * along;
    const sy = y + ny * off + 0.55 * along;
    const gold = rnd() < 0.4;
    const size = 0.6 + rnd() * rnd() * 1.6;
    stamp(sx, sy, size, gold ? 1.0 : 0.75, gold ? 0.8 : 0.93, gold ? 0.45 : 1.0, 0.7 + rnd() * 0.6);
  }
}

function paintPlane() {
  // Light spill under the plane.
  stamp(PLANE.x, PLANE.y, 130, 0.55, 0.75, 0.95, 0.09);
  const nose = planePoint(250, 0);
  const wingTip = planePoint(-200, -150);
  const tailTip = planePoint(-225, 0);
  const lowTip = planePoint(-125, 138);
  const foldMid = planePoint(-40, 8);
  // Upper wing: brightest facet.
  fillTri(
    nose[0], nose[1], wingTip[0], wingTip[1], tailTip[0], tailTip[1],
    [1.0, 1.0, 1.0], [0.86, 0.91, 0.98], [0.8, 0.85, 0.93]
  );
  // Lower body: mid facet, clearly darker than the wing.
  fillTri(
    nose[0], nose[1], tailTip[0], tailTip[1], lowTip[0], lowTip[1],
    [0.88, 0.9, 0.95], [0.52, 0.57, 0.68], [0.42, 0.47, 0.58]
  );
  // Keel sliver along the fold: a subtle shading step for depth.
  fillTri(
    nose[0], nose[1], foldMid[0], foldMid[1], tailTip[0], tailTip[1],
    [0.8, 0.83, 0.9], [0.6, 0.65, 0.75], [0.48, 0.53, 0.63]
  );
  // Fold line.
  drawLine(nose[0], nose[1], tailTip[0], tailTip[1], 1.4, 0.38, 0.43, 0.53, 0.55, 0, false);
  // Warm rim light on the edges facing the black hole.
  drawLine(nose[0], nose[1], wingTip[0], wingTip[1], 1.3, 1.0, 0.9, 0.66, 0.75, 0, true);
  drawLine(wingTip[0], wingTip[1], tailTip[0], tailTip[1], 1.0, 1.0, 0.85, 0.6, 0.3, 0, true);
  // Cool rim on the far edge.
  drawLine(nose[0], nose[1], lowTip[0], lowTip[1], 1.1, 0.75, 0.9, 1.0, 0.5, 0, true);
}

// ---------------------------------------------------------------------------
// 5. Speed lines streaming behind the plane, plus ambient light motes.
// ---------------------------------------------------------------------------
function paintSpeedLines() {
  const dirX = Math.cos(PLANE.angle);
  const dirY = Math.sin(PLANE.angle);
  const px = -dirY;
  const py = dirX;
  const tail = planePoint(-225, 0);
  const rnd = mulberry32(0x9e3779b9);
  for (let i = 0; i < 7; i++) {
    const back = 20 + rnd() * 200;
    const side = (rnd() - 0.5) * 220;
    const sx = tail[0] - dirX * back + px * side;
    const sy = tail[1] - dirY * back + py * side;
    const len = 70 + rnd() * 140;
    const ex = sx - dirX * len;
    const ey = sy - dirY * len;
    const w = 1.0 + rnd() * 1.5;
    const a = 0.16 + rnd() * 0.22;
    drawLine(sx, sy, ex, ey, w, 0.75, 0.9, 1.0, a, 1.6, true);
  }
}

function paintMotes() {
  const rnd = mulberry32(0x51ed51ed);
  for (let i = 0; i < 45; i++) {
    const x = 430 + rnd() * 590;
    const y = 380 + rnd() * 640;
    const size = 0.5 + rnd() * 1.4;
    const gold = rnd() < 0.35;
    stamp(x, y, size, gold ? 1.0 : 0.8, gold ? 0.82 : 0.92, gold ? 0.5 : 1.0, 0.25 + rnd() * 0.5);
  }
}

// ---------------------------------------------------------------------------
// 6. Vignette, tonemap, PNG encode.
// ---------------------------------------------------------------------------
function finish() {
  for (let y = 0; y < H; y++) {
    const dy = (y - H / 2) / 724;
    let idx = y * W * 3;
    for (let x = 0; x < W; x++) {
      const dx = (x - W / 2) / 724;
      const rn = Math.hypot(dx, dy);
      const vig = 1 - 0.4 * smoothstep(0.62, 1.15, rn);
      fb[idx] *= vig;
      fb[idx + 1] *= vig;
      fb[idx + 2] *= vig;
      idx += 3;
    }
  }
}

const CRC_TABLE = (() => {
  const table = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) {
      c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    }
    table[n] = c;
  }
  return table;
})();

function crc32(buf) {
  let c = 0xffffffff;
  for (let i = 0; i < buf.length; i++) {
    c = CRC_TABLE[(c ^ buf[i]) & 0xff] ^ (c >>> 8);
  }
  return (c ^ 0xffffffff) >>> 0;
}

function chunk(type, data) {
  const out = Buffer.alloc(12 + data.length);
  out.writeUInt32BE(data.length, 0);
  out.write(type, 4, "ascii");
  data.copy(out, 8);
  const crc = crc32(Buffer.concat([Buffer.from(type, "ascii"), data]));
  out.writeUInt32BE(crc, 8 + data.length);
  return out;
}

function encodePng() {
  const raw = Buffer.alloc(H * (1 + W * 3));
  const row = Buffer.alloc(W * 3);
  for (let y = 0; y < H; y++) {
    let idx = y * W * 3;
    for (let x = 0; x < W; x++) {
      row[x * 3] = Math.round(255 * clamp(1 - Math.exp(-1.75 * fb[idx]), 0, 1));
      row[x * 3 + 1] = Math.round(255 * clamp(1 - Math.exp(-1.75 * fb[idx + 1]), 0, 1));
      row[x * 3 + 2] = Math.round(255 * clamp(1 - Math.exp(-1.75 * fb[idx + 2]), 0, 1));
      idx += 3;
    }
    // Pick the better of filter 0 (None) and filter 1 (Sub) per row.
    let sumNone = 0;
    for (let i = 0; i < row.length; i++) {
      const v = row[i];
      sumNone += v < 128 ? v : 256 - v;
    }
    const sub = Buffer.alloc(W * 3);
    for (let i = 0; i < row.length; i++) {
      const left = i >= 3 ? row[i - 3] : 0;
      sub[i] = (row[i] - left) & 0xff;
    }
    let sumSub = 0;
    for (let i = 0; i < sub.length; i++) {
      const v = sub[i];
      sumSub += v < 128 ? v : 256 - v;
    }
    const off = y * (1 + W * 3);
    if (sumSub < sumNone) {
      raw[off] = 1;
      sub.copy(raw, off + 1);
    } else {
      raw[off] = 0;
      row.copy(raw, off + 1);
    }
  }
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(W, 0);
  ihdr.writeUInt32BE(H, 4);
  ihdr[8] = 8; // bit depth
  ihdr[9] = 2; // colour type: truecolour RGB
  ihdr[10] = 0;
  ihdr[11] = 0;
  ihdr[12] = 0;
  const idat = zlib.deflateSync(raw, { level: 9 });
  return Buffer.concat([
    Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]),
    chunk("IHDR", ihdr),
    chunk("IDAT", idat),
    chunk("IEND", Buffer.alloc(0)),
  ]);
}

function main() {
  const t0 = Date.now();
  paintBackground();
  paintStars();
  paintBlackHole();
  paintTrail();
  paintPlane();
  paintSpeedLines();
  paintMotes();
  finish();
  const png = encodePng();
  const outDir = process.env.MAKEFUN_OUTPUT_DIR || "/output";
  fs.mkdirSync(outDir, { recursive: true });
  const outPath = path.join(outDir, "entry.png");
  fs.writeFileSync(outPath, png);
  const sha = crypto.createHash("sha256").update(png).digest("hex");
  console.log("wrote " + outPath + " bytes=" + png.length + " sha256=" + sha + " ms=" + (Date.now() - t0));
}

main();
