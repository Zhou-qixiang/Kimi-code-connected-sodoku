'use strict';
/* =========================================================
 * 《连通数独》—— 统一大棋盘架构
 *
 * 一个 14×14 的统一坐标系，四个 6×6 数独区域十字交叉排布，
 * 在 2×2 角部真实重叠（共享格同时属于两个区域）：
 *
 *        奇偶(O)  rows 0-5  cols 4-9
 *   彩色(C) rows 4-9 cols 0-5   差值(D) rows 4-9 cols 8-13
 *        箭头(A)  rows 8-13 cols 4-9
 *
 * 重叠区：O∩C(4-5,4-5)  O∩D(4-5,8-9)  C∩A(8-9,4-5)  D∩A(8-9,8-9)
 *
 * 数据结构：
 *   board 用 14×14 二维数组统一存储（null = 不属于任何区域）
 *   oddEvenConstraints[] / differenceConstraints[]
 *   colorRegions[] / arrowConstraints[] ({box, direction, target})
 *
 * 题目生成流水线：
 *   1. 联合回溯生成完整答案（四个区域共享格天然一致）
 *   2. 根据答案推导特殊规则（规则永远成立）
 *   3. 逐个挖除数字，每步用求解器验证仍唯一解
 * ========================================================= */

/* ================= 一、布局与静态结构 ================= */
const SIZE = 6;          // 每个区域 6×6
const GH = 14, GW = 14;  // 统一棋盘 14×14
const NUMS = [1, 2, 3, 4, 5, 6];
const BOX_H = 2, BOX_W = 2; // 宫：2×2（每个 6×6 区域划分为 9 个 2×2 小宫）

const GRIDS = [
  { id: 'O', label: '奇偶数独', r0: 0, c0: 4, color: '#4f9cf9' },
  { id: 'C', label: '彩色数独', r0: 4, c0: 0, color: '#b678e0' },
  { id: 'D', label: '差值数独', r0: 4, c0: 8, color: '#45bd73' },
  { id: 'A', label: '箭头数独', r0: 8, c0: 4, color: '#e8a54a' },
];
const GRID_BY_ID = Object.fromEntries(GRIDS.map((g) => [g.id, g]));

const key = (r, c) => r + ',' + c;
const parseKey = (k) => k.split(',').map(Number);

/* 每个统一坐标属于哪些区域 */
const CELL_GRIDS = (() => {
  const map = {};
  for (const g of GRIDS)
    for (let i = 0; i < SIZE; i++)
      for (let j = 0; j < SIZE; j++) {
        const k = key(g.r0 + i, g.c0 + j);
        (map[k] = map[k] || []).push(g.id);
      }
  return map;
})();

/* 所有有效格（128 个） */
const ACTIVE = Object.keys(CELL_GRIDS).map(parseKey);
const ACTIVE_SET = new Set(CELL_GRIDS ? Object.keys(CELL_GRIDS) : []);

/* 数独约束单元：每个区域的 6 行 / 6 列 / 6 宫（统一坐标） */
const UNITS = [];
for (const g of GRIDS) {
  for (let i = 0; i < SIZE; i++) {
    UNITS.push({ grid: g.id, kind: 'row', cells: NUMS.map((_, j) => [g.r0 + i, g.c0 + j]) });
    UNITS.push({ grid: g.id, kind: 'col', cells: NUMS.map((_, j) => [g.r0 + j, g.c0 + i]) });
  }
  for (let br = 0; br < SIZE / BOX_H; br++)
    for (let bc = 0; bc < SIZE / BOX_W; bc++) {
      const cells = [];
      for (let i = 0; i < BOX_H; i++)
        for (let j = 0; j < BOX_W; j++)
          cells.push([g.r0 + br * BOX_H + i, g.c0 + bc * BOX_W + j]);
      UNITS.push({ grid: g.id, kind: 'box', cells });
    }
}

/* 格 -> 包含它的单元；格 -> 同行列宫的其它格（用于求解传播） */
const UNITS_BY_CELL = {};
const UNIT_PEERS = {};
for (const [r, c] of ACTIVE) { UNITS_BY_CELL[key(r, c)] = []; UNIT_PEERS[key(r, c)] = new Set(); }
UNITS.forEach((u, idx) => {
  const ks = u.cells.map(([r, c]) => key(r, c));
  ks.forEach((k) => {
    UNITS_BY_CELL[k].push(idx);
    ks.forEach((o) => { if (o !== k) UNIT_PEERS[k].add(o); });
  });
});

/* 区域格子集合（含其重叠角） */
function gridCellSet(gridId) {
  const g = GRID_BY_ID[gridId];
  const set = new Set();
  for (let i = 0; i < SIZE; i++)
    for (let j = 0; j < SIZE; j++) set.add(key(g.r0 + i, g.c0 + j));
  return set;
}

/* ================= 二、难度配置 ================= */
const DIFFS = {
  easy:   { label: '简单', dots: 8, diffs: 8, regionMin: 4, regionMax: 6, targetGivens: 56 },
  medium: { label: '中等', dots: 6, diffs: 6, regionMin: 4, regionMax: 6, targetGivens: 44 },
  hard:   { label: '困难', dots: 5, diffs: 5, regionMin: 3, regionMax: 5, targetGivens: 34 },
};

const REGION_COLORS = [
  'rgba(231, 76, 60, .38)', 'rgba(241, 196, 15, .34)', 'rgba(46, 204, 113, .32)',
  'rgba(52, 152, 219, .34)', 'rgba(155, 89, 182, .34)', 'rgba(230, 126, 34, .34)',
  'rgba(26, 188, 156, .32)',
];

/* ================= 三、工具 ================= */
const $ = (sel) => document.querySelector(sel);
const randInt = (n) => Math.floor(Math.random() * n);
function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = randInt(i + 1);
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}
function neighbors4(r, c) {
  return [[r + 1, c], [r - 1, c], [r, c + 1], [r, c - 1]]
    .filter(([rr, cc]) => rr >= 0 && rr < GH && cc >= 0 && cc < GW);
}
const tick = () => new Promise((res) => setTimeout(res, 0));

/* =========================================================
 * 四、求解器（唯一解验证）
 * 约束：区域行/列/宫 all-different + 奇偶 + 差值 + 彩色 + 箭头
 * ========================================================= */
function countSolutions(givens, rules, limit = 2) {
  /* 彩色区域 -> 额外 all-different 同伴 */
  const regionPeers = {};
  for (const reg of rules.colorRegions) {
    const ks = reg.cells.map(([r, c]) => key(r, c));
    for (const a of ks) for (const b of ks)
      if (a !== b) (regionPeers[a] = regionPeers[a] || new Set()).add(b);
  }
  /* 奇偶 / 差值 成对约束 */
  const pairs = [];
  for (const cn of rules.oddEvenConstraints)
    pairs.push({ i: key(...cn.a), j: key(...cn.b), type: 'parity' });
  for (const cn of rules.differenceConstraints)
    pairs.push({ i: key(...cn.a), j: key(...cn.b), type: 'diff', d: cn.value });
  const pairByCell = {};
  pairs.forEach((p, idx) => {
    (pairByCell[p.i] = pairByCell[p.i] || []).push(idx);
    (pairByCell[p.j] = pairByCell[p.j] || []).push(idx);
  });
  /* 箭头约束：target 必须是所在 2×2 宫的最大数字 */
  const arrows = rules.arrowConstraints.map((a) => {
    const [br, bc] = a.box;
    const cells = [];
    for (let i = 0; i < 2; i++)
      for (let j = 0; j < 2; j++) cells.push(key(br + i, bc + j));
    return { cells, target: key(...a.target) };
  });
  const arrowByCell = {};
  arrows.forEach((a, idx) => {
    a.cells.forEach((k) => (arrowByCell[k] = arrowByCell[k] || []).push(idx));
  });

  const assign = {};
  for (const [r, c] of ACTIVE) {
    const v = givens[r][c];
    if (v) assign[key(r, c)] = v;
  }
  let count = 0;

  /* 赋值后检查与 k 相关的特殊约束 */
  function constraintsOk(k) {
    for (const idx of pairByCell[k] || []) {
      const p = pairs[idx];
      const a = assign[p.i], b = assign[p.j];
      if (a && b) {
        if (p.type === 'parity' && a % 2 === b % 2) return false;
        if (p.type === 'diff' && Math.abs(a - b) !== p.d) return false;
      }
    }
    for (const idx of arrowByCell[k] || []) {
      const ar = arrows[idx];
      const tv = assign[ar.target];
      if (tv) {
        /* 目标已赋值：宫内其它格必须严格更小 */
        for (const ck of ar.cells) {
          if (ck === ar.target) continue;
          const ov = assign[ck];
          if (ov && ov >= tv) return false;
        }
      }
    }
    return true;
  }

  (function solve() {
    if (count >= limit) return;
    /* MRV：选候选最少的空格 */
    let best = null, bestDom = null;
    for (const [r, c] of ACTIVE) {
      const k = key(r, c);
      if (assign[k]) continue;
      const dom = [];
      for (let v = 1; v <= SIZE; v++) {
        let ok = true;
        for (const p of UNIT_PEERS[k]) if (assign[p] === v) { ok = false; break; }
        if (ok && regionPeers[k])
          for (const p of regionPeers[k]) if (assign[p] === v) { ok = false; break; }
        if (ok) dom.push(v);
      }
      if (dom.length === 0) return;
      if (!bestDom || dom.length < bestDom.length) {
        best = k; bestDom = dom;
        if (dom.length === 1) break;
      }
    }
    if (!best) { count++; return; }
    for (const v of bestDom) {
      assign[best] = v;
      if (constraintsOk(best)) solve();
      delete assign[best];
      if (count >= limit) return;
    }
  })();

  return count;
}

/* =========================================================
 * 五、题目生成
 * ========================================================= */

/* ---- 第 1 步：联合回溯生成完整答案（四区域共享格自动一致） ---- */
function genSolution() {
  const assign = {};
  const okWith = (k, v) => {
    for (const p of UNIT_PEERS[k]) if (assign[p] === v) return false;
    return true;
  };
  (function solve() {
    let best = null, bestDom = null;
    for (const [r, c] of ACTIVE) {
      const k = key(r, c);
      if (assign[k]) continue;
      const dom = NUMS.filter((v) => okWith(k, v));
      if (dom.length === 0) return false;
      if (!bestDom || dom.length < bestDom.length) {
        best = k; bestDom = dom;
        if (dom.length === 1) break;
      }
    }
    if (!best) return true;
    shuffle(bestDom);
    for (const v of bestDom) {
      assign[best] = v;
      if (solve()) return true;
      delete assign[best];
    }
    return false;
  })();

  const sol = Array.from({ length: GH }, () => Array(GW).fill(null));
  for (const [r, c] of ACTIVE) sol[r][c] = assign[key(r, c)];
  return sol;
}

/* ---- 第 2 步：根据答案推导特殊规则 ---- */

/* 通用：在指定区域内挑相邻格对（每格最多出现 maxDeg 次） */
function pickPairs(gridId, count, accept) {
  const set = gridCellSet(gridId);
  const pairs = [];
  for (const k of set) {
    const [r, c] = parseKey(k);
    for (const [rr, cc] of [[r, c + 1], [r + 1, c]])
      if (set.has(key(rr, cc))) pairs.push([[r, c], [rr, cc]]);
  }
  shuffle(pairs);
  const deg = {};
  const out = [];
  for (const [a, b] of pairs) {
    const ka = key(...a), kb = key(...b);
    if ((deg[ka] || 0) >= 2 || (deg[kb] || 0) >= 2) continue;
    if (!accept(a, b)) continue;
    deg[ka] = (deg[ka] || 0) + 1;
    deg[kb] = (deg[kb] || 0) + 1;
    out.push({ a, b });
    if (out.length >= count) break;
  }
  return out;
}

/* 彩色区域：在彩色数独范围内生成真正连通的区域（覆盖全部 36 格） */
function genColorRegions(sol, cfg) {
  const CSET = gridCellSet('C');
  const unassigned = new Set(CSET);
  const at = (k) => { const [r, c] = parseKey(k); return sol[r][c]; };
  const regions = [];

  while (unassigned.size) {
    const seed = [...unassigned][randInt(unassigned.size)];
    const target = cfg.regionMin + randInt(cfg.regionMax - cfg.regionMin + 1);
    const region = [seed];
    const vals = new Set([at(seed)]);
    unassigned.delete(seed);
    while (region.length < target) {
      const cand = [];
      for (const k of region) {
        const [r, c] = parseKey(k);
        for (const [rr, cc] of neighbors4(r, c)) {
          const nk = key(rr, cc);
          if (unassigned.has(nk) && CSET.has(nk) && !vals.has(at(nk)) && !cand.includes(nk))
            cand.push(nk);
        }
      }
      if (!cand.length) break;
      const pick = cand[randInt(cand.length)];
      region.push(pick);
      vals.add(at(pick));
      unassigned.delete(pick);
    }
    regions.push(region);
  }

  /* 过小的区域并入相邻区域（保持数字不重复） */
  for (let i = regions.length - 1; i >= 0; i--) {
    if (regions[i].length >= 3) continue;
    const vals = new Set(regions[i].map(at));
    let merged = false;
    for (let j = 0; j < regions.length && !merged; j++) {
      if (i === j || regions[j].length >= cfg.regionMax) continue;
      const jv = new Set(regions[j].map(at));
      if ([...vals].some((v) => jv.has(v))) continue;
      const adjacent = regions[i].some((k) => {
        const [r, c] = parseKey(k);
        return neighbors4(r, c).some(([rr, cc]) => regions[j].includes(key(rr, cc)));
      });
      if (adjacent) { regions[j].push(...regions[i]); regions.splice(i, 1); merged = true; }
    }
  }

  /* 着色：相邻区域颜色不同（先统一转成 [r,c] 并建立归属表） */
  const colored = regions.map((cells) => ({ cells: cells.map(parseKey), color: null }));
  const owner = {};
  colored.forEach((reg, idx) => reg.cells.forEach(([r, c]) => { owner[key(r, c)] = idx; }));
  colored.forEach((reg, idx) => {
    const usedColors = new Set();
    for (const [r, c] of reg.cells) {
      for (const [rr, cc] of neighbors4(r, c)) {
        const oi = owner[key(rr, cc)];
        if (oi !== undefined && oi !== idx && colored[oi].color)
          usedColors.add(colored[oi].color);
      }
    }
    const avail = REGION_COLORS.filter((cl) => !usedColors.has(cl));
    reg.color = avail.length ? avail[randInt(avail.length)] : REGION_COLORS[0];
  });
  return colored;
}

/* 箭头：由答案确定（非随机）——
 * 箭头区域每个 2×2 宫放置一个箭头，斜向指向宫内最大数字。
 * 方向：↘ down-right / ↙ down-left / ↗ up-right / ↖ up-left
 * 由于宫内数字本就不重复，最大值必然唯一。 */
const ARROW_DIRS = {
  '0,0': 'up-left', '0,1': 'up-right',
  '1,0': 'down-left', '1,1': 'down-right',
};
function genArrows(sol) {
  const g = GRID_BY_ID['A'];
  const arrows = [];
  for (let br = 0; br < SIZE / BOX_H; br++) {
    for (let bc = 0; bc < SIZE / BOX_W; bc++) {
      const r0 = g.r0 + br * BOX_H, c0 = g.c0 + bc * BOX_W;
      let maxV = -1, target = null;
      for (let i = 0; i < BOX_H; i++)
        for (let j = 0; j < BOX_W; j++) {
          const v = sol[r0 + i][c0 + j];
          if (v > maxV) { maxV = v; target = [r0 + i, c0 + j]; }
        }
      const local = (target[0] - r0) + ',' + (target[1] - c0);
      arrows.push({ box: [r0, c0], direction: ARROW_DIRS[local], target });
    }
  }
  return arrows;
}

/* ---- 第 3 步：挖除数字，每步验证唯一解 ---- */
async function digHoles(sol, rules, cfg) {
  const givens = sol.map((row) => row.slice());
  const order = shuffle(ACTIVE.slice());
  let remaining = ACTIVE.length;
  let checked = 0;
  for (const [r, c] of order) {
    if (remaining <= cfg.targetGivens) break;
    const backup = givens[r][c];
    givens[r][c] = 0;
    if (countSolutions(givens, rules, 2) !== 1) {
      givens[r][c] = backup;
    } else {
      remaining--;
    }
    if (++checked % 6 === 0) await tick(); // 让出主线程，避免卡顿
  }
  return givens;
}

/* ---- 生成完整题目 ---- */
async function generatePuzzle(diffKey) {
  const cfg = DIFFS[diffKey];
  for (let attempt = 0; attempt < 8; attempt++) {
    const solution = genSolution();
    const rules = {
      oddEvenConstraints: pickPairs('O', cfg.dots,
        (a, b) => solution[a[0]][a[1]] % 2 !== solution[b[0]][b[1]] % 2),
      differenceConstraints: pickPairs('D', cfg.diffs, () => true)
        .map(({ a, b }) => ({ a, b, value: Math.abs(solution[a[0]][a[1]] - solution[b[0]][b[1]]) })),
      colorRegions: genColorRegions(solution, cfg),
      arrowConstraints: genArrows(solution),
    };
    if (rules.oddEvenConstraints.length < 3 || rules.differenceConstraints.length < 3 ||
        rules.colorRegions.length < 3 || rules.arrowConstraints.length !== 9) continue;
    const givens = await digHoles(solution, rules, cfg);
    return { diffKey, cfg, solution, givens, ...rules };
  }
  throw new Error('题目生成失败，请重试');
}

/* =========================================================
 * 六、游戏状态
 * ========================================================= */
let game = null;

function startGame(diffKey) {
  showLoading(true);
  // 让加载动画先渲染，再开始生成
  setTimeout(async () => {
    try {
      const puzzle = await generatePuzzle(diffKey);
      initGame(puzzle);
    } catch (e) {
      alert(e.message);
    } finally {
      showLoading(false);
    }
  }, 30);
}

function initGame(puzzle) {
  game = {
    puzzle,
    values: puzzle.givens.map((row) => row.map((v) => v || 0)),
    notes: {},            // key -> Set
    selected: null,
    notesMode: false,
    errors: new Set(),
    seconds: 0,
    timerId: null,
    finished: false,
  };

  $('#start-screen').classList.add('hidden');
  $('#win-overlay').classList.add('hidden');
  $('#game-screen').classList.remove('hidden');
  $('#diff-label').textContent = puzzle.cfg.label;
  $('#btn-notes').classList.remove('active');
  setMessage('');

  renderBoard();
  renderNumpad();
  startTimer();
}

function backToStart() {
  stopTimer();
  game = null;
  $('#game-screen').classList.add('hidden');
  $('#win-overlay').classList.add('hidden');
  $('#start-screen').classList.remove('hidden');
}

function resetGame() {
  if (!game) return;
  game.values = game.puzzle.givens.map((row) => row.map((v) => v || 0));
  game.notes = {};
  game.errors.clear();
  game.finished = false;
  setMessage('');
  refreshAllCells();
}

/* =========================================================
 * 七、渲染
 * ========================================================= */
function renderBoard() {
  const board = $('#mega-board');
  board.innerHTML = '';
  const P = game.puzzle;

  /* 区域轮廓 + 标签（先渲染，位于格子下方） */
  for (const g of GRIDS) {
    const outline = document.createElement('div');
    outline.className = 'grid-outline';
    outline.style.left = `${(g.c0 / GW) * 100}%`;
    outline.style.top = `${(g.r0 / GH) * 100}%`;
    outline.style.width = `${(SIZE / GW) * 100}%`;
    outline.style.height = `${(SIZE / GH) * 100}%`;
    outline.style.borderColor = g.color;
    outline.style.background = g.color + '10';
    board.appendChild(outline);

    const label = document.createElement('div');
    label.className = 'grid-label';
    label.textContent = g.label;
    label.style.color = g.color;
    label.style.left = `${(g.c0 / GW) * 100}%`;
    label.style.top = `${(g.r0 / GH) * 100}%`;
    board.appendChild(label);
  }

  /* 箭头层 */
  board.appendChild(buildArrowSvg(P.arrowConstraints));

  /* 14×14 格子（无效格占位隐藏） */
  for (let r = 0; r < GH; r++) {
    for (let c = 0; c < GW; c++) {
      board.appendChild(buildCell(r, c));
    }
  }

  /* 奇偶白点 / 差值绿圈 */
  for (const cn of P.oddEvenConstraints) board.appendChild(buildMark(cn.a, cn.b, 'parity-dot'));
  for (const cn of P.differenceConstraints) board.appendChild(buildMark(cn.a, cn.b, 'diff-num', cn.value));

  refreshAllCells();
}

function buildCell(r, c) {
  const k = key(r, c);
  const grids = CELL_GRIDS[k];
  const cell = document.createElement('div');

  if (!grids) {
    cell.className = 'cell-void';
    return cell;
  }

  cell.className = 'cell';
  cell.dataset.pos = k;

  /* 宫内粗线（按每个所属区域分别判断） */
  for (const gid of grids) {
    const g = GRID_BY_ID[gid];
    const lr = r - g.r0, lc = c - g.c0;
    if (lc % BOX_W === 0 && lc !== 0) cell.classList.add('bl');
    if (lr % BOX_H === 0 && lr !== 0) cell.classList.add('bt');
  }

  if (grids.length > 1) {
    cell.classList.add('overlap');
    cell.title = '重叠格：同时属于两个区域，须满足双方规则';
  }

  if (game.puzzle.givens[r][c]) cell.classList.add('given');

  /* 彩色区域底色 */
  const reg = game.puzzle.colorRegions.find((rg) =>
    rg.cells.some(([rr, cc]) => rr === r && cc === c));
  if (reg) cell.style.backgroundColor = reg.color;

  const notes = document.createElement('div');
  notes.className = 'notes';
  cell.appendChild(notes);

  const val = document.createElement('span');
  val.className = 'val';
  cell.appendChild(val);

  cell.addEventListener('click', () => selectCell(r, c));
  return cell;
}

/* 箭头 SVG：viewBox 140×140，每格 10 单位。
 * 视觉规范：
 *  - 箭头居中于对应 2×2 宫的中心，不从格子边缘起笔
 *  - 整体长度约为原版的 60%，头部约为 50%，杆宽约为 60%
 *  - 保持 ↘ ↙ ↗ ↖ 四个斜向，箭头朝向最大数字格
 *  - 箭头层低于数字层（CSS z-index 已保证数字在最上方）
 */
const ARROW_HALF_LEN = 3.8;   // 箭头半长（整体 ≈ 原长度 × 0.6）
const ARROW_STROKE = 0.9;     // 杆宽（原 1.5 × 0.6）
const ARROW_HEAD = 4.2;       // 箭头三角形尺寸（userSpaceOnUse，≈ 原 × 0.5）
const ARROW_TAIL_R = 0.9;     // 箭尾圆点半径
function buildArrowSvg(arrows) {
  const NS = 'http://www.w3.org/2000/svg';
  const svg = document.createElementNS(NS, 'svg');
  svg.setAttribute('viewBox', '0 0 140 140');
  svg.id = 'arrow-svg';

  const defs = document.createElementNS(NS, 'defs');
  const marker = document.createElementNS(NS, 'marker');
  marker.setAttribute('id', 'arrowhead');
  marker.setAttribute('markerUnits', 'userSpaceOnUse');
  marker.setAttribute('markerWidth', String(ARROW_HEAD));
  marker.setAttribute('markerHeight', String(ARROW_HEAD));
  marker.setAttribute('refX', String(ARROW_HEAD * 0.8));
  marker.setAttribute('refY', String(ARROW_HEAD / 2));
  marker.setAttribute('orient', 'auto');
  const tip = document.createElementNS(NS, 'path');
  tip.setAttribute('d', `M0,0 L${ARROW_HEAD},${ARROW_HEAD / 2} L0,${ARROW_HEAD} Z`);
  tip.setAttribute('fill', 'rgba(232,165,74,.95)');
  marker.appendChild(tip);
  defs.appendChild(marker);
  svg.appendChild(defs);

  for (const ar of arrows) {
    /* 宫中心 */
    const cx = ar.box[1] * 10 + 10, cy = ar.box[0] * 10 + 10;
    /* 方向单位向量：宫中心 -> 目标格中心（即 ↘↙↗↖ 方向） */
    const tx = ar.target[1] * 10 + 5, ty = ar.target[0] * 10 + 5;
    const dx = tx - cx, dy = ty - cy;
    const len = Math.hypot(dx, dy) || 1;
    const ux = dx / len, uy = dy / len;
    /* 以宫中心为中点的短小箭头 */
    const tail = [cx - ux * ARROW_HALF_LEN, cy - uy * ARROW_HALF_LEN];
    const head = [cx + ux * ARROW_HALF_LEN, cy + uy * ARROW_HALF_LEN];

    const line = document.createElementNS(NS, 'line');
    line.setAttribute('x1', tail[0]); line.setAttribute('y1', tail[1]);
    line.setAttribute('x2', head[0]); line.setAttribute('y2', head[1]);
    line.setAttribute('stroke', 'rgba(232,165,74,.9)');
    line.setAttribute('stroke-width', String(ARROW_STROKE));
    line.setAttribute('stroke-linecap', 'round');
    line.setAttribute('marker-end', 'url(#arrowhead)');
    svg.appendChild(line);

    const dot = document.createElementNS(NS, 'circle');
    dot.setAttribute('cx', tail[0]);
    dot.setAttribute('cy', tail[1]);
    dot.setAttribute('r', String(ARROW_TAIL_R));
    dot.setAttribute('fill', 'rgba(232,165,74,.9)');
    svg.appendChild(dot);
  }
  return svg;
}

/* 两格之间的标记（白点 / 差值数字） */
function buildMark(a, b, cls, text) {
  const m = document.createElement('div');
  m.className = `mark ${cls}`;
  const fr = (a[0] + b[0]) / 2, fc = (a[1] + b[1]) / 2;
  m.style.left = `${((fc + 0.5) / GW) * 100}%`;
  m.style.top = `${((fr + 0.5) / GH) * 100}%`;
  if (text !== undefined) m.textContent = text;
  return m;
}

function renderNumpad() {
  const pad = $('#numpad');
  pad.innerHTML = '';
  NUMS.forEach((n) => {
    const btn = document.createElement('button');
    btn.className = 'num-btn';
    btn.textContent = n;
    btn.addEventListener('click', () => inputNumber(n));
    pad.appendChild(btn);
  });
}

/* 刷新所有格子的数字 / 候选 / 高亮 */
function refreshAllCells() {
  if (!game) return;
  document.querySelectorAll('.cell').forEach((cell) => {
    const [r, c] = cell.dataset.pos.split(',').map(Number);
    const k = key(r, c);
    const v = game.values[r][c];

    cell.querySelector('.val').textContent = v || '';
    const notesEl = cell.querySelector('.notes');
    notesEl.innerHTML = '';
    if (!v && game.notes[k]) {
      for (let n = 1; n <= SIZE; n++) {
        const s = document.createElement('span');
        s.textContent = game.notes[k].has(n) ? n : '';
        notesEl.appendChild(s);
      }
    }

    cell.classList.remove('selected', 'related', 'same-value', 'error');
    if (game.errors.has(k)) cell.classList.add('error');

    const sel = game.selected;
    if (sel) {
      if (sel.r === r && sel.c === c) {
        cell.classList.add('selected');
      } else {
        /* 同一约束单元（共享格会同时高亮两个区域的行列宫） */
        const shareUnit = (UNITS_BY_CELL[key(sel.r, sel.c)] || [])
          .some((ui) => UNITS[ui].cells.some(([rr, cc]) => rr === r && cc === c));
        if (shareUnit) cell.classList.add('related');
        const sv = game.values[sel.r][sel.c];
        if (sv && v === sv) cell.classList.add('same-value');
      }
    }
  });
}

/* =========================================================
 * 八、交互
 * ========================================================= */
function selectCell(r, c) {
  if (!game || game.finished) return;
  game.selected = { r, c };
  refreshAllCells();
}

function inputNumber(n) {
  if (!game || game.finished || !game.selected) return;
  const { r, c } = game.selected;
  if (game.puzzle.givens[r][c]) return;
  const k = key(r, c);

  if (game.notesMode) {
    if (game.values[r][c]) return;
    const set = game.notes[k] = game.notes[k] || new Set();
    set.has(n) ? set.delete(n) : set.add(n);
  } else {
    game.values[r][c] = game.values[r][c] === n ? 0 : n;
    delete game.notes[k];
  }
  game.errors.clear();
  refreshAllCells();
  checkWin();
}

function eraseCell() {
  if (!game || game.finished || !game.selected) return;
  const { r, c } = game.selected;
  if (game.puzzle.givens[r][c]) return;
  const k = key(r, c);
  if (game.values[r][c]) game.values[r][c] = 0;
  else delete game.notes[k];
  game.errors.clear();
  refreshAllCells();
}

/* 键盘 */
document.addEventListener('keydown', (e) => {
  if (!game || game.finished) return;
  if (e.key >= '1' && e.key <= '6') { inputNumber(Number(e.key)); e.preventDefault(); }
  else if (e.key === 'Backspace' || e.key === 'Delete' || e.key === '0') { eraseCell(); e.preventDefault(); }
  else if (e.key.startsWith('Arrow')) { moveSelection(e.key); e.preventDefault(); }
});

/* 方向键移动：跳过无效格 */
function moveSelection(keyName) {
  const dir = { ArrowUp: [-1, 0], ArrowDown: [1, 0], ArrowLeft: [0, -1], ArrowRight: [0, 1] }[keyName];
  if (!dir) return;
  let { r, c } = game.selected || { r: 0, c: 3 };
  for (let step = 0; step < Math.max(GH, GW); step++) {
    r += dir[0]; c += dir[1];
    if (r < 0 || r >= GH || c < 0 || c >= GW) return;
    if (ACTIVE_SET.has(key(r, c))) {
      game.selected = { r, c };
      refreshAllCells();
      return;
    }
  }
}

/* =========================================================
 * 九、检查答案
 * ========================================================= */
function findErrors() {
  const err = new Set();
  const V = game.values;
  const P = game.puzzle;

  const checkScope = (cells) => {
    const seen = {};
    cells.forEach(([r, c]) => {
      const v = V[r][c];
      if (v) (seen[v] = seen[v] || []).push([r, c]);
    });
    Object.values(seen).forEach((list) => {
      if (list.length > 1) list.forEach(([r, c]) => err.add(key(r, c)));
    });
  };

  /* 行 / 列 / 宫（四个区域全部单元，重叠格自动受双方约束） */
  UNITS.forEach((u) => checkScope(u.cells));
  /* 彩色区域 */
  P.colorRegions.forEach((reg) => checkScope(reg.cells));
  /* 奇偶 */
  P.oddEvenConstraints.forEach(({ a, b }) => {
    const va = V[a[0]][a[1]], vb = V[b[0]][b[1]];
    if (va && vb && va % 2 === vb % 2) { err.add(key(...a)); err.add(key(...b)); }
  });
  /* 差值 */
  P.differenceConstraints.forEach(({ a, b, value }) => {
    const va = V[a[0]][a[1]], vb = V[b[0]][b[1]];
    if (va && vb && Math.abs(va - vb) !== value) { err.add(key(...a)); err.add(key(...b)); }
  });
  /* 箭头：目标格必须是所在 2×2 宫的最大数字 */
  P.arrowConstraints.forEach((ar) => {
    const [br, bc] = ar.box;
    const tv = V[ar.target[0]][ar.target[1]];
    if (!tv) return;
    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < 2; j++) {
        const r = br + i, c = bc + j;
        if (r === ar.target[0] && c === ar.target[1]) continue;
        const ov = V[r][c];
        if (ov && ov >= tv) {
          err.add(key(...ar.target));
          err.add(key(r, c));
        }
      }
    }
  });
  return err;
}

function checkAnswer() {
  if (!game || game.finished) return;
  game.errors = findErrors();
  refreshAllCells();
  if (game.errors.size === 0) {
    const filled = ACTIVE.every(([r, c]) => game.values[r][c]);
    setMessage(filled ? '✔ 全部正确！' : '✔ 目前没有错误', 'ok');
  } else {
    setMessage(`✘ 发现 ${game.errors.size} 个格子有误（红色标出）`, 'bad');
  }
}

/* =========================================================
 * 十、胜负 / 计时 / 消息
 * ========================================================= */
function checkWin() {
  if (!ACTIVE.every(([r, c]) => game.values[r][c])) return;
  if (findErrors().size > 0) return;
  game.finished = true;
  stopTimer();
  showWin();
}

function showWin() {
  $('#win-time').textContent = `难度：${game.puzzle.cfg.label}　用时：${formatTime(game.seconds)}`;
  $('#win-overlay').classList.remove('hidden');
  const confetti = $('#confetti');
  confetti.innerHTML = '';
  const emojis = ['🎊', '🎉', '⭐', '✨', '🟦', '🟩', '🟨', '🟥'];
  for (let i = 0; i < 60; i++) {
    const p = document.createElement('span');
    p.className = 'confetti-piece';
    p.textContent = emojis[randInt(emojis.length)];
    p.style.left = `${Math.random() * 100}%`;
    p.style.animationDuration = `${2.2 + Math.random() * 2.5}s`;
    p.style.animationDelay = `${Math.random() * 1.5}s`;
    confetti.appendChild(p);
  }
}

function startTimer() {
  stopTimer();
  game.seconds = 0;
  $('#timer').textContent = '00:00';
  game.timerId = setInterval(() => {
    game.seconds++;
    $('#timer').textContent = formatTime(game.seconds);
  }, 1000);
}

function stopTimer() {
  if (game && game.timerId) clearInterval(game.timerId);
}

function formatTime(s) {
  return `${String(Math.floor(s / 60)).padStart(2, '0')}:${String(s % 60).padStart(2, '0')}`;
}

function setMessage(text, type) {
  const el = $('#message');
  el.textContent = text;
  el.className = `message ${type || ''}`;
}

function showLoading(on) {
  $('#loading-overlay').classList.toggle('hidden', !on);
}

/* =========================================================
 * 十一、事件绑定
 * ========================================================= */
document.querySelectorAll('.diff-btn').forEach((btn) => {
  btn.addEventListener('click', () => startGame(btn.dataset.diff));
});
$('#btn-back').addEventListener('click', backToStart);
$('#btn-again').addEventListener('click', backToStart);
$('#btn-erase').addEventListener('click', eraseCell);
$('#btn-reset').addEventListener('click', resetGame);
$('#btn-new').addEventListener('click', () => {
  if (game) startGame(game.puzzle.diffKey); // 同难度重新自动生成一题
});
$('#btn-check').addEventListener('click', checkAnswer);
$('#btn-notes').addEventListener('click', () => {
  if (!game) return;
  game.notesMode = !game.notesMode;
  $('#btn-notes').classList.toggle('active', game.notesMode);
});

/* 支持 URL 直达难度，如 index.html?diff=easy */
const urlDiff = new URLSearchParams(location.search).get('diff');
if (DIFFS[urlDiff]) startGame(urlDiff);
