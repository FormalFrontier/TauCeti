/* Tau Ceti exposition — per-area page: main-results cards + dependency graph.
   Vanilla JS, Canvas 2D. Loaded by a/<Area>/index.html, which carries the
   area slug in <body data-slug>. Fetches ../../data/areas/<slug>.json.

   The page has two modes, switched by the `mode-hl` class on <body>: the
   default "Main results" card view (the shard's score-picked `hl` ids) and
   the full graph. Entering the graph is hash-driven and sticky; only the
   explicit "Main results" toolbar button (or browser-back to an empty
   hash) returns to the cards. Areas with no highlights open straight in
   the graph. Hash routing: #d<id> selects declaration <id>, #cone=<id>
   shows its dependency cone, #graph opens the graph unselected.

   Adapted from Lean Pool's exposition graph viewer (Vasily Ilin,
   https://github.com/Vilin97/lean-pool, Apache 2.0). Changes for Tau Ceti:
   the minimal-file builder and registry-card strip are gone, and the side
   panel gains cross-area dependency sections (Tau Ceti areas are one
   integrated library, so declarations link into other areas' pages) plus
   each declaration's depth in the whole-library graph. Canvas labels drop
   the shared `TauCeti.` name prefix. */
(() => {
  'use strict';

  // ----- constants ---------------------------------------------------------

  const LAYER_X = 170; // x = layer * LAYER_X
  const ROW_Y = 26; // y = (order - (layerSize - 1) / 2) * ROW_Y
  const NODE_SIZE = 8; // node glyph, graph units
  const GRID_CELL = 64; // hit-test grid cell, graph units
  const CHEAP_EDGE_THRESHOLD = 8000; // straight edges while panning above this
  const DEP_LIST_INITIAL = 100; // panel Uses/Used-by rows before "Show all"
  const MAX_LABEL_PX = 400; // widen the left label cull by one label width
  const KINDS = ['theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure',
    'class', 'inductive', 'axiom', 'opaque'];
  const GITHUB_BLOB = 'https://github.com/TauCetiProject/TauCeti/blob/';
  const NAME_PREFIX = 'TauCeti.'; // stripped from canvas labels, not data
  const MONO = 'ui-monospace, SFMono-Regular, Menlo, Consolas, monospace';

  // ----- DOM ----------------------------------------------------------------

  const byId = (id) => document.getElementById(id);
  const canvas = byId('graph-canvas');
  const viewportEl = byId('graph-viewport');
  if (!canvas || !viewportEl) return;
  const ctx = canvas.getContext('2d');
  const tooltipEl = byId('graph-tooltip');
  const messageEl = byId('graph-message');
  const panelEl = byId('decl-panel');
  const panelBodyEl = byId('panel-body');
  const panelCloseEl = byId('panel-close');
  const searchInputEl = byId('search-input');
  const searchCountEl = byId('search-count');
  const fitButtonEl = byId('fit-button');
  const breadcrumbEl = byId('cone-breadcrumb');
  const coneBackEl = byId('cone-back');
  const coneLabelEl = byId('cone-label');
  const titleEl = byId('area-title');
  const statsEl = byId('info-stats');
  const legendEl = byId('kind-legend');
  const hlGridEl = byId('hl-grid');
  const hlSubEl = byId('hl-sub');
  const hlExploreEl = byId('hl-explore');
  const hlBackEl = byId('hl-back');
  const slug = document.body.dataset.slug || '';

  function elWith(tag, className, text) {
    const node = document.createElement(tag);
    if (className) node.className = className;
    if (text !== null && text !== undefined) node.textContent = text;
    return node;
  }

  function shortName(name) {
    return name.startsWith(NAME_PREFIX) ? name.slice(NAME_PREFIX.length) : name;
  }

  // ----- theme --------------------------------------------------------------

  let theme = null;
  let edgeColors = ['', '', '']; // [dim, normal, accent]
  let labelColor = '';

  function hexToRgb(hex) {
    let h = (hex || '').trim();
    if (h.startsWith('#')) h = h.slice(1);
    if (h.length === 3) h = h[0] + h[0] + h[1] + h[1] + h[2] + h[2];
    const num = parseInt(h, 16);
    if (h.length !== 6 || Number.isNaN(num)) return [128, 128, 128];
    return [(num >> 16) & 255, (num >> 8) & 255, num & 255];
  }

  function mixRgb(a, b, t) {
    return [
      Math.round(a[0] + (b[0] - a[0]) * t),
      Math.round(a[1] + (b[1] - a[1]) * t),
      Math.round(a[2] + (b[2] - a[2]) * t),
    ];
  }

  function rgbaStr(rgb, alpha) {
    return 'rgba(' + rgb[0] + ',' + rgb[1] + ',' + rgb[2] + ',' + alpha + ')';
  }

  function readTheme() {
    const rootStyle = getComputedStyle(document.documentElement);
    const token = (name, fallback) =>
      rootStyle.getPropertyValue(name).trim() || fallback;
    const kinds = {};
    for (const k of KINDS) kinds[k] = token('--kind-' + k, '#768390');
    theme = {
      fg: token('--fg', '#eef2fb'),
      muted: token('--muted', '#9aa6c9'),
      border: token('--border', '#38405e'),
      accent: token('--accent', '#5eead4'),
      kinds,
    };
  }

  function updateDerivedColors() {
    // The border token is rgba() in this theme; blend from a solid
    // navy-adjacent grey instead so edge colors stay parseable.
    const edgeRgb = mixRgb(hexToRgb('#38405e'), hexToRgb(theme.muted), 0.5);
    const alpha = view ? view.edgeAlpha : 0.4;
    edgeColors = [
      rgbaStr(edgeRgb, Math.max(0.02, alpha * 0.15)),
      rgbaStr(edgeRgb, alpha),
      rgbaStr(hexToRgb(theme.accent), 0.85),
    ];
    labelColor = rgbaStr(hexToRgb(theme.fg), 0.85);
  }

  // ----- model state --------------------------------------------------------

  let decls = [];
  let modules = [];
  let areaNames = []; // all area slugs; xdeps/xrev entries index into this
  let commit = 'main';
  let N = 0;
  let names = [];
  let labels = []; // names with the shared library prefix stripped
  let lowerNames = [];
  let nodeKinds = [];
  let deps = []; // Int32Array per node: nodes this one uses (this area)
  let rev = []; // Int32Array per node: nodes using this one (this area)

  let matchFlags = null; // Uint8Array(N), search matches
  let neighborFlags = null; // Uint8Array(N), selected + 1-step neighborhood
  let matchTotal = 0;
  let firstMatch = -1;
  let searchQuery = '';

  let fullView = null;
  let coneView = null;
  let coneRoot = -1;
  let view = null;

  let selected = -1; // shard-local declaration id
  let hoverId = -1; // shard-local declaration id

  const camera = { scale: 1, tx: 0, ty: 0, minScale: 0.05, maxScale: 8 };
  let dirty = true;
  let interacting = false;
  let autoFit = true; // refit on resize until the user pans/zooms
  let wheelTimer = 0;
  let cssW = 1;
  let cssH = 1;
  let dpr = 1;

  // ----- views (full graph / dependency cone) -------------------------------

  function gridKey(cx, cy) {
    return cx * 262144 + cy;
  }

  function buildGrid(xs, ys, n) {
    const map = new Map();
    for (let i = 0; i < n; i++) {
      const key = gridKey(Math.floor(xs[i] / GRID_CELL),
        Math.floor(ys[i] / GRID_CELL));
      let cell = map.get(key);
      if (!cell) {
        cell = [];
        map.set(key, cell);
      }
      cell.push(i);
    }
    return map;
  }

  // A view is a renderable (sub)graph: node positions, view-local edges, a
  // hit-test grid and kind groupings. All arrays are allocated once here,
  // never per frame.
  function buildView(ids, layerOf, orderOf, layerSizes) {
    const n = ids.length;
    const xs = new Float32Array(n);
    const ys = new Float32Array(n);
    let minX = 0;
    let maxX = 0;
    let minY = 0;
    let maxY = 0;
    for (let i = 0; i < n; i++) {
      const layer = layerOf[i];
      const size = layerSizes[layer] || 1;
      const x = layer * LAYER_X;
      const y = (orderOf[i] - (size - 1) / 2) * ROW_Y;
      xs[i] = x;
      ys[i] = y;
      if (i === 0) {
        minX = maxX = x;
        minY = maxY = y;
      } else {
        if (x < minX) minX = x;
        if (x > maxX) maxX = x;
        if (y < minY) minY = y;
        if (y > maxY) maxY = y;
      }
    }
    const toView = new Int32Array(N).fill(-1);
    for (let i = 0; i < n; i++) toView[ids[i]] = i;
    let edgeCount = 0;
    for (let i = 0; i < n; i++) {
      const list = deps[ids[i]];
      for (let j = 0; j < list.length; j++) {
        const s = toView[list[j]];
        if (s >= 0 && s !== i) edgeCount++;
      }
    }
    const edgeSrc = new Int32Array(edgeCount);
    const edgeDst = new Int32Array(edgeCount);
    let e = 0;
    for (let i = 0; i < n; i++) {
      const list = deps[ids[i]];
      for (let j = 0; j < list.length; j++) {
        const s = toView[list[j]];
        if (s >= 0 && s !== i) {
          edgeSrc[e] = s; // dependency on the left…
          edgeDst[e] = i; // …drawn toward the declaration using it
          e++;
        }
      }
    }
    const groupIndex = new Map();
    const groupLists = [];
    for (let i = 0; i < n; i++) {
      const kind = nodeKinds[ids[i]];
      let gi = groupIndex.get(kind);
      if (gi === undefined) {
        gi = groupLists.length;
        groupIndex.set(kind, gi);
        groupLists.push({ kind, list: [] });
      }
      groupLists[gi].list.push(i);
    }
    const kindGroups = groupLists.map((g) => ({
      kind: g.kind,
      indices: Int32Array.from(g.list),
    }));
    return {
      ids,
      n,
      xs,
      ys,
      toView,
      edgeSrc,
      edgeDst,
      kindGroups,
      grid: buildGrid(xs, ys, n),
      bounds: { minX, maxX, minY, maxY },
      edgeAlpha: Math.max(0.05, Math.min(0.55, 1500 / Math.max(1, edgeCount))),
    };
  }

  function pickNode(gx, gy, radius) {
    if (!view || view.n === 0) return -1;
    const cx0 = Math.floor((gx - radius) / GRID_CELL);
    const cx1 = Math.floor((gx + radius) / GRID_CELL);
    const cy0 = Math.floor((gy - radius) / GRID_CELL);
    const cy1 = Math.floor((gy + radius) / GRID_CELL);
    let best = -1;
    let bestD = radius * radius;
    for (let cx = cx0; cx <= cx1; cx++) {
      for (let cy = cy0; cy <= cy1; cy++) {
        const cell = view.grid.get(gridKey(cx, cy));
        if (!cell) continue;
        for (let j = 0; j < cell.length; j++) {
          const i = cell[j];
          const dx = view.xs[i] - gx;
          const dy = view.ys[i] - gy;
          const d = dx * dx + dy * dy;
          if (d <= bestD) {
            bestD = d;
            best = i;
          }
        }
      }
    }
    return best;
  }

  // ----- camera ---------------------------------------------------------------

  function toGraphX(sx) {
    return (sx - camera.tx) / camera.scale;
  }

  function toGraphY(sy) {
    return (sy - camera.ty) / camera.scale;
  }

  function availableWidth() {
    return panelEl && !panelEl.hidden
      ? Math.max(cssW - 400, cssW * 0.4)
      : cssW;
  }

  function fitCamera() {
    if (!view || view.n === 0) return;
    const pad = 60;
    const labelRoom = 150; // labels extend to the right of nodes
    const availW = availableWidth();
    const b = view.bounds;
    const bw = b.maxX - b.minX + pad * 2 + labelRoom;
    const bh = b.maxY - b.minY + pad * 2;
    let s = Math.min(availW / bw, cssH / bh);
    if (!Number.isFinite(s) || s <= 0) s = 1;
    s = Math.min(s, 1.2);
    camera.minScale = Math.min(0.05, s * 0.8);
    camera.scale = s;
    camera.tx = availW / 2 - ((b.minX + b.maxX) / 2 + labelRoom / 4) * s;
    camera.ty = cssH / 2 - ((b.minY + b.maxY) / 2) * s;
    autoFit = true;
    dirty = true;
  }

  function panTo(id) {
    const vi = view ? view.toView[id] : -1;
    if (vi < 0) return;
    autoFit = false;
    if (camera.scale < 0.75) camera.scale = Math.min(1, camera.maxScale);
    camera.tx = availableWidth() / 2 - view.xs[vi] * camera.scale;
    camera.ty = cssH / 2 - view.ys[vi] * camera.scale;
    dirty = true;
  }

  function zoomAt(mx, my, factor) {
    const old = camera.scale;
    const next = Math.min(camera.maxScale,
      Math.max(camera.minScale, old * factor));
    if (next === old) return;
    camera.tx = mx - (mx - camera.tx) * (next / old);
    camera.ty = my - (my - camera.ty) * (next / old);
    camera.scale = next;
    autoFit = false;
    dirty = true;
  }

  // ----- highlight state ------------------------------------------------------

  // 0 = nothing dimmed, 1 = search dimming, 2 = selection-neighborhood dimming.
  function dimModeNow() {
    if (searchQuery) return 1;
    if (selected >= 0) return 2;
    return 0;
  }

  function isLit(id, mode) {
    if (mode === 1) return matchFlags[id] === 1 || id === selected;
    if (mode === 2) return neighborFlags[id] === 1;
    return true;
  }

  function edgeClass(a, b, mode) {
    if (selected >= 0 && (a === selected || b === selected)) return 2;
    if (mode === 0) return 1;
    return isLit(a, mode) && isLit(b, mode) ? 1 : 0;
  }

  function recomputeNeighborhood() {
    neighborFlags.fill(0);
    if (selected < 0) return;
    neighborFlags[selected] = 1;
    const down = deps[selected];
    for (let j = 0; j < down.length; j++) neighborFlags[down[j]] = 1;
    const up = rev[selected];
    for (let j = 0; j < up.length; j++) neighborFlags[up[j]] = 1;
  }

  // ----- rendering ------------------------------------------------------------

  function render() {
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, cssW, cssH);
    if (!view || view.n === 0) return;
    const margin = 80;
    const gx0 = toGraphX(-margin);
    const gx1 = toGraphX(cssW + margin);
    const gy0 = toGraphY(-margin);
    const gy1 = toGraphY(cssH + margin);
    const mode = dimModeNow();
    drawEdges(mode, gx0, gy0, gx1, gy1);
    drawNodes(mode, gx0, gy0, gx1, gy1);
    drawRings();
    drawLabels(mode, gx0, gy0, gx1, gy1);
  }

  function drawEdges(mode, gx0, gy0, gx1, gy1) {
    const v = view;
    const total = v.edgeSrc.length;
    if (total === 0) return;
    const cheap = interacting && total > CHEAP_EDGE_THRESHOLD;
    const sc = camera.scale;
    const tx = camera.tx;
    const ty = camera.ty;
    const first = mode === 0 ? 1 : 0;
    const last = mode === 0 ? 1 : 2;
    for (let cls = first; cls <= last; cls++) {
      ctx.strokeStyle = edgeColors[cls];
      ctx.lineWidth = cls === 2 ? 1.6 : 1;
      ctx.beginPath();
      let any = false;
      for (let e = 0; e < total; e++) {
        const a = v.edgeSrc[e];
        const b = v.edgeDst[e];
        const x1 = v.xs[a];
        const y1 = v.ys[a];
        const x2 = v.xs[b];
        const y2 = v.ys[b];
        if ((x1 < gx0 && x2 < gx0) || (x1 > gx1 && x2 > gx1)
          || (y1 < gy0 && y2 < gy0) || (y1 > gy1 && y2 > gy1)) continue;
        if (edgeClass(v.ids[a], v.ids[b], mode) !== cls) continue;
        const sx1 = x1 * sc + tx;
        const sy1 = y1 * sc + ty;
        const sx2 = x2 * sc + tx;
        const sy2 = y2 * sc + ty;
        ctx.moveTo(sx1, sy1);
        if (cheap) ctx.lineTo(sx2, sy2);
        else ctx.quadraticCurveTo((sx1 + sx2) / 2, sy1, sx2, sy2);
        any = true;
      }
      if (any) ctx.stroke();
    }
  }

  function nodeScreenSize() {
    return Math.max(2.5, Math.min(16, NODE_SIZE * camera.scale));
  }

  function drawNodes(mode, gx0, gy0, gx1, gy1) {
    const v = view;
    const sc = camera.scale;
    const tx = camera.tx;
    const ty = camera.ty;
    const size = nodeScreenSize();
    const half = size / 2;
    const useRound = size >= 6 && typeof ctx.roundRect === 'function';
    const corner = size / 4;
    for (let pass = 0; pass < 2; pass++) {
      if (pass === 0 && mode === 0) continue; // no dim pass needed
      const wantDim = pass === 0;
      ctx.globalAlpha = wantDim ? 0.15 : 1;
      for (let g = 0; g < v.kindGroups.length; g++) {
        const group = v.kindGroups[g];
        ctx.fillStyle = theme.kinds[group.kind] || theme.muted;
        const list = group.indices;
        for (let j = 0; j < list.length; j++) {
          const i = list[j];
          const x = v.xs[i];
          const y = v.ys[i];
          if (x < gx0 || x > gx1 || y < gy0 || y > gy1) continue;
          const lit = mode === 0 || isLit(v.ids[i], mode);
          if (lit === wantDim) continue;
          const sx = x * sc + tx - half;
          const sy = y * sc + ty - half;
          if (useRound) {
            ctx.beginPath();
            ctx.roundRect(sx, sy, size, size, corner);
            ctx.fill();
          } else {
            ctx.fillRect(sx, sy, size, size);
          }
        }
      }
    }
    ctx.globalAlpha = 1;
  }

  function drawOneRing(id, color, grow, width) {
    const vi = view.toView[id];
    if (vi < 0) return;
    const sc = camera.scale;
    const sx = view.xs[vi] * sc + camera.tx;
    const sy = view.ys[vi] * sc + camera.ty;
    const r = nodeScreenSize() / 2 + grow;
    ctx.strokeStyle = color;
    ctx.lineWidth = width;
    ctx.beginPath();
    if (typeof ctx.roundRect === 'function') {
      ctx.roundRect(sx - r, sy - r, r * 2, r * 2, r / 2);
    } else {
      ctx.rect(sx - r, sy - r, r * 2, r * 2);
    }
    ctx.stroke();
  }

  function drawRings() {
    if (view === coneView && coneRoot >= 0) {
      drawOneRing(coneRoot, theme.accent, 6, 2);
    }
    if (selected >= 0) drawOneRing(selected, theme.accent, 3, 1.5);
    if (hoverId >= 0 && hoverId !== selected) {
      drawOneRing(hoverId, theme.muted, 3, 1);
    }
  }

  function drawLabels(mode, gx0, gy0, gx1, gy1) {
    const v = view;
    const effective = 10 * camera.scale;
    if (effective < 9) return;
    if (interacting && v.edgeSrc.length > CHEAP_EDGE_THRESHOLD) return;
    const sc = camera.scale;
    const tx = camera.tx;
    const ty = camera.ty;
    const offset = nodeScreenSize() / 2 + 5;
    ctx.font = Math.min(13, effective) + 'px ' + MONO;
    ctx.textBaseline = 'middle';
    ctx.textAlign = 'left';
    ctx.fillStyle = labelColor;
    // Labels extend right of their node, so a node just left of the viewport
    // may still own visible text: widen only the left cull bound.
    const labelGx0 = gx0 - MAX_LABEL_PX / sc;
    for (let i = 0; i < v.n; i++) {
      const x = v.xs[i];
      const y = v.ys[i];
      if (x < labelGx0 || x > gx1 || y < gy0 || y > gy1) continue;
      if (mode !== 0 && !isLit(v.ids[i], mode)) continue;
      ctx.fillText(labels[v.ids[i]], x * sc + tx + offset, y * sc + ty);
    }
  }

  let lastFrameAt = 0;

  function frame() {
    lastFrameAt = Date.now();
    if (dirty) {
      dirty = false;
      render();
    }
    requestAnimationFrame(frame);
  }

  // Fallback for contexts where requestAnimationFrame is throttled or
  // suspended (hidden/background tabs, some embedded webviews): keep dirty state
  // from going stale. A no-op whenever the rAF loop is running normally.
  setInterval(() => {
    if (dirty && Date.now() - lastFrameAt > 300) {
      dirty = false;
      render();
    }
  }, 250);

  // ----- tooltip --------------------------------------------------------------

  function positionTooltip(clientX, clientY) {
    const rect = viewportEl.getBoundingClientRect();
    let x = clientX - rect.left + 14;
    let y = clientY - rect.top + 14;
    const w = tooltipEl.offsetWidth;
    const h = tooltipEl.offsetHeight;
    if (x + w > rect.width - 8) x = Math.max(8, clientX - rect.left - w - 10);
    if (y + h > rect.height - 8) y = Math.max(8, clientY - rect.top - h - 10);
    tooltipEl.style.left = x + 'px';
    tooltipEl.style.top = y + 'px';
  }

  function showTooltip(id, clientX, clientY) {
    tooltipEl.textContent = '';
    tooltipEl.appendChild(elWith('span', 'tt-name', labels[id]));
    tooltipEl.appendChild(elWith('span', 'tt-kind', decls[id].kind || ''));
    tooltipEl.hidden = false;
    positionTooltip(clientX, clientY);
  }

  function hideTooltip() {
    tooltipEl.hidden = true;
  }

  // ----- side panel -----------------------------------------------------------

  function kindDotEl(kind) {
    const dot = elWith('span', 'kind-dot', null);
    if (KINDS.indexOf(kind) >= 0) dot.classList.add('k-' + kind);
    return dot;
  }

  function moduleSourcePath(moduleName) {
    return moduleName.replace(/\./g, '/') + '.lean';
  }

  function moduleDocsPath(moduleName) {
    return moduleName.replace(/\./g, '/') + '.html';
  }

  function appendDepSection(label, list) {
    panelBodyEl.appendChild(
      elWith('div', 'panel-h', label + ' (' + list.length + ')'));
    if (list.length === 0) {
      panelBodyEl.appendChild(
        elWith('div', 'panel-meta', 'none within this area'));
      return;
    }
    const ul = elWith('ul', 'dep-list', null);
    const appendRows = (from, to) => {
      for (let j = from; j < to; j++) {
        const target = list[j];
        const li = document.createElement('li');
        const btn = elWith('button', 'dep-link', null);
        btn.type = 'button';
        btn.appendChild(kindDotEl(decls[target].kind));
        btn.appendChild(document.createTextNode(shortName(names[target])));
        btn.addEventListener('click', () => {
          selectNode(target, { pan: true });
        });
        li.appendChild(btn);
        ul.appendChild(li);
      }
    };
    // Hub nodes can have thousands of dependents; cap the initial render.
    const initial = Math.min(list.length, DEP_LIST_INITIAL);
    appendRows(0, initial);
    if (list.length > initial) {
      const li = document.createElement('li');
      const more = elWith('button', 'dep-link dep-more',
        'Show all ' + list.length);
      more.type = 'button';
      more.addEventListener('click', () => {
        li.remove();
        appendRows(initial, list.length);
      });
      li.appendChild(more);
      ul.appendChild(li);
    }
    panelBodyEl.appendChild(ul);
  }

  // Cross-area references arrive as [areaIndex, declId, fullName] triples;
  // each row links into the owning area's graph page.
  function appendCrossSection(label, list) {
    if (!Array.isArray(list) || list.length === 0) return;
    panelBodyEl.appendChild(
      elWith('div', 'panel-h', label + ' (' + list.length + ')'));
    const ul = elWith('ul', 'dep-list', null);
    const appendRows = (from, to) => {
      for (let j = from; j < to; j++) {
        const entry = list[j];
        const area = areaNames[entry[0]] || '?';
        const li = document.createElement('li');
        const link = elWith('a', 'dep-link', null);
        link.href = '../' + encodeURIComponent(area) + '/index.html#d' + entry[1];
        link.appendChild(elWith('span', 'dep-area', area));
        link.appendChild(document.createTextNode(shortName(String(entry[2]))));
        li.appendChild(link);
        ul.appendChild(li);
      }
    };
    const initial = Math.min(list.length, DEP_LIST_INITIAL);
    appendRows(0, initial);
    if (list.length > initial) {
      const li = document.createElement('li');
      const more = elWith('button', 'dep-link dep-more',
        'Show all ' + list.length);
      more.type = 'button';
      more.addEventListener('click', () => {
        li.remove();
        appendRows(initial, list.length);
      });
      li.appendChild(more);
      ul.appendChild(li);
    }
    panelBodyEl.appendChild(ul);
  }

  function buildPanel(id) {
    const d = decls[id];
    panelBodyEl.textContent = '';

    const nameEl = elWith('h2', 'panel-name', d.name || '');
    if (d.private) {
      nameEl.appendChild(elWith('span', 'badge badge-private', 'private'));
    }
    panelBodyEl.appendChild(nameEl);

    const chips = elWith('div', 'panel-chips', null);
    const kindChip = elWith('span', 'kind-chip', null);
    kindChip.appendChild(kindDotEl(d.kind));
    kindChip.appendChild(document.createTextNode(d.kind || 'unknown'));
    chips.appendChild(kindChip);
    panelBodyEl.appendChild(chips);

    const moduleName = modules[d.module] || '';
    const lineText = d.endLine && d.endLine !== d.line
      ? d.line + '–' + d.endLine
      : String(d.line);
    panelBodyEl.appendChild(
      elWith('div', 'panel-meta', moduleName + ':' + lineText));

    const links = elWith('div', 'panel-links', null);
    const src = elWith('a', null, 'source');
    src.href = GITHUB_BLOB + encodeURIComponent(commit) + '/'
      + moduleSourcePath(moduleName)
      + '#L' + d.line + '-L' + (d.endLine || d.line);
    src.target = '_blank';
    src.rel = 'noopener';
    links.appendChild(src);
    if (!d.full) {
      const docs = elWith('a', null, 'API docs');
      docs.href = '../../../docs/' + moduleDocsPath(moduleName) + '#' + d.name;
      docs.target = '_blank';
      docs.rel = 'noopener';
      links.appendChild(docs);
    }
    panelBodyEl.appendChild(links);

    if (typeof d.ext === 'number' && d.ext > 0) {
      panelBodyEl.appendChild(elWith('div', 'panel-meta',
        'uses ' + d.ext + ' declaration' + (d.ext === 1 ? '' : 's')
        + ' from Mathlib/core'));
    }
    if (typeof d.gdepth === 'number') {
      panelBodyEl.appendChild(elWith('div', 'panel-meta',
        'depth ' + d.gdepth + ' in the whole library'));
    }

    const actions = elWith('div', 'panel-actions', null);
    const coneBtn = elWith('button', 'btn btn-accent', 'Dependency cone');
    coneBtn.type = 'button';
    coneBtn.addEventListener('click', () => {
      setHash('cone=' + id);
    });
    actions.appendChild(coneBtn);
    panelBodyEl.appendChild(actions);

    if (d.doc) {
      const doc = elWith('div', 'panel-doc', null);
      const parts = String(d.doc).split(/\n\s*\n/);
      for (const part of parts) {
        const trimmed = part.trim();
        if (!trimmed) continue;
        const paragraph = elWith('p', null, null);
        appendRich(paragraph, trimmed);
        doc.appendChild(paragraph);
      }
      panelBodyEl.appendChild(doc);
    }

    if (d.statement) {
      panelBodyEl.appendChild(elWith('pre', 'statement', d.statement));
    }

    appendDepSection('Uses', deps[id]);
    appendCrossSection('Uses from other areas', d.xdeps);
    appendDepSection('Used by', rev[id]);
    appendCrossSection('Used by other areas', d.xrev);
    panelBodyEl.scrollTop = 0;
  }

  // ----- selection ------------------------------------------------------------

  function selectNode(id, opts) {
    const options = opts || {};
    if (id < 0 || id >= N) return;
    if (view === coneView && coneView && coneView.toView[id] < 0) {
      // The target sits outside the cone: fall back to the full graph.
      exitCone(false);
    }
    selected = id;
    recomputeNeighborhood();
    buildPanel(id);
    panelEl.hidden = false;
    if (options.pan) panTo(id);
    if (options.hash !== false && view === fullView) setHash('d' + id);
    dirty = true;
  }

  function deselect(updateHash) {
    if (selected < 0) return;
    selected = -1;
    neighborFlags.fill(0);
    panelEl.hidden = true;
    dirty = true;
    if (updateHash && view === fullView) clearHash();
  }

  // ----- dependency cone --------------------------------------------------------

  // Marks everything reachable from `start` via `adjacency` (excluding start);
  // returns the count.
  function reachableSet(start, adjacency, flags) {
    const seen = new Uint8Array(N);
    seen[start] = 1;
    const stack = [start];
    let count = 0;
    while (stack.length) {
      const v = stack.pop();
      const list = adjacency[v];
      for (let j = 0; j < list.length; j++) {
        const w = list[j];
        if (!seen[w]) {
          seen[w] = 1;
          flags[w] = 1;
          count++;
          stack.push(w);
        }
      }
    }
    return count;
  }

  // Iterative Tarjan SCC over a view-local adjacency (arrays of ints).
  function tarjanScc(n, adj) {
    const index = new Int32Array(n).fill(-1);
    const low = new Int32Array(n);
    const onStack = new Uint8Array(n);
    const sccId = new Int32Array(n).fill(-1);
    const stack = [];
    const callStack = [];
    const iterStack = [];
    let counter = 0;
    let count = 0;
    for (let root = 0; root < n; root++) {
      if (index[root] !== -1) continue;
      callStack.push(root);
      iterStack.push(0);
      while (callStack.length) {
        const v = callStack[callStack.length - 1];
        if (iterStack[iterStack.length - 1] === 0 && index[v] === -1) {
          index[v] = counter;
          low[v] = counter;
          counter++;
          stack.push(v);
          onStack[v] = 1;
        }
        const edges = adj[v];
        let i = iterStack[iterStack.length - 1];
        let advanced = false;
        while (i < edges.length) {
          const w = edges[i];
          if (index[w] === -1) {
            iterStack[iterStack.length - 1] = i + 1;
            callStack.push(w);
            iterStack.push(0);
            advanced = true;
            break;
          }
          if (onStack[w] && index[w] < low[v]) low[v] = index[w];
          i++;
        }
        if (advanced) continue;
        callStack.pop();
        iterStack.pop();
        if (low[v] === index[v]) {
          for (;;) {
            const w = stack.pop();
            onStack[w] = 0;
            sccId[w] = count;
            if (w === v) break;
          }
          count++;
        }
        if (callStack.length) {
          const parent = callStack[callStack.length - 1];
          if (low[v] < low[parent]) low[parent] = low[v];
        }
      }
    }
    return { id: sccId, count };
  }

  // Longest-path layering of the subgraph induced by `ids`, with SCCs
  // condensed (every member of an SCC shares the layer). Within-layer order
  // follows the original shard `order`.
  function layerSubgraph(ids) {
    const n = ids.length;
    const local = new Int32Array(N).fill(-1);
    for (let i = 0; i < n; i++) local[ids[i]] = i;
    const adj = new Array(n); // dependency -> dependent
    for (let i = 0; i < n; i++) adj[i] = [];
    for (let i = 0; i < n; i++) {
      const list = deps[ids[i]];
      for (let j = 0; j < list.length; j++) {
        const s = local[list[j]];
        if (s >= 0 && s !== i) adj[s].push(i);
      }
    }
    const scc = tarjanScc(n, adj);
    const sccAdj = new Array(scc.count);
    for (let s = 0; s < scc.count; s++) sccAdj[s] = [];
    const indegree = new Int32Array(scc.count);
    for (let u = 0; u < n; u++) {
      const out = adj[u];
      const su = scc.id[u];
      for (let j = 0; j < out.length; j++) {
        const sv = scc.id[out[j]];
        if (su !== sv) {
          sccAdj[su].push(sv);
          indegree[sv]++;
        }
      }
    }
    const sccLayer = new Int32Array(scc.count);
    const queue = [];
    for (let s = 0; s < scc.count; s++) if (indegree[s] === 0) queue.push(s);
    let qi = 0;
    while (qi < queue.length) {
      const s = queue[qi++];
      const out = sccAdj[s];
      for (let j = 0; j < out.length; j++) {
        const t = out[j];
        if (sccLayer[s] + 1 > sccLayer[t]) sccLayer[t] = sccLayer[s] + 1;
        indegree[t]--;
        if (indegree[t] === 0) queue.push(t);
      }
    }
    const layerOf = new Int32Array(n);
    let maxLayer = 0;
    for (let i = 0; i < n; i++) {
      layerOf[i] = sccLayer[scc.id[i]];
      if (layerOf[i] > maxLayer) maxLayer = layerOf[i];
    }
    const byLayer = new Array(maxLayer + 1);
    for (let L = 0; L <= maxLayer; L++) byLayer[L] = [];
    for (let i = 0; i < n; i++) byLayer[layerOf[i]].push(i);
    const orderOf = new Int32Array(n);
    const layerSizes = new Array(maxLayer + 1).fill(0);
    for (let L = 0; L <= maxLayer; L++) {
      const members = byLayer[L];
      members.sort((a, b) => {
        const oa = (decls[ids[a]].order || 0) - (decls[ids[b]].order || 0);
        return oa !== 0 ? oa : ids[a] - ids[b];
      });
      layerSizes[L] = members.length;
      for (let j = 0; j < members.length; j++) orderOf[members[j]] = j;
    }
    return { layerOf, orderOf, layerSizes };
  }

  function enterCone(id) {
    if (id < 0 || id >= N) return;
    if (view === coneView && coneRoot === id) {
      if (selected !== id) selectNode(id, { hash: false });
      return;
    }
    const ancFlags = new Uint8Array(N);
    const descFlags = new Uint8Array(N);
    const ancestors = reachableSet(id, deps, ancFlags);
    const descendants = reachableSet(id, rev, descFlags);
    const memberList = [];
    for (let i = 0; i < N; i++) {
      if (i === id || ancFlags[i] || descFlags[i]) memberList.push(i);
    }
    const ids = Int32Array.from(memberList);
    const layered = layerSubgraph(ids);
    coneView = buildView(ids, layered.layerOf, layered.orderOf,
      layered.layerSizes);
    coneRoot = id;
    view = coneView;
    breadcrumbEl.hidden = false;
    coneBackEl.href = '#d' + id;
    coneLabelEl.textContent = ' · cone of ' + shortName(names[id]) + ': '
      + ancestors + ' ancestor' + (ancestors === 1 ? '' : 's')
      + ' · ' + descendants + ' descendant'
      + (descendants === 1 ? '' : 's')
      + ' within this area';
    updateDerivedColors();
    recomputeMatches();
    selected = id;
    recomputeNeighborhood();
    buildPanel(id);
    panelEl.hidden = false;
    hoverId = -1;
    hideTooltip();
    fitCamera();
    dirty = true;
  }

  function exitCone(updateHash) {
    const wasCone = view === coneView && coneView !== null;
    coneView = null;
    coneRoot = -1;
    if (!wasCone) return;
    view = fullView;
    breadcrumbEl.hidden = true;
    hoverId = -1;
    hideTooltip();
    updateDerivedColors();
    recomputeMatches();
    fitCamera();
    dirty = true;
    if (updateHash) {
      if (selected >= 0) setHash('d' + selected);
      else clearHash();
    }
  }

  // ----- main-results cards / mode switching ----------------------------------

  let highlights = []; // shard-local ids, best first; [] => graph-only page

  // graphMode=false shows the card view, true the graph. The canvas sizes
  // itself when revealed: the ResizeObserver fires and refits (or re-pans to
  // the selection) via resizeCanvas's stale-size handling.
  function setMode(graphMode) {
    document.body.classList.toggle('mode-hl', !graphMode);
    if (graphMode) dirty = true;
  }

  function firstParagraph(text) {
    const parts = String(text).split(/\n\s*\n/);
    for (const part of parts) {
      const trimmed = part.trim();
      if (trimmed) return trimmed;
    }
    return '';
  }

  // Docstring rendering: `backtick` spans become <code>, **double-starred**
  // spans become <strong>. Built from text nodes only, so no HTML in
  // docstrings is ever interpreted; unbalanced markers fall back to plain
  // text.
  function appendCode(parent, text) {
    const pieces = text.split('`');
    if (pieces.length % 2 === 0) {
      parent.appendChild(document.createTextNode(text));
      return;
    }
    for (let i = 0; i < pieces.length; i++) {
      if (!pieces[i]) continue;
      if (i % 2 === 1) parent.appendChild(elWith('code', null, pieces[i]));
      else parent.appendChild(document.createTextNode(pieces[i]));
    }
  }

  function appendRich(parent, text) {
    const pieces = text.split('**');
    if (pieces.length % 2 === 0) {
      appendCode(parent, text);
      return;
    }
    for (let i = 0; i < pieces.length; i++) {
      if (!pieces[i]) continue;
      if (i % 2 === 1) {
        const strong = elWith('strong', null, null);
        appendCode(strong, pieces[i]);
        parent.appendChild(strong);
      } else {
        appendCode(parent, pieces[i]);
      }
    }
  }

  function buildHighlightCard(id) {
    const d = decls[id];
    const card = elWith('article', 'hl-card', null);
    const name = elWith('a', 'hl-name', labels[id]);
    name.href = '#d' + id;
    card.appendChild(name);

    const meta = elWith('div', 'hl-meta', null);
    const kindChip = elWith('span', 'kind-chip', null);
    kindChip.appendChild(kindDotEl(d.kind));
    kindChip.appendChild(document.createTextNode(d.kind || ''));
    meta.appendChild(kindChip);
    meta.appendChild(elWith('span', null,
      'depth ' + (d.gdepth || 0) + ' in the library'));
    const uses = rev[id].length + (Array.isArray(d.xrev) ? d.xrev.length : 0);
    meta.appendChild(elWith('span', null,
      uses === 0 ? 'nothing builds on it yet'
        : 'used by ' + uses + ' declaration' + (uses === 1 ? '' : 's')));
    card.appendChild(meta);

    if (d.doc) {
      const doc = elWith('p', 'hl-doc', null);
      appendRich(doc, firstParagraph(d.doc));
      card.appendChild(doc);
    }
    if (d.statement) card.appendChild(elWith('pre', 'statement', d.statement));

    const links = elWith('div', 'hl-links', null);
    const graphLink = elWith('a', null, 'view in graph');
    graphLink.href = '#d' + id;
    links.appendChild(graphLink);
    const moduleName = modules[d.module] || '';
    const src = elWith('a', null, 'source');
    src.href = GITHUB_BLOB + encodeURIComponent(commit) + '/'
      + moduleSourcePath(moduleName)
      + '#L' + d.line + '-L' + (d.endLine || d.line);
    src.target = '_blank';
    src.rel = 'noopener';
    links.appendChild(src);
    if (!d.full) {
      const docsLink = elWith('a', null, 'API docs');
      docsLink.href = '../../../docs/' + moduleDocsPath(moduleName)
        + '#' + d.name;
      docsLink.target = '_blank';
      docsLink.rel = 'noopener';
      links.appendChild(docsLink);
    }
    card.appendChild(links);
    return card;
  }

  function buildHighlights() {
    if (!hlGridEl) return;
    hlGridEl.textContent = '';
    if (hlSubEl) {
      hlSubEl.textContent = 'the ' + highlights.length + ' most notable of '
        + N + ' declarations — picked by depth, documentation, and use';
    }
    if (highlights.length === 0) {
      hlGridEl.appendChild(elWith('div', 'hl-empty',
        'No documented theorems to feature in this area yet.'));
      return;
    }
    for (const id of highlights) hlGridEl.appendChild(buildHighlightCard(id));
  }

  // ----- search ---------------------------------------------------------------

  function updateSearchCount() {
    if (!searchCountEl) return;
    if (!searchQuery) {
      searchCountEl.textContent = '';
      return;
    }
    searchCountEl.textContent = matchTotal
      + (matchTotal === 1 ? ' match' : ' matches');
  }

  function recomputeMatches() {
    if (!matchFlags) return;
    matchFlags.fill(0);
    matchTotal = 0;
    firstMatch = -1;
    if (searchQuery && view) {
      for (let i = 0; i < view.n; i++) {
        const id = view.ids[i];
        if (lowerNames[id].indexOf(searchQuery) >= 0) {
          matchFlags[id] = 1;
          matchTotal++;
          if (firstMatch < 0) firstMatch = id;
        }
      }
    }
    updateSearchCount();
    dirty = true;
  }

  // ----- hash routing -----------------------------------------------------------

  function setHash(fragment) {
    if (location.hash === '#' + fragment) return;
    location.hash = fragment;
  }

  function clearHash() {
    if (!location.hash) return;
    history.pushState(null, '', location.pathname + location.search);
  }

  function applyHash() {
    if (N === 0) return;
    const h = location.hash;
    if (h === '#graph') {
      setMode(true);
      return;
    }
    let m = /^#cone=(\d+)$/.exec(h);
    if (m) {
      const id = Number(m[1]);
      if (id >= 0 && id < N) {
        setMode(true);
        enterCone(id);
        return;
      }
    }
    m = /^#d(\d+)$/.exec(h);
    if (m) {
      const id = Number(m[1]);
      if (id >= 0 && id < N) {
        setMode(true);
        if (view === coneView && coneView) exitCone(false);
        if (selected !== id) selectNode(id, { pan: true, hash: false });
        return;
      }
    }
    if (view === coneView && coneView) exitCone(false);
    deselect(false);
    // Only real navigation lands here (in-app hash clearing uses pushState,
    // which fires no hashchange): browser-back to an empty hash returns to
    // the cards when the area has any.
    if (highlights.length > 0) setMode(false);
  }

  // ----- pointer / wheel / keyboard interaction ---------------------------------

  let pointerActive = false;
  let pointerMoved = false;
  let lastX = 0;
  let lastY = 0;
  let downX = 0;
  let downY = 0;

  function pickAtEvent(ev) {
    const rect = canvas.getBoundingClientRect();
    const gx = toGraphX(ev.clientX - rect.left);
    const gy = toGraphY(ev.clientY - rect.top);
    return pickNode(gx, gy, 10 / camera.scale + NODE_SIZE / 2);
  }

  function updateHover(ev) {
    const vi = pickAtEvent(ev);
    const id = vi >= 0 ? view.ids[vi] : -1;
    if (id !== hoverId) {
      hoverId = id;
      dirty = true;
      canvas.style.cursor = id >= 0 ? 'pointer' : '';
      if (id >= 0) showTooltip(id, ev.clientX, ev.clientY);
      else hideTooltip();
    } else if (id >= 0) {
      positionTooltip(ev.clientX, ev.clientY);
    }
  }

  canvas.addEventListener('pointerdown', (ev) => {
    if (ev.button !== 0) return;
    pointerActive = true;
    pointerMoved = false;
    interacting = true;
    lastX = downX = ev.clientX;
    lastY = downY = ev.clientY;
    try {
      canvas.setPointerCapture(ev.pointerId);
    } catch (ignored) { /* older engines */ }
  });

  canvas.addEventListener('pointermove', (ev) => {
    if (pointerActive) {
      const dx = ev.clientX - lastX;
      const dy = ev.clientY - lastY;
      lastX = ev.clientX;
      lastY = ev.clientY;
      if (Math.abs(ev.clientX - downX) + Math.abs(ev.clientY - downY) > 4) {
        pointerMoved = true;
        viewportEl.classList.add('dragging');
        hideTooltip();
      }
      if (pointerMoved) {
        camera.tx += dx;
        camera.ty += dy;
        autoFit = false;
        dirty = true;
      }
    } else if (view) {
      updateHover(ev);
    }
  });

  function endPointer(ev, wasClick) {
    if (!pointerActive) return;
    pointerActive = false;
    interacting = false;
    viewportEl.classList.remove('dragging');
    dirty = true;
    if (wasClick && !pointerMoved && view) {
      const vi = pickAtEvent(ev);
      if (vi >= 0) selectNode(view.ids[vi], {});
      else deselect(true);
    }
  }

  canvas.addEventListener('pointerup', (ev) => endPointer(ev, true));
  canvas.addEventListener('pointercancel', (ev) => endPointer(ev, false));
  canvas.addEventListener('pointerleave', () => {
    if (!pointerActive) {
      hoverId = -1;
      hideTooltip();
      canvas.style.cursor = '';
      dirty = true;
    }
  });

  canvas.addEventListener('wheel', (ev) => {
    ev.preventDefault();
    const rect = canvas.getBoundingClientRect();
    const unit = ev.deltaMode === 1 ? 0.045 : 0.0015;
    zoomAt(ev.clientX - rect.left, ev.clientY - rect.top,
      Math.exp(-ev.deltaY * unit));
    interacting = true;
    clearTimeout(wheelTimer);
    wheelTimer = setTimeout(() => {
      interacting = false;
      dirty = true;
    }, 160);
  }, { passive: false });

  canvas.addEventListener('dblclick', (ev) => {
    if (view && pickAtEvent(ev) < 0) fitCamera();
  });

  document.addEventListener('keydown', (ev) => {
    if (ev.key === 'Escape' && ev.target === document.body) deselect(true);
  });

  if (searchInputEl) {
    searchInputEl.addEventListener('input', () => {
      searchQuery = searchInputEl.value.trim().toLowerCase();
      recomputeMatches();
    });
    searchInputEl.addEventListener('keydown', (ev) => {
      if (ev.key === 'Enter') {
        if (firstMatch >= 0) selectNode(firstMatch, { pan: true });
      } else if (ev.key === 'Escape') {
        searchInputEl.value = '';
        searchQuery = '';
        recomputeMatches();
        searchInputEl.blur();
      }
    });
  }

  if (fitButtonEl) fitButtonEl.addEventListener('click', () => fitCamera());
  if (panelCloseEl) panelCloseEl.addEventListener('click', () => deselect(true));
  if (hlExploreEl) {
    hlExploreEl.addEventListener('click', () => {
      // setHash no-ops when the hash is already #graph; switch directly then.
      if (location.hash === '#graph') setMode(true);
      else setHash('graph');
    });
  }
  if (hlBackEl) {
    hlBackEl.addEventListener('click', () => {
      if (view === coneView && coneView) exitCone(false);
      deselect(false);
      clearHash();
      setMode(false);
    });
  }
  window.addEventListener('hashchange', applyHash);

  // ----- resize wiring --------------------------------------------------------

  function resizeCanvas() {
    const rect = viewportEl.getBoundingClientRect();
    const w = Math.max(1, Math.round(rect.width));
    const h = Math.max(1, Math.round(rect.height));
    const stale = cssW <= 1 || cssH <= 1;
    const changed = w !== cssW || h !== cssH;
    cssW = w;
    cssH = h;
    dpr = window.devicePixelRatio || 1;
    canvas.width = Math.max(1, Math.round(cssW * dpr));
    canvas.height = Math.max(1, Math.round(cssH * dpr));
    // Keep the graph fitted across viewport changes until the user takes
    // over the camera (also heals a fit computed before layout settled).
    if (changed && view) {
      if (autoFit) fitCamera();
      else if (stale && selected >= 0) panTo(selected);
    }
    dirty = true;
  }

  if (typeof ResizeObserver === 'function') {
    new ResizeObserver(resizeCanvas).observe(viewportEl);
  }
  window.addEventListener('resize', resizeCanvas);

  // ----- info strip ---------------------------------------------------------------

  function fillInfoStrip(json) {
    if (titleEl) titleEl.textContent = json.area || slug;
    const stats = json.stats || {};
    if (statsEl) {
      const nodes = stats.nodes !== undefined ? stats.nodes : N;
      const edges = stats.edges !== undefined ? stats.edges : 0;
      const cross = (stats.xout || 0) + (stats.xin || 0);
      const maxDepth = stats.maxDepth !== undefined ? stats.maxDepth : 0;
      const avgDepth = stats.avgDepth !== undefined ? stats.avgDepth : 0;
      statsEl.textContent = nodes + ' nodes · ' + edges
        + ' edges · ' + cross + ' cross-area link' + (cross === 1 ? '' : 's')
        + ' · max depth ' + maxDepth + ' · avg depth ' + avgDepth;
    }
    if (legendEl) {
      legendEl.textContent = '';
      const counts = stats.kinds || {};
      const known = new Set(KINDS);
      const ordered = KINDS.filter((k) => counts[k])
        .concat(Object.keys(counts).filter((k) => !known.has(k)));
      for (const kind of ordered) {
        const chip = elWith('span', 'kind-chip', null);
        chip.appendChild(kindDotEl(kind));
        chip.appendChild(document.createTextNode(kind + ' ' + counts[kind]));
        legendEl.appendChild(chip);
      }
    }
  }

  // ----- data load ----------------------------------------------------------------

  function showMessage(text) {
    messageEl.textContent = text;
    messageEl.hidden = false;
  }

  function computeLayerSizes(layerOf) {
    let max = 0;
    for (let i = 0; i < layerOf.length; i++) {
      if (layerOf[i] > max) max = layerOf[i];
    }
    const sizes = new Array(max + 1).fill(0);
    for (let i = 0; i < layerOf.length; i++) sizes[layerOf[i]]++;
    return sizes;
  }

  function initData(json) {
    decls = Array.isArray(json.decls) ? json.decls : [];
    modules = Array.isArray(json.modules) ? json.modules : [];
    areaNames = Array.isArray(json.areas) ? json.areas : [];
    commit = json.commit || 'main';
    N = decls.length;
    fillInfoStrip(json);
    // The info strip just changed the viewport height; remeasure before the
    // initial fit/hash-driven pan so deep links center correctly.
    resizeCanvas();
    if (N === 0) {
      showMessage('This area has no declarations to display.');
      return;
    }
    names = new Array(N);
    labels = new Array(N);
    lowerNames = new Array(N);
    nodeKinds = new Array(N);
    deps = new Array(N);
    for (let i = 0; i < N; i++) {
      const d = decls[i];
      names[i] = d.name || '#' + i;
      labels[i] = shortName(names[i]);
      lowerNames[i] = names[i].toLowerCase();
      nodeKinds[i] = d.kind || 'def';
      const raw = Array.isArray(d.deps) ? d.deps : [];
      const cleaned = [];
      for (let j = 0; j < raw.length; j++) {
        const t = raw[j];
        if (typeof t === 'number' && t >= 0 && t < N) cleaned.push(t);
      }
      deps[i] = Int32Array.from(cleaned);
    }
    const revCounts = new Int32Array(N);
    for (let i = 0; i < N; i++) {
      const list = deps[i];
      for (let j = 0; j < list.length; j++) revCounts[list[j]]++;
    }
    rev = new Array(N);
    for (let i = 0; i < N; i++) rev[i] = new Int32Array(revCounts[i]);
    const cursor = new Int32Array(N);
    for (let i = 0; i < N; i++) {
      const list = deps[i];
      for (let j = 0; j < list.length; j++) {
        const t = list[j];
        rev[t][cursor[t]] = i;
        cursor[t]++;
      }
    }
    matchFlags = new Uint8Array(N);
    neighborFlags = new Uint8Array(N);
    const idsAll = new Int32Array(N);
    const layerOf = new Int32Array(N);
    const orderOf = new Int32Array(N);
    for (let i = 0; i < N; i++) {
      idsAll[i] = i;
      layerOf[i] = decls[i].layer || 0;
      orderOf[i] = decls[i].order || 0;
    }
    const layerSizes = Array.isArray(json.layers) && json.layers.length > 0
      ? json.layers
      : computeLayerSizes(layerOf);
    fullView = buildView(idsAll, layerOf, orderOf, layerSizes);
    view = fullView;
    updateDerivedColors();
    messageEl.hidden = true;
    fitCamera();
    const rawHighlights = Array.isArray(json.hl) ? json.hl : [];
    highlights = [];
    for (const value of rawHighlights) {
      if (typeof value === 'number' && value >= 0 && value < N) {
        highlights.push(value);
      }
    }
    buildHighlights();
    if (hlBackEl) hlBackEl.hidden = highlights.length === 0;
    if (highlights.length === 0) setMode(true);
    applyHash();
    dirty = true;
  }

  function loadShard() {
    showMessage('Loading…');
    if (hlGridEl) {
      hlGridEl.textContent = '';
      hlGridEl.appendChild(elWith('div', 'hl-empty', 'Loading…'));
    }
    fetch('../../data/areas/' + encodeURIComponent(slug) + '.json')
      .then((response) => {
        if (!response.ok) throw new Error('HTTP ' + response.status);
        return response.json();
      })
      .then((json) => {
        initData(json);
      })
      .catch((error) => {
        const text = 'Could not load the data for “' + slug
          + '” — data/areas/' + slug + '.json failed to load ('
          + error.message + ').';
        showMessage(text); // the graph-mode surface…
        if (hlGridEl) { // …and the card-mode surface
          hlGridEl.textContent = '';
          hlGridEl.appendChild(elWith('div', 'hl-empty', text));
        }
      });
  }

  // ----- boot ---------------------------------------------------------------------

  readTheme();
  updateDerivedColors();
  resizeCanvas();
  // Deep links (cross-area references, shared URLs) open the graph directly;
  // everything else starts on the main-results cards.
  if (/^#(d\d+|cone=\d+|graph)$/.test(location.hash)) setMode(true);
  loadShard();
  requestAnimationFrame(frame);
})();
