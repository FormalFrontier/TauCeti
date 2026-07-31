/* Landing page for the Tau Ceti exposition.
 *
 * Fetches data/index.json (relative to the exposition root) and renders:
 *   - stat tiles (areas / declarations / edges / deepest chain),
 *   - a segmented kind-breakdown bar with a legend,
 *   - the area dependency map (layered SVG: an arrow from A to B means
 *     declarations in A depend on declarations in B),
 *   - a sortable, filterable area table,
 *   - a "generated … · commit …" footer.
 *
 * Adapted from Lean Pool's exposition landing script (Vasily Ilin,
 * https://github.com/Vilin97/lean-pool, Apache 2.0); the area map is new
 * here — Lean Pool's projects are independent, Tau Ceti's areas are not.
 */
(function () {
  "use strict";

  const CANONICAL_KINDS = [
    "theorem", "lemma", "def", "abbrev", "instance",
    "structure", "class", "inductive", "axiom", "opaque",
  ];

  const COLUMNS = [
    { key: "area", label: "Area", numeric: false },
    { key: "nodes", label: "Decls", numeric: true },
    { key: "edges", label: "Edges", numeric: true },
    { key: "xout", label: "Uses", numeric: true },
    { key: "xin", label: "Used by", numeric: true },
    { key: "maxDepth", label: "Max depth", numeric: true },
    { key: "avgDepth", label: "Avg depth", numeric: true },
  ];

  // Default sort: declaration count, largest first.
  const state = { column: "nodes", descending: true, filter: "" };
  let areas = [];

  function element(id) {
    return document.getElementById(id);
  }

  function formatCount(value) {
    return Number(value).toLocaleString("en-US");
  }

  function kindColor(kind) {
    return CANONICAL_KINDS.includes(kind) ? `var(--kind-${kind})` : "var(--muted)";
  }

  // ---------- stat tiles ----------

  function renderTiles(totals) {
    const tiles = [
      ["Areas", totals.areas],
      ["Declarations", totals.decls],
      ["Dependency edges", totals.edges],
      ["Deepest chain", totals.maxDepth],
    ];
    const box = element("statTiles");
    for (const [label, value] of tiles) {
      const tile = document.createElement("div");
      tile.className = "stat-tile";
      const valueEl = document.createElement("div");
      valueEl.className = "stat-value";
      valueEl.textContent = formatCount(value);
      const labelEl = document.createElement("div");
      labelEl.className = "stat-label";
      labelEl.textContent = label;
      tile.append(valueEl, labelEl);
      box.appendChild(tile);
    }
    box.hidden = false;
  }

  // ---------- kind breakdown bar ----------

  function renderKindBreakdown(kinds) {
    const entries = Object.entries(kinds || {})
      .filter(([, count]) => count > 0)
      .sort((a, b) => b[1] - a[1]);
    if (entries.length === 0) return;
    const total = entries.reduce((sum, [, count]) => sum + count, 0);

    const bar = element("kindBar");
    const legend = element("kindLegend");
    for (const [kind, count] of entries) {
      const segment = document.createElement("div");
      segment.className = "kind-seg";
      segment.style.flexGrow = String(count);
      segment.style.background = kindColor(kind);
      const pct = ((100 * count) / total).toFixed(1);
      segment.title = `${kind} — ${formatCount(count)} (${pct}%)`;
      bar.appendChild(segment);

      const item = document.createElement("span");
      item.className = "legend-item";
      const dot = document.createElement("span");
      dot.className = "legend-dot";
      dot.style.background = kindColor(kind);
      const name = document.createElement("span");
      name.textContent = kind;
      const countEl = document.createElement("span");
      countEl.className = "legend-count";
      countEl.textContent = formatCount(count);
      item.append(dot, name, countEl);
      legend.appendChild(item);
    }
    element("kindBreakdown").hidden = false;
  }

  // ---------- area dependency map ----------

  const SVG_NS = "http://www.w3.org/2000/svg";
  const BOX_W = 168;
  const BOX_H = 42;
  const COL_GAP = 72;
  const ROW_GAP = 14;
  const MAP_PAD = 24;

  // Longest-path layers of the area graph with SCCs collapsed (areas can
  // depend on each other in cycles). Small n: recursion-free but simple.
  function areaLayers(count, dependencies) {
    // Tarjan SCC, iterative.
    const index = new Int32Array(count).fill(-1);
    const low = new Int32Array(count);
    const onStack = new Uint8Array(count);
    const sccOf = new Int32Array(count).fill(-1);
    const stack = [];
    let counter = 0;
    let sccCount = 0;
    for (let root = 0; root < count; root++) {
      if (index[root] !== -1) continue;
      const call = [root];
      const iter = [0];
      while (call.length) {
        const v = call[call.length - 1];
        if (iter[iter.length - 1] === 0 && index[v] === -1) {
          index[v] = low[v] = counter++;
          stack.push(v);
          onStack[v] = 1;
        }
        const edges = dependencies[v];
        let i = iter[iter.length - 1];
        let advanced = false;
        while (i < edges.length) {
          const w = edges[i];
          if (index[w] === -1) {
            iter[iter.length - 1] = i + 1;
            call.push(w);
            iter.push(0);
            advanced = true;
            break;
          }
          if (onStack[w] && index[w] < low[v]) low[v] = index[w];
          i++;
        }
        if (advanced) continue;
        call.pop();
        iter.pop();
        if (low[v] === index[v]) {
          for (;;) {
            const w = stack.pop();
            onStack[w] = 0;
            sccOf[w] = sccCount;
            if (w === v) break;
          }
          sccCount++;
        }
        if (call.length) {
          const parent = call[call.length - 1];
          if (low[v] < low[parent]) low[parent] = low[v];
        }
      }
    }
    // Tarjan emits dependencies-first, so a single pass suffices.
    const sccLayer = new Int32Array(sccCount);
    for (let v = 0; v < count; v++) {
      for (const w of dependencies[v]) {
        if (sccOf[w] !== sccOf[v]) {
          sccLayer[sccOf[v]] = Math.max(sccLayer[sccOf[v]], sccLayer[sccOf[w]] + 1);
        }
      }
    }
    return Array.from(sccOf, (s) => sccLayer[s]);
  }

  function renderAreaMap(rows, areaEdges) {
    if (!rows.length) return;
    const n = rows.length;
    const deps = Array.from({ length: n }, () => []);
    const edges = [];
    for (const [from, to, count] of areaEdges || []) {
      if (from >= 0 && from < n && to >= 0 && to < n && from !== to) {
        deps[from].push(to);
        edges.push({ from, to, count });
      }
    }
    const layers = areaLayers(n, deps);
    const layerCount = Math.max(...layers) + 1;

    // Rows within a column: two barycenter sweeps over dependency positions,
    // starting from an alphabetical order.
    const columns = Array.from({ length: layerCount }, () => []);
    rows.forEach((_, i) => columns[layers[i]].push(i));
    const rowOf = new Array(n).fill(0);
    for (const members of columns) {
      members.sort((a, b) => rows[a].slug.localeCompare(rows[b].slug));
      members.forEach((m, r) => { rowOf[m] = r; });
    }
    const neighbors = Array.from({ length: n }, () => []);
    for (const e of edges) {
      neighbors[e.from].push(e.to);
      neighbors[e.to].push(e.from);
    }
    for (let sweep = 0; sweep < 2; sweep++) {
      for (const members of columns) {
        members.sort((a, b) => {
          const bary = (v) => neighbors[v].length
            ? neighbors[v].reduce((s, w) => s + rowOf[w], 0) / neighbors[v].length
            : rowOf[v];
          const d = bary(a) - bary(b);
          return d !== 0 ? d : rows[a].slug.localeCompare(rows[b].slug);
        });
        members.forEach((m, r) => { rowOf[m] = r; });
      }
    }

    const tallest = Math.max(...columns.map((c) => c.length));
    const width = MAP_PAD * 2 + layerCount * BOX_W + (layerCount - 1) * COL_GAP;
    const height = MAP_PAD * 2 + tallest * BOX_H + (tallest - 1) * ROW_GAP;
    const x = (i) => MAP_PAD + layers[i] * (BOX_W + COL_GAP);
    const y = (i) => {
      const column = columns[layers[i]];
      const columnHeight = column.length * BOX_H + (column.length - 1) * ROW_GAP;
      return (height - columnHeight) / 2 + rowOf[i] * (BOX_H + ROW_GAP);
    };

    const svg = element("areaMap");
    svg.setAttribute("viewBox", `0 0 ${width} ${height}`);
    svg.setAttribute("width", width);
    svg.setAttribute("height", height);

    const defs = document.createElementNS(SVG_NS, "defs");
    const marker = document.createElementNS(SVG_NS, "marker");
    marker.setAttribute("id", "map-arrow");
    marker.setAttribute("viewBox", "0 0 8 8");
    marker.setAttribute("refX", "7");
    marker.setAttribute("refY", "4");
    // Fixed-size arrowheads: the default markerUnits scales them by
    // stroke width, which turns the widest edges into huge triangles.
    marker.setAttribute("markerUnits", "userSpaceOnUse");
    marker.setAttribute("markerWidth", "9");
    marker.setAttribute("markerHeight", "9");
    marker.setAttribute("orient", "auto-start-reverse");
    const tip = document.createElementNS(SVG_NS, "path");
    tip.setAttribute("d", "M 0 0 L 8 4 L 0 8 z");
    tip.setAttribute("fill", "currentColor");
    marker.appendChild(tip);
    defs.appendChild(marker);
    svg.appendChild(defs);

    // Arrows point from the user's left edge to the dependency's right edge
    // (dependencies sit in earlier columns). Same-column pairs (an area
    // cycle) arc out of the left side.
    const edgeEls = [];
    for (const e of edges) {
      const x1 = x(e.from);
      const y1 = y(e.from) + BOX_H / 2;
      const x2 = x(e.to) + BOX_W;
      const y2 = y(e.to) + BOX_H / 2;
      const path = document.createElementNS(SVG_NS, "path");
      path.setAttribute("class", "map-edge");
      if (layers[e.from] === layers[e.to]) {
        const bulge = BOX_W * 0.45;
        path.setAttribute("d", `M ${x1} ${y1} C ${x1 - bulge} ${y1}, ${x2 - BOX_W - bulge} ${y2}, ${x2 - BOX_W} ${y2}`);
      } else {
        const mid = (x1 + x2) / 2;
        path.setAttribute("d", `M ${x1} ${y1} C ${mid} ${y1}, ${mid} ${y2}, ${x2} ${y2}`);
      }
      path.setAttribute("stroke-width", Math.min(5, 1 + 1.6 * Math.log10(e.count + 1)).toFixed(2));
      path.setAttribute("marker-end", "url(#map-arrow)");
      svg.appendChild(path);
      edgeEls.push({ el: path, edge: e });
    }

    let tipEl = null;
    const showTip = (text, ev) => {
      if (!tipEl) {
        tipEl = document.createElement("div");
        tipEl.className = "map-tip";
        document.body.appendChild(tipEl);
      }
      tipEl.textContent = text;
      tipEl.style.left = `${Math.min(ev.clientX + 14, window.innerWidth - 260)}px`;
      tipEl.style.top = `${ev.clientY + 14}px`;
      tipEl.hidden = false;
    };
    const hideTip = () => { if (tipEl) tipEl.hidden = true; };

    rows.forEach((row, i) => {
      const g = document.createElementNS(SVG_NS, "g");
      g.setAttribute("class", "map-node");
      g.setAttribute("transform", `translate(${x(i)} ${y(i)})`);
      const rect = document.createElementNS(SVG_NS, "rect");
      rect.setAttribute("width", BOX_W);
      rect.setAttribute("height", BOX_H);
      rect.setAttribute("rx", 6);
      g.appendChild(rect);
      const name = document.createElementNS(SVG_NS, "text");
      name.setAttribute("x", 10);
      name.setAttribute("y", 18);
      name.textContent = row.slug;
      g.appendChild(name);
      const count = document.createElementNS(SVG_NS, "text");
      count.setAttribute("class", "map-count");
      count.setAttribute("x", 10);
      count.setAttribute("y", 33);
      count.textContent = `${formatCount(row.nodes)} decls`;
      g.appendChild(count);
      const link = document.createElementNS(SVG_NS, "a");
      link.setAttribute("href", `a/${encodeURIComponent(row.slug)}/`);
      link.appendChild(g);
      svg.appendChild(link);

      g.addEventListener("mouseenter", (ev) => {
        g.classList.add("hot");
        for (const { el, edge } of edgeEls) {
          if (edge.from === i || edge.to === i) el.classList.add("hot");
        }
        const uses = edges.filter((e) => e.from === i)
          .reduce((s, e) => s + e.count, 0);
        const usedBy = edges.filter((e) => e.to === i)
          .reduce((s, e) => s + e.count, 0);
        showTip(`${row.slug} — ${formatCount(uses)} `
          + `dependenc${uses === 1 ? "y" : "ies"} on other areas · `
          + `${formatCount(usedBy)} incoming from them`, ev);
      });
      g.addEventListener("mousemove", (ev) => showTip(tipEl ? tipEl.textContent : "", ev));
      g.addEventListener("mouseleave", () => {
        g.classList.remove("hot");
        for (const { el } of edgeEls) el.classList.remove("hot");
        hideTip();
      });
    });

    element("areaMapSection").hidden = false;
  }

  // ---------- area table ----------

  function sortValue(row, key) {
    if (key === "area") return row.slug.toLowerCase();
    return row[key];
  }

  function compareAreas(a, b) {
    const va = sortValue(a, state.column);
    const vb = sortValue(b, state.column);
    let cmp = va < vb ? -1 : va > vb ? 1 : 0;
    if (cmp === 0) cmp = a.slug < b.slug ? -1 : a.slug > b.slug ? 1 : 0;
    return state.descending ? -cmp : cmp;
  }

  function renderHead() {
    const row = element("areaHead");
    row.textContent = "";
    for (const column of COLUMNS) {
      const th = document.createElement("th");
      if (column.numeric) th.className = "num";
      th.setAttribute("aria-sort", state.column === column.key
        ? (state.descending ? "descending" : "ascending")
        : "none");
      const button = document.createElement("button");
      button.type = "button";
      button.className = "sort-button";
      button.textContent = column.label;
      if (state.column === column.key) {
        button.dataset.dir = state.descending ? "desc" : "asc";
      }
      button.addEventListener("click", () => {
        if (state.column === column.key) {
          state.descending = !state.descending;
        } else {
          state.column = column.key;
          state.descending = column.numeric; // numeric columns start descending
        }
        renderHead();
        renderBody();
      });
      th.appendChild(button);
      row.appendChild(th);
    }
  }

  function numericCell(text) {
    const td = document.createElement("td");
    td.className = "num";
    td.textContent = text;
    return td;
  }

  function renderRow(row) {
    const tr = document.createElement("tr");

    const areaCell = document.createElement("td");
    areaCell.className = "cell-area";
    const link = document.createElement("a");
    link.href = `a/${encodeURIComponent(row.slug)}/`;
    const title = document.createElement("span");
    title.className = "area-name";
    title.textContent = row.slug;
    const modules = document.createElement("span");
    modules.className = "area-modules";
    modules.textContent = `${formatCount(row.modules)} module${row.modules === 1 ? "" : "s"}`;
    link.append(title, modules);
    areaCell.appendChild(link);
    tr.appendChild(areaCell);

    tr.appendChild(numericCell(formatCount(row.nodes)));
    tr.appendChild(numericCell(formatCount(row.edges)));
    tr.appendChild(numericCell(formatCount(row.xout)));
    tr.appendChild(numericCell(formatCount(row.xin)));
    tr.appendChild(numericCell(formatCount(row.maxDepth)));
    tr.appendChild(numericCell(Number(row.avgDepth || 0).toFixed(2)));
    return tr;
  }

  function renderBody() {
    const query = state.filter;
    const rows = areas.filter((a) => !query || a.slug.toLowerCase().includes(query));
    rows.sort(compareAreas);

    const body = element("areaBody");
    body.textContent = "";
    const fragment = document.createDocumentFragment();
    for (const row of rows) fragment.appendChild(renderRow(row));
    body.appendChild(fragment);

    if (rows.length === 0) {
      const tr = document.createElement("tr");
      const td = document.createElement("td");
      td.colSpan = COLUMNS.length;
      td.className = "table-empty";
      td.textContent = "No areas match.";
      tr.appendChild(td);
      body.appendChild(tr);
    }

    element("areaCount").textContent = query
      ? `${rows.length} of ${areas.length} areas`
      : `${areas.length} areas`;
  }

  // ---------- footer ----------

  function renderFooter(data) {
    const footer = element("landingFooter");
    const date = (data.generated || "").slice(0, 10);
    const sha = (data.commit || "").slice(0, 7);
    footer.append(`generated ${date} · commit `);
    const link = document.createElement("a");
    link.className = "mono";
    link.href = `https://github.com/TauCetiProject/TauCeti/commit/${encodeURIComponent(data.commit || "")}`;
    link.textContent = sha;
    footer.appendChild(link);
  }

  // ---------- boot ----------

  function init(data) {
    areas = (data.areas || []).slice();
    renderTiles(data.totals || {});
    renderKindBreakdown((data.totals || {}).kinds);
    renderAreaMap(areas, data.areaEdges || []);
    renderHead();
    renderBody();
    renderFooter(data);
    element("areasSection").hidden = false;

    element("areaFilter").addEventListener("input", (event) => {
      state.filter = event.target.value.trim().toLowerCase();
      renderBody();
    });
  }

  fetch("data/index.json")
    .then((response) => {
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      return response.json();
    })
    .then(init)
    .catch((error) => {
      const box = element("loadError");
      box.hidden = false;
      box.textContent =
        `Failed to load data/index.json (${error.message}). `
        + "If you opened this page from disk, serve it over HTTP instead.";
    });
})();
