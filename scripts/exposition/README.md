# Exposition site: pipeline and data formats

The exposition is a static site published at
[`<pages-root>/exposition/`](https://taucetiproject.github.io/TauCeti/exposition/)
next to the doc-gen4 API reference (`/docs`) — interactive dependency graphs
and a declaration index for the whole library, split by top-level area
(`TauCeti/Algebra -> Algebra`, ...). It is produced in two steps:

1. **Extractor** (`Extract.lean`, run via `lake env lean --run` from the
   repository root after `lake build`): dumps one JSON object per library
   declaration (JSONL). Kernel-level dependency edges are pre-resolved to
   library declarations; compiler-generated auxiliaries are tunnelled
   through.
2. **Generator** (`generate.py`, pure stdlib): reads the dump and the Lean
   sources, computes per-area layered layouts, cross-area links and
   whole-library depths, and emits the static site.

```bash
lake env lean --run scripts/exposition/Extract.lean exposition-dump.jsonl
python3 scripts/exposition/generate.py \
  --dump exposition-dump.jsonl --repo-root . --out exposition-site \
  --commit "$(git rev-parse HEAD)"
python3 -m http.server --directory exposition-site  # then open http://localhost:8000
```

Both steps run in the Pages deploy (`.github/workflows/pages.yml`) on the
same cadence as the API docs, sharing their rebuild decision (the extractor
needs the built library). Tests: `test_layout.py`, `test_source_text.py`,
`test_generate.py` (wired into `ci.yml`; run directly with `python3`).

The pipeline is adapted from Lean Pool's exposition (Vasily Ilin,
https://github.com/Vilin97/lean-pool, Apache 2.0). Two structural
differences, both because Tau Ceti is one integrated library rather than a
pool of independent projects: declarations carry cross-area dependency
links and a whole-library depth alongside their area-local layer, and Lean
Pool's per-project registry cards and minimal-file builder are dropped.

## Extractor dump (JSONL, one line per declaration)

```json
{"id": "_private.TauCeti.X.0.Foo.aux",  // full (possibly mangled) name — unique
 "n": "TauCeti.Foo.aux",                // display name (private names demangled)
 "m": "TauCeti.Algebra.Group.Basic",    // defining module
 "k": "theorem",                        // coarse kind: theorem|def|instance|structure|class|inductive|axiom|opaque
 "r": [435, 0, 446, 23],                // range: start line, start col, end line, end col (1-based lines)
 "s": [435, 6],                         // selection (name token) line/col
 "d": "docstring",                      // optional
 "p": true,                             // optional: private
 "deps": ["<id>", ...],                 // library-internal dependency ids (other dump lines)
 "ext": 127}                            // count of distinct external (Mathlib/core) constants used
```

The generator refines `k` from source text (`lemma` vs `theorem`, `abbrev`
vs `def`, `instance`, ...) and slices the statement text (keyword up to the
top-level `:=` / `where` / `|` boundary).

## Site tree

```
exposition/
  index.html              # landing: library totals, area map, sortable area table
  decls/index.html        # all-declarations viewer
  a/<Area>/index.html     # per-area graph page (one per area)
  assets/…                # shared JS/CSS (copied verbatim from static/)
  data/index.json
  data/decls.json
  data/areas/<Area>.json
```

`<Area>` is the second component of the module name
(`TauCeti.Algebra.Group.Basic -> Algebra`). A module sitting directly under
`TauCeti/` would form a pseudo-area named after the module.

Relative bases from `a/<Area>/index.html`: exposition root `../..`, pages
root `../../..`, doc-gen4 page for a non-private declaration `Foo.bar` in
module `TauCeti.A.B`: `../../../docs/TauCeti/A/B.html#Foo.bar`. GitHub
source links pin the shard's `commit`:
`https://github.com/TauCetiProject/TauCeti/blob/<commit>/TauCeti/A/B.lean#L<line>-L<endLine>`.

## `data/areas/<Area>.json` (shard)

```json
{"schema": 1,
 "area": "Algebra",
 "commit": "<sha>",
 "areas": ["Algebra", ...],    // all area slugs — the index space for xdeps/xrev
 "stats": {"nodes": 1671, "edges": 8417,   // intra-area edges
           "xout": 1, "xin": 258,          // cross-area edges out of / into this area
           "maxDepth": 20, "avgDepth": 5.9,  // area-local layers
           "gmaxDepth": 24,                  // max whole-library depth in this area
           "kinds": {"theorem": 1027, ...}},
 "modules": ["TauCeti.Algebra.Group.Basic", ...],
 "layers": [40, 31, ...],      // node count per area-local layer
 "hl": [812, 64, ...],         // main results: node ids (≤ 12)
 "hldef": [3, 209, ...],       // notable definitions: node ids (≤ 8)
 "decls": [ ... ]}
```

`hl` and `hldef` drive the area page's default "Main results" card view.
With no human-curated registry to draw on, both lists are score-picked
(`select_highlights` / `select_notable_definitions` in `generate.py`):

* eligible nodes are documented, non-private, and not API-convention
  named (`…_hom_app_apply`); `hl` takes `theorem`/`lemma` kinds, `hldef`
  the definition kinds;
* theorems are ranked by whole-library depth with nudges for docstring
  substance, wide use, and capstones — plus a boost when the docstring
  opens with a bold title, especially one naming the result
  (`**Hurwitz's theorem.**`), so human-recognizable statements beat
  deeper plumbing; definitions rank mainly by how widely they are used;
* title variants collapse to the plainest one (`De Finetti's theorem`,
  not `…, mixture form`), at most two picks come from any one module,
  and titled picks are listed before Lean-named ones.

Either list may be empty; with no `hl` the page opens straight in the
graph view.

`decls[i]` — the node with id `i` (ids are shard-local array indices):

```json
{"name": "TauCeti.Foo.bar",
 "full": "_private....",       // only when it differs from name (⇒ no doc-gen page)
 "kind": "lemma",              // refined source keyword
 "module": 0,                  // index into modules
 "line": 435, "endLine": 446,
 "doc": "…",                   // optional
 "title": "Hurwitz's theorem", // optional: the doc's leading **bold** span
 "statement": "lemma bar (h : …) : …",  // ≤ 1200 chars, trimmed
 "private": true,              // optional
 "deps": [3, 17],              // intra-area dependencies (node ids)
 "xdeps": [[2, 25, "TauCeti.Baz.qux"], ...],  // optional: cross-area dependencies
 "xrev": [[5, 7, "TauCeti.Quux.corge"], ...], // optional: cross-area dependents
 "ext": 127,                   // distinct Mathlib/core constants used
 "gdepth": 9,                  // longest-path layer in the whole-library graph
 "layer": 5,                   // x: area-local longest-path layer
 "order": 12}                  // y: position within layer after crossing reduction
```

Cross-references are `[areaIndex, declId, fullName]` triples: `areaIndex`
into the shard's `areas`, `declId` into that area's own shard. Depth
definitions: `layer(n) = 0` if `n` has no dependencies inside the graph in
question, else `1 + max(layer(dep))`, with cycles collapsed via SCC
condensation; `layer` uses only intra-area edges, `gdepth` the whole
library's. `edges = Σ len(deps)`.

## `data/index.json`

```json
{"schema": 1, "commit": "abc123", "generated": "2026-07-31T12:00:00Z",
 "totals": {"areas": 19, "decls": 11375,
            "edges": 45069,     // intra + cross
            "xedges": 870,      // cross-area only
            "maxDepth": 26,     // whole-library longest chain
            "kinds": {"theorem": …}},
 "areas": [{"slug": "Algebra", "nodes": 1671, "edges": 8417,
            "xout": 1, "xin": 258, "maxDepth": 20, "avgDepth": 5.9,
            "modules": 110}, …],
 "areaEdges": [[3, 0, 51], …]}  // [fromIdx, toIdx, count]: area from uses area to
```

Areas are sorted by slug; `areaEdges` drives the landing page's area
dependency map.

## `data/decls.json` (all-declarations viewer index)

Compact arrays to keep the file small:

```json
{"schema": 1,
 "kinds": ["theorem", "lemma", …],
 "areas": ["Algebra", …],              // slugs, same order as index.json
 "decls": [["TauCeti.Foo.bar", 0, 0, 12], …]}  // [name, kindIdx, areaIdx, declId]
```

`declId` indexes into that area's shard `decls`; the viewer links a row to
`a/<Area>/index.html#d<declId>`.

## Page shells

`templates/area.html` is a template with literal `${SLUG}` and `${TITLE}`
placeholders (Python `string.Template`); the generator instantiates it once
per area. `index.html`, `decls/index.html` and everything under `assets/`
are copied verbatim from `static/` and fetch their JSON at runtime. URL
fragments on area pages: `#d<id>` (select declaration `id`), `#cone=<id>`
(dependency-cone mode for declaration `id`).
