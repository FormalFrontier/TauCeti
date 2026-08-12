#!/usr/bin/env python3
"""Generate the static exposition site from an extractor dump.

Reads the JSONL dump written by ``scripts/exposition/Extract.lean`` and the
Lean sources under the repository root, and writes a static site:

* ``data/areas/<Area>.json`` — one shard per top-level library area
  (``TauCeti.Algebra.* -> Algebra``): a layered dependency graph of the
  area's declarations, with cross-area edges resolved to (area, id, name)
  triples so the graph pages can link across areas, plus a score-picked
  list of the area's main results (``hl``) for the card view;
* ``data/index.json`` — library totals, per-area rows, and the area-level
  dependency matrix for the landing page;
* ``data/decls.json`` — a compact all-declarations index for the viewer;
* ``a/<Area>/index.html`` — one instantiated graph page per area, plus the
  static shell pages and assets copied verbatim from ``static/``.

Unlike Lean Pool's per-project exposition (from which this pipeline is
adapted — Vasily Ilin, https://github.com/Vilin97/lean-pool, Apache 2.0),
Tau Ceti is one integrated library: areas depend on each other, so shards
carry cross-area dependency lists (``xdeps``/``xrev``) and every declaration
records its depth in the whole-library graph (``gdepth``) alongside its
area-local layer.

Pure stdlib: no third-party dependencies, so CI needs no ``pip install``.

Usage::

    python3 scripts/exposition/generate.py \
        --dump exposition-dump.jsonl --repo-root . --out exposition-site \
        --commit <sha>
"""

from __future__ import annotations

import argparse
import html
import json
import logging
import math
import re
import shutil
import string
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

from layout import compute_layout, longest_path_layers
from source_text import SourceFile, statement_slice

logger = logging.getLogger(__name__)

PACKAGE_DIRECTORY = Path(__file__).resolve().parent
DEFAULT_STATIC_DIRECTORY = PACKAGE_DIRECTORY / "static"
DEFAULT_TEMPLATES_DIRECTORY = PACKAGE_DIRECTORY / "templates"

SCHEMA_VERSION = 1


@dataclass
class SiteSummary:
    """Totals reported after a site generation run."""

    areas: int
    decls: int
    edges: int
    cross_edges: int


class SourceCache:
    """Read and cache Lean source files by module name (one read per file)."""

    def __init__(self, repo_root: Path) -> None:
        """Remember the repository root that module paths resolve against."""
        self._repo_root = repo_root
        self._files: dict[str, SourceFile | None] = {}

    def get(self, module: str) -> SourceFile | None:
        """Return the parsed source for ``module``, or ``None`` if missing."""
        if module not in self._files:
            path = self._repo_root.joinpath(*module.split(".")).with_suffix(".lean")
            if path.is_file():
                text = path.read_text(encoding="utf-8")
                self._files[module] = SourceFile.from_text(text)
            else:
                logger.warning("source file missing for module %s: %s", module, path)
                self._files[module] = None
        return self._files[module]


def read_dump(dump_path: Path) -> list[dict]:
    """Parse the extractor JSONL dump into a list of record dicts.

    Records are deduplicated by ``id`` (first occurrence wins): a constant
    declared textually in two modules would otherwise become two nodes.
    """
    records: list[dict] = []
    seen_ids: set[str] = set()
    with Path(dump_path).open(encoding="utf-8") as dump_file:
        for line in dump_file:
            stripped = line.strip()
            if not stripped:
                continue
            record = json.loads(stripped)
            if record["id"] in seen_ids:
                logger.warning("duplicate dump record dropped: %s", record["id"])
                continue
            seen_ids.add(record["id"])
            records.append(record)
    return records


def area_for_module(module: str) -> str:
    """Return the area slug a module belongs to (second name component).

    A module sitting directly under the library root (``TauCeti.Basic``)
    forms a pseudo-area named after the module.
    """
    parts = module.split(".")
    return parts[1] if len(parts) > 1 else parts[0]


def _sorted_records(records: list[dict]) -> list[dict]:
    """Order records by (module, start line, name) — the shard id order."""
    return sorted(
        records, key=lambda record: (record["m"], record["r"][0], record["n"])
    )


def _kind_counts(kinds: list[str]) -> dict[str, int]:
    """Count kinds, ordered by descending count then name for determinism."""
    counts = Counter(kinds)
    return dict(sorted(counts.items(), key=lambda item: (-item[1], item[0])))


@dataclass
class SiteModel:
    """Everything derived from the dump before serialization.

    ``slugs`` fixes the area index space used everywhere else. Per area (in
    ``slugs`` order): the shard-ordered records, the intra-area dependency
    lists (shard-local ids), and the cross-area dependency/dependent lists
    (``(area index, local id)`` pairs). ``global_depths`` are longest-path
    layers over the whole library graph, intra- and cross-area edges alike,
    in the same per-area order.
    """

    slugs: list[str]
    ordered: dict[str, list[dict]]
    intra_deps: dict[str, list[list[int]]]
    cross_deps: dict[str, list[list[tuple[int, int]]]]
    cross_dependents: dict[str, list[list[tuple[int, int]]]]
    global_depths: dict[str, list[int]]
    area_edge_counts: dict[tuple[int, int], int]


def build_site_model(records: list[dict]) -> SiteModel:
    """Resolve the dump's name-based edges into the per-area model."""
    grouped: dict[str, list[dict]] = {}
    for record in records:
        grouped.setdefault(area_for_module(record["m"]), []).append(record)
    slugs = sorted(grouped)
    ordered = {slug: _sorted_records(grouped[slug]) for slug in slugs}
    position: dict[str, tuple[int, int]] = {}
    for area_index, slug in enumerate(slugs):
        for local_id, record in enumerate(ordered[slug]):
            position[record["id"]] = (area_index, local_id)

    intra_deps: dict[str, list[list[int]]] = {}
    cross_deps: dict[str, list[list[tuple[int, int]]]] = {}
    cross_dependents: dict[str, list[list[tuple[int, int]]]] = {
        slug: [[] for _ in ordered[slug]] for slug in slugs
    }
    area_edge_counts: dict[tuple[int, int], int] = {}
    for area_index, slug in enumerate(slugs):
        area_intra: list[list[int]] = []
        area_cross: list[list[tuple[int, int]]] = []
        for local_id, record in enumerate(ordered[slug]):
            intra: set[int] = set()
            cross: set[tuple[int, int]] = set()
            for dependency in record.get("deps", []):
                target = position.get(dependency)
                if target is None:  # dangling: dropped like Lean Pool does
                    continue
                target_area, target_local = target
                if target_area == area_index:
                    if target_local != local_id:
                        intra.add(target_local)
                else:
                    cross.add(target)
            area_intra.append(sorted(intra))
            area_cross.append(sorted(cross))
            for target_area, target_local in sorted(cross):
                cross_dependents[slugs[target_area]][target_local].append(
                    (area_index, local_id)
                )
                key = (area_index, target_area)
                area_edge_counts[key] = area_edge_counts.get(key, 0) + 1
        intra_deps[slug] = area_intra
        cross_deps[slug] = area_cross

    # Global depth: longest-path layers over the whole library graph. Nodes
    # are numbered by (area index, local id) in flattening order.
    offsets: dict[str, int] = {}
    total = 0
    for slug in slugs:
        offsets[slug] = total
        total += len(ordered[slug])
    global_adjacency: list[list[int]] = [[] for _ in range(total)]
    for area_index, slug in enumerate(slugs):
        base = offsets[slug]
        for local_id in range(len(ordered[slug])):
            targets = [
                offsets[slugs[target_area]] + target_local
                for target_area, target_local in cross_deps[slug][local_id]
            ]
            targets.extend(base + t for t in intra_deps[slug][local_id])
            global_adjacency[base + local_id] = targets
    flat_depths = longest_path_layers(global_adjacency)
    global_depths = {
        slug: flat_depths[offsets[slug] : offsets[slug] + len(ordered[slug])]
        for slug in slugs
    }

    return SiteModel(
        slugs=slugs,
        ordered=ordered,
        intra_deps=intra_deps,
        cross_deps=cross_deps,
        cross_dependents=cross_dependents,
        global_depths=global_depths,
        area_edge_counts=area_edge_counts,
    )


def _refined_kind_and_statement(
    record: dict, source: SourceFile | None
) -> tuple[str, str]:
    """Refine the extractor kind and slice the statement from the source."""
    if source is None:
        return record["k"], ""
    return statement_slice(source, record["r"], record["s"], record["k"])


def _cross_reference(model: SiteModel, target: tuple[int, int]) -> list:
    """Serialize one cross-area reference as ``[area, id, name]``."""
    target_area, target_local = target
    name = model.ordered[model.slugs[target_area]][target_local]["n"]
    return [target_area, target_local, name]


HIGHLIGHT_LIMIT = 12
HIGHLIGHT_DEF_LIMIT = 8
HIGHLIGHT_KINDS = frozenset({"theorem", "lemma"})
HIGHLIGHT_DEF_KINDS = frozenset({"def", "structure", "class", "inductive",
                                 "abbrev"})
HIGHLIGHT_MODULE_CAP = 2

# This repo's docstring convention opens notable declarations with a bold
# title: `**De Finetti's theorem.** An exchangeable process …`. That title
# is the human name a card should lead with.
_BOLD_LEAD = re.compile(r"^\*\*(.+?)\*\*")

# A title reads as a *named* result (Hurwitz's theorem, Gårding's
# inequality) when it pairs a result keyword with an eponym: a capitalized
# word that is not merely a generic sentence opener.
_NAMED_KEYWORDS = frozenset(
    {"correspondence", "criterion", "decomposition", "formula", "identity",
     "inequality", "law", "lemma", "principle", "rule", "theorem"}
)
_GENERIC_TITLE_OPENERS = frozenset(
    {"a", "all", "an", "any", "both", "bounded", "characterization",
     "classical", "classification", "comparison", "complete", "completely",
     "composing", "conditional", "convergence", "counting", "each",
     "equivalence", "every", "exchangeable", "existence", "factoring",
     "for", "generalized", "global", "half", "identification", "if",
     "improper", "integral", "local", "maximal", "membership", "minimal",
     "monotone", "motivating", "packaged", "pointwise", "rewriting",
     "rigidity", "strict", "that", "the", "this", "uniqueness", "weighted",
     "when", "where", "winding"}
)


def display_title(doc: str) -> str | None:
    """The docstring's leading bold span, trimmed — or ``None``."""
    match = _BOLD_LEAD.match(doc.strip())
    if not match:
        return None
    title = match.group(1).strip().rstrip(".:—–-").strip()
    return title or None


def _title_key(title: str) -> str:
    """Collapse a title to a dedup key: variants of one named result
    (`De Finetti's theorem`, `de Finetti's theorem, mixture form`) share
    the first few normalized words."""
    words = re.sub(r"[^a-z0-9 ]", " ", title.lower()).split()
    while words and words[0] in ("the", "a", "an"):
        words.pop(0)
    return " ".join(words[:3])


def _is_named_result(title: str) -> bool:
    """True when the title names a result after someone or something."""
    words = re.sub(r"[^0-9A-Za-zÀ-ÖØ-öø-ÿ' ]", " ", title).split()
    if not any(word.lower() in _NAMED_KEYWORDS for word in words):
        return False
    for index, word in enumerate(words):
        if not word[0].isupper():
            continue
        if index > 0:
            return True
        if word.lower().removesuffix("'s") not in _GENERIC_TITLE_OPENERS:
            return True
    return False

# Naming-convention API lemmas (`…NatIso_hom_app_apply`, `…Inclusion_comp`)
# score high on depth but are never an area's headline. A name is technical
# when its last underscore token is in STRONG, or its last two tokens are
# both API-ish (so `…_boundary_inv` — mathematics about an inverse — stays,
# while `…_inv_app` goes).
STRONG_API_TOKENS = frozenset(
    {"add", "app", "apply", "assoc", "aux", "bot", "cast", "coe", "comp",
     "def", "div", "empty", "eq", "fst", "id", "intCast", "map", "mk", "mul",
     "natCast", "neg", "none", "obj", "one", "pow", "refl", "self", "smul",
     "snd", "some", "sub", "succ", "symm", "tmul", "top", "trans", "univ",
     "zero"}
)
WEAK_API_TOKENS = frozenset({"hom", "inv"})


def _is_technical_name(name: str) -> bool:
    """True for API-convention names that should never make the cards."""
    tokens = name.rsplit(".", 1)[-1].split("_")
    last = tokens[-1]
    if last in STRONG_API_TOKENS:
        return True
    if len(last) > 2 and last.startswith("to") and last[2].isupper():
        return True  # coercion-comparison lemmas: `…_toLinearMap`
    api_tokens = STRONG_API_TOKENS | WEAK_API_TOKENS
    return (
        len(tokens) >= 2
        and last in api_tokens
        and tokens[-2] in api_tokens
    )


def _use_counts(
    nodes: list[dict],
    dependency_lists: list[list[int]],
    cross_dependent_counts: list[int],
) -> list[int]:
    """Per-node dependent counts, intra- and cross-area combined."""
    counts = [0] * len(nodes)
    for dependencies in dependency_lists:
        for target in dependencies:
            counts[target] += 1
    return [
        counts[local_id] + cross_dependent_counts[local_id]
        for local_id in range(len(nodes))
    ]


# A scored candidate: (negated score, title length — huge when untitled, so
# key collapsing prefers the plainly-titled variant —, name, local id,
# title-dedup key or None, module index).
_Candidate = tuple[float, int, str, int, str | None, int]


def _candidate(score: float, node: dict, local_id: int) -> _Candidate:
    title = node.get("title")
    return (
        -score,
        len(title) if title else 10**6,
        node["name"],
        local_id,
        _title_key(title) if title else None,
        node.get("module", 0),
    )


def _pick_diverse(scored: list[_Candidate], limit: int) -> list[int]:
    """Rank candidates into the final card list.

    Titled candidates sharing a dedup key collapse first — the variant
    with the shortest title survives (`De Finetti's theorem`, not its
    `…, mixture form` restatement), score breaking ties. Then a greedy
    score-ordered pass takes at most ``HIGHLIGHT_MODULE_CAP`` per module
    while other candidates remain, so one development cannot monopolize
    the cards; best-scored spillovers refill unused slots at the end.
    The final list leads with the titled picks (human-named results read
    first; Lean-named ones trail). Ordering is deterministic: ties break
    by title length then name.
    """
    best_for_key: dict[str, _Candidate] = {}
    pool: list[_Candidate] = []
    for row in scored:
        key = row[4]
        if key is None:
            pool.append(row)
            continue
        current = best_for_key.get(key)
        if current is None or (row[1], row[0], row[2]) < (
            current[1],
            current[0],
            current[2],
        ):
            best_for_key[key] = row
    pool.extend(best_for_key.values())
    pool.sort()
    picked: list[int] = []
    per_module: dict[int, int] = {}
    spillover: list[int] = []
    for row in pool:
        if len(picked) == limit:
            break
        module = row[5]
        if per_module.get(module, 0) >= HIGHLIGHT_MODULE_CAP:
            spillover.append(row[3])
            continue
        per_module[module] = per_module.get(module, 0) + 1
        picked.append(row[3])
    picked.extend(spillover[: limit - len(picked)])
    untitled = {row[3] for row in pool if row[4] is None}
    picked.sort(key=lambda local_id: local_id in untitled)  # stable
    return picked


def select_highlights(
    nodes: list[dict],
    dependency_lists: list[list[int]],
    cross_dependent_counts: list[int],
    limit: int = HIGHLIGHT_LIMIT,
) -> list[int]:
    """Pick an area's main results: the shard-local ids shown as cards.

    There is no human-curated registry to draw on, so notability is scored
    from the data: only documented, non-private theorems qualify (API-named
    lemmas excluded, see ``_is_technical_name``). The score favors depth
    in the whole-library graph (headline results sit at the end of long
    chains), with nudges for a substantial docstring, for being widely
    built upon, and for being a capstone nothing depends on yet — and
    boosts declarations whose docstring opens with a bold title,
    especially one naming the result (`**Hurwitz's theorem.**`): those are
    the human-recognizable statements a visitor scans for, even when they
    sit at moderate depth. Title variants collapse and modules are capped
    via ``_pick_diverse``.
    """
    use_counts = _use_counts(nodes, dependency_lists, cross_dependent_counts)
    max_global_depth = max((node["gdepth"] for node in nodes), default=0)
    max_uses = max(use_counts, default=0)
    scored: list[_Candidate] = []
    for local_id, node in enumerate(nodes):
        if node["kind"] not in HIGHLIGHT_KINDS or node.get("private"):
            continue
        doc = node.get("doc", "")
        if not doc or _is_technical_name(node["name"]):
            continue
        score = 3.0 * node["gdepth"] / max(max_global_depth, 1)
        # Docstring length is a weak nudge only: at full weight a wordy
        # corollary outranks the eponymous theorem it follows from.
        score += 0.5 * min(len(doc), 400) / 400.0
        if max_uses:
            score += 1.5 * math.log1p(use_counts[local_id]) / math.log1p(max_uses)
        if use_counts[local_id] == 0:
            score += 0.75  # capstone: nothing builds on it (yet)
        title = node.get("title")
        if title:
            score += 0.6
            if _is_named_result(title):
                score += 1.5
        scored.append(_candidate(score, node, local_id))
    return _pick_diverse(scored, limit)


def select_notable_definitions(
    nodes: list[dict],
    dependency_lists: list[list[int]],
    cross_dependent_counts: list[int],
    limit: int = HIGHLIGHT_DEF_LIMIT,
) -> list[int]:
    """Pick the definitions the area is built around.

    Complements ``select_highlights``: documented, non-private definition
    kinds, ranked mainly by how widely they are built upon (a definition
    matters through its uses, unlike a capstone theorem), with small
    nudges for depth, docstring substance, and a bold title. Same title
    dedup and module cap.
    """
    use_counts = _use_counts(nodes, dependency_lists, cross_dependent_counts)
    max_global_depth = max((node["gdepth"] for node in nodes), default=0)
    max_uses = max(use_counts, default=0)
    scored: list[_Candidate] = []
    for local_id, node in enumerate(nodes):
        if node["kind"] not in HIGHLIGHT_DEF_KINDS or node.get("private"):
            continue
        doc = node.get("doc", "")
        if not doc or _is_technical_name(node["name"]):
            continue
        score = 0.0
        if max_uses:
            score += 2.0 * math.log1p(use_counts[local_id]) / math.log1p(max_uses)
        score += 0.75 * node["gdepth"] / max(max_global_depth, 1)
        score += 0.25 * min(len(doc), 400) / 400.0
        if node.get("title"):
            score += 0.6
        scored.append(_candidate(score, node, local_id))
    return _pick_diverse(scored, limit)


def build_area_shard(
    model: SiteModel,
    slug: str,
    source_cache: SourceCache,
    commit: str,
) -> dict:
    """Build one ``data/areas/<Area>.json`` payload."""
    records = model.ordered[slug]
    modules = sorted({record["m"] for record in records})
    module_indices = {module: index for index, module in enumerate(modules)}
    dependency_lists = model.intra_deps[slug]
    layout = compute_layout(dependency_lists)
    nodes = []
    for local_id, record in enumerate(records):
        source = source_cache.get(record["m"])
        kind, statement = _refined_kind_and_statement(record, source)
        node: dict = {"name": record["n"]}
        if record["id"] != record["n"]:
            node["full"] = record["id"]
        node["kind"] = kind
        node["module"] = module_indices[record["m"]]
        node["line"] = record["r"][0]
        node["endLine"] = record["r"][2]
        if "d" in record:
            node["doc"] = record["d"]
            title = display_title(record["d"])
            if title:
                node["title"] = title
        node["statement"] = statement
        if record.get("p"):
            node["private"] = True
        node["deps"] = dependency_lists[local_id]
        cross = model.cross_deps[slug][local_id]
        if cross:
            node["xdeps"] = [_cross_reference(model, target) for target in cross]
        dependents = model.cross_dependents[slug][local_id]
        if dependents:
            node["xrev"] = [_cross_reference(model, target) for target in dependents]
        node["ext"] = record.get("ext", 0)
        node["gdepth"] = model.global_depths[slug][local_id]
        node["layer"] = layout.node_layers[local_id]
        node["order"] = layout.node_orders[local_id]
        nodes.append(node)
    node_count = len(nodes)
    average = sum(layout.node_layers) / node_count if node_count else 0.0
    stats = {
        "nodes": node_count,
        "edges": sum(len(dependencies) for dependencies in dependency_lists),
        "xout": sum(len(cross) for cross in model.cross_deps[slug]),
        "xin": sum(len(back) for back in model.cross_dependents[slug]),
        "maxDepth": max(layout.node_layers, default=0),
        "avgDepth": round(average, 2),
        "gmaxDepth": max(model.global_depths[slug], default=0),
        "kinds": _kind_counts([node["kind"] for node in nodes]),
    }
    cross_dependent_counts = [
        len(dependents) for dependents in model.cross_dependents[slug]
    ]
    return {
        "schema": SCHEMA_VERSION,
        "area": slug,
        "commit": commit,
        "areas": model.slugs,
        "stats": stats,
        "modules": modules,
        "layers": layout.layer_sizes,
        "hl": select_highlights(nodes, dependency_lists, cross_dependent_counts),
        "hldef": select_notable_definitions(
            nodes, dependency_lists, cross_dependent_counts
        ),
        "decls": nodes,
    }


def build_index(model: SiteModel, shards: dict[str, dict], commit: str) -> dict:
    """Build the ``data/index.json`` payload (areas in slug order)."""
    area_rows = []
    total_kinds: Counter[str] = Counter()
    intra_total = 0
    cross_total = 0
    for slug in model.slugs:
        shard = shards[slug]
        stats = shard["stats"]
        total_kinds.update(stats["kinds"])
        intra_total += stats["edges"]
        cross_total += stats["xout"]
        area_rows.append(
            {
                "slug": slug,
                "nodes": stats["nodes"],
                "edges": stats["edges"],
                "xout": stats["xout"],
                "xin": stats["xin"],
                "maxDepth": stats["maxDepth"],
                "avgDepth": stats["avgDepth"],
                "modules": len(shard["modules"]),
            }
        )
    global_max = max(
        (depth for depths in model.global_depths.values() for depth in depths),
        default=0,
    )
    totals = {
        "areas": len(area_rows),
        "decls": sum(row["nodes"] for row in area_rows),
        "edges": intra_total + cross_total,
        "xedges": cross_total,
        "maxDepth": global_max,
        "kinds": dict(
            sorted(total_kinds.items(), key=lambda item: (-item[1], item[0]))
        ),
    }
    area_edges = [
        [source, target, count]
        for (source, target), count in sorted(model.area_edge_counts.items())
    ]
    generated = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    return {
        "schema": SCHEMA_VERSION,
        "commit": commit,
        "generated": generated,
        "totals": totals,
        "areas": area_rows,
        "areaEdges": area_edges,
    }


def build_declaration_index(model: SiteModel, shards: dict[str, dict], index: dict) -> dict:
    """Build the compact ``data/decls.json`` payload for the viewer."""
    kinds = list(index["totals"]["kinds"])
    kind_indices = {kind: position for position, kind in enumerate(kinds)}
    rows = []
    for area_position, slug in enumerate(model.slugs):
        for declaration_id, node in enumerate(shards[slug]["decls"]):
            rows.append(
                [
                    node["name"],
                    kind_indices[node["kind"]],
                    area_position,
                    declaration_id,
                ]
            )
    return {
        "schema": SCHEMA_VERSION,
        "kinds": kinds,
        "areas": model.slugs,
        "decls": rows,
    }


def _write_json(path: Path, payload: dict) -> None:
    """Write compact JSON (preserving insertion key order) to ``path``."""
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
    path.write_text(text, encoding="utf-8")


def _write_area_pages(out_dir: Path, slugs: list[str], template_path: Path) -> None:
    """Instantiate ``templates/area.html`` once per area."""
    template = string.Template(template_path.read_text(encoding="utf-8"))
    for slug in slugs:
        page = template.safe_substitute(SLUG=slug, TITLE=html.escape(slug))
        page_directory = out_dir / "a" / slug
        page_directory.mkdir(parents=True, exist_ok=True)
        (page_directory / "index.html").write_text(page, encoding="utf-8")


def generate_site(
    dump_path: Path,
    repo_root: Path,
    out_dir: Path,
    commit: str = "main",
    static_dir: Path | None = None,
    templates_dir: Path | None = None,
) -> SiteSummary:
    """Generate the whole static site; return the run's totals.

    ``static_dir`` and ``templates_dir`` default to the package's ``static/``
    and ``templates/`` directories; tests inject fakes through them.
    """
    static_directory = Path(static_dir) if static_dir else DEFAULT_STATIC_DIRECTORY
    templates_directory = (
        Path(templates_dir) if templates_dir else DEFAULT_TEMPLATES_DIRECTORY
    )
    template_path = templates_directory / "area.html"
    if not static_directory.is_dir():
        raise FileNotFoundError(f"static asset directory not found: {static_directory}")
    if not template_path.is_file():
        raise FileNotFoundError(f"area page template not found: {template_path}")
    model = build_site_model(read_dump(dump_path))
    source_cache = SourceCache(Path(repo_root))
    shards = {
        slug: build_area_shard(model, slug, source_cache, commit)
        for slug in model.slugs
    }
    index = build_index(model, shards, commit)
    out_directory = Path(out_dir)
    out_directory.mkdir(parents=True, exist_ok=True)
    shutil.copytree(static_directory, out_directory, dirs_exist_ok=True)
    for slug, shard in shards.items():
        _write_json(out_directory / "data" / "areas" / f"{slug}.json", shard)
    _write_json(out_directory / "data" / "index.json", index)
    _write_json(
        out_directory / "data" / "decls.json",
        build_declaration_index(model, shards, index),
    )
    _write_area_pages(out_directory, model.slugs, template_path)
    return SiteSummary(
        areas=index["totals"]["areas"],
        decls=index["totals"]["decls"],
        edges=index["totals"]["edges"],
        cross_edges=index["totals"]["xedges"],
    )


def main() -> None:
    """CLI entry point."""
    parser = argparse.ArgumentParser(
        description="Generate the static exposition site from an extractor dump."
    )
    parser.add_argument(
        "--dump",
        type=Path,
        required=True,
        help="extractor JSONL dump (one JSON object per declaration)",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        required=True,
        help="repository root containing the TauCeti/ sources",
    )
    parser.add_argument(
        "--out",
        type=Path,
        required=True,
        help="output directory for the generated static site",
    )
    parser.add_argument(
        "--commit",
        default="main",
        help="commit SHA recorded in the data and used for GitHub source links",
    )
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    summary = generate_site(
        dump_path=arguments.dump,
        repo_root=arguments.repo_root,
        out_dir=arguments.out,
        commit=arguments.commit,
    )
    print(
        f"wrote {summary.areas} areas ({summary.decls} declarations, "
        f"{summary.edges} edges, {summary.cross_edges} cross-area) to {arguments.out}"
    )


if __name__ == "__main__":
    main()
