#!/usr/bin/env python3
"""Tests for the exposition site generator.

Run with:

    python3 scripts/exposition/test_generate.py
"""

import json
import pathlib
import tempfile
import unittest

from generate import (
    SourceCache,
    area_for_module,
    build_area_shard,
    build_declaration_index,
    build_index,
    build_site_model,
    generate_site,
    read_dump,
)


def record(
    name: str,
    module: str,
    line: int = 1,
    deps: list[str] | None = None,
    ext: int = 0,
    **extra,
):
    """One extractor dump record with sane defaults."""
    base = {
        "id": name,
        "n": name,
        "m": module,
        "k": "theorem",
        "r": [line, 0, line, 30],
        "s": [line, 8],
        "deps": deps or [],
        "ext": ext,
    }
    base.update(extra)
    return base


# Two areas: Analysis builds on Algebra (two cross edges), each area has one
# internal edge. Names sort so shard-local ids follow (module, line, name).
FIXTURE = [
    record("TauCeti.Alg.base", "TauCeti.Algebra.A", line=1),
    record("TauCeti.Alg.mid", "TauCeti.Algebra.A", line=5,
           deps=["TauCeti.Alg.base"], ext=2),
    record("TauCeti.Ana.base", "TauCeti.Analysis.B", line=1,
           deps=["TauCeti.Alg.base"]),
    record("TauCeti.Ana.top", "TauCeti.Analysis.B", line=5,
           deps=["TauCeti.Ana.base", "TauCeti.Alg.mid"]),
]


class AreaForModuleTest(unittest.TestCase):
    def test_second_component_names_the_area(self):
        self.assertEqual(area_for_module("TauCeti.Algebra.Group.Basic"), "Algebra")

    def test_root_level_module_forms_a_pseudo_area(self):
        self.assertEqual(area_for_module("TauCeti"), "TauCeti")


class ReadDumpTest(unittest.TestCase):
    def test_duplicates_and_blank_lines_are_dropped(self):
        with tempfile.TemporaryDirectory() as tmp:
            dump = pathlib.Path(tmp) / "dump.jsonl"
            lines = [json.dumps(record("TauCeti.A.x", "TauCeti.A.M")), "",
                     json.dumps(record("TauCeti.A.x", "TauCeti.A.M"))]
            dump.write_text("\n".join(lines), encoding="utf-8")
            records = read_dump(dump)
        self.assertEqual(len(records), 1)


class BuildSiteModelTest(unittest.TestCase):
    def setUp(self):
        self.model = build_site_model([dict(r) for r in FIXTURE])

    def test_areas_are_sorted(self):
        self.assertEqual(self.model.slugs, ["Algebra", "Analysis"])

    def test_intra_dependencies_are_local_ids(self):
        # Algebra order: base (line 1) then mid (line 5).
        self.assertEqual(self.model.intra_deps["Algebra"], [[], [0]])
        # Analysis order: base then top; top uses base locally.
        self.assertEqual(self.model.intra_deps["Analysis"], [[], [0]])

    def test_cross_dependencies_point_into_the_other_area(self):
        self.assertEqual(self.model.cross_deps["Analysis"][0], [(0, 0)])
        self.assertEqual(self.model.cross_deps["Analysis"][1], [(0, 1)])
        self.assertEqual(self.model.cross_deps["Algebra"], [[], []])

    def test_cross_dependents_mirror_cross_dependencies(self):
        self.assertEqual(self.model.cross_dependents["Algebra"][0], [(1, 0)])
        self.assertEqual(self.model.cross_dependents["Algebra"][1], [(1, 1)])

    def test_area_edge_counts_aggregate_per_pair(self):
        self.assertEqual(self.model.area_edge_counts, {(1, 0): 2})

    def test_global_depths_cross_area_chains(self):
        self.assertEqual(self.model.global_depths["Algebra"], [0, 1])
        # Ana.base sits above Alg.base; Ana.top above Alg.mid and Ana.base.
        self.assertEqual(self.model.global_depths["Analysis"], [1, 2])

    def test_dangling_and_self_dependencies_are_dropped(self):
        records = [
            record("TauCeti.A.x", "TauCeti.A.M",
                   deps=["TauCeti.A.x", "TauCeti.Gone.y"]),
        ]
        model = build_site_model(records)
        self.assertEqual(model.intra_deps["A"], [[]])
        self.assertEqual(model.cross_deps["A"], [[]])


class BuildAreaShardTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = pathlib.Path(self.tmp.name)
        module_dir = root / "TauCeti" / "Analysis"
        module_dir.mkdir(parents=True)
        (module_dir / "B.lean").write_text(
            "theorem base : True := trivial\n"
            "-- filler\n-- filler\n-- filler\n"
            "lemma top : True := trivial\n",
            encoding="utf-8",
        )
        self.model = build_site_model([dict(r) for r in FIXTURE])
        self.shard = build_area_shard(
            self.model, "Analysis", SourceCache(root), commit="abc123"
        )

    def tearDown(self):
        self.tmp.cleanup()

    def test_shard_header(self):
        self.assertEqual(self.shard["area"], "Analysis")
        self.assertEqual(self.shard["commit"], "abc123")
        self.assertEqual(self.shard["areas"], ["Algebra", "Analysis"])
        self.assertEqual(self.shard["modules"], ["TauCeti.Analysis.B"])

    def test_kind_is_refined_from_source(self):
        kinds = [node["kind"] for node in self.shard["decls"]]
        self.assertEqual(kinds, ["theorem", "lemma"])

    def test_statements_are_sliced(self):
        self.assertEqual(self.shard["decls"][0]["statement"],
                         "theorem base : True")

    def test_cross_references_carry_area_id_and_name(self):
        top = self.shard["decls"][1]
        self.assertEqual(top["xdeps"], [[0, 1, "TauCeti.Alg.mid"]])
        self.assertNotIn("xrev", top)

    def test_global_depth_is_recorded(self):
        self.assertEqual([node["gdepth"] for node in self.shard["decls"]],
                         [1, 2])

    def test_stats(self):
        stats = self.shard["stats"]
        self.assertEqual(stats["nodes"], 2)
        self.assertEqual(stats["edges"], 1)
        self.assertEqual(stats["xout"], 2)
        self.assertEqual(stats["xin"], 0)
        self.assertEqual(stats["maxDepth"], 1)
        self.assertEqual(stats["gmaxDepth"], 2)
        self.assertEqual(stats["kinds"], {"lemma": 1, "theorem": 1})

    def test_missing_source_keeps_extractor_kind(self):
        shard = build_area_shard(
            self.model, "Algebra", SourceCache(pathlib.Path(self.tmp.name)),
            commit="abc123",
        )
        self.assertEqual(shard["decls"][0]["kind"], "theorem")
        self.assertEqual(shard["decls"][0]["statement"], "")


class BuildIndexTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = pathlib.Path(self.tmp.name)
        self.model = build_site_model([dict(r) for r in FIXTURE])
        cache = SourceCache(root)
        self.shards = {
            slug: build_area_shard(self.model, slug, cache, "abc123")
            for slug in self.model.slugs
        }
        self.index = build_index(self.model, self.shards, "abc123")

    def tearDown(self):
        self.tmp.cleanup()

    def test_totals(self):
        totals = self.index["totals"]
        self.assertEqual(totals["areas"], 2)
        self.assertEqual(totals["decls"], 4)
        self.assertEqual(totals["edges"], 4)  # 2 intra + 2 cross
        self.assertEqual(totals["xedges"], 2)
        self.assertEqual(totals["maxDepth"], 2)  # global chain length
        self.assertEqual(totals["kinds"], {"theorem": 4})

    def test_area_rows_in_slug_order(self):
        rows = self.index["areas"]
        self.assertEqual([row["slug"] for row in rows], ["Algebra", "Analysis"])
        self.assertEqual(rows[0]["xin"], 2)
        self.assertEqual(rows[1]["xout"], 2)
        self.assertEqual(rows[0]["modules"], 1)

    def test_area_edges_matrix(self):
        self.assertEqual(self.index["areaEdges"], [[1, 0, 2]])

    def test_declaration_index(self):
        decls = build_declaration_index(self.model, self.shards, self.index)
        self.assertEqual(decls["areas"], ["Algebra", "Analysis"])
        self.assertEqual(decls["kinds"], ["theorem"])
        self.assertEqual(len(decls["decls"]), 4)
        self.assertEqual(decls["decls"][0], ["TauCeti.Alg.base", 0, 0, 0])


class GenerateSiteTest(unittest.TestCase):
    def test_end_to_end(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            dump = root / "dump.jsonl"
            dump.write_text(
                "\n".join(json.dumps(r) for r in FIXTURE), encoding="utf-8"
            )
            static = root / "static"
            (static / "assets").mkdir(parents=True)
            (static / "index.html").write_text("<html>", encoding="utf-8")
            (static / "assets" / "style.css").write_text("body{}", "utf-8")
            templates = root / "templates"
            templates.mkdir()
            (templates / "area.html").write_text(
                "<title>${TITLE}</title><body data-slug=\"${SLUG}\">",
                encoding="utf-8",
            )
            out = root / "site"
            summary = generate_site(
                dump_path=dump,
                repo_root=root,
                out_dir=out,
                commit="abc123",
                static_dir=static,
                templates_dir=templates,
            )
            self.assertEqual(summary.areas, 2)
            self.assertEqual(summary.decls, 4)
            self.assertEqual(summary.edges, 4)
            self.assertEqual(summary.cross_edges, 2)
            self.assertTrue((out / "index.html").is_file())
            self.assertTrue((out / "assets" / "style.css").is_file())
            index = json.loads((out / "data" / "index.json").read_text("utf-8"))
            self.assertEqual(index["commit"], "abc123")
            decls = json.loads((out / "data" / "decls.json").read_text("utf-8"))
            self.assertEqual(len(decls["decls"]), 4)
            for slug in ("Algebra", "Analysis"):
                shard_path = out / "data" / "areas" / f"{slug}.json"
                self.assertTrue(shard_path.is_file())
                page = (out / "a" / slug / "index.html").read_text("utf-8")
                self.assertIn(f'data-slug="{slug}"', page)
                self.assertIn(f"<title>{slug}</title>", page)


if __name__ == "__main__":
    unittest.main()
