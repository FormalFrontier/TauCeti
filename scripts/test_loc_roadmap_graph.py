#!/usr/bin/env python3
"""Unit tests for the per-roadmap line chart."""

import unittest

import loc_roadmap_graph as graph


def pr(number, title, area, additions, deletions, day="2026-07-01"):
    return {
        "number": number,
        "title": title,
        "labels": [{"name": area}],
        "mergedAt": f"{day}T12:00:00Z",
        "additions": additions,
        "deletions": deletions,
    }


class RoadmapSeries(unittest.TestCase):
    def test_excludes_maintenance_even_with_area_label(self):
        prs = [
            pr(1, "feat: add theorem", "roadmap/PDE", 20, 2),
            pr(2, "refactor(PDE): share proof", "roadmap/PDE", 100, 5),
            pr(3, "fix: repair theorem", "roadmap/PDE", 10, 1),
        ]
        dates, order, series, totals = graph.build_series(prs)
        self.assertEqual(dates, ["2026-07-01"])
        self.assertEqual(order, ["roadmap/PDE"])
        self.assertEqual(series, {"roadmap/PDE": [18]})
        self.assertEqual(totals, {"roadmap/PDE": 18})

    def test_still_excludes_none_and_unknown(self):
        prs = [
            pr(1, "feat: add theorem", "roadmap/none", 10, 0),
            pr(2, "feat: add another theorem", "roadmap/Unknown", 10, 0),
        ]
        self.assertEqual(graph.build_series(prs), ([], [], {}, {}))

    def test_rejects_negative_cumulative_area(self):
        prs = [
            pr(1, "feat: remove obsolete API", "roadmap/PDE", 0, 5),
        ]
        with self.assertRaisesRegex(ValueError, "negative cumulative"):
            graph.build_series(prs)


class TruncationTest(unittest.TestCase):
    """A cumulative chart cannot survive losing its oldest rows.

    `gh pr list` returns at most --limit results, newest first, and reports nothing when it
    stops there. The limit was 2000 while the repository had 5072 merged pull requests, so every
    band silently began 3000 pull requests too late and the chart looked entirely plausible.
    """

    def test_a_full_result_is_refused_rather_than_drawn(self):
        prs = [pr(n, "feat: add theorem", "roadmap/PDE", 1, 0)
               for n in range(graph.MERGED_PR_CEILING)]
        with self.assertRaisesRegex(RuntimeError, "ceiling"):
            graph.check_complete(prs)

    def test_a_short_result_is_accepted(self):
        self.assertIsNone(graph.check_complete([pr(1, "feat: x", "roadmap/PDE", 1, 0)]))

    def test_the_ceiling_is_well_clear_of_the_project(self):
        # The point of the ceiling is to stop a runaway query, not to bound the project. If it
        # ever sits near the real number of merged pull requests, the guard above starts firing
        # on healthy runs instead of on a bug.
        self.assertGreaterEqual(graph.MERGED_PR_CEILING, 50_000)


if __name__ == "__main__":
    unittest.main()
