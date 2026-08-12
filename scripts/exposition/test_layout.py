#!/usr/bin/env python3
"""Tests for the exposition layout module.

Run with:

    python3 scripts/exposition/test_layout.py
"""

import unittest

from layout import compute_layout, longest_path_layers


class LongestPathLayersTest(unittest.TestCase):
    def test_empty_graph(self):
        self.assertEqual(longest_path_layers([]), [])

    def test_isolated_nodes_share_layer_zero(self):
        self.assertEqual(longest_path_layers([[], [], []]), [0, 0, 0])

    def test_chain_layers_by_distance(self):
        # 2 -> 1 -> 0
        self.assertEqual(longest_path_layers([[], [0], [1]]), [0, 1, 2])

    def test_longest_path_wins_over_shortest(self):
        # 3 depends on 0 directly and via 1 -> 2; longest path decides.
        dependencies = [[], [0], [1], [0, 2]]
        self.assertEqual(longest_path_layers(dependencies), [0, 1, 2, 3])

    def test_cycle_members_share_a_layer(self):
        # 1 <-> 2 form an SCC above 0; 3 sits above the cycle.
        dependencies = [[], [0, 2], [1], [2]]
        layers = coalesced = longest_path_layers(dependencies)
        self.assertEqual(coalesced[0], 0)
        self.assertEqual(layers[1], layers[2])
        self.assertEqual(layers[3], layers[1] + 1)

    def test_deep_chain_does_not_recurse(self):
        # A 50k-node chain would blow the recursion limit if Tarjan or the
        # layering were recursive.
        n = 50_000
        dependencies = [[] if i == 0 else [i - 1] for i in range(n)]
        layers = longest_path_layers(dependencies)
        self.assertEqual(layers[-1], n - 1)


class ComputeLayoutTest(unittest.TestCase):
    def test_layer_sizes_count_nodes_per_layer(self):
        # Two roots, one node above each root, one node above both.
        dependencies = [[], [], [0], [1], [2, 3]]
        layout = compute_layout(dependencies)
        self.assertEqual(layout.node_layers, [0, 0, 1, 1, 2])
        self.assertEqual(layout.layer_sizes, [2, 2, 1])

    def test_orders_are_a_permutation_within_each_layer(self):
        dependencies = [[], [], [], [0, 2], [1], [2]]
        layout = compute_layout(dependencies)
        by_layer: dict[int, list[int]] = {}
        for node, layer in enumerate(layout.node_layers):
            by_layer.setdefault(layer, []).append(layout.node_orders[node])
        for orders in by_layer.values():
            self.assertEqual(sorted(orders), list(range(len(orders))))

    def test_barycenter_aligns_dependents_with_dependencies(self):
        # Layer 0 holds 0,1,2 (initial order 0,1,2). Node 3 uses only 2 and
        # node 4 uses only 0: after crossing reduction, 3 should sit below 4
        # (matching its dependency's row), not in id order.
        dependencies = [[], [], [], [2], [0]]
        layout = compute_layout(dependencies)
        self.assertGreater(layout.node_orders[3], layout.node_orders[4])

    def test_deterministic(self):
        dependencies = [[], [0], [0], [1, 2], [3], [0, 3]]
        first = compute_layout(dependencies)
        second = compute_layout(dependencies)
        self.assertEqual(first.node_layers, second.node_layers)
        self.assertEqual(first.node_orders, second.node_orders)
        self.assertEqual(first.layer_sizes, second.layer_sizes)


if __name__ == "__main__":
    unittest.main()
