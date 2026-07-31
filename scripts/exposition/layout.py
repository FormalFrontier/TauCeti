"""Layered layout for the exposition dependency graphs.

Pure Python, no third-party dependencies. Adapted from Lean Pool's exposition
layout module (Vasily Ilin, https://github.com/Vilin97/lean-pool, Apache 2.0).
The pipeline is:

1. iterative Tarjan strongly-connected components (the library has tens of
   thousands of nodes, so no recursion),
2. condensation + longest-path layering: layer 0 = no dependencies within the
   graph; every member of an SCC shares a layer; otherwise
   ``layer = 1 + max(layer(dep))`` over dependencies outside the SCC,
3. within-layer ordering by barycenter crossing reduction: the initial
   order is ascending node id (callers assign ids in ``(module, line)``
   order), then four alternating forward/backward sweeps sort each layer by
   average neighbor position with a deterministic tie-break on the initial
   order.

:func:`longest_path_layers` exposes step 2 alone: the generator uses it on
the whole library (all areas, cross-area edges included) to compute each
declaration's global depth without paying for crossing reduction.
"""

from __future__ import annotations

from dataclasses import dataclass

BARYCENTER_SWEEPS = 4


@dataclass
class Layout:
    """Computed positions: per-node layer and order, plus per-layer sizes."""

    node_layers: list[int]
    node_orders: list[int]
    layer_sizes: list[int]


def compute_layout(dependencies: list[list[int]]) -> Layout:
    """Return the layered layout for a dependency graph.

    ``dependencies[n]`` lists the node ids that node ``n`` depends on. Node
    ids double as the initial within-layer order, so callers must number
    nodes in ``(module, line)`` order.
    """
    node_layers = longest_path_layers(dependencies)
    node_orders, layer_sizes = _crossing_reduced_orders(dependencies, node_layers)
    return Layout(
        node_layers=node_layers, node_orders=node_orders, layer_sizes=layer_sizes
    )


def _strongly_connected_components(adjacency: list[list[int]]) -> list[list[int]]:
    """Return SCCs via iterative Tarjan, dependencies-first.

    With edges pointing node -> dependency, Tarjan emits each component
    after every component it can reach, so components appear in an order
    where all dependencies of a component precede it.
    """
    node_count = len(adjacency)
    visit_index = [-1] * node_count
    low_link = [0] * node_count
    on_stack = [False] * node_count
    stack: list[int] = []
    components: list[list[int]] = []
    counter = 0
    for root in range(node_count):
        if visit_index[root] != -1:
            continue
        work: list[tuple[int, int]] = [(root, 0)]
        while work:
            node, edge_index = work[-1]
            if edge_index == 0:
                visit_index[node] = low_link[node] = counter
                counter += 1
                stack.append(node)
                on_stack[node] = True
            descended = False
            for position in range(edge_index, len(adjacency[node])):
                neighbor = adjacency[node][position]
                if visit_index[neighbor] == -1:
                    work[-1] = (node, position + 1)
                    work.append((neighbor, 0))
                    descended = True
                    break
                if on_stack[neighbor]:
                    low_link[node] = min(low_link[node], visit_index[neighbor])
            if descended:
                continue
            work.pop()
            if work:
                parent = work[-1][0]
                low_link[parent] = min(low_link[parent], low_link[node])
            if low_link[node] == visit_index[node]:
                component: list[int] = []
                while True:
                    member = stack.pop()
                    on_stack[member] = False
                    component.append(member)
                    if member == node:
                        break
                components.append(component)
    return components


def longest_path_layers(dependencies: list[list[int]]) -> list[int]:
    """Return the longest-path layer of every node (SCCs share a layer)."""
    components = _strongly_connected_components(dependencies)
    component_of = [0] * len(dependencies)
    for component_index, members in enumerate(components):
        for node in members:
            component_of[node] = component_index
    component_layers = [0] * len(components)
    for component_index, members in enumerate(components):
        layer = 0
        for node in members:
            for dependency in dependencies[node]:
                if component_of[dependency] != component_index:
                    dependency_layer = component_layers[component_of[dependency]]
                    layer = max(layer, dependency_layer + 1)
        component_layers[component_index] = layer
    return [component_layers[component_of[node]] for node in range(len(dependencies))]


def _reorder_layer(
    members: list[int], neighbor_lists: list[list[int]], positions: list[int]
) -> None:
    """Sort one layer by average neighbor position; ties keep initial order.

    Nodes without neighbors keep their current position as barycenter, and
    the node id (== initial order) breaks ties deterministically.
    """

    def sort_key(node: int) -> tuple[float, int]:
        neighbors = neighbor_lists[node]
        if not neighbors:
            return (float(positions[node]), node)
        barycenter = sum(positions[neighbor] for neighbor in neighbors)
        return (barycenter / len(neighbors), node)

    members.sort(key=sort_key)
    for position, node in enumerate(members):
        positions[node] = position


def _crossing_reduced_orders(
    dependencies: list[list[int]], node_layers: list[int]
) -> tuple[list[int], list[int]]:
    """Return per-node within-layer orders and per-layer sizes."""
    layer_count = max(node_layers, default=-1) + 1
    layers: list[list[int]] = [[] for _ in range(layer_count)]
    for node in range(len(node_layers)):  # ascending id = initial order
        layers[node_layers[node]].append(node)
    dependents: list[list[int]] = [[] for _ in dependencies]
    for node, node_dependencies in enumerate(dependencies):
        for dependency in node_dependencies:
            dependents[dependency].append(node)
    positions = [0] * len(node_layers)
    for members in layers:
        for position, node in enumerate(members):
            positions[node] = position
    for sweep in range(BARYCENTER_SWEEPS):
        if sweep % 2 == 0:  # forward: order each layer by its dependencies
            for members in layers[1:]:
                _reorder_layer(members, dependencies, positions)
        else:  # backward: order each layer by its dependents
            for members in reversed(layers[:-1]):
                _reorder_layer(members, dependents, positions)
    return positions, [len(members) for members in layers]
