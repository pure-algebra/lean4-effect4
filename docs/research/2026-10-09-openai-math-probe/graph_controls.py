"""Finite exploratory controls over the fields of Tools.View.Graph.

This is an independent Python prototype, not an execution of upstream Lean.
Vertex positions and original edge occurrences stay distinct. Query relations
are selected before this layer; it never infers program semantics from topology.
"""
from dataclasses import dataclass
from itertools import combinations, permutations
import json

@dataclass(frozen=True)
class Edge:
    key: str
    src: int
    dst: int
    role: str = 'dependency'

@dataclass(frozen=True)
class Graph:
    n: int
    edges: tuple[Edge, ...]

    def validate(self):
        if self.n < 0 or any(not (0 <= e.src < self.n and 0 <= e.dst < self.n)
                             for e in self.edges):
            raise ValueError('invalid endpoint')
        return self

    def reachable(self, roots, *, reverse=False):
        self.validate()
        seen = set(roots)
        if not seen <= set(range(self.n)):
            raise ValueError('invalid root')
        todo = list(seen)
        while todo:
            u = todo.pop()
            for e in self.edges:
                a, b = (e.dst, e.src) if reverse else (e.src, e.dst)
                if a == u and b not in seen:
                    seen.add(b)
                    todo.append(b)
        return frozenset(seen)

    def forest(self):
        self.validate()
        parent = list(range(self.n))
        def root(u):
            while parent[u] != u:
                u = parent[u]
            return u
        keep = []
        for i, e in enumerate(self.edges):
            a, b = root(e.src), root(e.dst)
            if a != b:
                parent[b] = a
                keep.append(i)
        return tuple(keep)

    def select(self, nodes):
        self.validate()
        nodes = frozenset(nodes)
        if not nodes <= set(range(self.n)):
            raise ValueError('invalid selection')
        internal = tuple(i for i, e in enumerate(self.edges)
                         if e.src in nodes and e.dst in nodes)
        crossing = tuple(i for i, e in enumerate(self.edges)
                         if (e.src in nodes) != (e.dst in nodes))
        return internal, crossing


def closure_oracle(g, *, weak):
    """Independent finite path relation by transitive closure."""
    g.validate()
    reach = [[i == j for j in range(g.n)] for i in range(g.n)]
    for e in g.edges:
        reach[e.src][e.dst] = True
        if weak:
            reach[e.dst][e.src] = True
    for k in range(g.n):
        for i in range(g.n):
            for j in range(g.n):
                reach[i][j] |= reach[i][k] and reach[k][j]
    return reach


def refine_pair(a, b, rounds, *, roles=True):
    """Bounded directed vertex refinement; one palette for BOTH inputs."""
    colors = [[0] * a.n, [0] * b.n]
    for _ in range(rounds):
        signatures = []
        for g, cs in zip((a, b), colors):
            signatures.append([
                (cs[v], tuple(sorted((e.role if roles else '', cs[e.src])
                                      for e in g.edges if e.dst == v)),
                 tuple(sorted((e.role if roles else '', cs[e.dst])
                              for e in g.edges if e.src == v)))
                for v in range(g.n)])
        palette = {s: i for i, s in enumerate(sorted(set(signatures[0] + signatures[1])))}
        colors = [[palette[s] for s in ss] for ss in signatures]
    return [tuple(sorted(cs)) for cs in colors]


def edge_graph(n, pairs):
    return Graph(n, tuple(Edge(str(i), a, b) for i, (a, b) in enumerate(pairs)))


def bidirected(n, pairs):
    return edge_graph(n, [(x, y) for a, b in pairs for x, y in ((a, b), (b, a))])


def main():
    pairs = list(combinations(range(4), 2))
    graphs = 0
    selections = 0
    reach_checks = 0
    for bits in range(1 << len(pairs)):
        g = edge_graph(4, [p for i, p in enumerate(pairs) if bits & (1 << i)])
        keep = g.forest()
        sub = Graph(g.n, tuple(g.edges[i] for i in keep))
        original = closure_oracle(g, weak=True)
        assert original == closure_oracle(sub, weak=True)
        component_count = len({tuple(row) for row in original})
        assert len(keep) == g.n - component_count
        for root in range(g.n):
            expect = frozenset(i for i, yes in enumerate(closure_oracle(g, weak=False)[root]) if yes)
            assert g.reachable([root]) == expect
            reach_checks += 1
        for mask in range(1 << g.n):
            nodes = {v for v in range(g.n) if mask & (1 << v)}
            inside, cross = g.select(nodes)
            assert set(inside).isdisjoint(cross)
            assert set(inside) | set(cross) == {
                i for i, e in enumerate(g.edges) if e.src in nodes or e.dst in nodes}
            selections += 1
        graphs += 1
    for g in (Graph(0, ()), Graph(1, ()), edge_graph(2, [(0, 1), (0, 1), (0, 0)])):
        sub = Graph(g.n, tuple(g.edges[i] for i in g.forest()))
        assert closure_oracle(g, weak=True) == closure_oracle(sub, weak=True)
    refused = 0
    for g in (edge_graph(1, [(0, 1)]), edge_graph(2, [(-1, 0)])):
        try:
            g.forest()
        except ValueError:
            refused += 1
    assert refused == 2

    # A weak spanning forest loses directed paths and cycles.
    cycle = edge_graph(3, [(0, 1), (1, 2), (2, 0)])
    tree = Graph(3, tuple(cycle.edges[i] for i in cycle.forest()))
    assert closure_oracle(cycle, weak=True) == closure_oracle(tree, weak=True)
    assert cycle.reachable([2]) != tree.reachable([2])

    # Equal refinement colors do not certify connectedness, let alone isomorphism.
    six = bidirected(6, [(i, (i + 1) % 6) for i in range(6)])
    triangles = bidirected(6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)])
    left, right = refine_pair(six, triangles, 6)
    assert left == right
    assert closure_oracle(six, weak=True) != closure_oracle(triangles, weak=True)

    # Check permutation invariance without relying on independently numbered colors.
    specimen = Graph(4, (Edge('a', 0, 1, 'fork'), Edge('b', 1, 2, 'wait'), Edge('c', 0, 3, 'fork')))
    permutation_checks = 0
    for perm in permutations(range(4)):
        moved = Graph(4, tuple(Edge(e.key, perm[e.src], perm[e.dst], e.role) for e in specimen.edges))
        x, y = refine_pair(specimen, moved, 4)
        assert x == y
        permutation_checks += 1
    fork = Graph(2, (Edge('x', 0, 1, 'fork'),))
    wait = Graph(2, (Edge('x', 0, 1, 'wait'),))
    assert len(set(refine_pair(fork, wait, 1))) == 2
    assert len(set(refine_pair(fork, wait, 1, roles=False))) == 1

    result = {
        'evidence': 'finite independent Python prototype; not an upstream Lean execution',
        'undirected_graphs': graphs,
        'selections_checked': selections,
        'directed_reach_queries': reach_checks,
        'permutations_checked': permutation_checks,
        'invalid_endpoints_refused': refused,
        'weak_forest_loses_directed_paths': True,
        'equal_refinement_different_connectedness': True,
        'edge_roles_affect_refinement': True,
        'all_assertions_passed': True,
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
