"""Finite controls and predicate counts, not a compiler or a performance theorem."""
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
raw = json.loads((HERE / 'lean-output.json').read_text())


def reference_frontiers(addresses):
    """Instrument the same predicate calls as Build.frontier; compare with actual Lean output."""
    calls = 0

    def below(a, b):
        nonlocal calls
        calls += 1
        return len(a) < len(b) and b[:len(a)] == a

    result = [[b for b in addresses if below(a, b) and
               not any(below(a, c) and below(c, b) for c in addresses)] for a in addresses]
    return result, calls


def indexed_frontiers(addresses):
    """Nearest retained ancestor in a valid preorder, one push and at most one pop per entry."""
    assert addresses == sorted(addresses)  # producer's preorder, not arbitrary path order
    assert len(set(map(tuple, addresses))) == len(addresses)
    assert addresses and addresses[0] == []
    frontiers = [[] for _ in addresses]
    stack = []
    calls = 0
    for i, address in enumerate(addresses):
        while stack:
            calls += 1
            parent = addresses[stack[-1]]
            if len(parent) < len(address) and address[:len(parent)] == parent:
                break
            stack.pop()
        if stack:
            frontiers[stack[-1]].append(address)
        stack.append(i)
    return frontiers, calls


rows = []
for case in raw['cases']:
    reference, slow = reference_frontiers(case['addresses'])
    indexed, fast = indexed_frontiers(case['addresses'])
    assert reference == case['frontiers'] == indexed, case['name']
    assert case['fillingsPresent']
    assert case['productCounts'][1] == len(case['addresses'])
    rows.append(dict(name=case['name'], nodes=len(case['addresses']),
                     reference_predicate_calls=slow, indexed_prefix_tests=fast))

# Preorder is a real premise: refuse unsorted or duplicate locations.
for bad in [[[], [1], [0]], [[], [0], [0]]]:
    try:
        indexed_frontiers(bad)
    except AssertionError:
        pass
    else:
        raise AssertionError('invalid tree index input was accepted')


def reach(vertices, edges):
    closure = set(edges)
    for middle in vertices:
        closure |= {(a, b) for a in vertices for b in vertices
                    if (a, middle) in closure and (middle, b) in closure}
    return closure


# Algebraic graph connect is an all-to-all operation, not boundary sequencing.
left, right = {0, 1}, {2, 3}
base = {(0, 1), (2, 3)}
series = base | {(1, 2)}
connect = base | {(a, b) for a in left for b in right}
assert len(series) == 3 and len(connect) == 6
assert series != connect
assert reach(left | right, series) == reach(left | right, connect)
# An order/reachability reading is a different observation from immediate labelled edges.
assert (0, 3) not in series and (0, 3) in connect

result = dict(frontier_rows=rows,
              negative_tree_controls=['unsorted refused', 'duplicate refused'],
              composition=dict(series_edges=sorted(series), connect_edges=sorted(connect),
                               same_reachability=True, same_immediate_edges=False),
              graph_controls=raw['graphControls'],
              limits=['finite agreement, not a general frontier theorem',
                      'predicate counts exclude path-element comparisons and all other work',
                      'no runtime speed or compiler optimization claim'])
(HERE / 'comparison-output.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
