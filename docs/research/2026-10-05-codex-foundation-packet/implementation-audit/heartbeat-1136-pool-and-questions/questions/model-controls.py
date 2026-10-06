"""Finite transcription of Pool card transitions, not Lean or host execution."""
import json
from copy import deepcopy

initial = dict(items=[1], idle=[], leases={1: 'H'}, waiters=['A', 'B'], closing=False)
def partition(s):
    return sorted(s['idle'] + list(s['leases'])) == sorted(s['items']) and not set(s['idle']) & set(s['leases'])
def candidate_invariant(s):
    return s['closing'] or not s['idle'] or not s['waiters']
def give_back(s, item):
    r = deepcopy(s)
    del r['leases'][item]
    r['idle'].insert(0, item)
    return r

after = give_back(initial, 1)
assert partition(initial) and candidate_invariant(initial)
assert partition(after)
assert not candidate_invariant(after)
assert after['waiters'] == initial['waiters']
withdrawn = deepcopy(after)
withdrawn['waiters'].remove('A')
selected = withdrawn['waiters'][:1]
assert selected == ['B']
assert withdrawn['idle'] == [1]  # Selection is a hint, not a lease.
no_waiters = deepcopy(initial)
no_waiters['waiters'] = []
assert candidate_invariant(give_back(no_waiters, 1))
# Transition admission can hold even though the candidate state invariant does not.
def may_enrol(s):
    return not s['closing'] and not s['idle']
assert may_enrol(initial) and not may_enrol(after)
print(json.dumps(dict(evidence='finite pure Python model; not a Lean or host result', assertions=8,
    before=initial, after_return_before_helper=after, candidate_invariant=False,
    item_partition_preserved=True, selected_after_A_withdraws=selected,
    enrol_admission_before=True, enrol_admission_after=False), indent=2))
