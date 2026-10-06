#!/usr/bin/env python3
"""Finite mirror of QueueSteps' comparison projections. Not Lean or full evaluator."""
import copy
import json
import platform

checks = []
def check(name, actual, expected):
    assert actual == expected, (name, actual, expected)
    checks.append({'name': name, 'actual': actual, 'expected': expected})

def state(takers, peekers=()):
    return {'cap': 2, 'messages': [], 'takers': list(takers), 'offers': [], 'peekers': list(peekers)}

def encode_state(s):
    # Mirrors stateTerm's omission of bounds and peekers.
    return {'cap': s['cap'], 'msgs': s['messages'],
            'takers': [(t['id'], 1000+t['id']) for t in s['takers']], 'offers': []}

def model_offer_room(s, message):
    out = copy.deepcopy(s)
    out['messages'].append(message)
    takers = out['takers']
    signals = []
    if takers and len(out['messages']) >= takers[0]['min']:
        signals.append(takers[0]['id'])
    if out['messages']:
        signals.extend(out['peekers'])
    return out, signals

def projected_result(out, signals):
    # Mirrors again(...).filterMap(...takers.find?).
    wakes = [(n, 1000+n) for n in signals if any(t['id'] == n for t in out['takers'])]
    return ((('some', True), wakes), encode_state(out))

def concrete_room_result(s, message):
    out = copy.deepcopy(s)
    out['messages'].append(message)
    wakes = [(out['takers'][0]['id'], 1000+out['takers'][0]['id'])] if out['takers'] else []
    return ((('some', True), wakes), encode_state(out))

def exact_taker_decoder(out, signals):
    result = []
    for n in signals:
        matches = [t for t in out['takers'] if t['id'] == n]
        if len(matches) != 1:
            return None
        result.append((n, 1000+n))
    return result

t1 = {'id': 1, 'min': 1, 'max': 1}
s0 = state([t1])
s1 = state([t1], [2])
o0, g0 = model_offer_room(s0, 7)
o1, g1 = model_offer_room(s1, 7)
check('allowed C4 model notifications', g0, [1])
check('allowed C4 projected comparison', concrete_room_result(s0, 7) == projected_result(o0, g0), True)
check('outside-profile peeker model notifications', g1, [1, 2])
check('state encoding erases peeker', encode_state(s0) == encode_state(s1), True)
check('comparison erases peeker signal', projected_result(o0, g0) == projected_result(o1, g1), True)
check('outside-profile false positive of projection', concrete_room_result(s1, 7) == projected_result(o1, g1), True)
check('exact decoder allowed positive', exact_taker_decoder(o0, g0), [(1, 1001)])
check('exact decoder refuses dropped peeker', exact_taker_decoder(o1, g1), None)

s2 = state([{'id': 1, 'min': 2, 'max': 2}])
o2, g2 = model_offer_room(s2, 7)
check('stored two-bound request model not ready', g2, [])
check('stored bounds omitted from encoding', encode_state(s0) == encode_state(s2), True)
check('concrete scalar wake differs outside stored-bound premise', concrete_room_result(s2, 7) == projected_result(o2, g2), False)

# Same-shaped finite result mutations. Every reply and state stays fixed.
# These values mirror result structure, not Lean value encoding.
next_state = {'msgs': [2], 'takers': [(2, 1002)], 'offers': [], 'cap': 1}
take_good = ((('some', 1), [(101, 1101)], [(2, 1002)]), next_state)
take_bad_order = ((('some', 1), [(2, 1002)], [(101, 1101)]), next_state)
check('take positive same result', take_good == copy.deepcopy(take_good), True)
check('take same-shaped order mutant rejected', take_good == take_bad_order, False)
check('bare-state red rejects corrected result', take_good == next_state, False)
check('bare-state red also rejects broken-order result', take_bad_order == next_state, False)
offer_good = ((('none',), [(1, 1001)]), {'msgs': [1], 'takers': [(1, 1001)], 'offers': [101], 'cap': 1})
offer_no_wake = ((('none',), []), copy.deepcopy(offer_good[1]))
check('offer positive same result', offer_good == copy.deepcopy(offer_good), True)
check('offer same-shaped missing-wake mutant rejected', offer_good == offer_no_wake, False)

print(json.dumps({'scope': 'finite Python mirrors of projection and result comparison only',
                  'python': platform.python_version(), 'checks': checks,
                  'count': len(checks), 'lean_executed': False}, indent=2))
