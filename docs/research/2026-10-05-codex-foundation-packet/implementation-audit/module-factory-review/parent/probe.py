"""Finite design controls, not Lean or native-runtime execution.

Question: can identical primitive inventories justify replacing a module's
selection, ordering or private-state contract with one universal default?
Run from this scratch directory with Python 3. Writes outputs here only.
"""
import json
import platform
from pathlib import Path


def sweep(free, requests, strict):
    chosen = []
    for identity, count in requests:
        if count > free:
            if strict:
                break
            continue
        free -= count
        chosen.append(identity)
    return {"chosen": chosen, "free": free}


def borrow_pair(keys):
    # Each private counter starts at one. Both independent logical objects
    # promise a successful first borrow. The alias mutant violates freshness.
    store = {key: 1 for key in keys}
    results = []
    for key in keys:
        available = store[key] > 0
        results.append(available)
        if available:
            store[key] -= 1
        assert all(0 <= value <= 1 for value in store.values())
    return {"results": results, "values": list(store.values())}


checks = []


def record(name, inputs, actual, expected):
    assert actual == expected, (name, actual, expected)
    checks.append({"name": name, "inputs": inputs, "actual": actual,
                   "expected": expected, "pass": True})


requests = [("large", 2), ("small", 1)]
record("semaphore-live-eligibility", [1, requests], sweep(1, requests, False),
       {"chosen": ["small"], "free": 0})
record("strict-head-mutant-differs", [1, requests], sweep(1, requests, True),
       {"chosen": [], "free": 1})
record("enough-permits-positive", [3, requests],
       sweep(3, requests, False) == sweep(3, requests, True), True)

for order, same in [(["z", "a"], False), (["a", "z"], True)]:
    record("cache-insertion-versus-sorted-" + "".join(order), order,
           order[0] == sorted(order)[0], same)

record("separate-private-cells", [0, 1], borrow_pair([0, 1]),
       {"results": [True, True], "values": [0, 0]})
record("alias-mutant-local-bounds-still-pass", [0, 0], borrow_pair([0, 0]),
       {"results": [True, False], "values": [0]})
record("single-module-positive", [0], borrow_pair([0]),
       {"results": [True], "values": [0]})

result = {
    "kind": "finite Python design controls",
    "python": platform.python_version(),
    "frozen_source_commit": "a02126a85051ab7ec0be0a3bd30471feb18fbdd3",
    "native_or_Lean_execution": False,
    "checks": checks,
    "exclusions": [
        "No failing current module or generated artifact is alleged.",
        "The alias is a constructed violation of private allocation, not a reachable fresh allocation.",
        "These models do not establish native scheduling, cancellation, or liveness.",
        "The cache test concerns ordering only, not lookup or expiry."
    ]
}
Path(__file__).with_name("results.json").write_text(json.dumps(result, indent=2) + "\n")
print(f"{len(checks)} finite design controls passed; no Lean or runtime execution")
