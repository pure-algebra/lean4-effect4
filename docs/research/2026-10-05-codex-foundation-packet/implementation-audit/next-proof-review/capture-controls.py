"""Finite mirror of Authoring.Names.resolve and Env.push; no Lean execution.

Question: do name distinctness and stable elaboration matter independently
of the resulting value's type? Inputs are constructed, not reachable runs.
"""
import json
import platform
from pathlib import Path


def resolve(names, name):
    answer = None
    for index, current in enumerate(names):
        if current == name:
            answer = index
    return answer


def read(names, values, name):
    index = resolve(names, name)
    return None if index is None else values[index]


checks = []


def check(label, actual, expected):
    assert actual == expected, (label, actual, expected)
    checks.append(dict(label=label, actual=actual, expected=expected))


names = ["_%answer0"]
values = [41]
extended = names + ["_%acc1", "_%item1"]
check("minted caller positive before fold", read(names, values, names[0]), 41)
check("minted caller positive under fold", read(extended, values + [17, 23], names[0]), 41)
check("distinct suffix preserves earlier shadow resolution",
      read(["x", "x", "a", "b"], [1, 2, 3, 4], "x"), 2)
check("same-type accumulator collision changes identity",
      read(["_%acc1", "_%acc1", "_%item1"], [41, 17, 23], "_%acc1"), 17)
check("unbound name remains unbound", resolve(extended, "missing"), None)

# TermSrc is a function of the environment. A literal built from its length
# has no free variable and stays Nat-typed, yet re-elaboration changes it.
check("environment-sensitive source before extension", len(names), 1)
check("environment-sensitive source after extension", len(extended), 3)
check("closed constant positive before and after", (7, 7), (7, 7))

out = {
    "question": __doc__,
    "python": platform.python_version(),
    "command": "python3 capture-controls.py",
    "checks": checks,
    "passed": len(checks),
    "evidence": "Finite Python source mirror only; no Lean proof or runtime execution",
    "observation": "Selected index/value and environment-dependent literal",
    "excluded": ["actual wrapper", "reachability", "Lean elaboration", "universal theorem"],
}
Path(__file__).with_name("capture-controls.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({"passed": len(checks), "evidence": out["evidence"]}))
