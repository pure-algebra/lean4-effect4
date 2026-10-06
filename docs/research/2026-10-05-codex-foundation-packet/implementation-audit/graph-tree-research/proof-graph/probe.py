"""Finite mirrors, not Lean execution or evidence about the current report's size.

The first function follows Plan.walk's stack, seen set, stop set and loop bound.
The second follows the repaired Tools.Semantics.reachThrough queue discipline.
"""
import json


def nearest_walk(graph, start, stops, budget):
    stack = list(start)
    seen, nearest = set(), []
    for _ in range(budget):
        if not stack:
            break
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        if node in stops:
            nearest.append(node)
            continue
        stack.extend(graph.get(node, []))
    return nearest, stack


def reach(graph, start, budget):
    todo, seen = list(dict.fromkeys(start)), []
    for _ in range(budget):
        if not todo:
            break
        node = todo.pop(0)
        seen.append(node)
        todo.extend(d for d in dict.fromkeys(graph.get(node, []))
                    if d not in seen and d not in todo)
    return seen, todo


results = []


def check(name, condition):
    assert condition, name
    results.append({"control": name, "passed": True})


chain = {"a": ["b"], "b": ["goal"]}
check("nearest_positive_sufficient", nearest_walk(chain, ["a"], {"goal"}, 3) == (["goal"], []))
check("nearest_bounded_cut_has_pending", nearest_walk(chain, ["a"], {"goal"}, 2) == ([], ["goal"]))
check("nearest_current_return_discards_pending", nearest_walk(chain, ["a"], {"goal"}, 2)[0] == [])
diamond = {"a": ["b", "c"], "b": ["leaf"], "c": ["leaf"], "leaf": ["goal"]}
check("nearest_shared_descendant_control", nearest_walk(diamond, ["a"], {"goal"}, 8) == (["goal"], []))
seen, pending = reach(diamond, ["a", "a"], 5)
check("renderer_distinct_node_bound", set(seen) == {"a", "b", "c", "leaf", "goal"} and not pending)
check("renderer_reports_exhaustion", reach(chain, ["a"], 2) == (["a", "b"], ["goal"]))
check("renderer_cycle_terminates", reach({"a": ["b"], "b": ["a"]}, ["a"], 2) == (["a", "b"], []))
check("stop_is_cut_not_full_dependency", nearest_walk({"a": ["cut"], "cut": ["goal"]}, ["a"], {"cut", "goal"}, 8) == (["cut"], []))

print(json.dumps({"kind": "finite Python mirror", "controls": results,
 "excluded": ["Lean execution", "kernel proof", "current report exhaustion"],
 "finding": "Plan.walk discards unfinished stack; renderer already retains unfinished queue"}, indent=2))
