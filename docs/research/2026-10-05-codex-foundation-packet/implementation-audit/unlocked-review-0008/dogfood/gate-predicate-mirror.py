"""Finite mirror of scenario_gate metadata predicates, not Lean or scenario execution."""
import json
# Metadata follows reviewed declaration sources. A theorem's placement is its explicit attribute.
env = {
  "crew": ("def", None, "Test.Dogfood.Scenario.Workers"),
  "observe": ("def", None, "Test.Dogfood.Scenario.Workers"),
  "workers": ("theorem", "R6", "Test.Dogfood.Scenario.Workers"),
  "receipt_inert": ("theorem", "R6", "Test.Dogfood.Scenario"),
  "applied_selects": ("theorem", "R6", "Test.Dogfood.Scenario"),
  "control_retires": ("theorem", "R6", "Test.Dogfood.Scenario"),
  "releases_once": ("theorem", "R11", "Test.Dogfood.Scenario.Workers"),
  "replays": ("theorem", "R13", "Test.Dogfood.Scenario"),
  "play_id": ("theorem", None, "Test.Dogfood.Scenario"),
  "Effect4.Run.step_id": ("theorem", None, "Effect4.Laws.Run"),
}
clauses = ["receipt_inert", "applied_selects", "control_retires", "releases_once", "replays"]
# The real controls passed in the retained build. Their scenario behavior is not rerun here.
controls = [(c, red, True) for c in clauses for red in (False, True)]
def gate(top, declarations=("crew", "observe"), clause_claims=clauses, controls=controls, law_prefix=False):
  errors = []
  for n in declarations:
    if n not in env: errors.append("unresolved declaration: " + n)
  for n in [top] + list(clause_claims):
    info = env.get(n)
    if info is None or info[0] != "theorem": errors.append("not theorem: " + n)
    elif info[1] is None and not (law_prefix and (info[2] == "Effect4.Laws" or info[2].startswith("Effect4.Laws."))):
      errors.append("unplaced: " + n)
  for c in clause_claims:
    for red in (False, True):
      if not any(name == c and is_red == red for name, is_red, _ in controls): errors.append("missing control")
  for c, _, holds in controls:
    if c not in clause_claims: errors.append("unknown clause")
    elif not holds: errors.append("failed control")
  return errors
cases = {
 "positive_workers": gate("workers", law_prefix=True),
 "wrong_top_drops_cleanup_dependency": gate("receipt_inert", law_prefix=True),
 "bad_name": gate("workers", declarations=("Nowhere.program", "observe"), law_prefix=True),
 "unplaced_battery_top": gate("play_id", law_prefix=True),
 "untagged_law_top_committed_prefix_rule": gate("Effect4.Run.step_id", law_prefix=True),
 "placed_battery_positive": gate("replays", law_prefix=True),
}
assert cases["positive_workers"] == []
assert cases["wrong_top_drops_cleanup_dependency"] == []
assert cases["bad_name"] != []
assert cases["unplaced_battery_top"] != []
assert cases["untagged_law_top_committed_prefix_rule"] == []
assert cases["placed_battery_positive"] == []
print(json.dumps({"scope":"Python metadata predicate mirror only; not Lean or a proof-dependency query", "cases":cases}, indent=2))
