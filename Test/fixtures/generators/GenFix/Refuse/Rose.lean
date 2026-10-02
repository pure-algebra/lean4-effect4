/-!
# GenFix.Refuse.Rose — a nested family with no nullary constructor (a generator fixture)

The red control of `tools/Effect4Gen/Fold.lean --extras` on a nested family: `build`'s refusal
(the node a tag whose arguments do not have its sorts rebuilds to) is the family's first nullary
constructor, and this rose tree has none, so the extras refuse it by name.

Read by `scripts/test-generators.py`; not a battery module (`Test/fixtures/` is outside the
module-closure gate).
-/

namespace GenFix.Refuse

/-- A labelled rose tree: every node a label and its children; no leaf constructor. -/
inductive Rose
  | node (label : String) (kids : List Rose)

end GenFix.Refuse
