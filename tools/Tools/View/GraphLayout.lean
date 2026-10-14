import Tools.View.GraphCheck

/-! # Checked graph layout

This producer joins input admission, layout, and allocation admission.
The checker stays independent of layout's text measurement.
Placement: `docs/research/2026-10-13-graph-library-plan.md`, R14, concept 7, row 334 (3).
-/

namespace Tools.View.GraphLayout

/-- Check input, compute layout once, then check allocations and route lookups. -/
def checked (g : Graph) : Except GraphCheck.Refusal (GraphCheck.Checked g) :=
  match hi : GraphCheck.input g with
  | .error reason => .error reason
  | .ok () =>
    let value := g.layout
    match hl : GraphCheck.laid value with
    | .error reason => .error reason
    | .ok () =>
      .ok ⟨value, (GraphCheck.input_iff g).mp hi, (GraphCheck.laid_iff value).mp hl⟩

end Tools.View.GraphLayout
