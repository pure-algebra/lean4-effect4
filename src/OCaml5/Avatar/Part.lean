import OCaml5.Ml.Reflect

/-!
# OCaml5.Avatar.Part

**What it is.** The interface of the avatar's generated half. One `Part` per OCaml module of
`ocaml/avatar/`: the hand descriptions of its carriers (`OCaml5.Ml.Reflect`), the twins
`Tools/Describe.lean` read off the Lean environment (`OCaml5.Avatar.Derived.*`), and the block
rendered into the file. `OCaml5.Avatar.parts` lists the parts; `Tools/RenderDeep.lean` prints a
part's block, `ocaml/tools/fuzz.sh avatar` compiles and diffs it, and `OCaml5.Avatar.Check` compares
every guarded hand description with its derived twin.

**Depends on.** `OCaml5.Ml.Reflect`.

**Properties.**
* **Twins are paired by Lean name.** `Part.twins` pairs each guarded hand description with the
  derived description of the same `leanName`; a hand description with no twin is a row of the
  report, never a skipped one — *by construction*.
* **One order.** `guarded` is the order the projection report prints, which is the Lean file's
  declaration order — *tested* (`Check`, the pinned row count).
-/

namespace OCaml5.Avatar

open OCaml5.Ml

/-- One OCaml module of the avatar and the descriptions behind it. -/
structure Part where
  /-- The name `render-deep.sh`, `RenderDeep` and `fuzz.sh` use: `fibers`, `stores`, … -/
  name : String
  /-- The avatar file the block is rendered into. -/
  file : String
  /-- The hand descriptions under the projection guard, in report order. -/
  guarded : List TypeDesc
  /-- What `Tools/Describe.lean` derived from the environment; empty where the Lean carriers
  are archived (`forkflow`). -/
  derived : List TypeDesc := []
  /-- The generated block. -/
  generated : List Decl

/-- Each guarded description with its derived twin, when there is one. -/
def Part.twins (p : Part) : List (TypeDesc × Option TypeDesc) :=
  p.guarded.map fun h => (h, p.derived.find? (·.leanName == h.leanName))

end OCaml5.Avatar
