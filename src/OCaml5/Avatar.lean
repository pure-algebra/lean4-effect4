import OCaml5.Avatar.Part
import OCaml5.Avatar.Probe
import OCaml5.Avatar.Fibers
import OCaml5.Avatar.Stores
import OCaml5.Avatar.Context
import OCaml5.Avatar.Layer
import OCaml5.Avatar.ForkFlow

/-!
# OCaml5.Avatar

**What it is.** The avatar's generated half as one value: `parts`, one `Part` per OCaml module
of `ocaml/avatar/` (`OCaml5.Avatar.Part`). Everything a driver or a check needs is read off it:
`Tools/RenderDeep.lean` prints `(find? name).generated`, `OCaml5.Avatar.Check` compares
`guarded` with `derived` part by part, `ocaml/tools/fuzz.sh avatar` compiles `Fibers.checkModule`.

**Depends on.** The six part modules and `OCaml5.Avatar.Part`.

**Properties.**
* **Names are unique**, so `find?` is a function — *tested* (`Check`).
* **The order is the avatar's**: fibers, stores, context, layer, forkflow — *by construction*.
-/

namespace OCaml5.Avatar

/-- Every part of the avatar, in the avatar's order. -/
def parts : List Part := [Fibers.part, Stores.part, Context.part, Layer.part, ForkFlow.part]

/-- The part `render-deep.sh` names. -/
def find? (name : String) : Option Part := parts.find? (·.name == name)

end OCaml5.Avatar
