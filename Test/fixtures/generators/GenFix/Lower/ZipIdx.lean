/-!
# GenFix.Lower.ZipIdx — a root that reaches `List.zipIdx` through the LCNF route (a fixture)

The wave's `sub` reads a reference's arguments with their positions (`xs.zipIdx`, the form the
generated view's `app` arm lemma proves; probe Q, Q2), and `sub` is in the closures of
`ocaml/gen/api_gen.ml` and `ocaml/engine/api_engine.ml`. `List.zipIdx`'s mono declaration builds
`Array.mk l`, which the translator rendered as an OCaml record `{ to_list = l }`; under the
Array-as-list shim (`src/OCaml5/Lcnf/Types.lean`) no such record exists, so `ocamlopt` refused the
file ("Unbound record field to_list") while the translator's own check passed it (probe Q, Q5,
tested; seat W2's log `gen/lcnf-zipidx-base-dune.log` reproduces it at the base). With the
translator row of `Translate-array-mk.patch` (`Array.mk l` is `l`) the lowered file builds and its
answers agree with Lean's (`scripts/test-generators.py`, case `lcnf-zipidx`).
-/

namespace GenFix.Lower

/-- A reference's argument: named, or a hole. The closure destructs it, so the lowered file has a
type group (a closure with no type renders an empty `type` group, a syntax error `Ml.checkModule`
does not see: seat W2's finding, `gen/lcnf-zipidx-notype-dune.log`). -/
inductive Arg where
  | name (s : String)
  | hole

def Arg.text : Arg → String
  | .name s => s
  | .hole => "_"

/-- Each argument with its position, as `sub`'s `app` arm reads a reference's arguments. -/
def indexed (xs : List Arg) : List (String × Nat) := (xs.map Arg.text).zipIdx

/-- The positions of the arguments named `a`, summed: one observation of `indexed` the check
prints from OCaml and from Lean. -/
def positionsOfA (xs : List Arg) : Nat :=
  (indexed xs).foldl (fun acc p => if p.1 = "a" then acc + p.2 else acc) 0

#guard positionsOfA [.name "a", .name "b", .name "a", .hole, .name "a"] = 6
#guard indexed [.name "x", .hole] = [("x", 0), ("_", 1)]

end GenFix.Lower
