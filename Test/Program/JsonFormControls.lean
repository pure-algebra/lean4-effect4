import Effect4.Laws.Store.ShapeRead
import Effect4.Store.Domain.ProgramWire

/-!
# The JSON form of a program: the controls

The tools print a program as JSON with each list an array (`Canonical.printArrays`), the
encoding `ts/eff/eff.gen.ts` types, and read an agent's JSON in any order
(`Canonical.ofJsonAnyOrder`). The law is exactness modulo that normaliser
(`Canonical.ofJsonAnyOrder_exact`). These two lines are finite evaluations of the round trip,
which no theorem states.

* **Tested: a program written by hand as `ts/eff/eff.gen.ts` types it reads.**
* **Tested: the tools' print reads back with every object's entries reversed.**
-/

set_option autoImplicit false

namespace Test.Program.JsonFormControls

open Effect4 Effect4.Program Effect4.Program.Wire Effect4.Store

mutual
/-- Every object's entries reversed: a JSON value an agent may write. -/
def reverseObjs : Json → Json
  | .arr js => .arr (reverseList js)
  | .obj entries => .obj (reverseEntries entries).reverse
  | j => j

def reverseList : List Json → List Json
  | [] => []
  | j :: js => reverseObjs j :: reverseList js

def reverseEntries : List (String × Json) → List (String × Json)
  | [] => []
  | (n, j) :: entries => (n, reverseObjs j) :: reverseEntries entries
end

/-- A program whose lists are not empty: the atoms' arguments. -/
def listed : NativeEff :=
  .bind (.succeed (.app "cons" (.cons (.lit (.str "buy milk")) (.cons (.app "nil" .nil) .nil))))
    (.succeed (.app "length" (.cons (.var 0) .nil)))

/-- `listed` as `ts/eff/eff.gen.ts` types it, each list an array, written by hand. -/
def listedAsTs : Json :=
  let lit (tag : String) (v : Json) : Json :=
    .obj [("_tag", .str "lit"), ("value", .obj [("_tag", .str tag), ("value", v)])]
  .obj [("_tag", .str "bind"),
    ("first", .obj [("_tag", .str "succeed"), ("value", .obj [("_tag", .str "app"),
      ("atom", .str "cons"), ("args", .arr [lit "str" (.str "buy milk"),
        .obj [("_tag", .str "app"), ("atom", .str "nil"), ("args", .arr [])]])])]),
    ("rest", .obj [("_tag", .str "succeed"), ("value", .obj [("_tag", .str "app"),
      ("atom", .str "length"), ("args", .arr [.obj [("_tag", .str "var"),
        ("index", Effect4.Arch.Json.ofNat 0)]])])])]

-- tested: the program written by hand as `ts/eff/eff.gen.ts` types it reads
#guard ((Canonical.ofJsonAnyOrder listedAsTs : Option NativeEff).map hexOf) == some (hexOf listed)
-- tested: the tools' print reads back with every object's entries reversed
#guard ((Canonical.ofJsonAnyOrder (reverseObjs (Canonical.printArrays listed)) :
  Option NativeEff).map hexOf) == some (hexOf listed)

end Test.Program.JsonFormControls
