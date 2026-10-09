import Effect4.Laws.Store.ShapeRead
import Test.Program.SketchControls
import Test.Program.PartsControls

/-!
# The JSON form of a program: the controls

`src/Effect4/Store/Domain/ShapeRead.lean` reads a canonical carrier from its JSON print
(`Canonical.ofJson`), and from JSON whose objects are in any order (`Canonical.ofJsonAnyOrder`).
Its law is exactness (`Canonical.ofJson_exact`). These lines are finite evaluations of the round
trip, which no theorem states.

* **Tested: the round trip.** The sketch battery's program and seat HOST's client with the
  Queue's definitions read back from their prints.
* **Tested: any order.** With every object's entries reversed, the strict reader refuses, and
  the reader in any order reads the program back.
-/

set_option autoImplicit false

namespace Test.Program.JsonFormControls

open Effect4 Effect4.Program Effect4.Program.Wire Effect4.Store
open Test.Program.SketchControls
open Test.Program.PartsControls (definedClient builtOf)

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

-- tested: the sketch battery's program reads back from its print
#guard ((Canonical.ofJson (Canonical.print original) : Option NativeEff).map hexOf) ==
  some (hexOf original)
-- tested: so does the client with the Queue's definitions, a block at the root
#guard ((builtOf definedClient).map fun b =>
  ((Canonical.ofJson (Canonical.print b.program) : Option NativeEff).map hexOf) ==
    some (hexOf b.program)) == some true
-- tested: with every object reversed, the strict reader refuses, and the reader in any order
-- reads the program back
#guard ((Canonical.ofJson (reverseObjs (Canonical.print original)) : Option NativeEff).isNone,
  (Canonical.ofJsonAnyOrder (reverseObjs (Canonical.print original)) : Option NativeEff).map
    hexOf == some (hexOf original)) == (true, true)

end Test.Program.JsonFormControls
