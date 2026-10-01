import Effect4.Api
import Effect4.Schema.Bridge
import Effect4.Schema.Codec
import Effect4.Laws.Program.Typed.Membership

/-!
# RED CONTROL for `PedigreeProbe.lean`: every check below must FAIL.

Each line asserts the opposite of a fact the probe found, so the probe's guards are shown not
to be vacuous. Expected result: exit 1 with exactly four errors, R1 to R4, and no other error.
-/

set_option autoImplicit false

namespace DataProbe.PedigreeRed

open Effect4 Effect4.Program Effect4.Machine

-- R1 (must fail): "a schema struct reads back as a pair type".
#guard Effect4.Schema.Bridge.ofSchema
    (Effect4.Schema.struct [Effect4.Schema.property "id" Effect4.Schema.string]) =
  some (.prod .string .string)

-- R2 (must fail): "admission refuses an uninhabited product answer".
def pNeverPair : Api.Program :=
  .bind (.fail (.lit (.nat 1)))
    (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil))))
#guard (match Effect4.Program.admitProgram pNeverPair with | .ok _ => false | .error _ => true)

-- R3 (must fail): "the codec refuses a reordered object".
def someReordered : Json := .obj [("value", Effect4.Arch.Json.ofNat 1), ("_tag", .str "Some")]
#guard Effect4.Schema.decode (.option .nat) someReordered = none

-- R4 (must fail): a value fitting `prod never nat`.
theorem fits_prod_never_nat_inhabited (w : Typed.World) :
    Typed.Fits w (.list [.nat 0, .nat 1]) (.prod .never .nat) := by
  unfold Typed.Fits
  exact ⟨trivial, trivial⟩

end DataProbe.PedigreeRed
