import Effect4.Api
import Effect4.Schema.Bridge
import Effect4.Schema.Codec
import Effect4.Laws.Program.Typed.Membership

/-!
# RED CONTROL for `verify-Probe.lean`: every check below must FAIL.

Each line asserts the opposite of a fact `verify-Probe.lean` found, so its guards are shown not
to be vacuous. Expected: exit 1 with exactly five errors, VR1 to VR5, and no other error.
-/

set_option autoImplicit false

namespace DataProbe.PedigreeVerifyRed

open Effect4 Effect4.Program Effect4.Machine

-- VR1 (must fail): "a filter group whose id is isInt is refused by ofSchema".
def groupedInt : Representation :=
  .number none [Effect4.Schema.Check.group
    (Effect4.Schema.Check.named "effect/schema/isGreaterThanOrEqualTo"
      (.obj [("minimum", Effect4.Arch.Json.ofNat 5)])) []
    none (some ⟨"effect/schema/isInt", .null, none⟩)]
#guard Effect4.Schema.Bridge.ofSchema groupedInt = none

-- VR2 (must fail): "the codec refuses the exitOf image at the overlapping union".
def overlap : Ty := .union (.except .nat .nat) (.exitOf .nat .nat)
def jSuccess : Json := .obj [("_tag", .str "Success"), ("value", Effect4.Arch.Json.ofNat 1)]
#guard Effect4.Schema.decode overlap jSuccess = none

-- VR3 (must fail): "admission refuses a host row answering except never never".
def hostRow (request answer : Ty) : Effect4.Program.Row :=
  { name := "query", spelling := "Host.query", request, answer, error := .never,
    kind := .async, registration := .external, cite := "" }
def pHostNat : Api.Program := .perform (.external 0) (.lit (.nat 1))
#guard (match Effect4.Program.admitProgram pHostNat [hostRow .nat (.except .never .never)] with
  | .ok _ => false | .error _ => true)

-- VR4 (must fail): "admission refuses a request column prod never nat".
def pHostNeverRequest : Api.Program :=
  .bind (.fail (.lit (.nat 1)))
    (.perform (.external 0) (.app "pair" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil))))
#guard (match Effect4.Program.admitProgram pHostNeverRequest [hostRow (.prod .never .nat) .nat] with
  | .ok _ => false | .error _ => true)

-- VR5 (must fail): a value fits `except never never`.
theorem fits_except_never_never_inhabited (w : Typed.World) :
    Typed.Fits w (.ctor 0 [.nat 0]) (.except .never .never) := by
  unfold Typed.Fits
  exact trivial

end DataProbe.PedigreeVerifyRed
