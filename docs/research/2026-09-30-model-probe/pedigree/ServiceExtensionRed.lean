import Effect4.Program.Authoring.Services

/-!
# Red control for `ServiceExtension.lean` (expected to FAIL: exit 1)

The claim it falsifies: "any service-table extension is conservative on old programs". The
override of a key the built-in signature already types changes the old program's answer, so the
guard below does not evaluate to `true`.
-/

set_option autoImplicit false

namespace Research.Pedigree.ServicesRed

open Effect4 Effect4.Program

def natKey : ServiceKey := ⟨⟨10⟩, ⟨4⟩⟩
def readNat : NativeEff := .service natKey

def answerOf (sig : Signature NativeOp) (p : NativeEff) : Option Ty :=
  (typeOf sig p).map EffTy.answer

-- Expected to fail: the override is not conservative.
#guard answerOf (nativeSignatureWith [] [(natKey, .string)]) readNat ==
  answerOf (nativeSignature []) readNat

end Research.Pedigree.ServicesRed
