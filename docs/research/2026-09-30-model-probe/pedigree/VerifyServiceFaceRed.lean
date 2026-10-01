import Effect4.Api
import Effect4.Program.Authoring.Services

/-!
# Red control for `VerifyServiceFace.lean` (expected to FAIL: exit 1, one error)

The claim it falsifies: "a fresh service key is conservative on old programs at the faces"
(C7 for services, as finding P8 states it). The old program's printed text does not read back
under the extended signature.
-/

set_option autoImplicit false

namespace Research.PedigreeVerify.ServiceFaceRed

open Effect4 Effect4.Program

def freshKey : ServiceKey := ⟨⟨11⟩, ⟨20⟩⟩
def extended : Signature NativeOp := nativeSignatureWith [] [(freshKey, .nat)]
def oldProg : NativeEff :=
  .provideLayer (.succeed freshKey (.nat 1)) false (.succeed (.lit (.nat 0)))
def oldTy : EffTy := (typeOf nativeSignature oldProg).getD (EffTy.pure .unit)

def printedOld : Option (List TypeScript.ConstDecl) :=
  (Program.printModule nativeSignature "main" oldTy oldProg).toOption

-- Expected to fail: the extension refuses the old text.
#guard (printedOld.bind fun ds =>
    (Program.readModule extended (nativeSpell []) (ds.map TypeScript.Decl.const)).toOption) =
  some oldProg

end Research.PedigreeVerify.ServiceFaceRed
