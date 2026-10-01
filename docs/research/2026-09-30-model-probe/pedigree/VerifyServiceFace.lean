import Effect4.Api
import Effect4.Program.Authoring.Services

/-!
# Pedigree verifier probe (2026-09-30): a fresh service key and the printed face (C7)

Finite checks (tested, not proved). The seat's finding P8 says "C3 and C7, finitely: a fresh
service key and an appended host row are conservative on old programs". Its probe tested the
checker (C3) for services, not the faces (C7).

The printer spells a key with its carrier when the signature types it and bare when it does not
(`printKey`, `src/Effect4/Codegen/PrintLeaf.lean:300-306`); the reader admits a bare key only
when the signature does not type it (`readKey`, `src/Effect4/Codegen/Read.lean:346-361`). Today a
layer leaf's key is not looked up by the checker (`checkLayer`'s `.succeed` arm,
`src/Effect4/Program/Checker.lean:228-230`; decisions row 105 rules the lookup, not yet landed),
so a typed old program may provide a key the old signature does not type. Extending the service
table with that key:

- leaves the program's type unchanged (C3 holds here);
- changes its printed text, and the old text no longer reads back (C7 fails).

Once row 105 lands, such a program is refused by the old signature, so this failure is confined
to the window before row 105, or to any key position the checker does not look up.
-/

set_option autoImplicit false

namespace Research.PedigreeVerify.ServiceFace

open Effect4 Effect4.Program

def freshKey : ServiceKey := ⟨⟨11⟩, ⟨20⟩⟩

/-- The built-in signature extended by the fresh key, as `nativeSignatureWith` does it. -/
def extended : Signature NativeOp := nativeSignatureWith [] [(freshKey, .nat)]

/-- An old program: a layer provides the fresh key, and the body ignores it. -/
def oldProg : NativeEff :=
  .provideLayer (.succeed freshKey (.nat 1)) false (.succeed (.lit (.nat 0)))

def oldTy : EffTy := (typeOf nativeSignature oldProg).getD (EffTy.pure .unit)

-- The old signature does not type the key, the extension does.
#guard nativeSignature.serviceTy freshKey = none
#guard extended.serviceTy freshKey = some .nat

-- C3 holds for this program: typed today, and the same type under the extension.
#guard (typeOf nativeSignature oldProg).isSome
#guard typeOf extended oldProg = typeOf nativeSignature oldProg

def printed (sig : Signature NativeOp) : Option (List TypeScript.ConstDecl) :=
  (Program.printModule sig "main" oldTy oldProg).toOption

def readBack (sig : Signature NativeOp) (decls : Option (List TypeScript.ConstDecl)) :
    Option NativeEff :=
  decls.bind fun ds => (Program.readModule sig (nativeSpell []) (ds.map TypeScript.Decl.const)).toOption

-- The old text reads back under the old signature (the existing exact embedding).
#guard (printed nativeSignature).isSome
#guard readBack nativeSignature (printed nativeSignature) = some oldProg

/-- The rendered text of the key, as the printer spells it under a signature. -/
def keyText (sig : Signature NativeOp) : Option String :=
  (printKey sig freshKey).toOption.map (TypeScript.Render.expr TypeScript.house0 0)

-- C7 fails: the extension spells the key differently, and refuses the old text.
#guard keyText nativeSignature = some "Context.Service(\"k11_20\")"
#guard keyText extended = some "Context.Service<number>(\"k11_20\")"
#guard readBack extended (printed nativeSignature) = none
-- The extension's own text reads back under the extension.
#guard readBack extended (printed extended) = some oldProg

end Research.PedigreeVerify.ServiceFace
