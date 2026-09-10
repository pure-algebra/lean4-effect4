import Effect4.Laws.Program.LinkedRows
import Effect4.Codegen.Print
import Effect4.Program.Derived

open Effect4 Effect4.Machine Effect4.Program
namespace Test.Program.LinkedRowsContract
private def row : Effect4.Program.Row :=
  { name := "unitOp", spelling := "unitOp", shape := .call, kind := .async,
    request := .union .unit .never, answer := .union (.handle "Resource") .never,
    registration := .external, cite := "integration fixture" }
private def program : NativeEff := .perform (.external 0) (.lit .unit)
#guard (typeOf (nativeSignature [row]) program).map (·.answer) = some (.handle "Resource")
#guard match print (nativeSignature [row]) 0 program with
  | .ok (.call (.ident "unitOp") []) => true
  | _ => false
#guard (externalRow [row] 0).map (·.answer) = some (.handle "Resource")
#guard externalValue row.normalizeTypes.answer [] (.nat 0) = some (["Resource"], Value.external 0)
#guard externalValue row.answer [] (.nat 0) = none
#guard row.request = .union .unit .never
#guard (Store.Canonical.image Effect4.Program.Row).decode
  ((Store.Canonical.image Effect4.Program.Row).encode row) = some row
#guard EffTy.joinAnswer (.option (.union .nat .never)) (.option .nat) = some (.option .nat)
#guard EffTy.joinAnswer .nat .bool = none
#guard (effTy (nativeSignature [row]) [] (.perform (.external 1) (.lit .unit))).isNone
#guard (effTy (nativeSignature [row]) [] (.perform (.external 0) (.lit (.bool true)))).isNone
end Test.Program.LinkedRowsContract
