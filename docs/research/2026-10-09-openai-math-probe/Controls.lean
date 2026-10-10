import Effect4.Program.Definitions
import Effect4.Program.Native

/-! Finite control for the cache-key boundary in OPERATIONAL-PLAN.md.
The actual checker reads inherited types. Source syntax alone cannot key its answers.
TyCache.lean supplies the reusable theorem through the existing generated fold. -/
set_option autoImplicit false
namespace MathTransferProbe

open Effect4 Effect4.Program
-- Equal syntax, different inherited context: syntax alone cannot key checker answers.
def openBody : NativeEff := .succeed (.var 0)
def natResult := Checker.check (nativeSignature []) [.nat] [] openBody
def boolResult := Checker.check (nativeSignature []) [.bool] [] openBody
#guard natResult.isOk
#guard boolResult.isOk
#guard natResult != boolResult
#guard !(Checker.check (nativeSignature []) [] [] openBody).isOk
#eval (natResult.isOk, boolResult.isOk, natResult != boolResult)

end MathTransferProbe
