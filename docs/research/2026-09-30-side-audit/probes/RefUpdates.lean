import Effect4.Api
import TypeScript

namespace SideAuditNumbers
open Effect4 Effect4.Machine Effect4.Program

def refOverflow : Api.Program :=
  .bind (.perform .refMake (.lit (.nat 9007199254740991))) <|
  .bind (.perform (.refUpdateAndGet .incr) (.var 0)) <|
  .bind (.perform (.refUpdateAndGet .incr) (.var 0)) <|
  .succeed (.app "eq" (.cons (.var 1) (.cons (.var 2) .nil)))

#guard Api.typeOf refOverflow [] = some (EffTy.pure .bool)
#guard (Api.run refOverflow 1000).exit = some (.success (.bool false))
#guard (Api.print refOverflow).isOk
#eval match Api.print refOverflow with
  | .ok expression => TypeScript.Render.expr TypeScript.house0 0 expression
  | .error _ => "refused"

-- With slice 7b's proposed checked arithmetic, this catch intercepts the profile defect.
def catchesRefusal : Api.Program :=
  .catchCause
    (.bind (.succeed (.lit (.nat 9007199254740991))) <|
      .succeed (.app "add" (.cons (.var 0) (.cons (.lit (.nat 1)) .nil))))
    (.succeed (.lit (.nat 7)))
#guard Api.typeOf catchesRefusal [] = some (EffTy.pure .nat)
#guard (Api.print catchesRefusal).isOk
#eval match Api.print catchesRefusal with
  | .ok expression => TypeScript.Render.expr TypeScript.house0 0 expression
  | .error _ => "refused"
end SideAuditNumbers
