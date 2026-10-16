import Effect4.Api.HostSession

/-!
# Tools.RunRecord — one recorded host call, and a request's literal arguments

The two pieces of a recorded request that the lowered to-do host run needs
(`Test/Dogfood/Scenario/Todo/HostRun.lean`). They live apart from `Tools.RunChecks`, which reads
the law graph for its checks, so the LCNF route and the to-do lane's fixture import no law module.
`Tools.RunChecks` imports this module, and the names stay under `Tools.RunChecks`.
-/

set_option autoImplicit false

namespace Tools.RunChecks

open Effect4 Effect4.Machine Effect4.Program Effect4.Api.HostSession

/-- One host call of a recorded request: the row's position in the application's table, the
request, and the host's completion, as the face wrote them. -/
structure Call where
  row : Nat
  request : Val
  completion : Answer

/-- An argument of a recorded request as a source literal: a unit, a natural, a Boolean or a
string. The face writes each argument as a value; `none` for any other value. -/
def literal : Val → Option Lit
  | .unit => some .unit
  | .nat n => some (.nat n)
  | .bool b => some (.bool b)
  | .str s => some (.str s)
  | _ => none

end Tools.RunChecks
