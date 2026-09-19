import Effect4

/-!
# The exhaustiveness inventory's fixture

Three definitions whose rows `#exhaustive_gate` must get exactly right, pinned by
`#guard_msgs` in `Test/Audit/TraversalCensus.lean`. They exist to be read by that command and
have no other consumer: a `Ty` match with every constructor named and no wildcard must be
reported with `catchAll false`; the same match closed by `| _ =>` must be reported with
`catchAll true`; and a match on `Term` must not appear in a `Ty` report at all.
-/

namespace Test.Audit.ExhaustiveFixture

open Effect4.Program (Ty Term)

/-- Twenty arms, no wildcard: appending a constructor to `Ty` refuses this definition. -/
def catchAllAbsent : Ty → Nat
  | .never => 0
  | .unit => 1
  | .nat => 2
  | .int => 3
  | .string => 4
  | .bool => 5
  | .handle _ => 6
  | .option _ => 7
  | .list _ => 8
  | .prod _ _ => 9
  | .except _ _ => 10
  | .exitOf _ _ => 11
  | .causeOf _ => 12
  | .fiberOf _ _ => 13
  | .union _ _ => 14
  | .lit _ => 15
  | .refOf _ => 16
  | .deferredOf _ _ => 17
  | .var _ => 18
  | .unknown => 19

/-- The same match closed by a wildcard: appending a constructor leaves it compiling. -/
def catchAllPresent : Ty → Nat
  | .never => 0
  | .unit => 1
  | .prod _ _ => 9
  | _ => 19

/-- A match on another inductive: a `Ty` report must not name it. -/
def onTerm : Term → Nat
  | .var index => index
  | .lit _ => 0
  | .app _ _ => 1

end Test.Audit.ExhaustiveFixture
