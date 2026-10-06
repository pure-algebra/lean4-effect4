import Effect4

/-!
# The exhaustiveness inventory's fixture

Four definitions whose rows `#exhaustive_gate` must get exactly right, pinned by
`#guard_msgs` in `Test/Audit/TraversalCensus.lean`. They exist to be read by that command and
have no other consumer: a `Ty` match with every constructor named and no wildcard must be
reported with `catchAll false`; the same match closed by `| _ =>` must be reported with
`catchAll true`; a match on `Term` must not appear in a `Ty` report at all; and a private
definition must be reported under the name it was written with, marked `[private]`, never in
the `_private.<module>.0.…` form the environment stores (2026-10-01, seat G).
-/

namespace Test.Audit.ExhaustiveFixture

open Effect4.Program (Ty Term)

/-- Every constructor of `Ty` named, no wildcard: appending a constructor refuses this
definition. The data wave of 2026-10-03 appended the last eight arms. -/
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
  | .record _ => 20
  | .map _ _ => 21
  | .tuple _ => 22
  | .app _ _ => 23
  | .null => 24
  | .undefined => 25
  | .number => 26
  | .bytes => 27

/-- The same match closed by a wildcard: appending a constructor leaves it compiling. -/
def catchAllPresent : Ty → Nat
  | .never => 0
  | .unit => 1
  | .prod _ _ => 9
  | _ => 19

/-- Private: a row under the name it was written with, marked `[private]`. -/
private def privateCatchAll : Ty → Nat
  | .never => 0
  | _ => 1

/-- A match on another inductive: a `Ty` report must not name it. -/
def onTerm : Term → Nat
  | .var index => index
  | .lit _ => 0
  | .app _ _ => 1
  | .record _ _ _ => 2
  | .field _ _ _ => 3
  | .recordSet _ _ _ => 4
  | .tupleAt _ _ => 5
  | .fold _ _ _ _ => 6

end Test.Audit.ExhaustiveFixture
