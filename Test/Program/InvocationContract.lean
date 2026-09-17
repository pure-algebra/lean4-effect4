import Effect4.Api
import Effect4.Laws.Program.Invocation

/-!
# Invocation contract — shared asynchronous routing and admitted tables

DI-54 and DI-61. The production compiler routes asynchronous built-ins and
external rows through `asyncRoute` under `perform`. The universal compiler theorem
is ascribed below; the 55-operation route matrix is an independently written finite table.

The domain counterexample remains independent of the generated corpus and is now also an
actual `.ty` golden (`OCaml5.Eff.Corpus.pIllExternalDomain`). Existing historical corpus
verdicts did not change at DI-54; this new fixture closes the cross-language regression gap.

The execution checks name their concrete fuel, tape and table. Timed sleep requires an
advance; unanswered calls and exhausted fuel remain frontiers. The external replay theorem
compares the two forms on the admitted scalar fixture and checks that the reply is consumed.
None of these finite executions claims host conformance, resource liveness, or DI-57's
nonempty-table reference theorem. Admission and the optional print-image certificate stay
separate, and the decision-tape check remains a separate operation.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Program.InvocationContract

open Effect4
open Effect4.Machine
open Effect4.Program

/-! ## The 55 × 2 route matrix

`NativeOp.all` is every built-in operation value: 23 constructors, five function names and two
scope strategies expanded, external indices excluded (`Native.lean`, `Read.lean:2912`). The
request representatives satisfy each row's declared request type; that is not a claim that
their synthetic handles are live in a running store. -/

def requestFor (op : NativeOp) : Val :=
  match op.row.request with
  | .nat => .nat 1
  | .handle target => if target = NativeOp.refTarget then Val.cell ⟨0⟩ else Val.promise ⟨0⟩
  | .prod (.handle target) .nat =>
    .list [if target = NativeOp.refTarget then Val.cell ⟨0⟩ else Val.promise ⟨0⟩, .nat 1]
  | _ => .unit

/-- The four compiled shapes this matrix distinguishes: the synchronous thunk, an async
registration, the `badName` defect a wrong shape reaches, and everything else (the live
frontier and the immediate yield). -/
inductive Route | sync | async | defect | other
deriving DecidableEq, Repr

def route : NCode → Route
  | .sync _ => .sync
  | .async _ _ _ => .async
  | .failure _ => .defect
  | _ => .other

def observed (op : NativeOp) : Route :=
  let p := { rootPoint 100 with env := [requestFor op] }
  route (compileEff (.perform op (.var 0)) p)

/-- Written from the row declarations: synchronous rows compile to `.sync`;
`Deferred.await`, sleep and external rows compile to `.async`. -/
def expected : NativeOp → Route
  | .deferredAwait => .async
  | .sleep => .async
  | .external _ => .async
  | _ => .sync

#guard NativeOp.all.all (fun op => Val.hasTy (requestFor op) op.row.request)
#guard NativeOp.all.all (fun op => observed op == expected op)
#guard (NativeOp.all.filter (fun op => observed op == .sync)).length = 53
-- Both asynchronous built-ins compile to .async.
#guard (NativeOp.all.filter (fun op => (NativeOp.row op).kind == .async)).length = 2
#guard (NativeOp.all.filter (fun op => observed op == .async)).length = 2
#guard observed .sleep == .async
#guard observed (.external 0) == .async
#guard observed .deferredAwait == .async
-- No built-in reaches an unclassified shape.
#guard (NativeOp.all.filter (fun op => observed op == .other)).length = 0

/-! ## The timed sleep: raw `run` parks, `replay` with an advance finishes

`Api.run` takes no decision tape (`Api.lean`), so a positive sleep leaves a live timer
frontier there — a frontier, never a failure. The decision that finishes it is `.advance`. -/

def performSleep : Api.Program := .perform .sleep (.lit (.nat 1))

def sleepTape : List Api.Decision := [Api.evaluate, .advance 1, Api.flush]

#guard (Api.typeOf performSleep).isSome
#guard (Api.run performSleep 100).exit = none
#guard (Api.replay performSleep 100 sleepTape).exit = some (.success .unit)
-- Zero millis is the immediate yield.
#guard (Api.run (.perform .sleep (.lit (.nat 0))) 100).exit = some (.success .unit)
#guard (Api.run performSleep 100).outcome = .frontier

/-! ## An external call consumes its reply

The row and the reply are `docs/research/foundation-probes/Admission.lean:9-13`. -/

def goodRow : Row :=
  { name := "wait", spelling := "Host.wait", kind := .async, registration := .external,
    request := .nat, answer := .nat, error := .nat, cite := "scratch" }

/-- Lawful by name, typed, printable — and not registrable: the external oracle does not
answer a `.deferred` row. -/
def malformedRow : Row := { goodRow with registration := .deferred }

/-- Registered externally, but not an asynchronous row. -/
def syncRow : Row := { goodRow with kind := .sync }

def reply : Completion Val Err Defect FiberId Ann := .ofExit (.success (.nat 9))

def performExternal : Api.Program := .perform (.external 0) (.lit (.nat 7))

#guard LawfulTable [goodRow]
#guard LawfulTable [malformedRow]
#guard (Api.typeOf performExternal [goodRow]).isSome
#guard (Api.run performExternal 100 [reply] [goodRow]).exit = some (.success (.nat 9))
-- The wrong registration parks with the answer unused. A park is a frontier, not a refusal;
-- `checkTable` is what refuses the table.
#guard (Api.run performExternal 100 [reply] [malformedRow]).exit = none
-- The reply is consumed. Removing it leaves a live frontier.
#guard (Api.run performExternal 100 [reply] [goodRow]).stores.externals.answers.length = 0
#guard (Api.run performExternal 100 [] [goodRow]).exit = none
#guard (Api.run performExternal 100 [] [goodRow]).outcome = .frontier
#guard externalRow [goodRow] 0 = some goodRow

-- DI-61's two-spelling receipts (`sleep_print_same`, `replay_perform_external_eq_callback`)
-- retired with `callback`: there is one invocation form, so they had become `x = x`. The
-- compile-side twin is recorded the same way in `src/Effect4/Laws/Program/Invocation.lean`.

/-! ## `checkTable`: the table decision `LawfulTable` does not make -/

#guard checkTable [] = none
#guard checkTable [goodRow] = none
#guard checkTable [malformedRow] = some (.notExternal 0)
#guard checkTable [syncRow] = some (.notAsync 0)
#guard checkTable [goodRow, malformedRow] = some (.notExternal 1)
#guard checkTable [goodRow, goodRow] = none
#guard Api.checkTable [malformedRow] = some (.notExternal 0)

/-! ## The external registration lookup (`Admission.lean:62-74`, the six negatives)

`externalRow` is what the registration hook consults. One table and index it accepts, five it
refuses — out of range, empty, wrong registration, sync row, program row — and, as the sixth
negative, the reminder that a valid row is not a certificate for the request term. -/

#guard externalRow [goodRow] 1 = none
#guard externalRow [] 0 = none
#guard externalRow [malformedRow] 0 = none
#guard externalRow [syncRow] 0 = none
#guard externalRow [{ goodRow with kind := .program }] 0 = none
#guard (Api.typeOf performExternal [goodRow]) = some ⟨.nat, .nat, .empty⟩
-- A good row does not make a wrong request term typed.
#guard (Api.typeOf (.perform (.external 0) (.lit .unit)) [goodRow]).isNone

/-! ## DI-54: the domain counterexample and the two arms

The witness of `docs/research/2026-09-09-scout-proof-statements.md` §2: the bound variable has
type `never` (the answer of `fail`), and `never` is exactly the external placeholder's
declared request, so the request check passed and the program typed at the empty table. It is
refused now, and this is the only class of program whose verdict the guards changed.

Part 4 (2026-09-12, DI-15 subsumption at the row request): at a table that *does* supply the
row the same program is in the domain, and a `never` request is a subtype of every request
(TypeScript assignability), so it types there — the domain check, not the request check, is
what refuses it at the empty table. The verdict change is reported under DI-60 in the part-4
receipt. -/

def counterexample : Api.Program :=
  .bind (.fail (.lit (.nat 1))) (.perform (.external 0) (.var 0))

#guard Api.typeOf counterexample = none
#guard (Api.typeOf counterexample [goodRow]).isSome
-- In domain and typed, once the table supplies the row.
#guard (Api.typeOf (.bind (.fail (.lit (.nat 1))) (.perform (.external 0) (.lit (.nat 7))))
  [goodRow]).isSome
-- Out of domain at the empty table, whatever the request term.
#guard (Api.typeOf (.perform (.external 0) (.lit (.nat 7)))).isNone
#guard (Api.typeOf (.perform (.external 1) (.lit (.nat 7))) [goodRow]).isNone
-- Built-ins are always in domain; the guards changed nothing for them.
#guard (Api.typeOf (.perform .deferredMake (.lit .unit))).isSome
#guard (Api.typeOf Wire.Corpus.pAwait).isSome

/-! ## Admission and the print-image certificate

`Wire.Corpus.pAwait` is the historical wire program: it spells `perform` on an async row.
With `perform` unified as the one invocation form, it is admitted and readable. -/

def admitted (program : Api.Program) (table : RowTable := []) : Bool :=
  match Api.admitProgram program table with
  | .ok _ => true
  | .error _ => false

def refusal (program : Api.Program) (table : RowTable := []) : Option Api.AdmitRefusal :=
  match Api.admitProgram program table with
  | .ok _ => none
  | .error why => some why

#guard admitted Wire.Corpus.pAwait
#guard Api.readable Wire.Corpus.pAwait
#guard (Api.imageCertificate Wire.Corpus.pAwait []).isSome
#guard (Api.imageCertificate performSleep []).isSome
#guard Api.readable performSleep
-- The refusals, one fixture each.
#guard refusal counterexample = some .illTyped
#guard refusal performExternal [malformedRow] = some (.table (.notExternal 0))
-- A sync row is refused by the table under perform, which types against it.
#guard refusal performExternal [syncRow] = some (.table (.notAsync 0))
#guard refusal (.succeed (.lit (.nat 1))) [{ goodRow with spelling := "Ref.get" }]
  = some (.builtinCollision ("Ref.get", []))
#guard refusal (.succeed (.lit (.nat 1))) [goodRow, goodRow]
  = some (.duplicateKey ("Host.wait", []))
#guard refusal (.succeed (.lit (.nat 1))) [{ goodRow with shape := .value, trailing := ["x"] }]
  = some (.valueRowTrailing ("Host.wait", ["x"]))
#guard match Program.printEntry [{ goodRow with spelling := "a1" }] (nativeSignature [{ goodRow with spelling := "a1" }]) "main" (EffTy.pure .unit) (.succeed (.lit .unit)) with
  | .error (.unsafeName "a1") => true
  | _ => false
#guard match Program.printEntry [{ goodRow with spelling := "Effect.succeed" }] (nativeSignature [{ goodRow with spelling := "Effect.succeed" }]) "main" (EffTy.pure .unit) (.succeed (.lit .unit)) with
  | .error (.unsafeName "Effect.succeed") => true
  | _ => false
#guard (Api.printModule "main" (.succeed (.lit .unit)) [{ goodRow with spelling := "a1" }]).isNone
#guard admitted performExternal [goodRow]

/-! ## The checked entry points run what the raw ones run

The exit criterion of S1a: `runAdmitted` runs what `run` runs on every admitted fixture. The
certificate is consumed as an argument, so a caller cannot reach these without building it. -/

def runAdmittedExit (program : Api.Program) (table : RowTable) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : Option ExitV :=
  match Api.admitProgram program table with
  | .ok certificate => (Api.runAdmitted certificate fuel answers).exit
  | .error _ => none

def replayAdmittedExit (program : Api.Program) (table : RowTable) (fuel : Nat)
    (tape : List Api.Decision)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : Option ExitV :=
  match Api.admitProgram program table with
  | .ok certificate => (Api.replayAdmitted certificate fuel tape answers).exit
  | .error _ => none

#guard runAdmittedExit Wire.Corpus.pAwait [] 100 = (Api.run Wire.Corpus.pAwait 100).exit
#guard runAdmittedExit performExternal [goodRow] 100 [reply]
  = (Api.run performExternal 100 [reply] [goodRow]).exit
#guard runAdmittedExit performSleep [] 100 = (Api.run performSleep 100).exit
#guard replayAdmittedExit performSleep [] 100 sleepTape = some (.success .unit)
#guard runAdmittedExit performExternal [goodRow] 100 [reply] = some (.success (.nat 9))
-- The admitted entry points exercise the same positive routing behavior.
#guard runAdmittedExit performExternal [goodRow] 0 [reply] = none
#guard (Api.run performExternal 0 [reply] [goodRow]).outcome = .frontier

end Test.Program.InvocationContract
