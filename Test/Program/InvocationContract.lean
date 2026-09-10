import Effect4.Api
import Effect4.Laws.Program.Invocation

/-!
# Invocation contract — shared asynchronous routing and admitted tables

DI-54 and DI-61. The production compiler shares `asyncRoute` between `perform` and
`callback` for asynchronous built-ins and external rows. The universal compiler theorem
is ascribed below; the 55 × 2 route matrix is an independently written finite table.

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

/-! ## The frozen statements -/

section Statements

#check (@Effect4.Program.compile_perform_eq_callback :
  ∀ (op : NativeOp) (r : Term) (p : Point),
    ((∃ i, op = .external i) ∨ op.row.kind = .async) →
      compileEff (.perform op r) p = compileEff (.callback op r) p)

#check (@Effect4.Program.compileEff_callback_eq_asyncRoute :
  ∀ (op : NativeOp) (r : Term) (p : Point) {k : Nat},
    p.fuel = k + 1 → compileEff (.callback op r) p = asyncRoute op r p)

#check (@Effect4.Program.compile_perform_eq_callback_await :
  ∀ (r : Term) (p : Point),
    compileEff (.perform .deferredAwait r) p = compileEff (.callback .deferredAwait r) p)

#check (@Effect4.Program.compile_perform_eq_callback_of_await :
  ∀ (op : NativeOp) (r : Term) (p : Point),
    (NativeOp.row op).kind = .async → (∀ i, op ≠ .external i) → op ≠ .sleep →
      compileEff (.perform op r) p = compileEff (.callback op r) p)

#check (@Effect4.Program.compile_zero_fuel :
  ∀ (e : NativeEff) (p : Point), p.fuel = 0 → compileEff e p = frontier p)

#check (@Effect4.Program.checkTable_none_externalRow :
  ∀ {table : RowTable}, checkTable table = none →
    ∀ (i : Nat) (row : Row), table[i]? = some row → externalRow table i = some row.normalizeTypes)

#check (@Effect4.Program.checkTable : RowTable → Option TableRefusal)

#check (@Effect4.Api.admitProgram :
  ∀ (program : Api.Program) (table : RowTable),
    Except Api.AdmitRefusal (Api.AdmittedProgram program table))

#check (@Effect4.Api.imageCertificate :
  ∀ (program : Api.Program) (table : RowTable),
    Option (PLift (Api.readable program table = true)))

end Statements

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

def observed (callback : Bool) (op : NativeOp) : Route :=
  let p := { rootPoint 100 with env := [requestFor op] }
  route (compileEff (if callback then .callback op (.var 0) else .perform op (.var 0)) p)

/-- Written from the row declarations: synchronous rows use `perform` only;
`Deferred.await`, sleep and external rows register under both invocation forms. -/
def expected (callback : Bool) : NativeOp → Route
  | .deferredAwait => .async
  | .sleep => .async
  | .external _ => .async
  | _ => if callback then .defect else .sync

#guard NativeOp.all.length = 55
#guard NativeOp.all.all (fun op => Val.hasTy (requestFor op) op.row.request)
#guard NativeOp.all.all (fun op => observed false op == expected false op)
#guard NativeOp.all.all (fun op => observed true op == expected true op)
#guard (NativeOp.all.filter (fun op => observed false op == .sync)).length = 53
#guard (NativeOp.all.filter (fun op => observed true op == .defect)).length = 53
-- Both asynchronous built-ins register under either spelling.
#guard (NativeOp.all.filter (fun op => observed true op == .async)).length = 2
#guard (NativeOp.all.filter (fun op => (NativeOp.row op).kind == .async)).length = 2
#guard (NativeOp.all.filter (fun op => observed false op == .async)).length = 2
#guard observed false .sleep == .async
#guard observed true .sleep == .async
#guard observed false (.external 0) == .async
#guard observed true (.external 0) == .async
-- No built-in reaches an unclassified shape under `callback`.
#guard (NativeOp.all.filter (fun op => observed true op == .other)).length = 0
-- The two forms agree on both asynchronous built-ins, among all 55.
#guard (NativeOp.all.filter (fun op => observed false op == observed true op)).length = 2
#guard observed false .deferredAwait == observed true .deferredAwait

/-! ## The timed sleep: raw `run` parks, `replay` with an advance finishes

`Api.run` takes no decision tape (`Api.lean`), so a positive sleep leaves a live timer
frontier there — a frontier, never a failure. The decision that finishes it is `.advance`. -/

def performSleep : Api.Program := .perform .sleep (.lit (.nat 1))
def callbackSleep : Api.Program := .callback .sleep (.lit (.nat 1))

def sleepTape : List Api.Decision := [Api.evaluate, .advance 1, Api.flush]

#guard (Api.typeOf performSleep).isSome
#guard (Api.typeOf callbackSleep).isSome
#guard (Api.run callbackSleep 100).exit = none
#guard (Api.replay callbackSleep 100 sleepTape).exit = some (.success .unit)
-- Zero millis is the immediate yield.
#guard (Api.run (.callback .sleep (.lit (.nat 0))) 100).exit = some (.success .unit)
-- Both source spellings print the same call and now have the same timer behavior.
theorem sleep_print_same : Api.print performSleep = Api.print callbackSleep := rfl
#guard (Api.run performSleep 100).exit = none
#guard (Api.run performSleep 100).outcome = .frontier
#guard (Api.run callbackSleep 100).outcome = .frontier
#guard (Api.replay performSleep 100 sleepTape).exit = some (.success .unit)
#guard (Api.run (.perform .sleep (.lit (.nat 0))) 100).exit = some (.success .unit)

/-! ## An external call consumes its reply under both spellings

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
def callbackExternal : Api.Program := .callback (.external 0) (.lit (.nat 7))

#guard LawfulTable [goodRow]
#guard LawfulTable [malformedRow]
#guard (Api.typeOf performExternal [goodRow]).isSome
#guard (Api.typeOf callbackExternal [goodRow]).isSome
#guard (Api.run callbackExternal 100 [] [reply] [goodRow]).exit = some (.success (.nat 9))
-- The wrong registration parks with the answer unused. A park is a frontier, not a refusal;
-- `checkTable` is what refuses the table.
#guard (Api.run callbackExternal 100 [] [reply] [malformedRow]).exit = none
-- Both spellings consume the reply. Removing the reply leaves a live frontier.
#guard (Api.run performExternal 100 [] [reply] [goodRow]).exit = some (.success (.nat 9))
#guard (Api.run performExternal 100 [] [reply] [goodRow]).stores.externals.answers.length = 0
#guard (Api.run callbackExternal 100 [] [reply] [goodRow]).stores.externals.answers.length = 0
#guard (Api.run performExternal 100 [] [] [goodRow]).exit = none
#guard (Api.run callbackExternal 100 [] [] [goodRow]).exit = none
#guard (Api.run performExternal 100 [] [] [goodRow]).outcome = .frontier
#guard (Api.run callbackExternal 100 [] [] [goodRow]).outcome = .frontier
#guard externalRow [goodRow] 0 = some goodRow

/-- DI-61: API replay equality on the admitted scalar fixture, including its resulting
machine and trace. This concrete tape/table receipt does not generalize `run_eq_ref`. -/
theorem replay_perform_external_eq_callback :
    Api.replay performExternal 100 [Api.evaluate, Api.flush] [] [reply] [goodRow] =
      Api.replay callbackExternal 100 [Api.evaluate, Api.flush] [] [reply] [goodRow] := by
  rfl

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

#guard externalRow [goodRow] 0 = some goodRow
#guard externalRow [goodRow] 1 = none
#guard externalRow [] 0 = none
#guard externalRow [malformedRow] 0 = none
#guard externalRow [syncRow] 0 = none
#guard externalRow [{ goodRow with kind := .program }] 0 = none
#guard (Api.typeOf callbackExternal [goodRow]) = some ⟨.nat, .nat, .empty⟩
-- A good row does not make a wrong request term typed.
#guard (Api.typeOf (.callback (.external 0) (.lit .unit)) [goodRow]).isNone

/-! ## DI-54: the domain counterexample and the two arms

The witness of `docs/research/2026-09-09-scout-proof-statements.md` §2: the bound variable has
type `never` (the answer of `fail`), and `never` is exactly the external placeholder's
declared request, so the request check passed and the program typed at the empty table. It is
refused now, and this is the only class of program whose verdict the guards changed. -/

def counterexample : Api.Program :=
  .bind (.fail (.lit (.nat 1))) (.perform (.external 0) (.var 0))

#guard Api.typeOf counterexample = none
#guard (Api.typeOf counterexample [goodRow]).isNone
-- In domain and typed, once the table supplies the row.
#guard (Api.typeOf (.bind (.fail (.lit (.nat 1))) (.perform (.external 0) (.lit (.nat 7))))
  [goodRow]).isSome
-- Out of domain under both forms at the empty table, whatever the request term.
#guard (Api.typeOf (.perform (.external 0) (.lit (.nat 7)))).isNone
#guard (Api.typeOf (.callback (.external 0) (.lit (.nat 7)))).isNone
#guard (Api.typeOf (.perform (.external 1) (.lit (.nat 7))) [goodRow]).isNone
#guard (Api.typeOf (.callback (.external 1) (.lit (.nat 7))) [goodRow]).isNone
-- Built-ins are always in domain; the guards changed nothing for them.
#guard (Api.typeOf (.perform .deferredMake (.lit .unit))).isSome
#guard (Api.typeOf Wire.Corpus.pAwait).isSome

/-! ## Admission and the print-image certificate are separate

`Wire.Corpus.pAwait` is the historical wire program that justifies the unification: it spells
`perform` on an async row, so the reader canonicalises it to `callback` and `readable` refuses
it — while it types, admits and runs. -/

def admitted (program : Api.Program) (table : RowTable := []) : Bool :=
  match Api.admitProgram program table with
  | .ok _ => true
  | .error _ => false

def refusal (program : Api.Program) (table : RowTable := []) : Option Api.AdmitRefusal :=
  match Api.admitProgram program table with
  | .ok _ => none
  | .error why => some why

#guard admitted Wire.Corpus.pAwait
#guard !Api.readable Wire.Corpus.pAwait
#guard (Api.imageCertificate Wire.Corpus.pAwait []).isNone
#guard (Api.imageCertificate callbackSleep []).isSome
#guard !Api.readable performSleep
#guard (Api.imageCertificate performSleep []).isNone
-- The three refusals, one fixture each.
#guard refusal counterexample = some .illTyped
#guard refusal callbackExternal [malformedRow] = some (.table (.notExternal 0))
-- A sync row is refused by the *typing* under `callback` (the kind check, which runs first)
-- and by the *table* under `perform`, which types against it. Both refusals are real; the
-- order of `admitProgram`'s checks is what picks which one is reported.
#guard refusal callbackExternal [syncRow] = some .illTyped
#guard refusal performExternal [syncRow] = some (.table (.notAsync 0))
#guard refusal (.succeed (.lit (.nat 1))) [{ goodRow with spelling := "Ref.get" }]
  = some .unlawfulTable
#guard admitted callbackExternal [goodRow]
#guard admitted performExternal [goodRow]

/-! ## The checked entry points run what the raw ones run

The exit criterion of S1a: `runAdmitted` runs what `run` runs on every admitted fixture. The
certificate is consumed as an argument, so a caller cannot reach these without building it. -/

def runAdmittedExit (program : Api.Program) (table : RowTable) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : Option ExitV :=
  match Api.admitProgram program table with
  | .ok certificate => (Api.runAdmitted certificate fuel [] answers).exit
  | .error _ => none

def replayAdmittedExit (program : Api.Program) (table : RowTable) (fuel : Nat)
    (tape : List Api.Decision)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : Option ExitV :=
  match Api.admitProgram program table with
  | .ok certificate => (Api.replayAdmitted certificate fuel tape [] answers).exit
  | .error _ => none

#guard runAdmittedExit Wire.Corpus.pAwait [] 100 = (Api.run Wire.Corpus.pAwait 100).exit
#guard runAdmittedExit performExternal [goodRow] 100 [reply]
  = (Api.run performExternal 100 [] [reply] [goodRow]).exit
#guard runAdmittedExit callbackExternal [goodRow] 100 [reply]
  = (Api.run callbackExternal 100 [] [reply] [goodRow]).exit
#guard runAdmittedExit performSleep [] 100 = (Api.run performSleep 100).exit
#guard runAdmittedExit callbackSleep [] 100 = (Api.run callbackSleep 100).exit
#guard replayAdmittedExit callbackSleep [] 100 sleepTape = some (.success .unit)
#guard runAdmittedExit callbackExternal [goodRow] 100 [reply] = some (.success (.nat 9))
-- The admitted entry points exercise the same positive routing behavior.
#guard replayAdmittedExit performSleep [] 100 sleepTape = some (.success .unit)
#guard runAdmittedExit performExternal [goodRow] 100 [reply] = some (.success (.nat 9))
#guard runAdmittedExit performExternal [goodRow] 0 [reply] = none
#guard (Api.run performExternal 0 [] [reply] [goodRow]).outcome = .frontier

end Test.Program.InvocationContract
