import Test.Dogfood.Stage

/-!
# p5: a stateful service with a callback-taking API

The rc.112 source is `Test/Dogfood/rc112/p5-ledger-service.ts`. A `Ledger` service keeps an
`Account` record, with a list of tagged `Entry` variants, in one `Ref`, and changes it atomically.
`withdraw` fails with `InsufficientFunds{needed, available}`. `onChange` keeps a listener for the
caller's scope and removes it by identity, and every change runs each kept listener. `settle`
wraps a host timer with `Effect.callback`, whose returned effect cancels the timer.
`run-p5.ts` ran it on effect 4.0.0-rc.112 under bun 1.4.2 and recorded `[-15, [10, 10], "settled"]`
(`Test/Dogfood/rc112/hostruns.log`).

The model probe wrote no Lean program for p5: its note
(`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/note.md`, §3) finds it not
expressible. This battery ports what the probe and its verifier checked: the refusals of
`ProbeRefusals.lean` that name p5, and the truncating subtraction of `verify/VerifyPrograms.lean`
§4, at the same revision. It adds the account record and an `int` column, measured today, and
the one fragment that runs: `settle` on the logical clock, the verifier's alternative to a host
row (its finding X11).

**Changes since 2026-09-30.** Records landed (row 119): the `Account` value types, list field and
variants included, but a cell still holds a number only. No construct the probe used changed.

**What the language refuses** (sections 1 and 2): the `Account` record, the account id and the
history in a cell (`requestNotSubtype`); `InsufficientFunds{needed, available}` as a typed failure
(`errorNotAdmitted`); a signed number (table admission refuses an `int` column as uninhabited,
and `sub` truncates, so `10 - 25` answers `0` where rc.112 answers `-15`). A listener is code,
which no value holds; so are `Ref.modify`'s effect-valued answer and `Effect.callback`'s cancel
effect, and removal by identity needs equality on code (R7, row 82).

**Waits on:** R4 with rows 42–43 steps 3–5 (record and list cells); R3 with row 120 (the payload)
and row 121 (`int`); R7 with row 82 (listeners, the effect-valued answer, the cancel effect);
R10 with DI-89 (`forEach`) and DI-39 (`catchTag`); R6, parked, or the logical clock (`settle`).
The slices of row 204 that move it: state at any type, and error payloads.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.P5LedgerService

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The state: a record with a list of variants, in one cell -/

/-- `type Entry = { _tag: "Deposit"; amount } | { _tag: "Withdraw"; amount }`. -/
def entryTy : Ty :=
  .union (.record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)])
    (.record [("_tag", false, .lit "Withdraw"), ("amount", false, .nat)])

/-- `interface Account { id: string; balance: number; history: ReadonlyArray<Entry> }`. -/
def accountFields : List (String × Bool × Ty) :=
  [("id", false, .string), ("balance", false, .nat), ("history", false, .list entryTy)]

/-- The initial account, `{ id: "acc-1", balance: 0, history: [] }`. -/
def account0 : TermSrc :=
  record accountFields [("id", str "acc-1"), ("balance", nat 0), ("history", app "nil" [])]

/-- `Ref.make<Account>(…)`, the service's one cell. -/
def accountCell : Module NativeOp := program (Ref.make account0)

-- Since the data wave the account types as a value, its list of variants included.
#guard verdict (program (succeed account0)) = "built"
-- A cell holds a number only (rows 42–43): the checker refuses the record at the cell's request.
#guard verdict accountCell = "typing: requestNotSubtype"
-- The checker refuses the account id alone, and a list (the history; the listeners' list), the same way
-- (the model probe's `ProbeRefusals.lean`).
#guard typingReason? (program (Ref.make (str "acc-1"))) =
  some (.requestNotSubtype "refMake" .string .nat)
#guard typingReason? (program (Ref.make (app "cons" [nat 1, app "nil" []]))) =
  some (.requestNotSubtype "refMake" (.list .nat) .nat)

/-! ## 2. The failure and its arithmetic -/

/-- `new InsufficientFunds({ needed: 25, available: 10 })`. -/
def insufficientModule : Module NativeOp :=
  program (fail (record
    [("_tag", false, .lit "InsufficientFunds"), ("needed", false, .nat), ("available", false, .nat)]
    [("_tag", str "InsufficientFunds"), ("needed", nat 25), ("available", nat 10)]))

-- A typed failure carries no number (row 120), as a record or as the probe's nested pairs.
#guard verdict insufficientModule = "typing: errorNotAdmitted"
#guard verdict (program (fail (app "pair" [str "InsufficientFunds", app "pair" [nat 25, nat 10]]))) =
  "typing: errorNotAdmitted"

/-- `e.available - e.needed` with the recorded run's numbers. -/
def balanceAfter : Module NativeOp := program (succeed (app "sub" [nat 10, nat 25]))

-- The `sub` atom truncates at zero (`natSub`, `src/Effect4/Machine/Term.lean`): the program answers
-- `0` where rc.112 answers `-15`. This runs the Lean machine only; the other faces are not run here.
#guard (Effect4.Api.Author.build balanceAfter).toOption.map (·.runSync) = some (.success (.nat 0))
-- Green control: the same atom where the answer is a natural number.
#guard (Effect4.Api.Author.build (program (succeed (app "sub" [nat 25, nat 10])))).toOption.map
  (·.runSync) = some (.success (.nat 15))

/-- A host row answering a signed number. -/
def intRow : RowDef := Row.host "Ledger.balance" .unit .int
def intModule : Module NativeOp := { rows := [intRow], main := Row.call intRow unit }

-- `int` has no inhabitant (row 121, ruled, not landed): table admission refuses the column.
#guard verdict intModule = "admission"
#guard (match Effect4.Api.Author.build intModule with
  | .error (.admission r) => r == .uninhabited ["table", "0", "answer"]
  | _ => false)

/-! ## 3. The one fragment that runs: `settle` on the logical clock

rc.112's `settle` arms a host timer through `Effect.callback` and returns `clearTimeout` as the
cancellation. Read as the logical clock (DB-14), it is a `sleep` and an answer, with no host. The
cancellation effect has no spelling: `src/Effect4/Program/Eff.lean` keeps no cancel in syntax. -/

def settle : Module NativeOp := program (andThen (Effect.sleep (nat 5)) (succeed (str "settled")))

#guard verdict settle = "built"
-- With the clock advanced by 5 ms it answers rc.112's third item, `"settled"`.
#guard (Effect4.Api.Author.build settle).toOption.map (fun b =>
  (Effect4.Api.replay b.program 1000
    [Effect4.Api.evaluate, .advance (ClockMillis.ofNat 5), Effect4.Api.flush]).exit) =
  some (some (.success (.str "settled")))
-- Red control: with no clock decision the timer never fires, and the root has no exit.
#guard (Effect4.Api.Author.build settle).toOption.map (fun b => (Effect4.Api.run b.program 1000).exit) =
  some none
#guard (Effect4.Api.Author.build settle).toOption.map printedOf = some (true, true)

/-! ## 4. The forms -/

-- The form table admits neither `forEach` (DI-89) nor `catchTag` (DI-39, DI-89).
#guard ["Effect.forEach", "Effect.catchTag"].filter formAdmits = []

/-! ## 5. The stage

No encoding of the whole program exists, so the battery measures only `refused`. The slice that admits
the account cell writes the program in this battery, and measures the other four fields. -/

def measured : Reach :=
  { refused :=
      [ ("the Account record in one Ref", verdict accountCell)
      , ("InsufficientFunds{needed, available} as a typed failure", verdict insufficientModule)
      , ("a signed number", verdict intModule) ]
    admitted := false, answer := .notRun, printed := false, readBack := false }

/-- The stage p5 reaches today, as `Test/Dogfood/README.md` quotes it: no encoding of the program
builds, and the language refuses its state, its failure and its signed answer. -/
def stage : Reach :=
  { refused :=
      [ ("the Account record in one Ref", "typing: requestNotSubtype")
      , ("InsufficientFunds{needed, available} as a typed failure", "typing: errorNotAdmitted")
      , ("a signed number", "admission") ]
    admitted := false, answer := .notRun, printed := false, readBack := false }

#guard measured = stage

end Test.Dogfood.P5LedgerService
