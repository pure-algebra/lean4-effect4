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
variants included. Since the state plan's T3a a cell holds any type: the `Account` record in one
`Ref` builds, and it is read and written (section 1). The error payload landed
(decisions row 120, parts E1 and E2): `InsufficientFunds{needed, available}` with natural fields
builds as a typed failure and runs to `Err.payload`. It prints as a module that declares its
`Data.TaggedError` class and fails with `new InsufficientFunds({ … })`, and the module reads back
(section 5).

**Changes in the state plan's T3b.** A read-modify-write row carries a binder term. The pure part
of a deposit, one `Ref.modify` that adds to the balance, appends a `Deposit` entry and answers the
new balance, builds and runs over the `Account` record; its term captures the amount, an outer
binder (section 1). The term is no name's image, so the printer refused the row by name until the
state plan's T5, part A. Since then it prints as a function of the account and reads back.

**What the language refuses** (section 2): `needed` and `available` as rc.112 types them, signed
numbers (admission refuses `int` by the field's path; row 121); a
signed number (table admission refuses an `int` column as uninhabited,
and `sub` truncates, so `10 - 25` answers `0` where rc.112 answers `-15`). A listener is code,
which no value holds; so are `Ref.modify`'s effect-valued answer and `Effect.callback`'s cancel
effect, and removal by identity needs equality on code (R7, row 82).

**Waits on:** R4, the faces' part (the state plan's T5: a binder term prints as a function since
part A, and `Ref.make<A>` is part B); R3 with
row 121 (`int`); R7 with row 82 (listeners, the effect-valued answer, the cancel effect); R10 with
DI-89 (`forEach`) and DI-39 (`catchTag`); R6, parked, or the logical clock (`settle`). The slices
of row 204 that move it: state at any type, and error payloads.
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

/-- `{ id: "acc-1", balance: 1, history: [{ _tag: "Deposit", amount: 1 }] }`, a deposit's result. -/
def account1 : TermSrc :=
  record accountFields [("id", str "acc-1"), ("balance", nat 1),
    ("history", app "cons" [record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)]
      [("_tag", str "Deposit"), ("amount", nat 1)], app "nil" []])]

/-- The account in one cell, written and read: `Ref.set(state, account1)`, `Ref.get(state)`. -/
def accountReadWrite : Module NativeOp :=
  program (bindName "state" (Ref.make account0) fun state =>
    andThen (Ref.set state account1) (Ref.get state))

def built? (m : Module NativeOp) : Option Effect4.Api.Built := (Effect4.Api.Author.build m).toOption

/-- The record type of `Account`, its fields in canonical order. -/
def accountTy : Ty := (Ty.record accountFields).normalize

-- Since the data wave the account types as a value, its list of variants included.
#guard verdict (program (succeed account0)) = "built"
-- A cell holds any type since the state plan's T3a: the account builds at `Ref<Account>`.
#guard verdict accountCell = "built"
#guard (built? accountCell).map (fun b => b.ty.answer) = some (.refOf accountTy)
-- Written and read, it answers the account it holds.
#guard (built? accountReadWrite).map (fun b => (b.ty.answer,
    match b.runSync with | .success v => Record.read false v "balance" | .failure _ => none)) =
  some (accountTy, some (.nat 1))
-- The account id alone and a list (the history; the listeners' list) build the same way (the model
-- probe's `ProbeRefusals.lean` refused them).
#guard (built? (program (Ref.make (str "acc-1")))).map (fun b => b.ty.answer) =
  some (.refOf .string)
#guard (built? (program (Ref.make (app "cons" [nat 1, app "nil" []])))).map (fun b => b.ty.answer) =
  some (.refOf (.list .nat))

/-- `{ _tag: "Deposit", amount }`. -/
def depositEntry (amount : TermSrc) : TermSrc :=
  record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)]
    [("_tag", str "Deposit"), ("amount", amount)]

/-- `{ ...a, balance: a.balance + amount, history: [...a.history, { _tag: "Deposit", amount }] }`,
the account a deposit leaves (`p5-ledger-service.ts`, `deposit`). -/
def deposited (a amount : TermSrc) : TermSrc :=
  recordSet (recordSet a "balance" (app "add" [field a "balance", amount]))
    "history" (app "append" [field a "history", app "cons" [depositEntry amount, app "nil" []]])

/-- The pure part of a deposit as one atomic transition: `Ref.modify(state, a => [next.balance,
next])`. The amount is bound outside the term, which captures it. The module answers the balance
the row answered and the length of the history the cell holds after. rc.112's `transition` also
answers an effect and runs the listeners, which no value holds (section 2). -/
def depositModule (amount : Nat) : Module NativeOp :=
  program (bindName "state" (Ref.make account0) fun state =>
    bindName "amount" (succeed (nat amount)) fun amount =>
      bindName "balance" (Ref.modify "a"
          (app "pair" [app "add" [field (var "a") "balance", amount], deposited (var "a") amount])
          state) fun balance =>
        bindName "after" (Ref.get state) fun after =>
          succeed (app "pair" [balance, app "length" [field after "history"]]))

-- Since the state plan's T3b the atomic deposit builds over the `Account` record: the row answers
-- a number, `B`, and stores an account, `A`. It runs to the new balance and one history entry.
#guard (built? (depositModule 10)).map (fun b => (b.ty.answer, b.runSync)) =
  some (.prod .nat .nat, .success (.list [.nat 10, .nat 1]))
-- Its term captures the amount bound outside it. Since the state plan's T5 it prints as a
-- function of the account, and the module reads back.
#guard (built? (depositModule 10)).map printVerdict = some "printed"
#guard (built? (depositModule 10)).map readBackVerdict = some true
-- Red control: a deposit whose answer and next account are swapped is refused at the term's result.
#guard (typingReason? (program (bindName "state" (Ref.make account0) fun state =>
    Ref.modify "a" (app "pair" [deposited (var "a") (nat 10), field (var "a") "balance"]) state))).map
    (·.head) = some "resultNotSubtype"

/-! ## 2. The failure and its arithmetic -/

/-- `new InsufficientFunds({ needed: 25, available: 10 })`. -/
def insufficientModule : Module NativeOp :=
  program (fail (record
    [("_tag", false, .lit "InsufficientFunds"), ("needed", false, .nat), ("available", false, .nat)]
    [("_tag", str "InsufficientFunds"), ("needed", nat 25), ("available", nat 10)]))

-- The error payload carrier (row 120, part E1): the record is a typed failure (section 5); the
-- probe's nested pairs stay refused, since a pair's message is a string (DB-15).
#guard verdict insufficientModule = "built"
#guard verdict (program (fail (app "pair" [str "InsufficientFunds", app "pair" [nat 25, nat 10]]))) =
  "typing: errorNotAdmitted"

/-- `InsufficientFunds` with its fields typed as rc.112 types them, numbers that may be negative. -/
def insufficientIntModule : Module NativeOp :=
  program (fail (record
    [("_tag", false, .lit "InsufficientFunds"), ("needed", false, .int), ("available", false, .int)]
    [("_tag", str "InsufficientFunds"), ("needed", nat 25), ("available", nat 10)]))

-- Signed fields build (decisions row 317): the program's error is the record with its two `int`
-- fields.
#guard (Effect4.Api.Author.build insufficientIntModule).toOption.map (·.ty.error) =
  some (.record [("_tag", false, .lit "InsufficientFunds"), ("available", false, .int),
    ("needed", false, .int)])

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

-- A row that answers a signed number builds (decisions row 317).
#guard verdict intModule = "built"

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
the account cell writes the program in this battery, and measures the other four fields. The
payload part is measured on its own (decisions row 120, part E1). -/

def measured : Reach :=
  { refused := [("a signed number", verdict intModule)].filter (·.2 != "built")
    admitted := false, answer := .notRun, printed := false, readBack := false }

/-- The stage p5 reaches today, as `Test/Dogfood/README.md` quotes it: no encoding of the program
builds. Its signed answer is admitted since decisions row 317, so the language refuses no part
of it; its subtraction still truncates at zero until the integers packet's slice 5 (`minus`).
The `Account` record in one `Ref` builds since the state plan's T3a, and the pure part of a
deposit is one atomic `Ref.modify` over it since T3b (section 1). -/
def stage : Reach :=
  { refused := []
    admitted := false, answer := .notRun, printed := false, readBack := false }

#guard measured = stage

/-- The failure `run-p5.ts`'s `withdraw(25)` raises at a balance of 10:
`InsufficientFunds{needed: 25, available: 10}`, whose `available - needed` is the `-15` that
`hostruns.log` records. -/
def insufficient25 : Val :=
  recordOf ["_tag", "available", "needed"] [.str "InsufficientFunds", .nat 10, .nat 25]

/-- How far the payload part gets (decisions row 120, parts E1 and E2). -/
def payloadMeasured : List (String × PartReach) :=
  [("InsufficientFunds{needed, available} as a typed failure",
    partReach insufficientModule insufficient25)]

/-- The payload part's stage, as `Test/Dogfood/README.md` quotes it: built with natural fields, run
to `Err.payload`, printed as a module that declares its `InsufficientFunds` class (its fields in
their written order, `needed` before `available`), and read back. -/
def payloadStage : List (String × PartReach) :=
  [("InsufficientFunds{needed, available} as a typed failure", ⟨"built", true, "printed", true⟩)]

#guard payloadMeasured = payloadStage

/-- The requirements of the system map's §8 that this program waits on, as its row in
`Test/Dogfood/README.md` explains them. The semantics report lists the program under each and
prints `stage` beside it (decisions row 206). -/
def waitsOn : List String := ["R3", "R4", "R6", "R7", "R10"]

end Test.Dogfood.P5LedgerService
