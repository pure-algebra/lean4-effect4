import Effect4.Api
import Effect4.Program.Profile

/-!
# Host specification contract — the envelope, the frontier, and two models

Plan: `docs/research/2026-09-09-foundation-settlement-v2.md` §3 row S6a. Rows: DB-09's
amendment (the three parts of a profile), DI-57 (the statement, filed in
`Test/contracts/machine-scheduler-core.contract.md`), DI-58 (the envelope and the frontier
rule). The modules under contract are `src/Effect4/Program/Profile.lean` and the recorded-reply
section of `src/Effect4/Program/Admit.lean`.

Every obligation is ascribed at its exact proposition and supplied by name with `@`, so a
declaration that keeps the frozen name and weakens the statement fails here
(`Test/Program/TypedContract.lean` is the model). The executable receipts are `#guard`s over
first-order values; every one of them is a claim, and these are the claims:

**The envelope (DI-58).** One real parked external call — a `callback` on an asynchronous
external row, evaluated once — is the positive witness: its recorded reply is accepted and the
decision returned is exactly the `answerAsync` the record names. Seven malformed records at
that same machine are refused, one per part of the envelope: a **wrong table**, a **wrong row**,
a **wrong request**, a **wrong token**, a **wrong fiber**, a **wrong completion category**
(a success whose value the row's answer type refuses, and a failure whose error the row's error
type refuses), and a **duplicate** reply offered after the first has been applied. The duplicate
is refused because the machine no longer holds the park, which is the premise
`acceptedOnce_of_unparked` runs on.

**The frontier (v2 R4b).** The same program under `Api.replayChecked` with the tape
`[evaluate, flush]` and no recorded answer ends `.inl` at `Outcome.frontier` — a live frontier,
not a refusal — and the reply is still acceptable at that machine, unconsumed. Feeding it as a
decision in the tape finishes the run instead. An exhausted tape is therefore a frontier here,
and the assertion is on the frontier and never on a refusal.

**The two models.** `Profile.Scalar` and `Profile.Resource` (`src/Effect4/Program/Profile.lean`)
are `HostSpec`s proved `LawfulHostSpec`. The guards below exercise what the proofs cannot show
by themselves: a request inside the bound is answered and one outside it crosses as the
profile refusal (DI-56); acquire extends the slot table; the third `use` charges the call and
*then* fails, leaving the charged state (DB-07); release still steps from that state (cleanup
after failure); use after release and a second release have no step at all. The rolling-back
specification steps on the same call and is refuted as unlawful, which is what makes
`step_retains` more than decoration.

**The relations against a real machine.** `RelatedState` and `observe` are checked against the
stores an actual run leaves: the tree's own acquire/read/close program at this model's target
allocates exactly one external handle, which is the model's one slot; the observation holds
when the slot is closed and fails when it is left open (the leak check).
-/

set_option autoImplicit false

namespace Test.Program.HostSpecContract

open Effect4
open Effect4.Machine
open Effect4.Program

/-! ## The frozen statements -/

section Statements

/-! ### The profile's three parts (DB-09's amendment) -/

#check (@Effect4.Program.ProfileData.natBound : ProfileData → Nat)
#check (@Effect4.Program.ProfileData.admittedForms : ProfileData → List (CallClass × InvocationForms))
#check (@Effect4.Program.ProfileData.adapters : ProfileData → List (String × String))
#check (@Effect4.Program.ProfileData.imports : ProfileData → List String)
#check (@Effect4.Program.ProfileData.errorProjection : ProfileData → String)

#check (@Effect4.Program.ProfileData.admitsNat : ProfileData → Nat → Bool)

#check (@Effect4.Program.ProfileData.admitsNat_iff :
  ∀ (profile : ProfileData) (n : Nat), profile.admitsNat n = true ↔ n ≤ profile.natBound)

#check (@Effect4.Program.HostSpec.Rep :
  ∀ {HostState HostVal : Type}, HostSpec HostState HostVal → Ty → Val → HostVal → Prop)

#check (@Effect4.Program.HostSpec.RelatedState :
  ∀ {HostState HostVal : Type}, HostSpec HostState HostVal → Stores → HostState → Prop)

#check (@Effect4.Program.HostSpec.after :
  ∀ {HostState HostVal : Type}, HostSpec HostState HostVal → Row → Val → HostState → HostState)

#check (@Effect4.Program.HostSpec.RowStep :
  ∀ {HostState HostVal : Type}, HostSpec HostState HostVal →
    Row → Val → HostState → Completion Val Err Defect FiberId Ann → HostState → Prop)

#check (@Effect4.Program.HostSpec.observe :
  ∀ {HostState HostVal : Type}, HostSpec HostState HostVal → Stores → HostState → Prop)

#check (@Effect4.Program.LawfulHostSpec :
  ∀ {HostState HostVal : Type}, ProfileData → HostSpec HostState HostVal → Prop)

#check (@Effect4.Program.LawfulHostSpec.rep_scalar_bound :
  ∀ {HostState HostVal : Type} {profile : ProfileData} {spec : HostSpec HostState HostVal},
    LawfulHostSpec profile spec →
      ∀ (n : Nat) (hostValue : HostVal), spec.Rep .nat (.nat n) hostValue → n ≤ profile.natBound)

#check (@Effect4.Program.LawfulHostSpec.step_retains :
  ∀ {HostState HostVal : Type} {profile : ProfileData} {spec : HostSpec HostState HostVal},
    LawfulHostSpec profile spec →
      ∀ (row : Row) (request : Val) (state : HostState)
        (completion : Completion Val Err Defect FiberId Ann) (state' : HostState),
        spec.RowStep row request state completion state' → state' = spec.after row request state)

#check (@Effect4.Program.LawfulHostSpec.one_completion :
  ∀ {HostState HostVal : Type} {profile : ProfileData} {spec : HostSpec HostState HostVal},
    LawfulHostSpec profile spec →
      ∀ (row : Row) (request : Val) (state : HostState)
        (c₁ : Completion Val Err Defect FiberId Ann) (s₁ : HostState)
        (c₂ : Completion Val Err Defect FiberId Ann) (s₂ : HostState),
        spec.RowStep row request state c₁ s₁ → spec.RowStep row request state c₂ s₂ → c₁ = c₂)

/-! ### The two models -/

#check (@Effect4.Program.Profile.Scalar.lawful :
  LawfulHostSpec Profile.Scalar.profile Profile.Scalar.spec)

#check (@Effect4.Program.Profile.Scalar.in_profile :
  ∀ (n : Nat), n ≤ Profile.Scalar.profile.natBound →
    Profile.Scalar.spec.RowStep Profile.Scalar.waitRow (.nat n) ()
      (.ofExit (.success (.nat n))) ())

#check (@Effect4.Program.Profile.Scalar.out_of_profile :
  ∀ (n : Nat), ¬ n ≤ Profile.Scalar.profile.natBound →
    Profile.Scalar.spec.RowStep Profile.Scalar.waitRow (.nat n) ()
      (.ofExit (.failure (Cause.fail Profile.Scalar.refusal))) ())

#check (@Effect4.Program.Profile.Scalar.no_step_of_wrong_shape :
  ∀ (s : String), ¬ ∃ completion state',
    Profile.Scalar.spec.RowStep Profile.Scalar.waitRow (.str s) () completion state')

#check (@Effect4.Program.Profile.Resource.lawful :
  LawfulHostSpec Profile.Resource.profile Profile.Resource.spec)

#check (@Effect4.Program.Profile.Resource.acquire_extends :
  ∀ (state : Profile.Resource.State),
    Profile.Resource.spec.RowStep Profile.Resource.acquireRow .unit state
      (.ofExit (.success (Value.external state.slots.length)))
      { state with slots := state.slots ++ [true] })

#check (@Effect4.Program.Profile.Resource.use_fails_after_mutation :
  Profile.Resource.spec.RowStep Profile.Resource.useRow (Value.external 0)
    Profile.Resource.spentState
    (.ofExit (.failure (Cause.fail Profile.Resource.spent)))
    ⟨[true], Profile.Resource.quota + 1⟩)

#check (@Effect4.Program.Profile.Resource.use_failure_mutated :
  (⟨[true], Profile.Resource.quota + 1⟩ : Profile.Resource.State) ≠ Profile.Resource.spentState)

#check (@Effect4.Program.Profile.Resource.release_after_failure :
  Profile.Resource.spec.RowStep Profile.Resource.releaseRow (Value.external 0)
    ⟨[true], Profile.Resource.quota + 1⟩ (.ofExit (.success .unit))
    ⟨[false], Profile.Resource.quota + 1⟩)

#check (@Effect4.Program.Profile.Resource.no_use_after_release :
  ¬ ∃ completion state',
    Profile.Resource.spec.RowStep Profile.Resource.useRow (Value.external 0)
      ⟨[false], Profile.Resource.quota + 1⟩ completion state')

#check (@Effect4.Program.Profile.Resource.no_double_release :
  ¬ ∃ completion state',
    Profile.Resource.spec.RowStep Profile.Resource.releaseRow (Value.external 0)
      ⟨[false], Profile.Resource.quota + 1⟩ completion state')

#check (@Effect4.Program.Profile.Resource.rollback_steps :
  Profile.Resource.rollbackSpec.RowStep Profile.Resource.useRow (Value.external 0)
    Profile.Resource.spentState (.ofExit (.failure (Cause.fail Profile.Resource.spent)))
    Profile.Resource.spentState)

#check (@Effect4.Program.Profile.Resource.rollback_not_lawful :
  ¬ LawfulHostSpec Profile.Resource.profile Profile.Resource.rollbackSpec)

#check (@Effect4.Program.Profile.graphOf_snd :
  ∀ {σ : Type} {outcome : Option (Completion Val Err Defect FiberId Ann)} {mutated : σ}
    {completion : Completion Val Err Defect FiberId Ann} {state' : σ},
    Profile.graphOf outcome mutated = some (completion, state') → state' = mutated)

/-! ### The envelope (DI-58) -/

#check (@Effect4.Program.Envelope : RowTable → NativeMachine → RecordedReply → Prop)

#check (@Effect4.Program.acceptReply :
  RowTable → NativeMachine → RecordedReply → Option NativeDecision)

#check (@Effect4.Program.acceptReply_envelope :
  ∀ (table : RowTable) (m : NativeMachine) (r : RecordedReply) (d : NativeDecision),
    acceptReply table m r = some d → Envelope table m r)

#check (@Effect4.Program.acceptReply_decision :
  ∀ (table : RowTable) (m : NativeMachine) (r : RecordedReply) (d : NativeDecision),
    acceptReply table m r = some d → d = .answerAsync r.fiber r.token r.completion)

#check (@Effect4.Program.acceptReply_of_envelope :
  ∀ (table : RowTable) (m : NativeMachine) (r : RecordedReply),
    Envelope table m r →
      acceptReply table m r = some (.answerAsync r.fiber r.token r.completion))

#check (@Effect4.Program.acceptReply_none_of_table :
  ∀ (table : RowTable) (m : NativeMachine) (r : RecordedReply),
    r.table ≠ table → acceptReply table m r = none)

#check (@Effect4.Program.acceptReply_none_of_request :
  ∀ (table : RowTable) (m : NativeMachine) (r : RecordedReply),
    requestOf m r.fiber r.token ≠ some (r.op, r.request) → acceptReply table m r = none)

#check (@Effect4.Program.acceptReply_none_of_admit :
  ∀ (table : RowTable) (m : NativeMachine) (r : RecordedReply),
    admit table m (.answerAsync r.fiber r.token r.completion) ≠ none →
      acceptReply table m r = none)

#check (@Effect4.Program.acceptReply_none_of_unparked :
  ∀ (table : RowTable) (m : NativeMachine) (r : RecordedReply),
    requestOf m r.fiber r.token = none → acceptReply table m r = none)

#check (@Effect4.Program.AcceptedOnce :
  NativeEff → Nat → RowTable → NativeMachine → RecordedReply → Prop)

#check (@Effect4.Program.acceptedOnce_of_unparked :
  ∀ (program : NativeEff) (fuel : Nat) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply),
    requestOf (steppedBy program fuel table m (.answerAsync r.fiber r.token r.completion))
        r.fiber r.token = none →
      AcceptedOnce program fuel table m r)

end Statements

/-! ## The profile's data

`ProfileData` is data: every field is comparable, and the whole structure is. -/

section Data

#guard rc112.name = "effect@4.0.0-rc.112"
#guard rc112.natBound = 9007199254740991
#guard rc112.formsOf (.row .sync) = some ⟨true, false⟩
#guard rc112.formsOf (.row .async) = some ⟨true, true⟩
#guard rc112.formsOf (.row .program) = some ⟨false, false⟩
-- What the pinned runner does today: `callback` registers an external row, `perform` reaches
-- the placeholder's `.program` kind and answers `frontier`. DI-61 (a) flips the first Boolean.
#guard rc112.formsOf .external = some ⟨false, true⟩
#guard rc112.adapterOf "kvGet" = some "prelude.KvHandle.get"
#guard rc112.adapterOf "sqliteOpen" = some "prelude.Sql.open"
#guard rc112.adapterOf "notARow" = none
#guard rc112.adapters.length = Packages.table.length
#guard rc112.adapters.map Prod.fst = Packages.table.map Row.name
#guard rc112.imports.length = 4
#guard rc112.errorProjection = "DB-15 pair: (reason tag, driver message) as prod string string"
-- a profile is data: two profiles compare
#guard rc112 = rc112
#guard rc112 ≠ Profile.Scalar.profile

end Data

/-! ## The scalar model -/

section ScalarModel

open Effect4.Program.Profile

#guard Scalar.profile.admitsNat 8
#guard !Scalar.profile.admitsNat 9

-- inside the bound: the request is echoed
#guard Scalar.outcome? Scalar.waitRow (.nat 3) () = some (.ofExit (.success (.nat 3)))
#guard Scalar.step? Scalar.waitRow (.nat 3) () = some (.ofExit (.success (.nat 3)), ())
-- outside it: the distinguished profile refusal, not an ordinary answer (DI-56)
#guard Scalar.outcome? Scalar.waitRow (.nat 9) () =
  some (.ofExit (.failure (Cause.fail Scalar.refusal)))
#guard Scalar.refusal = Err.tagged "ProfileRefusal" "nat outside the profile"
-- a request of the wrong shape, and an unknown row: no step at all
#guard (Scalar.step? Scalar.waitRow (.str "3") ()).isNone
#guard (Scalar.step? Scalar.waitRow .unit ()).isNone
#guard (Scalar.step? { Scalar.waitRow with name := "other" } (.nat 3) ()).isNone

-- the two relations, on stores the model can meet
#guard Scalar.RelatedState Stores.empty ()
#guard Scalar.observe Stores.empty ()
#guard ¬ Scalar.observe
  { Stores.empty with externals := ExternalStore.ofAnswers [.ofExit (.success (.nat 9))] } ()

end ScalarModel

/-! ## The allocating model -/

section ResourceModel

open Effect4.Program.Profile

#guard Resource.quota = 2

-- acquire extends the slot table and answers the handle at the new index
#guard Resource.step? Resource.acquireRow .unit Resource.State.empty =
  some (.ofExit (.success (Value.external 0)), ⟨[true], 0⟩)
#guard Resource.step? Resource.acquireRow .unit ⟨[true], 0⟩ =
  some (.ofExit (.success (Value.external 1)), ⟨[true, true], 0⟩)
-- a use inside the budget charges the call and answers
#guard Resource.step? Resource.useRow (Value.external 0) ⟨[true], 0⟩ =
  some (.ofExit (.success (.nat 1)), ⟨[true], 1⟩)
#guard Resource.step? Resource.useRow (Value.external 0) ⟨[true], 1⟩ =
  some (.ofExit (.success (.nat 2)), ⟨[true], 2⟩)
-- failure after mutation: the third use charges, then fails, and leaves the charged state
#guard Resource.step? Resource.useRow (Value.external 0) Resource.spentState =
  some (.ofExit (.failure (Cause.fail Resource.spent)), ⟨[true], 3⟩)
#guard (⟨[true], 3⟩ : Resource.State) ≠ Resource.spentState
-- cleanup after failure: release still steps from the state the failure left
#guard Resource.step? Resource.releaseRow (Value.external 0) ⟨[true], 3⟩ =
  some (.ofExit (.success .unit), ⟨[false], 3⟩)
-- use after release, and a second release: no step at all, which is a frontier and not a refusal
#guard (Resource.step? Resource.useRow (Value.external 0) ⟨[false], 3⟩).isNone
#guard (Resource.step? Resource.releaseRow (Value.external 0) ⟨[false], 3⟩).isNone
-- a handle that was never acquired has no step either
#guard (Resource.step? Resource.useRow (Value.external 5) ⟨[true], 0⟩).isNone
#guard (Resource.step? Resource.releaseRow (Value.external 5) ⟨[true], 0⟩).isNone
-- and a request of the wrong shape
#guard (Resource.step? Resource.useRow (.nat 0) ⟨[true], 0⟩).isNone
#guard (Resource.step? Resource.acquireRow (.nat 0) ⟨[true], 0⟩).isNone

-- the rolling-back specification steps on the same call and hands back the uncharged state,
-- which is exactly what `step_retains` refuses
#guard Resource.rollbackStep? Resource.useRow (Value.external 0) Resource.spentState =
  some (.ofExit (.failure (Cause.fail Resource.spent)), Resource.spentState)
#guard Resource.rollbackStep? Resource.useRow (Value.external 0) ⟨[true], 0⟩ =
  some (.ofExit (.success (.nat 1)), ⟨[true], 1⟩)

/-! ### The relations, against the stores a real run leaves

The tree's own resource program at this model's target (`Test/Api/AcquireHandleContract.lean`,
`harness/truth/Truth.lean`'s `acquireHandleTable`): acquire under a scope, read, then close on
scope exit. One external handle is allocated, which is the model's one slot. -/

def resourceTable : RowTable :=
  [ { name := "acquire", spelling := "Host.acquire", kind := .async, registration := .external,
      request := .unit, answer := .handle Resource.target, error := .never,
      cite := "Test/Program/HostSpecContract.lean" }
  , { name := "close", spelling := "Host.close", kind := .async, registration := .external,
      request := .handle Resource.target, answer := .unit, error := .never,
      cite := "Test/Program/HostSpecContract.lean" }
  , { name := "read", spelling := "Host.read", kind := .async, registration := .external,
      request := .handle Resource.target, answer := .nat, error := .never,
      cite := "Test/Program/HostSpecContract.lean" } ]

def resourceProgram : NativeEff :=
  .scoped (.bind (.acquireRelease (.callback (.external 0) (.lit .unit))
      (.callback (.external 1) (.var 0)))
    (.callback (.external 2) (.var 0)))

def resourceAnswers : List (Completion Val Err Defect FiberId Ann) :=
  [.ofExit (.success (.nat 0)), .ofExit (.success (.nat 7)), .ofExit (.success .unit)]

def resourceRun : Api.Run := Api.run resourceProgram 1000 [] resourceAnswers resourceTable

#guard resourceRun.exit = some (.success (.nat 7))
#guard resourceRun.stores.externals.allocated = [Resource.target]
-- one machine handle, one model slot: the state relation holds at the run's end
#guard Resource.RelatedState resourceRun.stores ⟨[false], 1⟩
#guard ¬ Resource.RelatedState resourceRun.stores ⟨[false, false], 1⟩
-- the observation holds when the slot is closed, and fails when it is left open (the leak)
#guard Resource.observe resourceRun.stores ⟨[false], 1⟩
#guard ¬ Resource.observe resourceRun.stores ⟨[true], 1⟩

end ResourceModel

/-! ## The envelope, on a real parked external call (DI-58) -/

section Envelope

/-- Two asynchronous external rows over the scalars, so that "the wrong row" is a row that
exists (scout B's fixture, `docs/research/2026-09-09-scout-proof-statements.md` §2). -/
def scalarRow (name : String) : Row :=
  { name, spelling := name, kind := .async, request := .nat, answer := .nat, error := .nat,
    cite := "Test/Program/HostSpecContract.lean", registration := .external }

def table : RowTable := [scalarRow "first", scalarRow "second"]

/-- One registered external call, and nothing else. -/
def program : NativeEff := .callback (.external 0) (.lit (.nat 7))

def reply : Completion Val Err Defect FiberId Ann := .ofExit (.success (.nat 9))

/-- The machine after one `evaluate`: the root is parked on the external registration. -/
def parked : NativeMachine := (Api.replay program 40 [Api.evaluate] [] [] table).machine

/-- The correct record of that call's reply. -/
def record : RecordedReply := ⟨table, Api.root, 0, .external 0, .nat 7, reply⟩

-- the premises the positive case rests on, seen
#guard LawfulTable table
#guard requestOf parked Api.root 0 = some (.external 0, .nat 7)
#guard admit table parked (.answerAsync Api.root 0 reply) = none
#guard Envelope table parked record

-- POSITIVE: the record is accepted, and the decision is exactly the one it names
#guard (acceptReply table parked record).isSome
#guard acceptReply table parked record = some (.answerAsync Api.root 0 reply)

-- REFUSED 1: a wrong table
#guard (acceptReply table parked { record with table := [] }).isNone
#guard (acceptReply table parked { record with table := [scalarRow "first"] }).isNone
-- REFUSED 2: a wrong row
#guard (acceptReply table parked { record with op := .external 1 }).isNone
-- REFUSED 3: a wrong request
#guard (acceptReply table parked { record with request := .nat 8 }).isNone
-- REFUSED 4: a wrong token
#guard (acceptReply table parked { record with token := 1 }).isNone
-- REFUSED 5: a wrong fiber
#guard (acceptReply table parked { record with fiber := ⟨1⟩ }).isNone
-- REFUSED 6: a wrong completion category — a success the row's answer type refuses, and a
-- failure the row's error type refuses
#guard (acceptReply table parked
  { record with completion := .ofExit (.success (.str "9")) }).isNone
#guard (acceptReply table parked
  { record with completion := .ofExit (.failure (Cause.fail (.tagged "notNat" "m"))) }).isNone
-- and the failure the row's error type *does* admit is accepted: the refusal is the type's,
-- not the category's
#guard (acceptReply table parked
  { record with completion := .ofExit (.failure (Cause.fail (.tag 5))) }).isSome

/-- The machine after the accepted reply is applied: the same step the checked replay takes. -/
def answered : NativeMachine :=
  steppedBy program 40 table parked (.answerAsync Api.root 0 reply)

-- REFUSED 7: a duplicate reply, once the first has been applied. The park is gone, which is
-- the premise `acceptedOnce_of_unparked` runs on.
#guard requestOf answered Api.root 0 = none
#guard (acceptReply table answered record).isNone
#guard (acceptReply table answered { record with token := 1 }).isNone

end Envelope

/-! ## An exhausted tape is a frontier, never a refusal (v2 R4b) -/

section Frontier

/-- The same program, the ordinary tape, and **no** recorded answer supplied to the oracle. -/
def exhausted : Api.Run ⊕ (Nat × Api.Decision × Refusal × Api.Machine) :=
  Api.replayChecked program 40 [Api.evaluate, Api.flush] [] [] table

-- the tape ran out with the call outstanding: a live frontier, and no refusal
#guard match exhausted with
  | .inl run => run.outcome == Api.Outcome.frontier
  | .inr _ => false
#guard match exhausted with
  | .inl _ => true
  | .inr _ => false
-- and the reply is unconsumed: it is still acceptable at the machine the frontier left
#guard match exhausted with
  | .inl run => (acceptReply table run.machine record).isSome
  | .inr _ => false
#guard match exhausted with
  | .inl run => requestOf run.machine Api.root 0 == some (.external 0, .nat 7)
  | .inr _ => false

/-- The same run with the reply fed in as a decision: the frontier is not a dead end. -/
def completed : Api.Run ⊕ (Nat × Api.Decision × Refusal × Api.Machine) :=
  Api.replayChecked program 40
    [Api.evaluate, .answerAsync Api.root 0 reply, Api.flush] [] [] table

#guard match completed with
  | .inl run => run.outcome == Api.Outcome.finished
  | .inr _ => false
#guard match completed with
  | .inl run => run.exit == some (.success (.nat 9))
  | .inr _ => false

/-- A malformed reply in the tape is a refusal, and it names its position. This is the other
side of the rule: a valid prefix parks, a malformed envelope refuses. -/
def refused : Api.Run ⊕ (Nat × Api.Decision × Refusal × Api.Machine) :=
  Api.replayChecked program 40
    [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (.str "9"))), Api.flush]
    [] [] table

#guard match refused with
  | .inl _ => false
  | .inr (position, _, why, _) => position == 1 && why == Refusal.answerType Api.root 0 .nat

end Frontier

end Test.Program.HostSpecContract
