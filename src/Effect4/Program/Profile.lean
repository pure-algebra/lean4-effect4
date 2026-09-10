import Effect4.Program.Native

/-!
# Program.Profile — the target profile: what is data, what is specification

Rows: DB-09's amendment (v2 §2, "the target profile has three parts with three kinds of
content"), DB-07 (runtime state remains observable on failure), DB-15 (the error projection),
DI-56 (an out-of-profile value has an execution outcome), DI-61 (a) (invocation forms).
Plan: `docs/research/2026-09-09-foundation-settlement-v2.md` §3 row S6a; the design inputs are
`docs/research/2026-09-09-foundation-review.md` §5 (the four parts of a host contract) and
`docs/research/2026-09-09-tie-together-codex-review.md` §3 (the state-indexed relations).

## The three parts, and which one this module owns

DB-09's amendment splits a target profile into three parts with three kinds of content:

1. **`ProfileData`** — serialisable policy and identity: the scalar domain and its refusal
   rule, which invocation forms each call class admits, adapter identities, imports, the
   error projection. *Data only.* No field of `ProfileData` is a function or a proposition.
2. **`HostSpec`** — the Lean specification: the value correspondence, the state relation, the
   call protocol and the observation relation, as relations over abstract host state and host
   values. Functions and propositions live **here**, where DB-09's amendment allows them
   ("functions in checking and semantic code are allowed; functions in canonical programs are
   not").
3. **`Binding`** — the runtime adapter and its evidence: `harness/truth/prelude.ts`, the
   recorder's tapes, the differentials, the finite host tests. **Not in this module and not in
   this slice**; S6b is where a binding meets `harness/truth/Truth.lean`.

This module owns 1 and 2, and two small models of 2 that show the laws are inhabited and are
not vacuous. It owns no adapter, no tape, no third package.

## What this module refuses

* **A function-typed field of `ProfileData`.** Anything that wants a function is `HostSpec`'s.
  Keeping the data first-order is what makes a profile storable, comparable and generatable,
  the same discipline the exclusion list applies to canonical programs.
* **A wire ordinal.** No constructor here is numbered and nothing here derives `Canonical`. A
  profile does not cross the program wire (`src/Effect4/Program/Wire.lean` encodes `Eff`, its
  terms and its rows — not a profile), so it claims no ordinal and no golden byte. Publishing
  a profile would be a new decision with its own byte discipline, taken there.
* **A stateless value correspondence for handles.** `Rep` below is `Ty → Val → HostVal → Prop`
  with no state in it. That is enough to say what a *scalar* means and enough to *name* a
  resource, but not enough to say a resource is live: liveness is `RelatedState`'s. The
  state-indexed `Realizes(P, w, τ, …)` of the Codex review §3.2 is the shape a later slice
  needs; this one records the limit rather than pretending the relation is stronger.
* **A claim that an unanswered call is a refusal.** The frontier rule (v2 R4b, DI-58):
  `RowStep` is a *partial* relation, and a call with no step is a call the host has not
  answered yet. The `Refusal` alphabet of `src/Effect4/Program/Admit.lean` is for malformed
  envelopes; an exhausted tape is `replayCheckedFrom`'s `[] ↦ replayEval` frontier.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## Part one: `ProfileData`, serialisable policy and identity

Every field below is first-order data with decidable equality. The whole structure is
`Repr`-printable and comparable, so two profiles can be diffed and a profile can be projected
to the TypeScript estate the way `ts/eff/packages.gen.ts` projects the package tables. -/

/-- Which syntactic invocation forms a class of call admits. `Eff` has two
(`src/Effect4/Program/Eff.lean`): `perform op request`, the direct invocation, and
`callback op request`, the registered one. A form that is *not* admitted is refused by the
compile — `badShape`, or a `frontier` at the placeholder row — never silently answered
(`src/Effect4/Program/Compile.lean`, `asyncRoute` and the `perform` arm). -/
structure InvocationForms where
  perform : Bool
  callback : Bool
deriving DecidableEq, Repr

/-- What a profile keys its invocation policy on. `RowKind` alone cannot say it: an external
row registers by its index at compile time, before any table is read, and its placeholder row
carries `kind := .program` (`src/Effect4/Program/Native.lean`), so "external" is a class of
call and not a row kind. -/
inductive CallClass
  | row (kind : RowKind)
  | external
deriving DecidableEq, Repr

/-- The serialisable half of a target profile: identity, the scalar domain, the invocation
policy, the adapter and import identities, and the name of the error projection. Data only —
adding a function-typed field here is the mistake this structure exists to prevent. -/
structure ProfileData where
  /-- The profile's identity, as the pinned package spells it. -/
  name : String
  /-- The upper bound of the scalar domain: the largest `Nat` this target represents exactly.
  A request or answer above it is outside the profile, and its execution outcome is a
  distinguished refusal rather than an ordinary failure (DI-56). -/
  natBound : Nat
  /-- Which invocation forms each call class admits. -/
  admittedForms : List (CallClass × InvocationForms)
  /-- Row name to adapter identifier: what implements the row on this target. An identifier,
  never an implementation. -/
  adapters : List (String × String)
  /-- The module specifiers a binding for this profile must import. -/
  imports : List String
  /-- The name of the error projection this profile uses (DB-15). A name, because the
  projection itself is code and code is `Binding`'s. -/
  errorProjection : String
deriving DecidableEq, Repr

namespace ProfileData

/-- The invocation policy at a call class; `none` when the profile says nothing about it,
which is not the same as refusing it. -/
def formsOf (profile : ProfileData) (call : CallClass) : Option InvocationForms :=
  (profile.admittedForms.find? fun entry => entry.1 == call).map Prod.snd

/-- The adapter identifier bound to a row name. -/
def adapterOf (profile : ProfileData) (row : String) : Option String :=
  (profile.adapters.find? fun entry => entry.1 == row).map Prod.snd

/-- The scalar refusal rule, as a decision on the value's magnitude. -/
def admitsNat (profile : ProfileData) (n : Nat) : Bool := n ≤ profile.natBound

/-- The Boolean policy and the proposition the models guard on are the same thing. -/
theorem admitsNat_iff (profile : ProfileData) (n : Nat) :
    profile.admitsNat n = true ↔ n ≤ profile.natBound := by
  simp [admitsNat]

end ProfileData

/-- The first target profile: `effect@4.0.0-rc.112` on the pinned host (DB-09).

`natBound` is JavaScript's `Number.MAX_SAFE_INTEGER`, `2^53 - 1`: above it the host's `+`
stops being exact (`harness/truth/prelude.ts`, `add`), which is the arithmetic DI-56 rules on.

`admittedForms` records the runner's invocation routes (DI-61): asynchronous built-ins
and external rows admit both spellings, while synchronous rows retain `perform` only.
The shared production dispatcher and its independent route matrix establish this boundary
(`src/Effect4/Program/Compile.lean`; `Test/Program/InvocationContract.lean`).

`adapters` names the prelude exports the eight canonical package rows are bound to
(`src/Effect4/Program/Packages.lean`; `harness/truth/prelude.ts`, its `Sql`, `Kv`, `SqlHandle`
and `KvHandle` members). `imports` is that file's own import list. -/
def rc112 : ProfileData where
  name := "effect@4.0.0-rc.112"
  natBound := 2 ^ 53 - 1
  admittedForms :=
    [ (.row .sync, ⟨true, false⟩)
    , (.row .async, ⟨true, true⟩)
    , (.row .program, ⟨false, false⟩)
    , (.external, ⟨true, true⟩) ]
  adapters :=
    [ ("sqliteOpen", "prelude.Sql.open")
    , ("sqlUnsafe", "prelude.SqlHandle.unsafe")
    , ("sqliteClose", "prelude.Sql.close")
    , ("kvMake", "prelude.Kv.make")
    , ("kvGet", "prelude.KvHandle.get")
    , ("kvSet", "prelude.KvHandle.set")
    , ("kvRemove", "prelude.KvHandle.remove")
    , ("kvHas", "prelude.KvHandle.has") ]
  imports :=
    [ "effect"
    , "effect/unstable/persistence"
    , "effect/unstable/reactivity/Reactivity"
    , "@effect/sql-sqlite-bun" ]
  errorProjection := "DB-15 pair: (reason tag, driver message) as prod string string"

/-! ## Part two: `HostSpec`, the Lean specification

Four relations and one function, over two abstract types — the host's state and the host's
values. Neither type is a second heap: `HostState` is whatever a binding needs in order to say
which resources exist and what they hold, and `HostVal` is whatever crosses the boundary. The
machine's side of each relation is the tree's own data (`Ty`, `Val`, `Stores`, `Completion`),
so a specification is written without naming a single host object.

`after` is the one function field, and it is what makes DB-07 statable: a row's work reaches a
state *before* its outcome is decided, and `LawfulHostSpec.step_retains` says every step lands
on that state whether the call succeeded or failed. Scout B's transformer counterexample is
why it is a field and not a convention: `StateT σ (Except ε)` discards the state on failure and
`ExceptT ε (StateM σ)` keeps it (`docs/research/2026-09-09-scout-proof-statements.md` §4). -/

/-- A target's semantics, as relations. `HostState` and `HostVal` are abstract: a binding
chooses them and nothing here inspects them. -/
structure HostSpec (HostState HostVal : Type) where
  /-- The value correspondence: a host value means this machine value at this type. Stateless
  by construction — the module header says what that costs for handles. -/
  Rep : Ty → Val → HostVal → Prop
  /-- The state relation: which machine stores a host state may stand beside. -/
  RelatedState : Stores → HostState → Prop
  /-- The state a row's work reaches, before its outcome is decided. -/
  after : Row → Val → HostState → HostState
  /-- The call protocol, as one relation: from this state, this row at this request may
  complete this way and leave that state. A *partial* relation — a call with no step is a call
  the host has not answered, which is a frontier and not a refusal (DI-58). Both the success
  and the failure transition carry an after-state; `step_retains` fixes which one. -/
  RowStep : Row → Val → HostState → Completion Val Err Defect FiberId Ann → HostState → Prop
  /-- The observation the differential compares under: what a run's stores and the host's state
  must agree on. The comparator's own losses are named where it lives
  (`harness/truth/run-truth.ts`), not here. -/
  observe : Stores → HostState → Prop

/-- The three laws a specification owes. Each is earned by a fixture in
`Test/Program/HostSpecContract.lean`. -/
structure LawfulHostSpec {HostState HostVal : Type}
    (profile : ProfileData) (spec : HostSpec HostState HostVal) : Prop where
  /-- The scalar domain is the profile's: a natural number is represented only inside the
  bound. This is what makes `natBound` policy and not a comment (DI-56). -/
  rep_scalar_bound :
    ∀ (n : Nat) (hostValue : HostVal), spec.Rep .nat (.nat n) hostValue → n ≤ profile.natBound
  /-- DB-07: a step lands on the state its work reached, whichever way it completed. A
  specification whose failure arm rolls back to the before-state cannot satisfy this;
  `Profile.Resource.rollback_not_lawful` is the refutation that says the field is not
  decoration. -/
  step_retains :
    ∀ (row : Row) (request : Val) (state : HostState)
      (completion : Completion Val Err Defect FiberId Ann) (state' : HostState),
      spec.RowStep row request state completion state' → state' = spec.after row request state
  /-- DI-58, at the specification: at most one completion per outstanding call. Two
  completions of the same call from the same state cannot both step. -/
  one_completion :
    ∀ (row : Row) (request : Val) (state : HostState)
      (c₁ : Completion Val Err Defect FiberId Ann) (s₁ : HostState)
      (c₂ : Completion Val Err Defect FiberId Ann) (s₂ : HostState),
      spec.RowStep row request state c₁ s₁ → spec.RowStep row request state c₂ s₂ → c₁ = c₂

namespace Profile

/-! ## The shape both models share

Each model's step relation is the graph of a partial function: the completion is decided, and
whatever completes lands on the state the row's work reached. `graphOf` is that shape, and the
two laws about a graph are proved once here rather than in each model. -/

/-- A decided completion, paired with the state the row's work reached. -/
def graphOf {σ : Type} (outcome : Option (Completion Val Err Defect FiberId Ann)) (mutated : σ) :
    Option (Completion Val Err Defect FiberId Ann × σ) :=
  match outcome with
  | some completion => some (completion, mutated)
  | none => none

/-- Whatever steps lands on the mutated state: `LawfulHostSpec.step_retains` for a graph. -/
theorem graphOf_snd {σ : Type} {outcome : Option (Completion Val Err Defect FiberId Ann)}
    {mutated : σ} {completion : Completion Val Err Defect FiberId Ann} {state' : σ}
    (h : graphOf outcome mutated = some (completion, state')) : state' = mutated := by
  unfold graphOf at h
  split at h
  · exact (congrArg Prod.snd (Option.some.inj h)).symm
  · exact absurd h.symm (Option.some_ne_none _)

/-- A partial function has at most one value: `LawfulHostSpec.one_completion` for a graph. -/
theorem graph_functional {α β : Type} {step : Option (α × β)} {a₁ a₂ : α} {b₁ b₂ : β}
    (h₁ : step = some (a₁, b₁)) (h₂ : step = some (a₂, b₂)) : a₁ = a₂ ∧ b₁ = b₂ :=
  let h := Option.some.inj (h₁.symm.trans h₂)
  ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## Two models

Neither is an adapter and neither runs: each is a `HostSpec` whose relations are decidable
graphs, proved lawful, with the transitions the settlement asks for stated as theorems and
exercised in the battery as `#guard`s. They exist to show that `LawfulHostSpec`'s fields are
inhabited, that they are not vacuous, and that the three transitions the reviews named —
failure after mutation, cleanup after failure, use after release — are expressible.

`Profile.Scalar` is the pure case: one row, no host state, a bound small enough that a fixture
violates it. `Profile.Resource` is the allocating case: acquire, use, release over a table of
open slots and a use budget. -/

/-! ### The scalar model -/

namespace Scalar

/-- One row, `Host.wait : nat → nat`, pure: it answers its own request. It transcribes no
rc.112 export — it is a specification fixture, and its `cite` says where it is written. -/
def waitRow : Row where
  name := "wait"
  spelling := "Host.wait"
  kind := .async
  registration := .external
  request := .nat
  answer := .nat
  error := .prod .string .string
  cite := "src/Effect4/Program/Profile.lean"

/-- A deliberately tiny scalar domain, so that a request of `9` is out of profile and every
fixture fits on one line. rc.112's own bound is `rc112.natBound`. -/
def profile : ProfileData where
  name := "hostspec-scalar-model"
  natBound := 8
  admittedForms := [(.external, ⟨false, true⟩)]
  adapters := [("wait", "model.Host.wait")]
  imports := []
  errorProjection := rc112.errorProjection

/-- DI-56's distinguished refusal: a value outside the scalar domain neither answers nor fails
the way the program failed — it crosses as its own tagged host error, so a comparator can
classify the run "outside the profile" instead of as agreement or disagreement. The pair is
DB-15's. -/
def refusal : Err := .tagged "ProfileRefusal" "nat outside the profile"

/-- The host value: a number, and nothing else. -/
abbrev HostVal := Nat

/-- No host state at all: the row is pure. -/
abbrev State := Unit

/-- A number means a number, inside the bound. -/
def Rep (ty : Ty) (value : Val) (hostValue : HostVal) : Prop :=
  ty = .nat ∧ value = .nat hostValue ∧ hostValue ≤ profile.natBound

/-- A pure row mints no handle, so a related store has an empty external allocation table. -/
def RelatedState (stores : Stores) (_state : State) : Prop :=
  stores.externals.allocated = []

/-- What the differential compares: every recorded answer was consumed. -/
def observe (stores : Stores) (_state : State) : Prop :=
  stores.externals.answers = []

instance (stores : Stores) (state : State) : Decidable (RelatedState stores state) :=
  inferInstanceAs (Decidable (_ = _))

instance (stores : Stores) (state : State) : Decidable (observe stores state) :=
  inferInstanceAs (Decidable (_ = _))

/-- The row's work changes nothing. -/
def after (_row : Row) (_request : Val) (state : State) : State := state

/-- How the call completes: the request echoed inside the bound, the profile refusal outside
it, and no step at all for another row or a request of the wrong shape. -/
def outcome? (row : Row) (request : Val) (_state : State) :
    Option (Completion Val Err Defect FiberId Ann) :=
  match request with
  | .nat n =>
    if row.name = waitRow.name then
      if n ≤ profile.natBound then some (.ofExit (.success (.nat n)))
      else some (.ofExit (.failure (Cause.fail refusal)))
    else none
  | _ => none

/-- The step, as the graph of a partial function. -/
def step? (row : Row) (request : Val) (state : State) :
    Option (Completion Val Err Defect FiberId Ann × State) :=
  graphOf (outcome? row request state) (after row request state)

def spec : HostSpec State HostVal where
  Rep := Rep
  RelatedState := RelatedState
  after := after
  RowStep := fun row request state completion state' =>
    step? row request state = some (completion, state')
  observe := observe

theorem lawful : LawfulHostSpec profile spec where
  rep_scalar_bound := by
    intro n hostValue h
    obtain ⟨_, hv, hb⟩ := h
    injection hv with heq
    subst heq
    exact hb
  step_retains := fun _ _ _ _ _ h => graphOf_snd h
  one_completion := fun _ _ _ _ _ _ _ h₁ h₂ => (graph_functional h₁ h₂).1

/-! The three facts the settlement asks a scalar row to show. -/

theorem outcome_in_profile (n : Nat) (h : n ≤ profile.natBound) :
    outcome? waitRow (.nat n) () = some (.ofExit (.success (.nat n))) := if_pos h

theorem outcome_out_of_profile (n : Nat) (h : ¬ n ≤ profile.natBound) :
    outcome? waitRow (.nat n) () = some (.ofExit (.failure (Cause.fail refusal))) := if_neg h

/-- A request inside the bound is answered by echoing it. -/
theorem in_profile (n : Nat) (h : n ≤ profile.natBound) :
    spec.RowStep waitRow (.nat n) () (.ofExit (.success (.nat n))) () := by
  show step? waitRow (.nat n) () = _
  unfold step?
  rw [outcome_in_profile n h]
  rfl

/-- A request outside the bound completes as the profile refusal, not as an answer: the run is
outside the profile and says so (DI-56). -/
theorem out_of_profile (n : Nat) (h : ¬ n ≤ profile.natBound) :
    spec.RowStep waitRow (.nat n) () (.ofExit (.failure (Cause.fail refusal))) () := by
  show step? waitRow (.nat n) () = _
  unfold step?
  rw [outcome_out_of_profile n h]
  rfl

/-- Nothing else steps: a request of the wrong shape is a call the host has not answered. -/
theorem no_step_of_wrong_shape (s : String) :
    ¬ ∃ completion state', spec.RowStep waitRow (.str s) () completion state' := by
  rintro ⟨completion, state', h⟩
  have hn : (none : Option (Completion Val Err Defect FiberId Ann × State)) =
      some (completion, state') := h
  exact absurd hn.symm (Option.some_ne_none _)

end Scalar

/-! ### The allocating model -/

namespace Resource

/-- The handle target the three rows share. -/
def target : String := "HostSpec.Resource"

/-- How many `use` calls the host serves before the budget is spent. Small on purpose: the
mutate-then-fail transition is reached by the third call. -/
def quota : Nat := 2

/-- `acquire : unit → handle`. Its shape is the tree's own resource fixture
(`Test/Api/AcquireHandleContract.lean`, `harness/truth/Truth.lean`'s `acquireHandleTable`),
whose adapter is `Host.acquire` in `harness/truth/prelude.ts`. -/
def acquireRow : Row where
  name := "acquire"
  spelling := "Host.acquire"
  kind := .async
  registration := .external
  request := .unit
  answer := .handle target
  error := .never
  cite := "src/Effect4/Program/Profile.lean"

/-- `use : handle → nat`. It fails when the budget is spent — *after* it has charged the call,
which is the transition DB-07 is about.

This is a **stricter** row than the tree's `read` (`harness/truth/Truth.lean`'s
`acquireHandleTable`): `read` exists to observe release and answers `1` on a closed resource
(`harness/truth/prelude.ts`, `Host.read`), so it is not a `use` in this model's sense and this
model does not specify it. -/
def useRow : Row where
  name := "use"
  spelling := "Host.use"
  kind := .async
  registration := .external
  request := .handle target
  answer := .nat
  error := .prod .string .string
  cite := "src/Effect4/Program/Profile.lean"

/-- `release : handle → unit`. Releasing twice has no step: the second release is a call the
host will not answer. The pinned adapter agrees — `Host.close` throws on a closed resource
(`harness/truth/prelude.ts`). -/
def releaseRow : Row where
  name := "release"
  spelling := "Host.release"
  kind := .async
  registration := .external
  request := .handle target
  answer := .unit
  error := .never
  cite := "src/Effect4/Program/Profile.lean"

def profile : ProfileData where
  name := "hostspec-resource-model"
  natBound := 8
  admittedForms := [(.external, ⟨false, true⟩)]
  adapters :=
    [ ("acquire", "model.Host.acquire")
    , ("use", "model.Host.use")
    , ("release", "model.Host.release") ]
  imports := []
  errorProjection := rc112.errorProjection

/-- The budget's failure, as DB-15's pair. -/
def spent : Err := .tagged "Resource" "the resource's use budget is spent"

/-- The host's state: one slot per `acquire` in allocation order, `true` while the resource is
open, and the number of `use` calls already charged. Acquisition *extends* the slot list and
release *closes* a slot; the two are different transitions, which is the distinction the Codex
review §3.2 asks a state relation to keep. -/
structure State where
  slots : List Bool
  uses : Nat
deriving DecidableEq, Repr

namespace State

def empty : State := ⟨[], 0⟩

/-- Is the resource at this index open? An index past the end is not. -/
def isOpen (state : State) (index : Nat) : Bool :=
  match state.slots[index]? with
  | some b => b
  | none => false

end State

/-- The host value: a number, a resource, or nothing. -/
inductive HostVal
  | num (n : Nat)
  | res (index : Nat)
  | unit
deriving DecidableEq, Repr

/-- A number means a number inside the bound; a resource means the external handle at its
index; nothing means `unit`. Liveness is deliberately absent — see the module header. -/
def Rep (ty : Ty) (value : Val) : HostVal → Prop
  | .num n => ty = .nat ∧ value = .nat n ∧ n ≤ profile.natBound
  | .res index => ty = .handle target ∧ value = Value.external index
  | .unit => ty = .unit ∧ value = .unit

/-- Every acquired resource has exactly one machine handle, in the same order. Acquisition
extends both sides; nothing on the machine's side records a close, which is why the leak check
is `observe`'s and not this relation's. -/
def RelatedState (stores : Stores) (state : State) : Prop :=
  stores.externals.allocated.length = state.slots.length

/-- What the differential compares: the counts agree and nothing is left open. The second
conjunct is the leak check — the obligation the Codex review §3.3 raises about a scope whose
owner fails after registering cleanup. -/
def observe (stores : Stores) (state : State) : Prop :=
  stores.externals.allocated.length = state.slots.length ∧
    state.slots.all (fun isOpen => !isOpen) = true

instance (stores : Stores) (state : State) : Decidable (RelatedState stores state) :=
  inferInstanceAs (Decidable (_ = _))

instance (stores : Stores) (state : State) : Decidable (observe stores state) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The state a row's work reaches: `acquire` appends a slot, `use` charges the call, `release`
closes the slot it names. This is the state every step lands on, success or failure
(`LawfulHostSpec.step_retains`). -/
def after (row : Row) (request : Val) (state : State) : State :=
  if row.name = acquireRow.name then { state with slots := state.slots ++ [true] }
  else if row.name = useRow.name then { state with uses := state.uses + 1 }
  else if row.name = releaseRow.name then
    match request with
    | Value.external index => { state with slots := state.slots.set index false }
    | _ => state
  else state

/-- How the call completes. Three rows, and `none` — no step — wherever the host owes no
answer: an unknown row, a request of the wrong shape, a `use` after release, a second
release. -/
def outcome? (row : Row) (request : Val) (state : State) :
    Option (Completion Val Err Defect FiberId Ann) :=
  if row.name = acquireRow.name then
    match request with
    | .unit => some (.ofExit (.success (Value.external state.slots.length)))
    | _ => none
  else if row.name = useRow.name then
    match request with
    | Value.external index =>
      if state.isOpen index then
        if state.uses + 1 ≤ quota then some (.ofExit (.success (.nat (state.uses + 1))))
        else some (.ofExit (.failure (Cause.fail spent)))
      else none
    | _ => none
  else if row.name = releaseRow.name then
    match request with
    | Value.external index =>
      if state.isOpen index then some (.ofExit (.success .unit)) else none
    | _ => none
  else none

/-- The step, as the graph of a partial function: whatever completes, lands on `after`. -/
def step? (row : Row) (request : Val) (state : State) :
    Option (Completion Val Err Defect FiberId Ann × State) :=
  graphOf (outcome? row request state) (after row request state)

def spec : HostSpec State HostVal where
  Rep := Rep
  RelatedState := RelatedState
  after := after
  RowStep := fun row request state completion state' =>
    step? row request state = some (completion, state')
  observe := observe

theorem lawful : LawfulHostSpec profile spec where
  rep_scalar_bound := by
    intro n hostValue h
    cases hostValue with
    | num m =>
      obtain ⟨_, hv, hb⟩ := h
      injection hv with heq
      subst heq
      exact hb
    | res index => obtain ⟨ht, _⟩ := h; exact Ty.noConfusion ht
    | unit => obtain ⟨ht, _⟩ := h; exact Ty.noConfusion ht
  step_retains := fun _ _ _ _ _ h => graphOf_snd h
  one_completion := fun _ _ _ _ _ _ _ h₁ h₂ => (graph_functional h₁ h₂).1

/-! The transitions the settlement asks an allocating row to show. -/

/-- One open resource, with the budget already spent. -/
def spentState : State := ⟨[true], quota⟩

/-- Acquire extends the slot list, and the answer is the handle at the new index. -/
theorem acquire_extends (state : State) :
    spec.RowStep acquireRow .unit state
      (.ofExit (.success (Value.external state.slots.length)))
      { state with slots := state.slots ++ [true] } := rfl

/-- **Failure after mutation.** The third `use` charges the call and then fails; the state it
leaves is the charged one, not the one it started from. DB-07 in the small. -/
theorem use_fails_after_mutation :
    spec.RowStep useRow (Value.external 0) spentState
      (.ofExit (.failure (Cause.fail spent))) ⟨[true], quota + 1⟩ := rfl

/-- What it left is not what it started from: the mutation is retained, not rolled back. -/
theorem use_failure_mutated : (⟨[true], quota + 1⟩ : State) ≠ spentState := by decide

/-- **Cleanup after failure.** Release still steps from the state the failed `use` left, and
closes the slot. -/
theorem release_after_failure :
    spec.RowStep releaseRow (Value.external 0) ⟨[true], quota + 1⟩
      (.ofExit (.success .unit)) ⟨[false], quota + 1⟩ := rfl

/-- **Use after release is refused by having no step**, not by a completion: the host owes an
answer it will never give, which is a frontier and not a refusal (DI-58). -/
theorem no_use_after_release :
    ¬ ∃ completion state',
        spec.RowStep useRow (Value.external 0) ⟨[false], quota + 1⟩ completion state' := by
  rintro ⟨completion, state', h⟩
  have hn : (none : Option (Completion Val Err Defect FiberId Ann × State)) =
      some (completion, state') := h
  exact absurd hn.symm (Option.some_ne_none _)

/-- A second release has no step either. -/
theorem no_double_release :
    ¬ ∃ completion state',
        spec.RowStep releaseRow (Value.external 0) ⟨[false], quota + 1⟩ completion state' := by
  rintro ⟨completion, state', h⟩
  have hn : (none : Option (Completion Val Err Defect FiberId Ann × State)) =
      some (completion, state') := h
  exact absurd hn.symm (Option.some_ne_none _)

/-! ### The refutation: `step_retains` is not decoration

The same three rows with one change — the failure arm rolls back to the before-state, which is
what `StateT σ (Except ε)` does (scout B §4) — is not a lawful specification. -/

/-- Does this completion carry a failure? -/
def failing : Completion Val Err Defect FiberId Ann → Bool
  | .ofExit (.failure _) => true
  | _ => false

/-- The rolling-back step: `step?` except that a failure hands back the state the call started
from. -/
def rollbackStep? (row : Row) (request : Val) (state : State) :
    Option (Completion Val Err Defect FiberId Ann × State) :=
  match outcome? row request state with
  | some completion =>
    some (completion, if failing completion then state else after row request state)
  | none => none

def rollbackSpec : HostSpec State HostVal :=
  { spec with
    RowStep := fun row request state completion state' =>
      rollbackStep? row request state = some (completion, state') }

/-- The rolling-back specification does step, on the same call. -/
theorem rollback_steps :
    rollbackSpec.RowStep useRow (Value.external 0) spentState
      (.ofExit (.failure (Cause.fail spent))) spentState := rfl

/-- And it is therefore not lawful: `step_retains` refuses it. The witness is that same third
`use` — it charged the call and then handed back the uncharged state. -/
theorem rollback_not_lawful : ¬ LawfulHostSpec profile rollbackSpec := by
  intro lawful
  have retained : spentState = after useRow (Value.external 0) spentState :=
    lawful.step_retains useRow (Value.external 0) spentState _ _ rollback_steps
  exact absurd retained (by decide)

end Resource

end Profile

end Effect4.Program
