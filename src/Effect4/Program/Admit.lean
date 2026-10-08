import Effect4.Program.Compile
import Effect4.Program.Typing.Call

/-! Checked decisions refine the machine's existing tape walk. The machine
retains its raw total runner; this boundary reports the first refused answer. -/

namespace Effect4.Program
open Effect4 Effect4.Machine

abbrev NativeMachine := RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
abbrev NativeDecision := RunDecision EffName EffThunk Val Err Defect FiberId Ann
abbrev NativeReplay := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- The executable counterpart of `Handle.existsIn`. Unknown kind bytes are not
handles in the machine's `MintedIn` judgment; value typing checks their shape. -/
def handleLive (m : NativeMachine) (handle : UInt8 × Nat) : Bool :=
  match HandleKind.ofByte? handle.1 with
  | some .fiber => (m.fibers.map RunFiber.id).contains ⟨handle.2⟩
  | some .cell => decide (handle.2 < m.state.refs.length)
  | some .promise => decide (handle.2 < m.state.deferreds.cells.length)
  | some .scope => (m.state.scopes.entryAt handle.2).isSome
  | some .memoMap => (m.state.memo.mapAt ⟨handle.2⟩).isSome
  | some .external => decide (handle.2 < m.state.externals.allocated.length)
  | none => true

def mintedIn (m : NativeMachine) (v : Val) : Bool :=
  (Store.Val.handles v).all (handleLive m)

/-- A matching external park retains its row and evaluated request in `current`.
`Machine/Fibers.lean` only replaces that current code when the answer is taken. -/
def requestOf (m : NativeMachine) (fiber : FiberId) (token : Nat) : Option (NativeOp × Val) := do
  let f ← m.fiber? fiber
  guard (f.parked = .withGuard token)
  match f.frame.current with
  | .async (.external op request _) _ _ => some (op, request)
  | _ => none

/-- One call the machine is waiting on: the parked fiber, the guard token it parked on, the row
it called and the request it evaluated. A record, so the most-read field of a run's response
crosses a boundary with its field names (decisions row 16); its codec is generated
(`Api/RunnerDerived.lean`, the `Runner` group). -/
structure Await where
  fiber : FiberId
  token : Nat
  op : NativeOp
  request : Val
deriving DecidableEq

def awaits (m : NativeMachine) : List Await :=
  m.fibers.filterMap fun f =>
    match f.parked with
    | .withGuard token => (requestOf m f.id token).map fun (op, req) => ⟨f.id, token, op, req⟩
    | .notParked => none

/-- Operational refusals, separate from program failures and live frontiers. -/
inductive Refusal
  | notParked (fiber : FiberId)
  | staleToken (fiber : FiberId) (parkedOn : Nat) (offered : Nat)
  | notExternal (fiber : FiberId) (token : Nat)
  | answerType (fiber : FiberId) (token : Nat) (expected : Ty)
  | errorType (fiber : FiberId) (token : Nat) (expected : Ty)
  | deadHandle (fiber : FiberId) (token : Nat)
  /-- A host failure carrying `badName` or `notImplemented`, the machine's own markers for
  malformed code (decisions row 191, `E4-HOST-CE-008`). -/
  | reservedDefect (fiber : FiberId) (token : Nat)
  | unknownCell (cell : RefKey)
  | oracleType (position : Nat) (expected : Ty)
deriving DecidableEq, Repr

/-- Check the answer's type before liveness, so a typed but unallocated handle
is reported as `deadHandle`. A failure is refused first for a reserved defect, then checked
reason by reason against the error column. A reference read must satisfy the same answer
type. -/
def admitAnswer (row : Row) (m : NativeMachine) (fiber : FiberId) (token : Nat) :
    Completion Val Err Defect FiberId Ann → Option Refusal
  | .ofExit (.success v) =>
    if (externalValue row.answer m.state.externals.allocated v).isNone then
      some (.answerType fiber token row.answer)
    else if !mintedIn m v then some (.deadHandle fiber token)
    else none
  | .ofExit (.failure cause) =>
    if cause.reasons.any reservedDie then some (.reservedDefect fiber token)
    else if cause.reasons.all (errAdmits row.error) then none
    else some (.errorType fiber token row.error)
  | .ofRefGet cell =>
    match m.state.refs[cell.index]? with
    | none => some (.unknownCell cell)
    | some v =>
      if !Val.hasTy v row.answer m.state.externals.allocated then some (.answerType fiber token row.answer)
      else if !mintedIn m v then some (.deadHandle fiber token)
      else none

def admit (table : RowTable) (m : NativeMachine) : NativeDecision → Option Refusal
  | .answerAsync fiber token answer =>
    match m.fiber? fiber with
    | none => some (.notParked fiber)
    | some f =>
      match f.parked with
      | .notParked => some (.notParked fiber)
      | .withGuard parkedOn =>
        if parkedOn ≠ token then some (.staleToken fiber parkedOn token)
        else match requestOf m fiber token with
          | some (.external i, _) =>
            match externalRow table i with
            | some row => admitAnswer row m fiber token answer
            | none => some (.notExternal fiber token)
          | _ => some (.notExternal fiber token)
  | _ => none

/-- The first rejected registration remains visible even when another fiber
subsequently consumes the oracle head or the rejecting fiber is interrupted. -/
def oracleRefusal (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (m : NativeMachine) : Option Refusal := do
  let (i, answer, remaining) ← m.state.externals.rejected
  let expected := match externalRow table i, answer with
    | some row, .ofExit (.failure _) => row.error
    | some row, _ => row.answer
    | none, _ => Ty.never
  some (.oracleType (answers.length - remaining) expected)

/-- The same stopping rules as `replayEval` and `answersValid`: no decision
beyond a stuck state or exhausted driver fuel is inspected. -/
def replayCheckedFrom (program : NativeEff) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (position : Nat) (tape : List NativeDecision) (m : NativeMachine) :
    NativeReplay ⊕ (Nat × NativeDecision × Refusal × NativeMachine) :=
  letI := evaluatorFor program table
  match tape with
  | [] => .inl (replayEval (interpOf program table) fuel [] m)
  | decision :: rest =>
    match m.stuck with
    | some why => .inl (.stuck why m)
    | none =>
      match admit table m decision with
      | some why => .inr (position, decision, why, m)
      | none =>
        let r := stepDecisionState (interpOf program table) fuel m decision
        match oracleRefusal answers table r.1 with
        | some why => .inr (position, decision, why, r.1)
        | none =>
          if r.2 then replayCheckedFrom program fuel answers table (position + 1) rest r.1
          else .inl (.frontier .fuel r.1)
termination_by tape

/-- Every external frontier after each applied decision, in fiber order. -/
def replayStepsFrom (program : NativeEff) (fuel : Nat) (table : RowTable)
    (position : Nat) (tape : List NativeDecision) (m : NativeMachine) :
    List (Nat × NativeDecision × List Await) :=
  letI := evaluatorFor program table
  match tape with
  | [] => []
  | decision :: rest =>
    match m.stuck with
    | some _ => []
    | none =>
      let r := stepDecisionState (interpOf program table) fuel m decision
      (position, decision, awaits r.1) ::
        if r.2 then replayStepsFrom program fuel table (position + 1) rest r.1 else []
termination_by tape

/-! ## Recorded replies and their envelope (DI-58)

A checked replay above consumes *decisions*. A recorded host reply is not a decision: it is a
record a driver decoded, and DI-58 is the ruling that the driver must check the record against
the machine before turning it into one. `Envelope` is that check and `acceptReply` is the
turning.

Scout B elaborated and proved this shape before the settlement ruled on it
(`docs/research/2026-09-09-scout-proof-statements.md` §2 P1(b)); the definitions and the two
implications below are its work, landed here with the laws the settlement adds.

**What is refused, and what is not.** Refusals are for *malformed envelopes only*: a wrong
table, row, request, token or fiber, a completion the row's answer or error type refuses, and
a duplicate or stale reply. An unanswered call, an exhausted tape, or a decision that does not
advance the machine is a **frontier**, and `replayCheckedFrom` already spells it as one
(`[] ↦ replayEval …`, and `r.2 = false ↦ .frontier`). A fixture that expects a run to finish
fails its own completion assertion; it does not turn a valid prefix into a refusal.

**What the table field is.** `RecordedReply` stores the whole `RowTable` rather than an
identity or a digest of one. That is deliberate: publishing a table identity is a decision
nobody has taken (DI-22 on what an external index is a position in), and full equality needs
none. -/

/-- One decoded host reply: the table it was recorded against, the parked call it answers, the
row and request it claims that call made, and the completion it carries. -/
structure RecordedReply where
  table : RowTable
  fiber : FiberId
  token : Nat
  op : NativeOp
  request : Val
  completion : Completion Val Err Defect FiberId Ann

/-- The envelope of a recorded reply, in three parts, all decidable: the reply was recorded
against *this* table; the machine really holds that parked call, at that token, on that row and
that evaluated request (`requestOf`); and the answer this runner would be handed is admissible
(`admit`, whose `Refusal` alphabet covers the answer type, the error type, dead handles and
unknown cells). -/
def Envelope (table : RowTable) (m : NativeMachine) (r : RecordedReply) : Prop :=
  r.table = table ∧ requestOf m r.fiber r.token = some (r.op, r.request) ∧
    admit table m (.answerAsync r.fiber r.token r.completion) = none

instance (table : RowTable) (m : NativeMachine) (r : RecordedReply) :
    Decidable (Envelope table m r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Turn a recorded reply into a decision, or refuse it. The only decision this ever returns is
the `answerAsync` the record names, so a driver cannot smuggle a different one through. -/
def acceptReply (table : RowTable) (m : NativeMachine) (r : RecordedReply) :
    Option NativeDecision :=
  if Envelope table m r then some (.answerAsync r.fiber r.token r.completion) else none

/-- An accepted reply establishes its envelope (scout B). -/
theorem acceptReply_envelope (table : RowTable) (m : NativeMachine) (r : RecordedReply)
    (d : NativeDecision) (h : acceptReply table m r = some d) : Envelope table m r := by
  unfold acceptReply at h
  split at h
  · assumption
  · exact absurd h.symm (Option.some_ne_none _)

/-- An accepted reply returns exactly the decision the record names, and nothing else. -/
theorem acceptReply_decision (table : RowTable) (m : NativeMachine) (r : RecordedReply)
    (d : NativeDecision) (h : acceptReply table m r = some d) :
    d = .answerAsync r.fiber r.token r.completion := by
  unfold acceptReply at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h.symm (Option.some_ne_none _)

/-- The converse: an envelope is accepted. Together with the two above, `acceptReply` is the
envelope and nothing more. -/
theorem acceptReply_of_envelope (table : RowTable) (m : NativeMachine) (r : RecordedReply)
    (h : Envelope table m r) :
    acceptReply table m r = some (.answerAsync r.fiber r.token r.completion) :=
  if_pos h

/-- A reply recorded against a different table is refused, whatever else is right about it. -/
theorem acceptReply_none_of_table (table : RowTable) (m : NativeMachine) (r : RecordedReply)
    (h : r.table ≠ table) : acceptReply table m r = none :=
  if_neg fun envelope => h envelope.1

/-- A reply whose claimed row or request is not the parked one is refused. -/
theorem acceptReply_none_of_request (table : RowTable) (m : NativeMachine) (r : RecordedReply)
    (h : requestOf m r.fiber r.token ≠ some (r.op, r.request)) : acceptReply table m r = none :=
  if_neg fun envelope => h envelope.2.1

/-- A reply this runner would refuse to admit is refused here first. -/
theorem acceptReply_none_of_admit (table : RowTable) (m : NativeMachine) (r : RecordedReply)
    (h : admit table m (.answerAsync r.fiber r.token r.completion) ≠ none) :
    acceptReply table m r = none :=
  if_neg fun envelope => h envelope.2.2

/-- No park, no reply: a machine that is not holding that call at that token accepts nothing
for it. This is what a stale token and a duplicate reply both come down to — `requestOf`
answers `none` unless the fiber is parked `.withGuard token` on an external registration
(`requestOf`, above). -/
theorem acceptReply_none_of_unparked (table : RowTable) (m : NativeMachine) (r : RecordedReply)
    (h : requestOf m r.fiber r.token = none) : acceptReply table m r = none :=
  acceptReply_none_of_request table m r
    (by rw [h]; exact fun hc => absurd hc.symm (Option.some_ne_none _))

/-! ## Replies at the call's checked instance (decisions row 183)

A row with a type parameter answers at the instance that the checker chose at the call
(`callAt`, `Program/Typing/Call.lean`). A value of the request cannot recover that choice: the
empty list is a member of every list type. So an external registration keeps the address of
its call (`EffName.external`'s `origin`). A reply that the row's own columns refuse is checked
again at the call's instance.

The instance check never allocates. An allocation request, a number at a handle column, stays
the row's own (`admitAnswer`), because the machine's preparation reads the row's column
(`prepareExternalAnswer`). So the instance path stands only at a row whose answer column is
no handle. A delayed cell read stays the row's own too. -/

/-- The address of the call that a parked external registration came from. -/
def originOf (m : NativeMachine) (fiber : FiberId) (token : Nat) : Option (List Nat) := do
  let f ← m.fiber? fiber
  guard (f.parked = .withGuard token)
  match f.frame.current with
  | .async (.external _ _ origin) _ _ => some origin
  | _ => none

/-- Whether a column allocates an external handle at a reply: a handle type at its top. -/
def allocates : Ty → Bool
  | .handle _ => true
  | _ => false

/-- **The answer check at a call's checked instance.** A success is a member of the instance's
answer column and holds no handle. A failure holds no reserved defect, and its reasons are
members of the instance's error column. A delayed cell read is refused here. -/
def admitInstance (c : CallInstance NativeOp) (m : NativeMachine) (fiber : FiberId) (token : Nat) :
    Completion Val Err Defect FiberId Ann → Option Refusal
  | .ofExit (.success v) =>
    if Val.hasTy v c.answer m.state.externals.allocated && (Store.Val.handles v).isEmpty then none
    else some (.answerType fiber token c.answer)
  | .ofExit (.failure cause) =>
    if cause.reasons.any reservedDie then some (.reservedDefect fiber token)
    else if cause.reasons.all (errAdmits c.error) then none
    else some (.errorType fiber token c.error)
  | .ofRefGet _ => some (.answerType fiber token c.answer)

/-- **The envelope of a recorded reply at its call's checked instance.** The reply was recorded
against this table. The machine holds that parked call, at that token, on that external row,
whose answer column allocates nothing. The program's instance at the call's address is an
instance of that row, and it admits the completion. `instanceAt` is the program's lookup by
address (`callAt`). -/
def InstanceEnvelope (table : RowTable) (instanceAt : List Nat → Option (CallInstance NativeOp))
    (m : NativeMachine) (r : RecordedReply) : Prop :=
  r.table = table ∧ requestOf m r.fiber r.token = some (r.op, r.request) ∧
    ∃ i row origin c, r.op = .external i ∧ externalRow table i = some row ∧
      allocates row.answer = false ∧ originOf m r.fiber r.token = some origin ∧
      instanceAt origin = some c ∧ c.op = r.op ∧
      admitInstance c m r.fiber r.token r.completion = none

/-- Turn a recorded reply into a decision at its call's checked instance, or refuse it. As
`acceptReply`, the only decision it returns is the `answerAsync` the record names. -/
def acceptAtInstance (table : RowTable) (instanceAt : List Nat → Option (CallInstance NativeOp))
    (m : NativeMachine) (r : RecordedReply) : Option NativeDecision :=
  if r.table = table ∧ requestOf m r.fiber r.token = some (r.op, r.request) then
    match r.op, originOf m r.fiber r.token with
    | .external i, some origin =>
      match externalRow table i, instanceAt origin with
      | some row, some c =>
        if allocates row.answer = false ∧ c.op = r.op ∧
            admitInstance c m r.fiber r.token r.completion = none then
          some (.answerAsync r.fiber r.token r.completion)
        else none
      | _, _ => none
    | _, _ => none
  else none

/-- The machine after the checked replay applies one decision: the same step
`replayCheckedFrom` takes, named so that a law about "after the reply" can be stated without
re-deriving the evaluator instance. -/
def steppedBy (program : NativeEff) (fuel : Nat) (table : RowTable) (m : NativeMachine)
    (d : NativeDecision) : NativeMachine :=
  letI := evaluatorFor program table
  (stepDecisionState (interpOf program table) fuel m d).1

/-- **At most one accepted completion per outstanding call** (DI-58, v2 R4b): once a reply has
been accepted and applied, the same reply is refused. -/
def AcceptedOnce (program : NativeEff) (fuel : Nat) (table : RowTable) (m : NativeMachine)
    (r : RecordedReply) : Prop :=
  ∀ d, acceptReply table m r = some d →
    acceptReply table (steppedBy program fuel table m d) r = none

/-- The one-completion law, from the one fact that carries it: applying the answer takes the
fiber off its guard, so the machine afterwards holds no park at that token and
`acceptReply_none_of_unparked` refuses the second reply. The premise is about the stepped
machine, so a fixture supplies it by evaluation — see `Test/Program/HostSpecContract.lean`. -/
theorem acceptedOnce_of_unparked (program : NativeEff) (fuel : Nat) (table : RowTable)
    (m : NativeMachine) (r : RecordedReply)
    (h : requestOf (steppedBy program fuel table m (.answerAsync r.fiber r.token r.completion))
      r.fiber r.token = none) :
    AcceptedOnce program fuel table m r := by
  intro d hd
  have hdec := acceptReply_decision table m r d hd
  subst hdec
  exact acceptReply_none_of_unparked table _ r h

end Effect4.Program
