import Effect4.Program.Compile

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
  | .async (.external op request) _ _ => some (op, request)
  | _ => none

abbrev Await := FiberId × Nat × NativeOp × Val

def awaits (m : NativeMachine) : List Await :=
  m.fibers.filterMap fun f =>
    match f.parked with
    | .withGuard token => (requestOf m f.id token).map fun (op, req) => (f.id, token, op, req)
    | .notParked => none

/-- Operational refusals, separate from program failures and live frontiers. -/
inductive Refusal
  | notParked (fiber : FiberId)
  | staleToken (fiber : FiberId) (parkedOn : Nat) (offered : Nat)
  | notExternal (fiber : FiberId) (token : Nat)
  | answerType (fiber : FiberId) (token : Nat) (expected : Ty)
  | errorType (fiber : FiberId) (token : Nat) (expected : Ty)
  | deadHandle (fiber : FiberId) (token : Nat)
  | unknownCell (cell : RefKey)
  | oracleType (position : Nat) (expected : Ty)
deriving DecidableEq, Repr

/-- Check the answer's type before liveness, so a typed but unallocated handle
is reported as `deadHandle`. A reference read must satisfy the same answer type. -/
def admitAnswer (row : Row) (m : NativeMachine) (fiber : FiberId) (token : Nat) :
    Completion Val Err Defect FiberId Ann → Option Refusal
  | .ofExit (.success v) =>
    if (externalValue row.answer m.state.externals.allocated v).isNone then
      some (.answerType fiber token row.answer)
    else if !mintedIn m v then some (.deadHandle fiber token)
    else none
  | .ofExit (.failure cause) =>
    if cause.reasons.all (errAdmits row.error) then none
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
          else .inl (.frontier r.1)
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

end Effect4.Program
