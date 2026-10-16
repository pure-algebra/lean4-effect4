import Effect4.Program.Admit
import Effect4.Program.TyDecls

/-!
# Program.AdmitIn — reply admission under a declaration table

Reply admission (`Program/Admit.lean`) reads a row's columns with `Val.hasTy`, which reads no
table. So at a column that names a declared type it refuses every honest answer, and at a column
`handle n` it reads a natural as an allocation request even where `n` is declared. This module
writes each reader beside its original, under a table (decisions rows 400 to 402; the plan
`docs/research/2026-10-16-usability-scope/wiring-plan.md`, increment W2b):

* **The allocation classifier** (`allocatesIn`): a column allocates an external handle at a reply
  only where its head is a handle that the table does not declare (decisions row 401 (3)).
* **Membership under the table** (`Val.hasTyIn`) wherever the original reads `Val.hasTy`: the
  success value (`externalValueIn`), the error column (`errAdmitsIn`), a delayed cell read
  (`admitAnswerIn`), the call's checked instance (`admitInstanceIn`), and the row protocol's check
  (`externalAdmitsIn`).
* **The decision check and the recorded reply** (`admitIn`, `EnvelopeIn`, `acceptReplyIn`,
  `acceptAtInstanceIn`), each the original at its readers under the table.

Each reader is its original at the empty table by definition: it matches on the table first. So
every law of the original holds unchanged where the table is empty. The instance path keeps the
machine's own test (`allocates`): the machine's preparation reads the row's column as it is
(`prepareExternalAnswer`), so the instance path stands only at a column that is no handle.

The laws are `Laws/Program/AdmitIn.lean`. No caller reads these yet; the session moves in the
plan's increment W4. This module is not a Lean module (decisions row 200): it imports
`Program/Admit.lean`, which is not one.
-/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- **The allocation classifier under a table** (decisions row 401 (3)): a column allocates an
external handle at a reply where its head is a handle whose name the table does not declare. At
the empty table it is `allocates`. -/
def allocatesIn (decls : TyDecls) (t : Ty) : Bool :=
  match decls with
  | [] => allocates t
  | _ => allocates t && (t.refName?.bind decls.body?).isNone

/-- A reply's data: the value itself, where it is a member of the column under the table and
holds no handle. -/
def dataValueIn (decls : TyDecls) (ty : Ty) (allocated : List String) (value : Val) :
    Option (List String × Val) :=
  if Val.hasTyIn decls [] value ty allocated && (Store.Val.handles value).isEmpty then
    some (allocated, value)
  else none

/-- **A reply's success value under a table**: at a handle column whose name the table does not
declare, a natural at the next index is an allocation request, as `externalValue` reads it.
Every other value, and every value at a declared name, is data, read by membership under the
table. At the empty table it is `externalValue`. -/
def externalValueIn (decls : TyDecls) (ty : Ty) (allocated : List String) (value : Val) :
    Option (List String × Val) :=
  match decls with
  | [] => externalValue ty allocated value
  | _ =>
    match ty, value with
    | .handle target, .nat index =>
      if (decls.body? target).isSome then dataValueIn decls ty allocated value
      else if externalHandleTarget target && index == allocated.length then
        some (allocated ++ [target], Value.external index)
      else none
    | _, _ => dataValueIn decls ty allocated value

/-- A reason fits an error column under a table: a typed failure's value is a member of the
column. At the empty table it is `errAdmits`. -/
def errAdmitsIn (decls : TyDecls) (ty : Ty) : Reason Err Defect FiberId Ann → Bool :=
  match decls with
  | [] => errAdmits ty
  | _ => reasonAdmits (fun v t => Val.hasTyIn decls [] v t []) ty

/-- **The answer check under a table**: `admitAnswer` at the readers under the table. At the
empty table it is `admitAnswer`. -/
def admitAnswerIn (decls : TyDecls) (row : Row) (m : NativeMachine) (fiber : FiberId)
    (token : Nat) (answer : Completion Val Err Defect FiberId Ann) : Option Refusal :=
  match decls with
  | [] => admitAnswer row m fiber token answer
  | _ =>
    match answer with
    | .ofExit (.success v) =>
      if (externalValueIn decls row.answer m.state.externals.allocated v).isNone then
        some (.answerType fiber token row.answer)
      else if !mintedIn m v then some (.deadHandle fiber token)
      else none
    | .ofExit (.failure cause) =>
      if cause.reasons.any reservedDie then some (.reservedDefect fiber token)
      else if cause.reasons.all (errAdmitsIn decls row.error) then none
      else some (.errorType fiber token row.error)
    | .ofRefGet cell =>
      match m.state.refs[cell.index]? with
      | none => some (.unknownCell cell)
      | some v =>
        if !Val.hasTyIn decls [] v row.answer m.state.externals.allocated then
          some (.answerType fiber token row.answer)
        else if !mintedIn m v then some (.deadHandle fiber token)
        else none

/-- **The decision check under a table**: `admit` with the answer check under the table. At the
empty table it is `admit`. -/
def admitIn (decls : TyDecls) (table : RowTable) (m : NativeMachine) (d : NativeDecision) :
    Option Refusal :=
  match decls with
  | [] => admit table m d
  | _ =>
    match d with
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
              | some row => admitAnswerIn decls row m fiber token answer
              | none => some (.notExternal fiber token)
            | _ => some (.notExternal fiber token)
    | _ => none

/-- The envelope of a recorded reply under a table: `Envelope` at the decision check under the
table. -/
def EnvelopeIn (decls : TyDecls) (table : RowTable) (m : NativeMachine) (r : RecordedReply) :
    Prop :=
  r.table = table ∧ requestOf m r.fiber r.token = some (r.op, r.request) ∧
    admitIn decls table m (.answerAsync r.fiber r.token r.completion) = none

instance (decls : TyDecls) (table : RowTable) (m : NativeMachine) (r : RecordedReply) :
    Decidable (EnvelopeIn decls table m r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **A recorded reply turned into a decision under a table**, or refused. At the empty table it
is `acceptReply`. -/
def acceptReplyIn (decls : TyDecls) (table : RowTable) (m : NativeMachine) (r : RecordedReply) :
    Option NativeDecision :=
  match decls with
  | [] => acceptReply table m r
  | _ => if EnvelopeIn decls table m r then some (.answerAsync r.fiber r.token r.completion)
    else none

/-- **The answer check at a call's checked instance, under a table.** At the empty table it is
`admitInstance`. -/
def admitInstanceIn (decls : TyDecls) (c : CallInstance NativeOp) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (answer : Completion Val Err Defect FiberId Ann) :
    Option Refusal :=
  match decls with
  | [] => admitInstance c m fiber token answer
  | _ =>
    match answer with
    | .ofExit (.success v) =>
      if Val.hasTyIn decls [] v c.answer m.state.externals.allocated &&
          (Store.Val.handles v).isEmpty then none
      else some (.answerType fiber token c.answer)
    | .ofExit (.failure cause) =>
      if cause.reasons.any reservedDie then some (.reservedDefect fiber token)
      else if cause.reasons.all (errAdmitsIn decls c.error) then none
      else some (.errorType fiber token c.error)
    | .ofRefGet _ => some (.answerType fiber token c.answer)

/-- **A recorded reply at its call's checked instance, under a table.** The row's column must
allocate nothing by the machine's own test (`allocates`), since the machine prepares the reply at
that column. At the empty table it is `acceptAtInstance`. -/
def acceptAtInstanceIn (decls : TyDecls) (table : RowTable)
    (instanceAt : List Nat → Option (CallInstance NativeOp)) (m : NativeMachine)
    (r : RecordedReply) : Option NativeDecision :=
  match decls with
  | [] => acceptAtInstance table instanceAt m r
  | _ =>
    if r.table = table ∧ requestOf m r.fiber r.token = some (r.op, r.request) then
      match r.op, originOf m r.fiber r.token with
      | .external i, some origin =>
        match externalRow table i, instanceAt origin with
        | some row, some c =>
          if allocates row.answer = false ∧ c.op = r.op ∧
              admitInstanceIn decls c m r.fiber r.token r.completion = none then
            some (.answerAsync r.fiber r.token r.completion)
          else none
        | _, _ => none
      | _, _ => none
    else none

/-- **A row's own admission under a table** (the row protocol's check). At the empty table it is
`externalAdmits`. -/
def externalAdmitsIn (decls : TyDecls) (table : RowTable) (i : Nat)
    (answer : Completion Val Err Defect FiberId Ann) (allocated : List String := []) : Bool :=
  match decls with
  | [] => externalAdmits table i answer allocated
  | _ =>
    match externalRow table i, answer with
    | some row, .ofExit (.success v) =>
      (externalValueIn decls row.answer allocated v).isSome && (Store.Val.handles v).isEmpty
    | some row, .ofExit (.failure cause) =>
      !cause.reasons.any reservedDie && cause.reasons.all (errAdmitsIn decls row.error)
    | _, _ => false

end Effect4.Program
