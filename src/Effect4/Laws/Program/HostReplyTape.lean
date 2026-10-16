import Effect4.Laws.Program.HostSource
import Effect4.Laws.Api.HostSession
import Effect4.Laws.Program.LinkedRows
import Effect4.Laws.Program.Template

/-!
Concept: translation-simulation, R6.
Question: admitted reply facts serve Run.CallTree.request_leads and Routing authorization.
Reach: actual session admission, checked external-only source, and actual recorded histories.
Limit: reply shape alone proves neither the call-prefix simulation nor progress or outside-host agreement.
Unlock: the operational prefix uses submitted exits after excluding delayed cell reads at the real boundary.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program Effect4.Run

/-- A program part retains an external row through definition and parameter extensions.
Consumer: checked reply columns in `request_leads`. -/
theorem part_external_row {sig : Signature NativeOp} {root : NativeEff} {env : TyEnv}
    {path rest : List Nat} {part : Part NativeOp} {index : Nat}
    (call : sig.callOf (.external index) = none)
    (param : sig.paramOf (.external index) = none)
    (held : root.partAt sig env path = some (part, rest)) :
    part.sig.rowOf (.external index) = sig.rowOf (.external index) := by
  unfold Eff.partAt at held
  split at held
  · split at held
    · obtain ⟨params, same⟩ := Part.bodyAt_sig held
      rw [same]
      cases params <;> simp only [Signature.withParams, Signature.withDefs, call, param]
    · cases held
      simp only [Signature.withDefs, call]
    · cases held
      simp only [Signature.withDefs, call]
    · cases held
  · cases held
    rfl

/-- A linked external row retains the table's closed reply columns.
Consumer: checked instance admission agrees with table-only reply admission. -/
theorem ConcreteReplies.row {table : RowTable} (closed : ConcreteReplies table)
    {index : Nat} {row : Row} (found : externalRow table index = some row) :
    row.answer.closed = true ∧ row.error.closed = true := by
  obtain ⟨raw, member, _, _, rfl⟩ := externalRow_raw found
  have both := List.all_eq_true.mp closed raw (List.mem_of_getElem? member)
  simp only [Bool.and_eq_true] at both
  exact ⟨Ty.closed_normalize _ both.1, Ty.closed_normalize _ both.2⟩

/-- A checked call's concrete reply columns are the linked row's columns.
Consumer: the actual call-indexed admission branch of `request_leads`. -/
theorem instance_reply_columns {app : SigApp} (closed : ConcreteReplies app.rows)
    {program : Api.Program} {path : List Nat} {checked : CallInstance NativeOp}
    {index : Nat} {row : Row} (found : externalRow app.rows index = some row)
    (atCall : Api.HostSession.instanceAt program app path = some checked)
    (operation : checked.op = .external index) :
    checked.answer = row.answer ∧ checked.error = row.error := by
  obtain ⟨part, rest, request, env, ty, held, _, _, _, typed, answer, error, _⟩ :=
    programCallAt_rowTy atCall
  rw [operation] at typed
  have same := part_external_row (index := index) (by rfl) (by rfl) held
  change part.sig.rowOf (.external index) = (nativeSignature app.rows).rowOf (.external index) at same
  rw [same, externalRow_signature found] at typed
  obtain ⟨bindings, _, answerTy, errorTy⟩ :=
    checkRow_rowBindings ((rowTy_eq_some_iff _ _ _ _).mp typed)
  have both := closed.row found
  rw [Ty.instantiate_closed _ _ both.1] at answerTy
  rw [Ty.instantiate_closed _ _ both.2] at errorTy
  have normalized := externalRow_normalized found
  have answerNormal := congrArg Row.answer normalized
  have errorNormal := congrArg Row.error normalized
  exact ⟨answer.symm.trans (answerTy.trans answerNormal),
    error.symm.trans (errorTy.trans errorNormal)⟩

/-- A plain admitted exit passes the local host check at the current allocation table.
Consumer: the actual reply tape in `request_leads`. -/
theorem admitted_exit_tape {app : SigApp} {m : NativeMachine} {fiber : FiberId}
    {token index : Nat} {row : Row} {exit : ExitV}
    (found : externalRow app.rows index = some row)
    (accepted : admitAnswer app.types row m fiber token (.ofExit exit) = none) :
    externalAdmits app index (.ofExit exit) m.state.externals.allocated = true := by
  unfold externalAdmits
  rw [found]
  cases exit with
  | success value =>
    simp only [admitAnswer] at accepted
    cases converted : externalValue app.types row.answer m.state.externals.allocated value with
    | none => simp only [converted, Option.isNone_none, if_true] at accepted; cases accepted
    | some result =>
      have free := externalValue_input_handleFree _ _ _ result.1 value result.2 converted
      simp only [converted, Option.isSome_some, free, List.isEmpty_nil, Bool.and_self]
  | failure cause =>
    simp only [admitAnswer] at accepted
    split at accepted
    · cases accepted
    · next noReserved =>
      split at accepted
      · next typed =>
        have absent : cause.reasons.any reservedDie = false := Bool.eq_false_iff.mpr noReserved
        simp only [absent, Bool.not_false, typed, Bool.true_and]
      · cases accepted

/-- Concrete checked-instance admission passes the same row check at current allocations.
Consumer: the actual call-indexed reply tape in `request_leads`. -/
theorem instance_exit_tape {app : SigApp} (closed : ConcreteReplies app.rows)
    {program : Api.Program} {m : NativeMachine} {record : RecordedReply} {exit : ExitV}
    (envelope : InstanceEnvelope app (Api.HostSession.instanceAt program app) m record)
    (completion : record.completion = .ofExit exit) :
    ∃ index, record.op = .external index ∧
      externalAdmits app index (.ofExit exit) m.state.externals.allocated = true := by
  obtain ⟨_, _, index, row, origin, checked, operation, found, noAllocation,
    _, atCall, same, admitted⟩ := envelope
  obtain ⟨answer, error⟩ := instance_reply_columns closed found atCall (same.trans operation)
  refine ⟨index, operation, ?_⟩
  rw [completion] at admitted
  unfold externalAdmits
  rw [found]
  cases exit with
  | success value =>
    simp only [admitInstance] at admitted
    split at admitted
    · next typed =>
      rw [answer] at typed
      dsimp only
      rw [externalValue_unallocating noAllocation, if_pos typed]
      simp only [Option.isSome_some, Bool.true_and]
      exact (Bool.and_eq_true_iff.mp typed).2
    · cases admitted
  | failure cause =>
    simp only [admitInstance] at admitted
    split at admitted
    · cases admitted
    · next noReserved =>
      split at admitted
      · next typed =>
        have absent : cause.reasons.any reservedDie = false := Bool.eq_false_iff.mpr noReserved
        rw [error] at typed
        simp only [absent, Bool.not_false, typed, Bool.true_and]
      · cases admitted

/-- Every admitted history retains the existing source ownership carrier.
Consumer: the actual external-call address in `request_leads`. -/
theorem ExternalOnly.owned_history {built : Api.Built} (source : ExternalOnly built.program)
    (compileFuel : Nat) (m : NativeMachine) (history : HistoryOf built compileFuel m) :
    ConfigurationAt built.program m := by
  have moved := history_keeps built compileFuel
    (fun m => ConfigurationAt built.program m ∧ HeapSites.HeapOk (fun _ => True) m.state.refs)
    ⟨load_at built.program source.fragment compileFuel,
      load_heap built.program compileFuel (fun _ => True)⟩
    (fun before row held _ => heap_reply_decision built.program source.fragment built.table
      (fun _ => True) (source.sites _) row.1 before row.2 held.1 held.2) m history
  exact moved.1

/-- A live external request comes from an actual call in the authored source.
Consumer: the operational call prefix retains the actual source row. -/
theorem request_source {root : NativeEff} {m : NativeMachine} {fiber : FiberId} {token : Nat}
    {op : NativeOp} {request : Val} (owned : ConfigurationAt root m)
    (call : Program.requestOf m fiber token = some (op, request)) :
    ∃ origin term, Node.at_ (.eff root) origin = some (.eff (.perform op term)) := by
  obtain ⟨current, controller, cancel, origin, found, _, code⟩ :=
    requestOf_current m fiber token op request call
  have held := (configuration_fiber root m fiber current owned found).frame.1
  rw [code] at held
  obtain ⟨term, site⟩ := held.1
  exact ⟨origin, term, site⟩

/-- Neither admission branch accepts a delayed cell read from an empty reference heap.
Consumer: the actual recorded reply tape in CallTree.request_leads. -/
theorem accepted_exit (app : SigApp) (calls : List (List Nat × CallInstance NativeOp))
    (m : NativeMachine) (fiber : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann) (empty : m.state.refs = [])
    (accepted : Accepted app calls m (.answerAsync fiber token answer)) :
    ∃ exit, answer = .ofExit exit := by
  cases answer with
  | ofExit exit => exact ⟨exit, rfl⟩
  | ofRefGet cell =>
    obtain ⟨record, plain | specialized⟩ := accepted
    · have same := acceptReply_decision app m record _ plain
      simp only [RunDecision.answerAsync.injEq] at same
      have envelope := acceptReply_envelope app m record _ plain
      unfold Envelope at envelope
      rw [← same.2.2] at envelope
      obtain ⟨_, _, row, _, _, admitted⟩ := admitted_row app m record.fiber record.token
        (.ofRefGet cell) envelope.2.2
      rw [empty_heap_refused app.types row m record.fiber record.token cell empty] at admitted
      cases admitted
    · obtain ⟨envelope, same⟩ := acceptAtInstance_sound app _ m record _ specialized
      simp only [RunDecision.answerAsync.injEq] at same
      obtain ⟨_, _, _, _, _, checked, _, _, _, _, _, _, admitted⟩ := envelope
      rw [← same.2.2] at admitted
      cases admitted

/-- Every accepted answer at a reached external-only run is an exit.
Consumer: the actual session prefix's host tape, without a host-driven-script restriction. -/
theorem reached_answer_exit (s : Run) (reached : Run.Reached s)
    (source : ExternalOnly s.built.program) (fiber : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann)
    (accepted : Accepted s.built.app s.session.calls s.machine (.answerAsync fiber token answer)) :
    ∃ exit, answer = .ofExit exit :=
  accepted_exit _ _ _ _ _ _
    (source.empty_heap s.budget.compileFuel s.machine (Run.reached_history s reached).2) accepted

end Effect4.Program.SourceScope
