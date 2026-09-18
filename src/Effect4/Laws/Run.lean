import Effect4.Run
import Effect4.Laws.Api.Runner
import Effect4.Laws.Api.HostSession
import Effect4.Laws.Api.Frontier
import Effect4.Laws.Program.Admit

/-!
# Laws.Run — what a run guarantees

The run API of scout A (`docs/research/2026-09-17-host-session-api-scout-A.md` §4.3, §4.5)
and the obligations it names.

* **Opening cannot refuse** (`open_total`): given a certificate, `HostSession.start` returns
  the very session `Run.open` builds. Every one of its refusals is impossible, the admission
  it re-derives included.
* **A run is its own recording** (`journal_replays`): a run that was opened and played is
  reached again by opening it under the same name and playing its journal. This is what makes
  "replay this run" a statement about a run rather than a convention between drivers.
* **Driving is playing** (`drive_eq_play`): the run a host drove is the run its rows reach,
  so replay plays rows and never calls a host.
* **A host inside the envelope is never refused for it** (`drive_envelope`, and the stronger
  `answer_accepted` under it): if every completion a host gives is one the machine admits,
  the three rows of an answer are bound, received and applied — not refused.
* **The claims are the machine's** (`bindCall_at`, `receive_rows`, `answer_rows`): a call
  built by `Call.at` is never stale, and the conveniences are the rows they say they are.
* **One completion per call** (`answer_once`): after an answer is applied the machine holds
  no call at that key, so there is nothing left to answer there and the recorded rows are
  refused if they are played again.
* **The ordinary run is the ordinary run** (`runPure_eq_run`): the journal `[evaluate,
  flush]` leaves the machine `Api.run` leaves.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Session Header Call Reply Key Answer Phase BoundCall ReplySlot)
open Effect4.Api.Runner (Command Runner)

/-! ## Playing rows -/

theorem step_session (s : Run) (c : Command) :
    (s.step c).session = (Api.Runner.result s.runner c).session := rfl

theorem step_phases (s : Run) (c : Command) :
    (s.step c).phases = s.phases ++ [(Api.Runner.result s.runner c).phase] := rfl

theorem step_journal (s : Run) (c : Command) : (s.step c).journal = s.journal ++ [c] := rfl

/-! Each row's transition, named so that a proof can rewrite with a fact about it. -/

theorem step_session_bind (s : Run) (call : Call) (token : Nat) :
    (s.step (.bind call token)).session =
      (Api.HostSession.bindCall s.session call token).session := rfl

theorem step_phases_bind (s : Run) (call : Call) (token : Nat) :
    (s.step (.bind call token)).phases =
      s.phases ++ [(Api.HostSession.bindCall s.session call token).phase] := rfl

theorem step_session_submit (s : Run) (reply : Reply) :
    (s.step (.submit reply)).session = (Api.HostSession.submit s.session reply).session := rfl

theorem step_phases_submit (s : Run) (reply : Reply) :
    (s.step (.submit reply)).phases =
      s.phases ++ [(Api.HostSession.submit s.session reply).phase] := rfl

theorem step_session_apply (s : Run) (key : Key) :
    (s.step (.apply key)).session =
      (Api.HostSession.applyReply s.session key s.budget.fuel).session := rfl

theorem step_phases_apply (s : Run) (key : Key) :
    (s.step (.apply key)).phases =
      s.phases ++ [(Api.HostSession.applyReply s.session key s.budget.fuel).phase] := rfl

theorem step_session_control (s : Run) (d : Api.Decision) :
    (s.step (.control d)).session =
      (Api.HostSession.advance s.session s.budget.fuel d).session := rfl

theorem step_phases_control (s : Run) (d : Api.Decision) :
    (s.step (.control d)).phases =
      s.phases ++ [(Api.HostSession.advance s.session s.budget.fuel d).phase] := rfl

theorem step_built (s : Run) (c : Command) : (s.step c).built = s.built := rfl

theorem step_budget (s : Run) (c : Command) : (s.step c).budget = s.budget := rfl

theorem play_nil (s : Run) : s.play [] = s := rfl

theorem play_cons (s : Run) (c : Command) (rows : List Command) :
    s.play (c :: rows) = (s.step c).play rows := rfl

theorem play_single (s : Run) (c : Command) : s.play [c] = s.step c := rfl

/-- Rows act on runs: a concatenation plays as its parts, in order. -/
theorem play_append (s : Run) (a b : List Command) : s.play (a ++ b) = (s.play a).play b := by
  simp only [Run.play, List.foldl_append]

/-- No transition writes the header, so the name and the profile of a run are the ones it was
opened under, however many rows it has played. -/
theorem result_header (p : Runner) (c : Command) :
    (Api.Runner.result p c).session.header = p.session.header := by
  cases c with
  | bind call token =>
    unfold Api.Runner.result Api.HostSession.bindCall
    dsimp only
    repeat' split
    all_goals rfl
  | submit reply =>
    unfold Api.Runner.result Api.HostSession.submit
    dsimp only
    repeat' split
    all_goals rfl
  | apply key =>
    unfold Api.Runner.result Api.HostSession.applyReply
    dsimp only
    repeat' split
    all_goals rfl
  | control decision =>
    unfold Api.Runner.result Api.HostSession.advance
    dsimp only
    repeat' split
    all_goals rfl

theorem step_id (s : Run) (c : Command) : (s.step c).id = s.id :=
  congrArg Header.session (result_header s.runner c)

theorem step_profile (s : Run) (c : Command) : (s.step c).profile = s.profile :=
  congrArg Header.profile (result_header s.runner c)

/-! An opened run has played nothing. -/

theorem open_phases (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String) :
    (Run.open b id budget profile).phases = [] := rfl

theorem open_journal (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String) :
    (Run.open b id budget profile).journal = [] := rfl

theorem open_machine (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String) :
    (Run.open b id budget profile).machine = Api.load b.program budget.compileFuel := rfl

/-! ## A run is its own recording -/

/-- A run that was opened and then played. Nothing else makes a `Run`: the fields are only
ever written by `Run.open` and `Run.step`. -/
inductive Reached : Run → Prop
  | opened (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String) :
      Reached (Run.open b id budget profile)
  | step (s : Run) (c : Command) : Reached s → Reached (s.step c)

theorem Reached.play (s : Run) (rows : List Command) (h : Reached s) : Reached (s.play rows) := by
  induction rows generalizing s with
  | nil => exact h
  | cons c rest ih => exact ih (s.step c) (.step s c h)

theorem Reached.open (b : Api.Built) (id : String) (budget : Api.Budget := {})
    (profile : String := "") : Reached (Run.open b id budget profile) := .opened b id budget profile

/-- **O-9.** A run replays from its own journal: opening the same built program under the
same name and budget and playing the rows it recorded reaches exactly that run, phases and
ledger included. No host is called, because a host is not in the journal. -/
theorem journal_replays (s : Run) (h : Reached s) :
    (Run.open s.built s.id s.budget s.profile).play s.journal = s := by
  induction h with
  | opened b id budget profile => rfl
  | step s c hs ih =>
    rw [step_built, step_id, step_budget, step_profile, step_journal, play_append, ih,
      play_single]

/-! ## Driving is playing -/

/-- **O-6.** The run a host drove is the run its rows reach from where the drive started. The
host chose the rows; nothing else about it is left in the run, so a replay of those rows
calls no host. -/
theorem drive_eq_play {σ : Type} (r : Reactor σ) (rounds : Nat) (s : Run) (st : σ) :
    (driveFrom r rounds s st).1 = s.play (driveFrom r rounds s st).2.1 := by
  induction rounds generalizing s st with
  | zero => rfl
  | succ rounds ih =>
    rw [driveFrom]
    split
    · split
      · rfl
      · split
        · rfl
        · dsimp only
          rw [play_append]
          exact ih _ _
    · split
      · rfl
      · dsimp only
        split
        · rfl
        · dsimp only
          rw [play_append]
          exact ih _ _

/-! ## Opening cannot refuse -/

/-- A program has at most one admission certificate against one table: every field but the
type is a proof, and the type is the one the checker computes, so two certificates agree. -/
theorem admitted_unique (program : Api.Program) (table : RowTable)
    (a b : AdmittedProgram program table) : a = b := by
  obtain ⟨⟨tya, ha⟩, _, _, _, _, _⟩ := a
  obtain ⟨⟨tyb, hb⟩, _, _, _, _, _⟩ := b
  have hty : tya = tyb := Option.some.inj (ha.symm.trans hb)
  subst hty
  rfl

/-- Admission answers with the certificate it is given: every check `admitProgram` runs is a
field of the certificate, so none of them can fail. This is the fact `HostSession.start`
needs and the tree did not have. -/
theorem admitProgram_certificate (program : Api.Program) (table : RowTable)
    (c : AdmittedProgram program table) : admitProgram program table = .ok c := by
  unfold admitProgram
  split
  · rename_i pos h
    rw [c.intFreeTable] at h
    cases h
  · split
    · rename_i pos h
      rw [c.intFreeProgram] at h
      cases h
    · split
      · rename_i h
        unfold checkTypedProgram at h
        split at h
        · rename_i hnone
          rw [c.typed] at hnone
          cases hnone
        · cases h
      · rename_i typing h
        have hty : typing.ty = c.ty := Option.some.inj (typing.typed.symm.trans c.typed)
        split
        · rename_i pos hpos
          rw [hty, c.intFreeType] at hpos
          cases hpos
        · split
          · split
            · rename_i why hrunnable
              rw [c.runnable] at hrunnable
              cases hrunnable
            · exact congrArg Except.ok (admitted_unique program table _ c)
          · rename_i hlawful
            exact absurd c.lawful hlawful

/-- **O-1.** Opening cannot refuse. With a `Built` in hand the checked `start` of
`HostSession` returns exactly the session `Run.open` builds: its five identity refusals are
impossible because the header is built from the `Built` instead of being supplied beside it,
and its admission refusal is impossible because the certificate is what admission produces.
The one thing left to get wrong is an empty name, which is why `start` still has that
refusal and `open` takes the name. -/
theorem open_total (b : Api.Built) (id : String) (budget : Api.Budget) (profile : String)
    (hid : id ≠ "") :
    Api.HostSession.start b.program b.table profile
        ⟨Api.HostSession.version, id, profile, b.table⟩ budget.compileFuel
      = .ok (Run.open b id budget profile).session := by
  unfold Api.HostSession.start
  rw [if_neg (fun h => h rfl), if_neg hid, if_neg (fun h => h rfl), if_neg (fun h => h rfl),
    admitProgram_certificate b.program b.table b.admitted]
  rfl

/-! ## Small facts the answer rows need -/

/-- A key with no slot gets a fresh one at the end of the list, and reading it there finds
no completion. -/
theorem readReply_append_fresh (slots : List ReplySlot) (key : Key)
    (h : slots.any (fun slot => slot.key == key) = false) :
    Api.HostSession.readReply (slots ++ [⟨key, none⟩]) key = none := by
  induction slots with
  | nil => simp only [List.nil_append, Api.HostSession.readReply, if_pos]
  | cons slot rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
    simp only [List.cons_append, Api.HostSession.readReply, if_neg h.1]
    exact ih h.2

/-- A key with no binding is bound by the one appended at the end, and that is the binding
the session finds. -/
theorem find_append_fresh (active : List BoundCall) (bound : BoundCall) (key : Key)
    (hkey : bound.key = key) (h : active.any (fun b => b.key == key) = false) :
    (active ++ [bound]).find? (fun b => b.key == key) = some bound := by
  induction active with
  | nil => simp only [List.nil_append, List.find?_cons, hkey, beq_self_eq_true]
  | cons first rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    simp only [List.cons_append, List.find?_cons, h.1]
    exact ih h.2

/-- A machine holding a call is waiting on at least that one. -/
theorem awaits_ne_nil (m : NativeMachine) (fiber : FiberId) (token : Nat)
    (op : NativeOp) (request : Val) (h : requestOf m fiber token = some (op, request)) :
    (awaits m).isEmpty = false := by
  obtain ⟨f, controller, cancel, hf, hp, hc⟩ := requestOf_current m fiber token op request h
  have hid : f.id = fiber := by
    have hfound := List.find?_some hf
    simpa using hfound
  have hmem : (f.id, token, op, request) ∈ awaits m := by
    refine List.mem_filterMap.mpr ⟨f, List.mem_of_find?_eq_some hf, ?_⟩
    rw [hp, hid]
    aesop (add norm simp [h])
  have hne : awaits m ≠ [] := List.ne_nil_of_mem hmem
  cases hlist : awaits m with
  | nil => exact absurd hlist hne
  | cons a rest => rfl

/-- A machine holding a call is waiting on a host, so the protocol state is `awaitingAsync`
— the state every receipt and every answer is an edge from. -/
theorem observe_awaitingAsync (m : NativeMachine) (fiber : FiberId) (token : Nat)
    (op : NativeOp) (request : Val) (h : requestOf m fiber token = some (op, request)) :
    Api.HostProtocol.observe m = .awaitingAsync :=
  (Api.observe_awaitingAsync_iff Exhaustion.tape m).mpr
    ((Api.exists_awaitHost_iff Exhaustion.tape m).mpr (awaits_ne_nil m fiber token op request h))

/-- A receipt is an edge from `awaitingAsync` to itself. -/
theorem allows_submit (key : Key) :
    Api.HostProtocol.allows .awaitingAsync (.submit key) .awaitingAsync = true := by
  show Api.HostProtocol.hostProtocol.transitions.contains
    ⟨.awaitingAsync, .submit, .awaitingAsync⟩ = true
  decide

/-- An answer is an edge from `awaitingAsync` to every state, so the machine it leaves is
never a protocol refusal. -/
theorem allows_answer (key : Key) (target : Api.HostProtocol.State) :
    Api.HostProtocol.allows .awaitingAsync (.answer key) target = true := by
  have every : ∀ t : Api.HostProtocol.State,
      Api.HostProtocol.hostProtocol.transitions.contains
        ⟨.awaitingAsync, .answer, t⟩ = true := by
    intro t
    cases t <;> decide
  exact every target

/-- A control row is never refused for an envelope: the envelope is what a reply carries and
a control carries none. -/
theorem advance_not_envelope {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (decision : NativeDecision) :
    (Api.HostSession.advance s fuel decision).phase ≠ .refused .envelope := by
  unfold Api.HostSession.advance
  dsimp only
  repeat' split
  all_goals intro h; cases h

/-! ## The claims are the machine's -/

/-- The facade's request projection is the program plane's: one is defined as the other. The
session module reads the facade's name and the envelope reads the program plane's, so a proof
that joins them needs this. -/
theorem api_requestOf (m : Api.Machine) (fiber : FiberId) (token : Nat) :
    Api.requestOf m fiber token = requestOf m fiber token := rfl

attribute [local simp] api_requestOf Api.HostSession.Call.claim Run.machine Run.id

/-- The shape of the call the machine is holding at a key: the run's own name, table and next
call id, and the row and the request `requestOf` reports. Nothing in it is the caller's. -/
theorem at_eq (s : Run) (key : Key) (call : Call)
    (h : Api.HostSession.Call.at s key = some call) :
    ∃ op request, requestOf s.machine key.fiber key.token = some (op, request) ∧
      call = Api.HostSession.Call.claim s key op request := by
  unfold Api.HostSession.Call.at at h
  aesop

/-- And the converse: a machine holding a call has a claim for it. -/
theorem at_of_requestOf (s : Run) (key : Key) (op : NativeOp) (request : Val)
    (h : requestOf s.machine key.fiber key.token = some (op, request)) :
    Api.HostSession.Call.at s key = some (Api.HostSession.Call.claim s key op request) := by
  unfold Api.HostSession.Call.at
  rw [h]
  rfl

/-- A machine holding no call at a key has no claim for it. -/
theorem at_none (s : Run) (key : Key) (h : requestOf s.machine key.fiber key.token = none) :
    Api.HostSession.Call.at s key = none := by
  unfold Api.HostSession.Call.at
  rw [h]
  rfl

/-- **O-5.** A call built from the machine is never stale: `Call.at` restates exactly what
`bindCall` checks it against. -/
theorem bindCall_at (s : Run) (key : Key) (call : Call)
    (h : Api.HostSession.Call.at s key = some call) :
    (Api.HostSession.bindCall s.session call key.token).phase ≠ .refused .staleCall := by
  obtain ⟨op, request, hr, rfl⟩ := at_eq s key call h
  unfold Api.HostSession.bindCall
  aesop (add norm simp [hr])

/-- Binding a call the machine is holding, at a key the session has no binding for, is
accepted: the binding and its empty slot go to the end of the ledger and the next call id
advances. -/
theorem bindCall_at_bound (s : Run) (key : Key) (call : Call)
    (hcall : Api.HostSession.Call.at s key = some call)
    (hfresh : s.session.active.any (fun b => b.key == key) = false) :
    Api.HostSession.bindCall s.session call key.token =
      ⟨.bound, { s.session with
        active := s.session.active ++ [⟨call, key.token⟩]
        pending := s.session.pending ++ [⟨key, none⟩]
        nextCall := s.session.nextCall + 1 }⟩ := by
  have hfresh' : s.session.active.any (fun b => b.key == (⟨key.fiber, key.token⟩ : Key)) = false :=
    hfresh
  obtain ⟨op, request, hr, rfl⟩ := at_eq s key call hcall
  unfold Api.HostSession.bindCall
  aesop (add norm simp [hr, hfresh', Run.id])

/-! ## Rows -/

/-- **O-2.** Receiving is the two rows it says it is: the call bound to its guard, then the
completion received against it. -/
theorem receive_rows (s : Run) (key : Key) (c : Answer) (call : Call)
    (h : Api.HostSession.Call.at s key = some call) :
    Rows.receive s key c = [.bind call key.token, .submit (Rows.reply s call key c)] := by
  unfold Rows.receive
  rw [h]

/-- A key the machine holds no call at has nothing to receive. -/
theorem receive_none (s : Run) (key : Key) (c : Answer)
    (h : Api.HostSession.Call.at s key = none) : Rows.receive s key c = [] := by
  unfold Rows.receive
  rw [h]

/-- **O-3.** Answering is receiving, then applying. -/
theorem answer_rows (s : Run) (key : Key) (c : Answer) (call : Call)
    (h : Api.HostSession.Call.at s key = some call) :
    Rows.answer s key c = Rows.receive s key c ++ [.apply key] := by
  unfold Rows.answer Rows.receive
  rw [h]
  rfl

/-- A key the machine holds no call at has nothing to answer. -/
theorem answer_none (s : Run) (key : Key) (c : Answer)
    (h : Api.HostSession.Call.at s key = none) : Rows.answer s key c = [] := by
  unfold Rows.answer
  rw [h]

/-- The three rows of an answer, written out. -/
theorem answer_rows_three (s : Run) (key : Key) (c : Answer) (call : Call)
    (h : Api.HostSession.Call.at s key = some call) :
    Rows.answer s key c =
      [.bind call key.token, .submit (Rows.reply s call key c), .apply key] := by
  unfold Rows.answer
  rw [h]

/-! ## A receipt and an answer that are accepted -/

/-- A slot is there for a key that was just bound. -/
theorem any_append_key (slots : List ReplySlot) (key : Key) :
    (slots ++ [(⟨key, none⟩ : ReplySlot)]).any (fun slot => slot.key == key) = true := by
  simp only [List.any_append, List.any_cons, List.any_nil, beq_self_eq_true, Bool.true_or,
    Bool.or_true]

/-- Preflight succeeds on a reply that names a binding the machine still holds and carries a
completion the machine admits; the decision it returns is the answer that reply records. -/
theorem preflight_ok {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) (bound : BoundCall)
    (hver : reply.version = Api.HostSession.version)
    (hsess : reply.session = s.header.session)
    (hfind : s.active.find? (fun b => b.key == reply.key) = some bound)
    (hid : reply.callId = bound.call.callId)
    (henv : Envelope table s.machine (bound.record reply)) :
    Api.HostSession.preflight s reply =
      .ok (.answerAsync bound.call.fiber bound.token reply.completion) := by
  have hreq : requestOf s.machine bound.call.fiber bound.token =
      some (bound.call.op, bound.call.request) := henv.2.1
  unfold Api.HostSession.preflight
  rw [if_neg (fun h => h hver), if_neg (fun h => h hsess), hfind]
  simp only [hid, ne_eq, not_true_eq_false, if_false, api_requestOf, hreq, reduceCtorEq]
  rw [acceptReply_of_envelope table s.machine (bound.record reply) henv]
  rfl

/-- A receipt on a bound key with a fresh slot, an admitted completion and a machine waiting
on a host is accepted: it stores the completion and changes nothing else. -/
theorem submit_accepted {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) (bound : BoundCall)
    (hver : reply.version = Api.HostSession.version)
    (hsess : reply.session = s.header.session)
    (hfind : s.active.find? (fun b => b.key == reply.key) = some bound)
    (hid : reply.callId = bound.call.callId)
    (hslot : Api.HostSession.readReply s.pending reply.key = none)
    (hany : s.pending.any (fun slot => slot.key == reply.key) = true)
    (henv : Envelope table s.machine (bound.record reply))
    (hobs : Api.HostProtocol.observe s.machine = .awaitingAsync) :
    Api.HostSession.submit s reply =
      ⟨.preflight, { s with pending := Api.HostSession.storeReply s.pending reply }⟩ := by
  unfold Api.HostSession.submit
  rw [hslot, preflight_ok s reply bound hver hsess hfind hid henv]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, hany, Bool.not_true, hobs,
    allows_submit reply.key, if_false]

/-- Applying a received completion for a bound key, on a machine waiting on a host, is
accepted: it is applied, or the fuel ran out and the run is at a frontier. It is never
refused. -/
theorem applyReply_accepted {program : Api.Program} {table : RowTable} (s : Session program table)
    (key : Key) (fuel : Nat) (bound : BoundCall) (reply : Reply) (decision : NativeDecision)
    (hfind : s.active.find? (fun b => b.key == key) = some bound)
    (hread : Api.HostSession.readReply s.pending key = some reply)
    (hpre : Api.HostSession.preflight s reply = .ok decision)
    (hobs : Api.HostProtocol.observe s.machine = .awaitingAsync) :
    (Api.HostSession.applyReply s key fuel).phase = .applied ∨
      (Api.HostSession.applyReply s key fuel).phase = .frontier := by
  cases fuel with
  | zero => exact Or.inr rfl
  | succ fuel =>
    unfold Api.HostSession.applyReply
    simp only [hfind, hread, hpre, hobs, allows_answer key, Bool.not_true, Bool.false_eq_true,
      if_false]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl

/-! ## The answer law -/

/-- **The answer law.** Three rows, three verdicts. A call the machine is holding, at a key
the session has no record of, answered with a completion the machine admits: the call is
bound, the completion is received, and it is applied — or, when the row's fuel ran out, the
run is left at a frontier with the completion received. No row of it is refused, and in
particular no row of it is refused for an envelope.

The hypotheses are exactly what the session checks: `Call.at` reports a call (so the machine
is holding one at that key), the session has no binding and no slot for that key, and the
completion is one `admit` accepts at that guard — the third part of `Envelope`. -/
theorem answer_accepted (s : Run) (key : Key) (c : Answer) (call : Call)
    (hat : Api.HostSession.Call.at s key = some call)
    (hfresh : s.session.active.any (fun b => b.key == key) = false)
    (hslot : s.session.pending.any (fun slot => slot.key == key) = false)
    (hfits : admit s.built.table s.machine (.answerAsync key.fiber key.token c) = none) :
    (s.answer key c).phases = s.phases ++ [.bound, .preflight, .applied] ∨
      (s.answer key c).phases = s.phases ++ [.bound, .preflight, .frontier] := by
  obtain ⟨op, request, hr, hshape⟩ := at_eq s key call hat
  have hfib : call.fiber = key.fiber := by
    simp only [hshape, Api.HostSession.Call.claim]
  have hop : call.op = op := by
    simp only [hshape, Api.HostSession.Call.claim]
  have hreq : call.request = request := by
    simp only [hshape, Api.HostSession.Call.claim]
  have htab : call.table = s.built.table := by
    simp only [hshape, Api.HostSession.Call.claim]
  have hbkey : (⟨call, key.token⟩ : BoundCall).key = key := by
    show (⟨call.fiber, key.token⟩ : Key) = key
    rw [hfib]
  have hobs : Api.HostProtocol.observe s.session.machine = .awaitingAsync :=
    observe_awaitingAsync s.session.machine key.fiber key.token op request hr
  -- the run after the bind row
  have hb := bindCall_at_bound s key call hat hfresh
  have ha1 : (s.step (.bind call key.token)).session.active =
      s.session.active ++ [(⟨call, key.token⟩ : BoundCall)] := by
    rw [step_session_bind, hb]
  have hp1 : (s.step (.bind call key.token)).session.pending =
      s.session.pending ++ [(⟨key, none⟩ : ReplySlot)] := by
    rw [step_session_bind, hb]
  have hm1 : (s.step (.bind call key.token)).session.machine = s.session.machine := by
    rw [step_session_bind, hb]
  have hh1 : (s.step (.bind call key.token)).session.header = s.session.header := by
    rw [step_session_bind, hb]
  have hph1 : (s.step (.bind call key.token)).phases = s.phases ++ [Phase.bound] := by
    rw [step_phases_bind, hb]
  -- the receipt is accepted
  have hfind : (s.step (.bind call key.token)).session.active.find?
      (fun b => b.key == (Rows.reply s call key c).key) = some ⟨call, key.token⟩ := by
    rw [ha1]
    exact find_append_fresh s.session.active ⟨call, key.token⟩ key hbkey hfresh
  have hslot1 : Api.HostSession.readReply (s.step (.bind call key.token)).session.pending
      (Rows.reply s call key c).key = none := by
    rw [hp1]
    exact readReply_append_fresh s.session.pending key hslot
  have hany1 : (s.step (.bind call key.token)).session.pending.any
      (fun slot => slot.key == (Rows.reply s call key c).key) = true := by
    rw [hp1]
    exact any_append_key s.session.pending key
  have henv : Envelope s.built.table (s.step (.bind call key.token)).session.machine
      ((⟨call, key.token⟩ : BoundCall).record (Rows.reply s call key c)) := by
    rw [hm1]
    refine ⟨htab, ?_, ?_⟩
    · show requestOf s.session.machine call.fiber key.token = some (call.op, call.request)
      rw [hfib, hop, hreq]
      exact hr
    · show admit s.built.table s.session.machine (.answerAsync call.fiber key.token c) = none
      rw [hfib]
      exact hfits
  have hobs1 : Api.HostProtocol.observe (s.step (.bind call key.token)).session.machine =
      .awaitingAsync := by
    rw [hm1]
    exact hobs
  have hsub := submit_accepted (s.step (.bind call key.token)).session (Rows.reply s call key c)
    ⟨call, key.token⟩ rfl (by rw [hh1]; rfl) hfind rfl hslot1 hany1 henv hobs1
  have hpre := preflight_ok (s.step (.bind call key.token)).session (Rows.reply s call key c)
    ⟨call, key.token⟩ rfl (by rw [hh1]; rfl) hfind rfl henv
  -- the run after the receipt row
  have ha2 : ((s.step (.bind call key.token)).step (.submit (Rows.reply s call key c))).session.active
      = (s.step (.bind call key.token)).session.active := by
    rw [step_session_submit, hsub]
  have hp2 : ((s.step (.bind call key.token)).step (.submit (Rows.reply s call key c))).session.pending
      = Api.HostSession.storeReply (s.step (.bind call key.token)).session.pending
        (Rows.reply s call key c) := by
    rw [step_session_submit, hsub]
  have hm2 : ((s.step (.bind call key.token)).step (.submit (Rows.reply s call key c))).session.machine
      = (s.step (.bind call key.token)).session.machine := by
    rw [step_session_submit, hsub]
  have hph2 : ((s.step (.bind call key.token)).step (.submit (Rows.reply s call key c))).phases
      = s.phases ++ [Phase.bound] ++ [Phase.preflight] := by
    rw [step_phases_submit, hsub, hph1]
  -- the answer is applied, or the fuel ran out
  have hfind2 : ((s.step (.bind call key.token)).step
      (.submit (Rows.reply s call key c))).session.active.find? (fun b => b.key == key)
      = some ⟨call, key.token⟩ := by
    rw [ha2]
    exact hfind
  have hread2 : Api.HostSession.readReply ((s.step (.bind call key.token)).step
      (.submit (Rows.reply s call key c))).session.pending key
      = some (Rows.reply s call key c) := by
    rw [hp2]
    exact Api.HostSession.readReply_store_self (s.step (.bind call key.token)).session.pending
      (Rows.reply s call key c) hany1
  have hpre2 : Api.HostSession.preflight ((s.step (.bind call key.token)).step
      (.submit (Rows.reply s call key c))).session (Rows.reply s call key c)
      = .ok (.answerAsync call.fiber key.token c) := by
    rw [step_session_submit, hsub]
    exact hpre
  have hobs2 : Api.HostProtocol.observe ((s.step (.bind call key.token)).step
      (.submit (Rows.reply s call key c))).session.machine = .awaitingAsync := by
    rw [hm2]
    exact hobs1
  have happly := applyReply_accepted ((s.step (.bind call key.token)).step
    (.submit (Rows.reply s call key c))).session key s.budget.fuel ⟨call, key.token⟩
    (Rows.reply s call key c) (.answerAsync call.fiber key.token c) hfind2 hread2 hpre2 hobs2
  have hplay : s.answer key c = ((s.step (.bind call key.token)).step
      (.submit (Rows.reply s call key c))).step (.apply key) := by
    show s.play (Rows.answer s key c) = _
    rw [answer_rows_three s key c call hat]
    rfl
  rw [hplay, step_phases_apply, step_budget, step_budget, hph2]
  rcases happly with h | h
  · left
    rw [h]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · right
    rw [h]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

/-! ## A host inside the envelope -/

/-- Playing rows never changes what was built. -/
theorem play_built (s : Run) (rows : List Command) : (s.play rows).built = s.built := by
  induction rows generalizing s with
  | nil => rfl
  | cons c rest ih => rw [play_cons, ih, step_built]

/-- A machine waiting on a call is holding it. -/
theorem requestOf_of_mem_awaits (m : NativeMachine) (a : Await) (h : a ∈ awaits m) :
    requestOf m a.1 a.2.1 = some (a.2.2.1, a.2.2.2) := by
  obtain ⟨f, hf, hsome⟩ := List.mem_filterMap.mp h
  split at hsome
  · rename_i token hpark
    cases hreq : requestOf m f.id token with
    | none =>
      rw [hreq] at hsome
      cases hsome
    | some pair =>
      rw [hreq] at hsome
      simp only [Option.map_some, Option.some.injEq] at hsome
      rw [← hsome]
      exact hreq
  · cases hsome

/-- The row a host call names is an external row of the run's table. -/
theorem rowOf_external (s : Run) (op : NativeOp) (row : Program.Row) (h : s.rowOf op = some row) :
    ∃ i, op = .external i ∧ externalRow s.built.table i = some row := by
  unfold Run.rowOf at h
  split at h
  · rename_i i
    exact ⟨i, rfl, h⟩
  · cases h

/-- What the drive knows about the call it picked: the machine is waiting on it, and the
session has neither a binding nor a slot for it. -/
theorem freshCall_facts (s : Run) (await : Await) (h : s.freshCall = some await) :
    await ∈ s.outstanding ∧
      (s.session.active.any fun b => b.key == (⟨await.1, await.2.1⟩ : Key)) = false ∧
      (s.session.pending.any fun slot => slot.key == (⟨await.1, await.2.1⟩ : Key)) = false := by
  unfold Run.freshCall at h
  have hp := List.find?_some h
  refine ⟨List.mem_of_find?_eq_some h, ?_, ?_⟩ <;> aesop

/-- A host stays inside the envelope: every completion it gives for a call a machine is
holding, on the row that call was made on, is one the machine admits. It is the third part of
`Envelope` (`Program/Admit.lean`) asked of the host, and the two parts it does not mention —
the table and the parked request — are the ones the run builds rather than the host. -/
def Reactor.Envelops {σ : Type} (r : Reactor σ) (table : RowTable) : Prop :=
  ∀ (m : Api.Machine) (fiber : FiberId) (token i : Nat) (row : Program.Row)
    (request : Val) (st : σ) (c : Answer) (next : σ),
    requestOf m fiber token = some (.external i, request) →
    externalRow table i = some row →
    r row request st = some (c, next) →
    admit table m (.answerAsync fiber token c) = none

/-- **O-7.** A host inside the envelope is never refused for one. Every phase a drive writes
is a phase of an answer the session accepted (bound, received, applied or a fuel frontier) or
of a flush, and a flush carries no envelope at all. -/
theorem drive_envelope {σ : Type} (r : Reactor σ) (table : RowTable) (henv : r.Envelops table)
    (rounds : Nat) (s : Run) (st : σ) (htable : s.built.table = table) :
    ∃ added, (driveFrom r rounds s st).1.phases = s.phases ++ added ∧
      Phase.refused .envelope ∉ added := by
  induction rounds generalizing s st with
  | zero => exact ⟨[], (List.append_nil _).symm, List.not_mem_nil⟩
  | succ rounds ih =>
    rw [driveFrom]
    split
    · rename_i await hfresh
      split
      · exact ⟨[], (List.append_nil _).symm, List.not_mem_nil⟩
      · rename_i row hrow
        split
        · exact ⟨[], (List.append_nil _).symm, List.not_mem_nil⟩
        · rename_i completion next hreact
          obtain ⟨hmem, hactive, hpending⟩ := freshCall_facts s await hfresh
          obtain ⟨i, hop, hext⟩ := rowOf_external s await.2.2.1 row hrow
          have hreq : requestOf s.machine await.1 await.2.1 =
              some (await.2.2.1, await.2.2.2) := requestOf_of_mem_awaits s.machine await hmem
          have hreqi : requestOf s.machine (⟨await.1, await.2.1⟩ : Key).fiber
              (⟨await.1, await.2.1⟩ : Key).token = some (.external i, await.2.2.2) := by
            rw [← hop]
            exact hreq
          have hfits : admit s.built.table s.machine
              (.answerAsync (⟨await.1, await.2.1⟩ : Key).fiber
                (⟨await.1, await.2.1⟩ : Key).token completion) = none := by
            rw [htable]
            exact henv s.machine await.1 await.2.1 i row await.2.2.2 st completion next
              hreqi (by rw [← htable]; exact hext) hreact
          have hanswer := answer_accepted s ⟨await.1, await.2.1⟩ completion
            (Api.HostSession.Call.claim s ⟨await.1, await.2.1⟩ (.external i) await.2.2.2)
            (at_of_requestOf s ⟨await.1, await.2.1⟩ (.external i) await.2.2.2 hreqi)
            hactive hpending hfits
          have hplayed : s.play (Rows.answer s ⟨await.1, await.2.1⟩ completion) =
              s.answer ⟨await.1, await.2.1⟩ completion := rfl
          obtain ⟨rest, hrest, hnorest⟩ :=
            ih (s.play (Rows.answer s ⟨await.1, await.2.1⟩ completion)) next
              (by rw [play_built]; exact htable)
          rcases hanswer with hph | hph <;>
            exact ⟨[Phase.bound, Phase.preflight, _] ++ rest,
              by rw [hrest, hplayed, hph, List.append_assoc], by
                simp only [List.cons_append, List.nil_append, List.mem_cons]
                aesop⟩
    · split
      · exact ⟨[], (List.append_nil _).symm, List.not_mem_nil⟩
      · dsimp only
        split
        · exact ⟨[(Api.HostSession.advance s.session s.budget.fuel Api.flush).phase],
            step_phases_control s Api.flush,
            by simp only [List.mem_singleton]
               exact fun h => advance_not_envelope s.session s.budget.fuel Api.flush h.symm⟩
        · obtain ⟨rest, hrest, hnorest⟩ := ih (s.play Rows.flush) st
            (by rw [play_built]; exact htable)
          refine ⟨(Api.HostSession.advance s.session s.budget.fuel Api.flush).phase :: rest, ?_, ?_⟩
          · rw [hrest]
            show ((s.step (.control Api.flush)).phases) ++ rest = _
            rw [step_phases_control, List.append_assoc]
            rfl
          · simp only [List.mem_cons]
            intro hmem
            rcases hmem with h | h
            · exact advance_not_envelope s.session s.budget.fuel Api.flush h.symm
            · exact hnorest h

/-! ## One completion per call -/

/-- **O-4.** One completion per call. Once an answer has been applied, the machine holds no
call at that key, so there is nothing left to answer there: the rows of a second answer are
empty and playing them changes nothing.

The scout expects a refusal here. What happens instead is that there are no rows, because the
rows are built from the machine — the stronger statement, and the one a driver sees. The
refusal is still there for a row that was recorded earlier: `acceptReply_after_applied`. -/
theorem answer_once (s : Run) (key : Key) (bound : BoundCall) (c : Answer)
    (hfind : s.session.active.find? (fun b => b.key == key) = some bound)
    (hkey : bound.key = key)
    (hphase : (Api.HostSession.applyReply s.session key s.budget.fuel).phase = .applied) :
    Rows.answer (s.step (.apply key)) key c = [] := by
  have hfiber : bound.call.fiber = key.fiber := congrArg Api.HostProtocol.Key.fiber hkey
  have htoken : bound.token = key.token := congrArg Api.HostProtocol.Key.token hkey
  have hguard := Api.HostSession.applied_guard_absent s.session s.budget.fuel bound
    (by rw [hkey]; exact hfind) (by rw [hkey]; exact hphase)
  rw [hkey] at hguard
  refine answer_none _ _ _ (at_none _ _ ?_)
  rw [← hfiber, ← htoken]
  exact hguard

/-- And the recorded row is refused: the machine accepts no second completion for a call
whose answer was applied (`applied_reply_refused`). -/
theorem acceptReply_after_applied (s : Run) (key : Key) (bound : BoundCall) (reply : Reply)
    (hfind : s.session.active.find? (fun b => b.key == key) = some bound)
    (hkey : bound.key = key)
    (hphase : (Api.HostSession.applyReply s.session key s.budget.fuel).phase = .applied) :
    acceptReply s.built.table (s.step (.apply key)).machine (bound.record reply) = none := by
  have h := Api.HostSession.applied_reply_refused s.session s.budget.fuel bound reply
    (by rw [hkey]; exact hfind) (by rw [hkey]; exact hphase)
  rw [hkey] at h
  exact h

/-! ## The ordinary run -/

/-- The machine a replay reached, whichever way it ended. -/
def machineOf : NativeReplay → Api.Machine
  | .finished m => m
  | .frontier _ m => m
  | .stuck _ m => m

/-- A decision tape replayed from a machine, at the program's own evaluator. -/
def replayFrom (program : Api.Program) (table : RowTable) (fuel : Nat)
    (tape : List Api.Decision) (m : Api.Machine) : NativeReplay :=
  letI := evaluatorFor program table
  replayEval (interpOf program table) fuel tape m

/-- Whether one decision had enough command fuel, at the program's own evaluator. -/
def enoughFor (program : Api.Program) (table : RowTable) (fuel : Nat) (m : Api.Machine)
    (d : Api.Decision) : Bool :=
  letI := evaluatorFor program table
  (stepDecisionState (interpOf program table) fuel m d).2

/-- The run a replay result reports, as `Api.replay` reports it. -/
def runOf : NativeReplay → Api.Run
  | .finished machine => ⟨.finished, machine, []⟩
  | .frontier why machine => ⟨.frontier, machine, Api.frontierReasons why machine⟩
  | .stuck why machine => ⟨.stuck why, machine, []⟩

/-- The raw replay entry point, in the two pieces above. -/
theorem replay_eq (program : Api.Program) (fuel : Nat) (tape : List Api.Decision)
    (table : RowTable) (compileFuel : Nat) :
    Api.replay program fuel tape [] table compileFuel =
      runOf (replayFrom program table fuel tape (Api.load program compileFuel)) := rfl

/-- However a replay ended, the run it reports carries the machine it reached. -/
theorem replay_machine (program : Api.Program) (fuel : Nat) (tape : List Api.Decision)
    (table : RowTable) (compileFuel : Nat) :
    (Api.replay program fuel tape [] table compileFuel).machine =
      machineOf (replayFrom program table fuel tape (Api.load program compileFuel)) := by
  rw [replay_eq]
  cases replayFrom program table fuel tape (Api.load program compileFuel) <;> rfl

/-- An empty tape reaches the machine it started from. -/
theorem machineOf_nil (program : Api.Program) (table : RowTable) (fuel : Nat)
    (m : Api.Machine) : machineOf (replayFrom program table fuel [] m) = m := by
  unfold replayFrom
  simp only [replayEval]
  repeat' split
  all_goals rfl

/-- One decision of a tape, when the machine is live and the step had enough fuel. -/
theorem replayFrom_cons (program : Api.Program) (table : RowTable) (fuel : Nat)
    (d : Api.Decision) (tape : List Api.Decision) (m : Api.Machine)
    (hstuck : m.stuck = none) (henough : enoughFor program table fuel m d = true) :
    replayFrom program table fuel (d :: tape) m =
      replayFrom program table fuel tape (steppedBy program fuel table m d) := by
  unfold enoughFor at henough
  unfold replayFrom steppedBy
  simp only [replayEval, hstuck, henough, if_true]

/-- What a control row can do: refuse and change nothing, or step the machine and retire the
bindings the step removed. -/
theorem advance_step {program : Api.Program} {table : RowTable} (s : Session program table)
    (fuel : Nat) (d : NativeDecision) :
    (∃ why, Api.HostSession.advance s fuel d = ⟨.refused why, s⟩) ∨
      (s.machine.stuck = none ∧ Api.HostSession.advance s fuel d =
        ⟨if enoughFor program table fuel s.machine d then .progressed else .frontier,
          Api.HostSession.retire { s with
            machine := steppedBy program fuel table s.machine d }⟩) := by
  unfold Api.HostSession.advance
  split
  · exact Or.inl ⟨_, rfl⟩
  · split
    · exact Or.inl ⟨_, rfl⟩
    · rename_i hlive
      split
      rename_i pair machine enough heq
      split
      · exact Or.inl ⟨_, rfl⟩
      · refine Or.inr ⟨?_, ?_⟩
        · cases hs : s.machine.stuck with
          | none => rfl
          | some why => rw [hs] at hlive; exact absurd rfl hlive
        · unfold enoughFor steppedBy
          rw [heq]

/-- A control row that progressed: the machine before it was not stuck, the step had enough
fuel, and the machine it leaves is the one the raw stepper leaves. Retiring the bindings a
step removed does not touch the machine. -/
theorem advance_progressed {program : Api.Program} {table : RowTable}
    (s : Session program table) (fuel : Nat) (d : NativeDecision)
    (h : (Api.HostSession.advance s fuel d).phase = .progressed) :
    s.machine.stuck = none ∧ enoughFor program table fuel s.machine d = true ∧
      (Api.HostSession.advance s fuel d).session.machine =
        steppedBy program fuel table s.machine d := by
  rcases advance_step s fuel d with ⟨why, hrefuse⟩ | ⟨hstuck, hstep⟩
  · rw [hrefuse] at h
    cases h
  · refine ⟨hstuck, ?_, ?_⟩
    · rw [hstep] at h
      cases he : enoughFor program table fuel s.machine d with
      | true => rfl
      | false =>
        rw [he] at h
        simp only [Bool.false_eq_true, if_false, reduceCtorEq] at h
    · rw [hstep]
      rfl

/-- **O-10.** The ordinary run is the ordinary run: the journal `[evaluate, flush]` leaves
the machine `Api.run` leaves. Both step by `stepDecisionState`, one decision at a time; the
session adds the protocol edge and the retirement of removed bindings, and neither of those
touches the machine.

The hypothesis is that both rows progressed. A run that gets stuck, or whose step runs out of
fuel, stops at a frontier in both routes, but not at the same place: the session keeps the
machine it stepped to and stops, while `Api.replay` keeps stepping the rest of its tape. -/
theorem runPure_eq_run (b : Api.Built) (id : String) (budget : Api.Budget)
    (h : (Run.runPure b id budget).phases = [.progressed, .progressed]) :
    (Run.runPure b id budget).machine =
      (Api.run b.program budget.fuel [] b.table budget.compileFuel).machine := by
  have hphases : ((Run.open b id budget).step (.control Api.evaluate)).phases ++
      [(Api.HostSession.advance
        ((Run.open b id budget).step (.control Api.evaluate)).session budget.fuel
        Api.flush).phase] = [Phase.progressed, Phase.progressed] := h
  rw [step_phases_control, open_phases] at hphases
  simp only [List.nil_append, List.cons_append, List.cons.injEq] at hphases
  obtain ⟨h1, h2⟩ := hphases
  obtain ⟨hstuck1, henough1, hmachine1⟩ :=
    advance_progressed (Run.open b id budget).session budget.fuel Api.evaluate h1
  obtain ⟨hstuck2, henough2, hmachine2⟩ :=
    advance_progressed ((Run.open b id budget).step (.control Api.evaluate)).session budget.fuel
      Api.flush h2.1
  have hstuck1' : (Api.load b.program budget.compileFuel).stuck = none := hstuck1
  have henough1' : enoughFor b.program b.table budget.fuel
      (Api.load b.program budget.compileFuel) Api.evaluate = true := henough1
  have hm1 : ((Run.open b id budget).step (.control Api.evaluate)).session.machine =
      steppedBy b.program budget.fuel b.table (Api.load b.program budget.compileFuel)
        Api.evaluate := hmachine1
  have hstuck2' : (steppedBy b.program budget.fuel b.table
      (Api.load b.program budget.compileFuel) Api.evaluate).stuck = none := by
    rw [← hm1]
    exact hstuck2
  have henough2' : enoughFor b.program b.table budget.fuel (steppedBy b.program budget.fuel
      b.table (Api.load b.program budget.compileFuel) Api.evaluate) Api.flush = true := by
    rw [← hm1]
    exact henough2
  have hlhs : (Run.runPure b id budget).machine = steppedBy b.program budget.fuel b.table
      (steppedBy b.program budget.fuel b.table (Api.load b.program budget.compileFuel)
        Api.evaluate) Api.flush := by
    rw [← hm1]
    exact hmachine2
  rw [hlhs, Api.run, replay_machine,
    replayFrom_cons b.program b.table budget.fuel Api.evaluate [Api.flush]
      (Api.load b.program budget.compileFuel) hstuck1' henough1',
    replayFrom_cons b.program b.table budget.fuel Api.flush []
      (steppedBy b.program budget.fuel b.table (Api.load b.program budget.compileFuel)
        Api.evaluate) hstuck2' henough2',
    machineOf_nil]

end Effect4.Run
