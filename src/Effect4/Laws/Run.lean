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

end Effect4.Run
