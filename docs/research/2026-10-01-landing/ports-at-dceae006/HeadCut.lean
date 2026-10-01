import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.Lift

/-!
# Synthesis seat, formal pass (2026-10-01): the budget cut at the merged head

Port of the PROOFS seat's `probes/StaleCode.lean` (window part) and the PROOFS verifier's
`verify-probes/VerifySplit.lean` to the tree after the merge of `codex/slice6-fixes`
(`0c534f06`): H1's `CodeInert` (a halted machine, a queued `finish`, or a published exit makes
the current code inert) and H2's `ExitOk`. The program, tape and machines are the seat's.

* `m6_not_inert`, `window_untyped`, `capstone_false_window`, `ledger_jointly_false_window`:
  at the budget-6 cut the root is running, not exited, not halted, and the machine the capstone
  receives carries no queue, so H1's clause still types its stale code slot, and fails.
* `m9_root_inert` (control): on the finished run (budget 9) the root's exit is published, so
  H1's clause makes the stale code inert: the finished-run refutation of the earlier note is
  closed by H1's published-exit disjunct (only this obstruction is shown absent; that the typed
  state holds at `m9` is not claimed).
* `seat_split_not_decisionLift` (red control, ported): a `J` true at the cut with an `I` whose
  code clause is keyed on queued `finish` cannot instantiate the tree's `DecisionLift`.
* `running_exempt_at_m6` (positive control for the recommended amendment): a code clause that
  also treats a running fiber with no queued continuation as inert holds at the window.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Research.Synthesis.HeadCut
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def sleepy : NativeEff := .perform .sleep (.lit (.nat 1))
def prog : NativeEff :=
  .catchIf yes (.uninterruptible (.bind sleepy (.bind (.succeed (n 0)) (.fail (n 42)))))
    (.succeed (n 0))
def ty : EffTy := ⟨.nat, .never, .empty⟩
def interruptRoot : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root
def tape : List Api.Decision :=
  [Api.evaluate, Api.flush, interruptRoot, .advance (ClockMillis.ofNat 1), Api.flush]
def m6 : RState := (replayR prog 6 tape).machine
def m9 : RState := (replayR prog 9 tape).machine

def staleFail : RProgram → Bool
  | .pure (.failure c) => c.reasons.any (fun r => r.tag == ReasonTag.fail)
  | _ => false

theorem typed_source : Api.typeOf prog = some ty := by rfl'
theorem closed_ty : ClosedEff ty := ⟨rfl, rfl⟩
theorem answerFree : ∀ d ∈ tape, NoHostAnswer d := by
  intro d hd
  simp only [tape, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> trivial
theorem reach6 : RReachable (prog : ProgramSource) 6 m6 := ⟨tape, answerFree, rfl⟩

theorem m6_stuck_none : m6.stuck = none := by decide +kernel
theorem m6_root_running : ∃ f ∈ m6.fibers, f.id = Api.root ∧ f.running = true ∧ f.exit = none ∧
    f.frame.stack.length = 0 ∧ staleFail f.frame.current = true := by decide +kernel
theorem m6_only_root : ∀ f ∈ m6.fibers, f.id = Api.root ∧ f.running = true ∧ f.exit = none := by
  decide +kernel

theorem any_fail_not_clean (c : CauseV)
    (hany : c.reasons.any (fun r => r.tag == ReasonTag.fail) = true)
    (hclean : cleanExit (.failure c) = true) : False := by
  obtain ⟨r, hr, htag⟩ := List.any_eq_true.mp hany
  have hall := List.all_eq_true.mp hclean r hr
  have hne : r.tag ≠ ReasonTag.fail := bne_iff_ne.mp hall
  exact hne (beq_iff_eq.mp htag)

/-- At the cut, H1's inertness does not apply to the root: no halt, no queue, no published exit. -/
theorem m6_not_inert : ¬ CodeInert m6 [] (.fiber Api.root) := by
  intro h
  rcases h with hs | hterm
  · rw [m6_stuck_none] at hs
    exact Bool.noConfusion hs
  · rcases hterm with ⟨_, hmem⟩ | ⟨fb, hfb, _, hex⟩
    · cases hmem
    · rw [(m6_only_root fb hfb).2.2] at hex
      exact Bool.noConfusion hex

/-- A stale `Fail` over an empty stack is not a typed saved position at the root's type
(error `never`) when its code is not inert. -/
theorem stale_not_saved (w : W) (m : RState) (q : List RCmd) (p : Expect) (x : RSaved)
    (hni : ¬ CodeInert m q p) (hlen : x.stack.length = 0)
    (hstale : staleFail x.current = true) :
    ¬ SavedPosition (prog : ProgramSource) w m q p ty x := by
  rintro ⟨tin, code0, stack, _⟩
  have code := code0 hni
  have hnil : x.stack = [] := List.eq_nil_of_length_eq_zero hlen
  rw [hnil] at stack
  cases stack
  cases hcur : x.current with
  | vis op k =>
    rw [hcur] at hstale
    exact Bool.noConfusion hstale
  | pure ex =>
    rw [hcur] at code hstale
    cases ex with
    | success v => exact Bool.noConfusion hstale
    | failure c =>
      exact any_fail_not_clean c hstale
        (cleanExit_of_never_fits w ty c rfl (TypedProg.pure_inv code).1)

/-- **The merged typed state fails at the cut machine, at every world** (the default empty
queue is what `decision_preserves` and `typedState_reachable` read). -/
theorem window_untyped (w : W) : ¬ TypedState (prog : ProgramSource) ty w m6 := by
  intro typed
  obtain ⟨f, hf, hid, _, _, hlen, hstale⟩ := m6_root_running
  have declared : expectOf w (.fiber f.id) = some ty := by
    change w.Γ f.id = some ty
    rw [hid]
    exact typed.1.root
  have hni : ¬ CodeInert m6 [] (.fiber f.id) := by rw [hid]; exact m6_not_inert
  exact stale_not_saved w m6 [] _ f.frame hni hlen hstale (((typed.2.1.c0 f hf).c0).c0 ty declared)

/-- `M6Ledger.typedState_reachable`'s proposition at the merged head, refuted at the cut. -/
theorem capstone_false_window : ¬ (Api.typeOf prog [] = some ty → ClosedEff ty →
    RReachable (prog : ProgramSource) 6 m6 → ∃ w, TypedState (prog : ProgramSource) ty w m6) := by
  intro h
  obtain ⟨w, hw⟩ := h typed_source closed_ty reach6
  exact window_untyped w hw

theorem admitted_noAnswer (J : W → RState → Prop) (fuel : Nat) :
    ∀ (tape : List Api.Decision), (∀ d ∈ tape, NoHostAnswer d) → ∀ m : RState,
      letI := termEvaluatorFor prog
      Effect4.Machine.Lift.AdmittedReplay J (fun w m d => AnswerOk w m d) (interpR prog) fuel m tape
  | [], _, _ => trivial
  | d :: tape, h, m => by
    intro _
    refine ⟨fun w _ => ?_, fun _ => admitted_noAnswer J fuel tape
      (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) _⟩
    have hd := h d List.mem_cons_self
    cases d with
    | answerAsync id token answer => exact hd.elim
    | fire owner => trivial
    | flush => trivial
    | evaluate id => trivial
    | yieldVerdict id verdict => trivial
    | interruptFrom who extra target => trivial
    | installMiddleware => trivial
    | advance millis => trivial

/-- `decision_preserves`'s proposition at the merged head, at this program and budget. -/
def DecisionPreserves (fuel : Nat) : Prop :=
  ∀ (d : Api.Decision) (w : W) (m : RState), TypedState (prog : ProgramSource) ty w m →
    AnswerOk w m d → ∃ w', w.leHost w' ∧ TypedState (prog : ProgramSource) ty w'
      (letI := termEvaluatorFor prog
       stepDecisionState (interpR prog) fuel m d).1

/-- `typedState_load`'s conclusion at the merged head, at this program and budget. -/
def Loads (fuel : Nat) : Prop := ∃ w, TypedState (prog : ProgramSource) ty w (loadR prog fuel fuel)

/-- **The merged ledger's M5 and M6b cannot both hold at this program** (budget 6). -/
theorem ledger_jointly_false_window : ¬ (Loads 6 ∧ DecisionPreserves 6) := by
  rintro ⟨⟨w0, h0⟩, pres⟩
  letI := termEvaluatorFor prog
  obtain ⟨w, _, hw⟩ := Effect4.Machine.Lift.replayEval_lift hostOrder
    (fun w m => TypedState (prog : ProgramSource) ty w m) (fun w m d => AnswerOk w m d)
    (interpR prog) 6 (fun w m d _ ht ha => pres d w m ht ha) tape w0 (loadR prog 6 6) h0
    (admitted_noAnswer _ 6 tape answerFree _)
  exact window_untyped w hw

/-! ## Control: the finished run is covered by H1's published-exit disjunct -/

theorem m9_root_published : ∃ f ∈ m9.fibers, f.id = Api.root ∧ f.exit.isSome = true ∧
    staleFail f.frame.current = true := by decide +kernel

theorem m9_root_inert : CodeInert m9 [] (.fiber Api.root) := by
  obtain ⟨f, hf, hid, hex, _⟩ := m9_root_published
  exact Or.inr (Or.inr ⟨f, hf, hid, hex⟩)

/-! ## Red control on a split keyed on queued `finish`, against the tree's decision lift -/

def finishFor (id : FiberId) : RCmd → Prop
  | .finish target _ => target = id
  | _ => False

def SeatCode (w : W) (m : RState) (q : List RCmd) : Prop :=
  ∀ f ∈ m.fibers, f.exit = none → (∀ c ∈ q, ¬ finishFor f.id c) →
    ∀ t, w.Γ f.id = some t →
      Contracts.SavedOk (TypedProg (prog : ProgramSource)) ExitOk (frameProtocols prog) w t f.frame

theorem stale_not_savedOk (w : W) (x : RSaved) (hlen : x.stack.length = 0)
    (hstale : staleFail x.current = true) :
    ¬ Contracts.SavedOk (TypedProg (prog : ProgramSource)) ExitOk (frameProtocols prog) w ty x := by
  rintro ⟨tin, code, stack, _⟩
  have hnil : x.stack = [] := List.eq_nil_of_length_eq_zero hlen
  rw [hnil] at stack
  cases stack
  cases hcur : x.current with
  | vis op k =>
    rw [hcur] at hstale
    exact Bool.noConfusion hstale
  | pure ex =>
    rw [hcur] at code hstale
    cases ex with
    | success v => exact Bool.noConfusion hstale
    | failure c =>
      exact any_fail_not_clean c hstale
        (cleanExit_of_never_fits w ty c rfl (TypedProg.pure_inv code).1)

theorem seat_split_not_decisionLift
    (J : W → RState → Prop) (I : W → RState → List RCmd → Prop)
    (O : W → RState → List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann RProgram) → Prop)
    (A : W → RState → Api.Decision → Prop)
    (hJ : ∃ w, J w m6 ∧ w.Γ Api.root = some ty)
    (hI : ∀ w m q, I w m q → SeatCode w m q) :
    letI := termEvaluatorFor prog
    ¬ Effect4.Machine.Lift.DecisionLift hostOrder (interpR prog) J I O A := by
  intro lift
  letI := termEvaluatorFor prog
  obtain ⟨w, hj, hroot⟩ := hJ
  have hi := lift.evaluate w m6 Api.root hj m6_stuck_none
  obtain ⟨f, hf, hid, _, hexit, hlen, hstale⟩ := m6_root_running
  have nofinish : ∀ c ∈ [Cmd.evaluate Api.root, Cmd.drainDue], ¬ finishFor f.id c := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact id
  have declared : w.Γ f.id = some ty := by rw [hid]; exact hroot
  exact stale_not_savedOk w f.frame hlen hstale (hI w m6 _ hi f hf hexit nofinish ty declared)

/-! ## Positive control for the recommended amendment: running fibers with no queued
continuation are inert -/

/-- The commands that run a fiber's current code: `loop`, `deliver`. (`finish` is already
H1's terminal case.) -/
def continues (id : FiberId) : RCmd → Bool
  | .loop target _ => target == id
  | .deliver target _ => target == id
  | _ => false

def positionId : Expect → Option FiberId
  | .root => some Api.root
  | .fiber id => some id
  | .hook _ => none

/-- H1's inertness, extended: a running fiber whose code no queued command continues. -/
def CodeInertRun (m : RState) (q : List RCmd) (p : Expect) : Prop :=
  CodeInert m q p ∨ ∃ id, positionId p = some id ∧
    (∃ f ∈ m.fibers, f.id = id ∧ f.running = true) ∧ q.all (fun c => !continues id c) = true

theorem running_exempt_at_m6 : CodeInertRun m6 [] (.fiber Api.root) := by
  obtain ⟨f, hf, hid, hrun, _⟩ := m6_root_running
  exact Or.inr ⟨Api.root, rfl, ⟨f, hf, hid, hrun⟩, rfl⟩

end Research.Synthesis.HeadCut

open Research.Synthesis.HeadCut in
#print axioms m6_stuck_none
open Research.Synthesis.HeadCut in
#print axioms m6_root_running
open Research.Synthesis.HeadCut in
#print axioms m6_not_inert
open Research.Synthesis.HeadCut in
#print axioms window_untyped
open Research.Synthesis.HeadCut in
#print axioms capstone_false_window
open Research.Synthesis.HeadCut in
#print axioms ledger_jointly_false_window
open Research.Synthesis.HeadCut in
#print axioms m9_root_inert
open Research.Synthesis.HeadCut in
#print axioms seat_split_not_decisionLift
open Research.Synthesis.HeadCut in
#print axioms running_exempt_at_m6
