import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.Lift

/-!
# Formal pass, seat PROOFS — red control: the stale code slot on a reachable, host-free run

Base `efd67af1`. Reading aid for `note.md` §3 (gap G1) and §5 (probe A). No tracked file
is changed and no production statement is amended here.

The program is `E4-SCHED-CE-008`'s preempted catch with a timer in place of the deferred
answer (so the tape has no host answer, as `RReachable` requires) and one pure bind (so that
a uniform command budget stops between the walk that finishes the root and its queued
`finish`). After the signed divergence `U-01` the root's *exit* is the recorded interrupt
with no `Fail` reason, which fits the checked type `⟨nat, never, ∅⟩`. Its *code slot* still
holds the escaped `Fail 42`: `popR` returns `(frame, some exit)` without writing `current`
(`Laws/Program/EvaluateR.lean:67,99`), and nothing after it clears `current`
(`RunFiber.publish`, `RunFiber.cleared`, `Machine/Fibers.lean:1747-1764`).

Claims, all at budget 6 or 7 on one tape:
* `reach6`, `reach7`: both machines are `RReachable` (no host answer on the tape).
* `window6`: at budget 6 the cut lands between the finishing walk and its `finish`; the root
  has not exited, its stack is empty, its code slot holds the `Fail`.
* `residue6_*`: the residue the cut drops is exactly `[finish root e, drainDue]` with `e`
  clean, recomputed from the decision's own pieces; its root projection agrees with `m6`.
* `untyped_of_stale`, `window_untyped`, `finished_untyped`: at every world, `TypedState`
  fails at both machines (the saved-state clause of the generated `RunFiberOk`).
* `capstone_false_finished`: the current `M6Ledger.typedState_reachable` proposition is false
  at budget 7, on a finished run with no host answer (a new host-free refutation; rows 95–107
  do not touch it; row 133's exited-fiber exemption does).
* `capstone_false_window`: the same proposition is false at budget 6, where the root has not
  exited and the machine carries no residue — so no exemption keyed on a queued `finish`
  (row 133) can be read off the machine that `RReachable` hands the capstone.
* `ledger_jointly_false_window`, `ledger_jointly_false_finished`: by the tree's replay lift,
  the ledger's `typedState_load` and `decision_preserves` cannot both hold at this program at
  budget 6 or 7.
* Positive control `exitsTyped6`, `exitsTyped7`: the observation-level clause (every recorded
  exit fits its fiber's declared type) holds at both machines at the initial world.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace FormalPass.Proofs.StaleCode
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def sleepy : NativeEff := .perform .sleep (.lit (.nat 1))

/-- `catchAll(uninterruptible(sleep(1) >> succeed 0 >> fail 42), _ => succeed 0)`. -/
def prog : NativeEff :=
  .catchIf yes (.uninterruptible (.bind sleepy (.bind (.succeed (n 0)) (.fail (n 42)))))
    (.succeed (n 0))

def ty : EffTy := ⟨.nat, .never, .empty⟩

def interruptRoot : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root

/-- Run the root to its park, record an interrupt while it is masked, fire the timer. -/
def tape : List Api.Decision :=
  [Api.evaluate, Api.flush, interruptRoot, .advance (ClockMillis.ofNat 1), Api.flush]

def m6 : RState := (replayR prog 6 tape).machine
def m7 : RState := (replayR prog 7 tape).machine

/-- A pure failure that carries a typed `Fail` reason. -/
def staleFail : RProgram → Bool
  | .pure (.failure c) => c.reasons.any (fun r => r.tag == ReasonTag.fail)
  | _ => false

/-- An exit that is a failure with no `Fail` reason; `none` is vacuously fine. -/
def exitFailClean : Option ExitV → Bool
  | none => true
  | some (.failure c) => cleanExit (.failure c)
  | some (.success _) => false

/-! ## Reachability -/

theorem typed_source : Api.typeOf prog = some ty := by rfl'

theorem closed_ty : ClosedEff ty := ⟨rfl, rfl⟩

theorem answerFree : ∀ d ∈ tape, NoHostAnswer d := by
  intro d hd
  simp only [tape, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> trivial

theorem reach6 : RReachable (prog : ProgramSource) 6 m6 := ⟨tape, answerFree, rfl⟩
theorem reach7 : RReachable (prog : ProgramSource) 7 m7 := ⟨tape, answerFree, rfl⟩

/-! ## The two machines -/

/-- Budget 6 stops in the `advance` decision, between the walk that finished the root and
its `finish`: the root has not exited, its stack is empty, its code slot holds the `Fail`. -/
theorem window6 : ∃ f ∈ m6.fibers, f.id = Api.root ∧ f.exit = none ∧
    f.frame.stack.length = 0 ∧ staleFail f.frame.current = true := by decide +kernel

/-- Budget 7 finishes; the root's exit is clean, its code slot still holds the `Fail`. -/
theorem finished7 : ∃ f ∈ m7.fibers, f.id = Api.root ∧ f.exit.isSome = true ∧
    exitFailClean f.exit = true ∧ f.frame.stack.length = 0 ∧
    staleFail f.frame.current = true := by decide +kernel

/-- Every fiber of the budget-7 machine has exited and it is not stuck: the run finished
(`replayEval` classifies a settled machine with every fiber exited as `finished`). -/
theorem finished7m : m7.finished = true ∧ m7.stuck = none := by decide +kernel

/-- Both machines hold only the root. -/
theorem only_root6 : ∀ f ∈ m6.fibers, f.id = Api.root ∧ exitFailClean f.exit = true := by decide +kernel
theorem only_root7 : ∀ f ∈ m7.fibers, f.id = Api.root ∧ exitFailClean f.exit = true := by decide +kernel

/-! ## The residue the cut drops, recomputed from the decision's pieces -/

/-- The settled prefix before the `advance` decision. -/
def before : RState := (replayR prog 6 (tape.take 3)).machine

/-- `advanceState`'s first round at budget 6 (`Machine/Fibers.lean:2066-2080`): the clock
step fires the sleep, `drainOwed` turns it into a resume, the command loop runs at budget 6. -/
def cut : RState × List RCmd :=
  letI := termEvaluatorFor prog
  match (interpR prog).clockStep (ClockMillis.ofNat 1) before.state with
  | (none, st) => ({ before with state := st }, [])
  | (some owed, st) =>
    let r := drainOwed { before with state := st } [owed]
    driveState (interpR prog) 6 r.1 (r.2 ++ [Cmd.drainDue])

def isFinishOf (id : FiberId) : RCmd → Bool
  | .finish target ex => target == id && cleanExit ex
  | _ => false

def isDrainDue : RCmd → Bool
  | .drainDue => true
  | _ => false

/-- The dropped residue is the root's `finish` with a clean exit, then the due drain. -/
theorem residue6_shape : cut.2.length = 2 ∧
    (cut.2.head?.map (isFinishOf Api.root)) = some true ∧
    (cut.2.getLast?.map isDrainDue) = some true := by decide +kernel

def rootShape (m : RState) : Option (Option ExitV × Nat × Bool) :=
  (m.fiber? Api.root).map fun f => (f.exit, f.frame.stack.length, staleFail f.frame.current)

/-- The recomputed cut and the replay's frontier machine agree on the root. -/
theorem residue6_machine : rootShape cut.1 = rootShape m6 := by decide +kernel

/-! ## The typed state fails at both machines -/

theorem any_fail_not_clean (c : CauseV)
    (hany : c.reasons.any (fun r => r.tag == ReasonTag.fail) = true)
    (hclean : cleanExit (.failure c) = true) : False := by
  obtain ⟨r, hr, htag⟩ := List.any_eq_true.mp hany
  have hall := List.all_eq_true.mp hclean r hr
  have hne : r.tag ≠ ReasonTag.fail := bne_iff_ne.mp hall
  exact hne (beq_iff_eq.mp htag)

/-- A stale `Fail` over an empty stack cannot be typed at the root's declared type, whose
error column is `never`: the saved-state clause forces the code slot to type there. -/
theorem untyped_of_stale (m : RState) (w : W)
    (h : ∃ f ∈ m.fibers, f.id = Api.root ∧ f.frame.stack.length = 0 ∧
      staleFail f.frame.current = true) :
    ¬ TypedState (prog : ProgramSource) ty w m := by
  intro typed
  obtain ⟨f, hf, hid, hlen, hstale⟩ := h
  have declared : expectOf w (.fiber f.id) = some ty := by
    change w.Γ f.id = some ty
    rw [hid]
    exact typed.1.root
  obtain ⟨tin, code, stack, _⟩ := ((typed.2.1.c0 f hf).c0).c0 ty declared
  have hnil : f.frame.stack = [] := List.eq_nil_of_length_eq_zero hlen
  rw [hnil] at stack
  cases stack
  cases hcur : f.frame.current with
  | vis op k =>
    rw [hcur] at hstale
    exact Bool.noConfusion hstale
  | pure ex =>
    rw [hcur] at code hstale
    cases ex with
    | success v => exact Bool.noConfusion hstale
    | failure c =>
      have fits := TypedProg.pure_inv code
      exact any_fail_not_clean c hstale (cleanExit_of_never_fits w ty c rfl fits)

theorem window_untyped (w : W) : ¬ TypedState (prog : ProgramSource) ty w m6 := by
  obtain ⟨f, hf, hid, _, hlen, hstale⟩ := window6
  exact untyped_of_stale m6 w ⟨f, hf, hid, hlen, hstale⟩

theorem finished_untyped (w : W) : ¬ TypedState (prog : ProgramSource) ty w m7 := by
  obtain ⟨f, hf, hid, _, _, hlen, hstale⟩ := finished7
  exact untyped_of_stale m7 w ⟨f, hf, hid, hlen, hstale⟩

/-! ## The capstone proposition, at these two machines -/

/-- `M6Ledger.typedState_reachable`'s proposition at budget 7: false on a finished run whose
tape has no host answer. -/
theorem capstone_false_finished : ¬ (Api.typeOf prog [] = some ty → ClosedEff ty →
    RReachable (prog : ProgramSource) 7 m7 → ∃ w, TypedState (prog : ProgramSource) ty w m7) := by
  intro h
  obtain ⟨w, hw⟩ := h typed_source closed_ty reach7
  exact finished_untyped w hw

/-- The same proposition at budget 6, where the root has not exited and the machine the
capstone receives carries no residue. -/
theorem capstone_false_window : ¬ (Api.typeOf prog [] = some ty → ClosedEff ty →
    RReachable (prog : ProgramSource) 6 m6 → ∃ w, TypedState (prog : ProgramSource) ty w m6) := by
  intro h
  obtain ⟨w, hw⟩ := h typed_source closed_ty reach6
  exact window_untyped w hw

/-! ## The ledger's M5 and M6b cannot both hold at this program

`M3bAssembly.typedState_load` and `M6Ledger.decision_preserves` (`Typed/Assembly.lean:154,224`)
give the capstone at every replay by the tree's own lift (`Laws/Machine/Lift.lean`,
`replayEval_lift`); the capstone fails at budgets 6 and 7, so the two declared obligations are
jointly false here. -/

/-- A tape with no host answer is admitted by `AnswerOk` at every machine it meets. -/
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

/-- `decision_preserves`'s proposition at this program and budget. -/
def DecisionPreserves (fuel : Nat) : Prop :=
  ∀ (d : Api.Decision) (w : W) (m : RState), TypedState (prog : ProgramSource) ty w m →
    AnswerOk w m d → ∃ w', w.leHost w' ∧ TypedState (prog : ProgramSource) ty w'
      (letI := termEvaluatorFor prog
       stepDecisionState (interpR prog) fuel m d).1

/-- `typedState_load`'s conclusion at this program and budget. -/
def Loads (fuel : Nat) : Prop := ∃ w, TypedState (prog : ProgramSource) ty w (loadR prog fuel fuel)

theorem ledger_jointly_false_window : ¬ (Loads 6 ∧ DecisionPreserves 6) := by
  rintro ⟨⟨w0, h0⟩, pres⟩
  letI := termEvaluatorFor prog
  obtain ⟨w, _, hw⟩ := Effect4.Machine.Lift.replayEval_lift hostOrder
    (fun w m => TypedState (prog : ProgramSource) ty w m) (fun w m d => AnswerOk w m d)
    (interpR prog) 6 (fun w m d _ ht ha => pres d w m ht ha) tape w0 (loadR prog 6 6) h0
    (admitted_noAnswer _ 6 tape answerFree _)
  exact window_untyped w hw

theorem ledger_jointly_false_finished : ¬ (Loads 7 ∧ DecisionPreserves 7) := by
  rintro ⟨⟨w0, h0⟩, pres⟩
  letI := termEvaluatorFor prog
  obtain ⟨w, _, hw⟩ := Effect4.Machine.Lift.replayEval_lift hostOrder
    (fun w m => TypedState (prog : ProgramSource) ty w m) (fun w m d => AnswerOk w m d)
    (interpR prog) 7 (fun w m d _ ht ha => pres d w m ht ha) tape w0 (loadR prog 7 7) h0
    (admitted_noAnswer _ 7 tape answerFree _)
  exact finished_untyped w hw

/-! ## Positive control: the observation-level clause survives the cut -/

/-- Every recorded exit fits its fiber's declared type: the part of the typed state that the
observation `obs` (every fiber's exit and the stores) reads, and that M7 transfers. -/
def ExitsTyped (w : W) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, ∀ ex, f.exit = some ex → ∀ t, w.Γ f.id = some t → FitsExit w t ex

theorem exitsTyped_of (m : RState) (w : W)
    (h : ∀ f ∈ m.fibers, f.id = Api.root ∧ exitFailClean f.exit = true) : ExitsTyped w m := by
  intro f hf ex hex t _
  have hc := (h f hf).2
  rw [hex] at hc
  cases ex with
  | success v => exact Bool.noConfusion hc
  | failure c => exact fitsExit_of_clean w t c hc

theorem exitsTyped6 : ExitsTyped (initialWorld ty) m6 := exitsTyped_of m6 _ only_root6
theorem exitsTyped7 : ExitsTyped (initialWorld ty) m7 := exitsTyped_of m7 _ only_root7

end FormalPass.Proofs.StaleCode

open FormalPass.Proofs.StaleCode in
#print axioms typed_source
open FormalPass.Proofs.StaleCode in
#print axioms reach6
open FormalPass.Proofs.StaleCode in
#print axioms reach7
open FormalPass.Proofs.StaleCode in
#print axioms window6
open FormalPass.Proofs.StaleCode in
#print axioms finished7
open FormalPass.Proofs.StaleCode in
#print axioms finished7m
open FormalPass.Proofs.StaleCode in
#print axioms only_root6
open FormalPass.Proofs.StaleCode in
#print axioms only_root7
open FormalPass.Proofs.StaleCode in
#print axioms residue6_shape
open FormalPass.Proofs.StaleCode in
#print axioms residue6_machine
open FormalPass.Proofs.StaleCode in
#print axioms untyped_of_stale
open FormalPass.Proofs.StaleCode in
#print axioms window_untyped
open FormalPass.Proofs.StaleCode in
#print axioms finished_untyped
open FormalPass.Proofs.StaleCode in
#print axioms capstone_false_finished
open FormalPass.Proofs.StaleCode in
#print axioms capstone_false_window
open FormalPass.Proofs.StaleCode in
#print axioms admitted_noAnswer
open FormalPass.Proofs.StaleCode in
#print axioms ledger_jointly_false_window
open FormalPass.Proofs.StaleCode in
#print axioms ledger_jointly_false_finished
open FormalPass.Proofs.StaleCode in
#print axioms exitsTyped6
open FormalPass.Proofs.StaleCode in
#print axioms exitsTyped7
