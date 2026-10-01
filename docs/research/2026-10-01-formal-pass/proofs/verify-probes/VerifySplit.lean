import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.Lift

/-!
# Verifier of seat PROOFS — probe A re-examined, and G1's proposed split against the lift

Base `ea5b28b5` (src unchanged since `d20f3292`). The program, tape and machines are copied
from the seat's `probes/StaleCode.lean` (not imported; that file is not a module).

1. `seat_split_not_decisionLift` (red control on G1's amendment): for *any* `J` that holds at
   the cut machine `m6` with the root declared at its type, and *any* `I` whose code clause is
   the seat's ("`SavedOk` for every fiber that is neither exited nor has a queued `finish`"),
   the tree's `DecisionLift` is false: its `evaluate` field derives `I` at the fresh queue
   `[evaluate root, drainDue]` from `J` alone, and at `m6` no `finish` is queued. So "J with no
   code typing, I with row 133's clause, M6b = `stepDecisionState_lift`" cannot be instantiated.
2. `m6_root_running`, `running_clause_vacuous_at_m6` (positive control for the alternative): the
   window fiber is `running`, so a machine-only clause that types the code of every fiber that is
   neither exited nor running holds at `m6` at every world and queue.
3. `budget7_is_fuel_frontier` (red control on the seat's wording): the budget-7 replay is a fuel
   frontier, not a finished run; `finished9` and `capstone_false_finished9`: at budget 9 the
   replay *is* finished and the root's code slot still holds the escaped `Fail`, so the current
   capstone is false on a finished run.
4. `worldValid_not_upward_closed`: `WorldValid` (exact support) is not upward closed along
   `leHost`, so the typed state is not a Kripke (upward-closed) predicate; only its value and
   code judgments are monotone.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace FormalPass.Proofs.Verify.Split
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

abbrev RR := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit
def isFinished : RR → Bool | .finished _ => true | _ => false
def isFuel : RR → Bool | .frontier .fuel _ => true | _ => false

theorem typed_source : Api.typeOf prog = some ty := by rfl'
theorem closed_ty : ClosedEff ty := ⟨rfl, rfl⟩
theorem answerFree : ∀ d ∈ tape, NoHostAnswer d := by
  intro d hd
  simp only [tape, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> trivial

/-! ## Facts about the window machine -/

theorem m6_stuck_none : m6.stuck = none := by decide +kernel

/-- The window fiber is running: the walk finished inside the loop, `finish` is not yet run. -/
theorem m6_root_running : ∃ f ∈ m6.fibers, f.id = Api.root ∧ f.running = true ∧ f.exit = none ∧
    f.frame.stack.length = 0 ∧ staleFail f.frame.current = true := by decide +kernel

theorem m6_only_root : ∀ f ∈ m6.fibers, f.id = Api.root ∧ f.running = true := by decide +kernel

/-! ## 1. The seat's split does not instantiate the decision lift -/

/-- A queued `finish` for this fiber. -/
def finishFor (id : FiberId) : RCmd → Prop
  | .finish target _ => target = id
  | _ => False

/-- The seat's configuration code clause (row 133 as the seat states it). -/
def SeatCode (w : W) (m : RState) (q : List RCmd) : Prop :=
  ∀ f ∈ m.fibers, f.exit = none → (∀ c ∈ q, ¬ finishFor f.id c) →
    ∀ t, w.Γ f.id = some t →
      Contracts.SavedOk (TypedProg (prog : ProgramSource)) FitsExit (frameProtocols prog) w t f.frame

theorem any_fail_not_clean (c : CauseV)
    (hany : c.reasons.any (fun r => r.tag == ReasonTag.fail) = true)
    (hclean : cleanExit (.failure c) = true) : False := by
  obtain ⟨r, hr, htag⟩ := List.any_eq_true.mp hany
  have hall := List.all_eq_true.mp hclean r hr
  have hne : r.tag ≠ ReasonTag.fail := bne_iff_ne.mp hall
  exact hne (beq_iff_eq.mp htag)

/-- A stale `Fail` over an empty stack is not `SavedOk` at the root's type (error `never`). -/
theorem stale_not_savedOk (w : W) (x : RSaved) (hlen : x.stack.length = 0)
    (hstale : staleFail x.current = true) :
    ¬ Contracts.SavedOk (TypedProg (prog : ProgramSource)) FitsExit (frameProtocols prog) w ty x := by
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
        (cleanExit_of_never_fits w ty c rfl (TypedProg.pure_inv code))

/-- **The seat's split cannot instantiate `DecisionLift`.** Any `J` that holds at the cut
machine (as a cut-tolerant capstone predicate must) and declares the root at its type, with any
`I` that implies the seat's code clause, makes `DecisionLift.evaluate` false at `m6`. -/
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

/-! ## 2. The running-relative clause holds at the window -/

/-- Code typing for every fiber that is neither exited nor running (machine-only). -/
def RunningCode (w : W) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, f.exit = none → f.running = false →
    ∀ t, w.Γ f.id = some t →
      Contracts.SavedOk (TypedProg (prog : ProgramSource)) FitsExit (frameProtocols prog) w t f.frame

theorem running_clause_vacuous_at_m6 (w : W) : RunningCode w m6 := by
  intro f hf _ hrun
  rw [(m6_only_root f hf).2] at hrun
  exact Bool.noConfusion hrun

/-! ## 3. Budget 7 is a fuel frontier; budget 9 is a finished run with the stale slot -/

theorem budget7_is_fuel_frontier : isFuel (replayR prog 7 tape) = true := by decide +kernel

/-- Red control on the seat's wording ("the same program finishes at budget 7"). -/
theorem budget7_not_finished : isFinished (replayR prog 7 tape) = false := by decide +kernel

theorem finished9 : isFinished (replayR prog 9 tape) = true := by decide +kernel

theorem m9_root_stale : ∃ f ∈ m9.fibers, f.id = Api.root ∧ f.exit.isSome = true ∧
    f.frame.stack.length = 0 ∧ staleFail f.frame.current = true := by decide +kernel

theorem reach9 : RReachable (prog : ProgramSource) 9 m9 := ⟨tape, answerFree, rfl⟩

theorem untyped9 (w : W) : ¬ TypedState (prog : ProgramSource) ty w m9 := by
  intro typed
  obtain ⟨f, hf, hid, _, hlen, hstale⟩ := m9_root_stale
  have declared : expectOf w (.fiber f.id) = some ty := by
    change w.Γ f.id = some ty
    rw [hid]
    exact typed.1.root
  exact stale_not_savedOk w f.frame hlen hstale (((typed.2.1.c0 f hf).c0).c0 ty declared)

/-- The current capstone is false on a *finished*, host-free run. -/
theorem capstone_false_finished9 : ¬ (Api.typeOf prog [] = some ty → ClosedEff ty →
    RReachable (prog : ProgramSource) 9 m9 → ∃ w, TypedState (prog : ProgramSource) ty w m9) := by
  intro h
  obtain ⟨w, hw⟩ := h typed_source closed_ty reach9
  exact untyped9 w hw

/-! ## 4. The typed state is not upward closed -/

theorem worldValid_not_upward_closed :
    ∃ (w w' : W) (m : RState), w.leHost w' ∧ WorldValid ty w m ∧ ¬ WorldValid ty w' m := by
  let w := initialWorld ty
  let m := loadR prog 3 3
  have fresh : w.Γ ⟨1⟩ = none := rfl
  obtain ⟨le, here, _⟩ := fork_extension w ⟨1⟩ ty fresh
  refine ⟨w, w.addFiber ⟨1⟩ ty, m, ⟨le, fun _ _ h => h⟩, initial_world_valid ty prog 3 3 closed_ty, ?_⟩
  intro valid
  have hmem := (valid.fibers ⟨1⟩).mp (by rw [here]; rfl)
  revert hmem
  decide

end FormalPass.Proofs.Verify.Split

open FormalPass.Proofs.Verify.Split in
#print axioms m6_stuck_none
open FormalPass.Proofs.Verify.Split in
#print axioms m6_root_running
open FormalPass.Proofs.Verify.Split in
#print axioms m6_only_root
open FormalPass.Proofs.Verify.Split in
#print axioms stale_not_savedOk
open FormalPass.Proofs.Verify.Split in
#print axioms seat_split_not_decisionLift
open FormalPass.Proofs.Verify.Split in
#print axioms running_clause_vacuous_at_m6
open FormalPass.Proofs.Verify.Split in
#print axioms budget7_is_fuel_frontier
open FormalPass.Proofs.Verify.Split in
#print axioms budget7_not_finished
open FormalPass.Proofs.Verify.Split in
#print axioms finished9
open FormalPass.Proofs.Verify.Split in
#print axioms m9_root_stale
open FormalPass.Proofs.Verify.Split in
#print axioms untyped9
open FormalPass.Proofs.Verify.Split in
#print axioms capstone_false_finished9
open FormalPass.Proofs.Verify.Split in
#print axioms worldValid_not_upward_closed
