import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.Lift
import Test.Counterexamples.Machine.Semantics.H1Shapes

/-!
# `E4-TYPED-CE-011`: the saved-code clause at a budget cut, and row 134's split

The formal pass's probe A (`docs/research/2026-10-01-formal-pass/proofs/probes/StaleCode.lean`),
its verifier's `verify-probes/VerifySplit.lean` and probe C (`probes/HaltTyped.lean`), first
restated against the merged typed state of `0c534f06` (H1's `CodeInert`, the scheduler facts,
H2's `ExitOk`; now the copies in `H1Shapes.lean`), then read against decisions row 134's split
(`MachineTyped` `J`, `ConfigTyped` `I`, `Laws/Program/Typed/Assembly.lean`). The synthesis
seat's port at `dceae006` (`docs/research/2026-10-01-landing/ports-at-dceae006/HeadCut.lean`) is
the base of the cut and split sections.

The program is `E4-SCHED-CE-008`'s preempted catch with a one-millisecond timer in place of the
deferred answer (the tape has no host answer, as `RReachable` requires) and one pure bind (so a
uniform command budget can stop between the walk that finishes the root and its queued `finish`).
After the signed divergence `U-01` the root's exit is the recorded interrupt with no `Fail`
reason, which fits `⟨nat, never, ∅⟩`; its code slot still holds the escaped `Fail 42`.

Historical, against H1's typed state (red):
* the window (budget 6): the cut lands between the finishing walk and its `finish`; the root
  is running, not exited, not halted, and the machine the capstone receives carries no queue,
  so H1's clause types its stale code and fails at every world (`window_untyped`); H1's
  `typedState_reachable` is false there (`capstone_false_window`), and its `typedState_load` and
  `decision_preserves` are jointly false at this program (`ledger_jointly_false_window`);
* the finished run (budgets 7 and 9) is covered by H1's published-exit disjunct (`m7_root_inert`,
  `m9_root_inert`), so `E4-TYPED-CE-011` claims the cut only (decisions row 134);
* the proofs seat's split keyed on a queued `finish` cannot instantiate `DecisionLift`
  (`seat_split_not_decisionLift`);
* probe C holds by design under H1 (`CodeInert` tolerates a halt): `H1.typedState_halt`,
  `H1.halting_result_typed`, `H1.typed_not_imply_running` (`E4-TYPED-CE-014`).

Row 134's split (positive): `J` holds at the cut and at the finished run, at an explicit world
(`machineTyped_m6`, `machineTyped_m9`), so the amended capstone is not refuted by probe A; the
loop-entry premise holds there (`evaluate_entry_m6`); the running-keyed clause is the reason
(`running_clause_vacuous_at_m6`, `liveCode_m6`). Row 139 side by side with probe C: the generated
part still tolerates a halt (`typedState_halt`), `J` does not (`machineTyped_not_halted_here`).
`WorldValid` is not upward closed along `leHost` (`worldValid_not_upward_closed`).

Probe-author lessons kept (`proofs/note.md` §5, `verify.md` item 11): replay facts by
`decide +kernel`, never elaborator `decide`; no `classify (replayR …)`; `Api.typeOf` by `rfl'`;
a refutation of a replay fact is proved as a positive equation (`budget7_not_finished`), since a
false claim under `decide +kernel` exhausts memory.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Counterexamples.Machine.Semantics.StaleCode
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
def m9 : RState := (replayR prog 9 tape).machine

/-- A pure failure that carries a typed `Fail` reason. -/
def staleFail : RProgram → Bool
  | .pure (.failure c) => c.reasons.any (fun r => r.tag == ReasonTag.fail)
  | _ => false

/-- An exit that is a failure carrying interruptions only, so no `Fail` reason and no defect;
`none` is vacuously fine. (Before decisions row 152 this read `cleanExit`; a clean exit may die
with a shape defect, which membership at an exit type now refuses.) -/
def exitFailClean : Option ExitV → Bool
  | none => true
  | some (.failure c) => c.reasons.all fun r => r.tag == .interrupt
  | some (.success _) => false

abbrev RR := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit
def isFinished : RR → Bool | .finished _ => true | _ => false
def isFuel : RR → Bool | .frontier .fuel _ => true | _ => false

/-! ## Reachability and the machines -/

theorem typed_source : Api.typeOf prog = some ty := by rfl'

theorem answerFree : ∀ d ∈ tape, NoHostAnswer d := by
  intro d hd
  simp only [tape, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl <;> trivial

theorem reach6 : RReachable (prog : ProgramSource) 6 m6 := ⟨tape, answerFree, rfl⟩
theorem reach7 : RReachable (prog : ProgramSource) 7 m7 := ⟨tape, answerFree, rfl⟩
theorem reach9 : RReachable (prog : ProgramSource) 9 m9 := ⟨tape, answerFree, rfl⟩

/-- Budget 6 stops in the `advance` decision, between the walk that finished the root and
its `finish`: the root has not exited, its stack is empty, its code slot holds the `Fail`. -/
theorem window6 : ∃ f ∈ m6.fibers, f.id = Api.root ∧ f.exit = none ∧
    f.frame.stack.length = 0 ∧ staleFail f.frame.current = true := by decide +kernel

theorem m6_stuck_none : m6.stuck = none := by decide +kernel

/-- The window fiber is running: the walk finished inside the loop, `finish` is not yet run. -/
theorem m6_root_running : ∃ f ∈ m6.fibers, f.id = Api.root ∧ f.running = true ∧ f.exit = none ∧
    f.frame.stack.length = 0 ∧ staleFail f.frame.current = true := by decide +kernel

theorem m6_only_root : ∀ f ∈ m6.fibers, f.id = Api.root ∧ f.running = true ∧ f.exit = none := by
  decide +kernel

/-- Budget 7's machine: every fiber has exited, and it is not stuck. -/
theorem finished7m : m7.finished = true ∧ m7.stuck = none := by decide +kernel

/-- Budget 7 is a fuel frontier, not a finished run (`verify.md` item 3). -/
theorem budget7_is_fuel_frontier : isFuel (replayR prog 7 tape) = true := by decide +kernel

/-- The negation of the earlier wording, as a positive equation. -/
theorem budget7_not_finished : isFinished (replayR prog 7 tape) = false := by decide +kernel

/-- Budget 7's root: exited with a clean exit, its code slot still holding the `Fail`. -/
theorem finished7 : ∃ f ∈ m7.fibers, f.id = Api.root ∧ f.exit.isSome = true ∧
    exitFailClean f.exit = true ∧ f.frame.stack.length = 0 ∧
    staleFail f.frame.current = true := by decide +kernel

/-- Budget 9 finishes the replay. -/
theorem finished9 : isFinished (replayR prog 9 tape) = true := by decide +kernel

theorem m9_root_stale : ∃ f ∈ m9.fibers, f.id = Api.root ∧ f.exit.isSome = true ∧
    f.frame.stack.length = 0 ∧ staleFail f.frame.current = true := by decide +kernel

/-- Both machines hold only the root, whose exit (if any) is a clean failure. -/
theorem only_root6 : ∀ f ∈ m6.fibers, f.id = Api.root ∧ exitFailClean f.exit = true := by
  decide +kernel
theorem only_root7 : ∀ f ∈ m7.fibers, f.id = Api.root ∧ exitFailClean f.exit = true := by
  decide +kernel

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

/-! ## Historical: H1's typed state fails at the cut (`E4-TYPED-CE-011`) -/

theorem any_fail_not_clean (c : CauseV)
    (hany : c.reasons.any (fun r => r.tag == ReasonTag.fail) = true)
    (hclean : cleanExit (.failure c) = true) : False := by
  obtain ⟨r, hr, htag⟩ := List.any_eq_true.mp hany
  have hall := List.all_eq_true.mp hclean r hr
  have hne : r.tag ≠ ReasonTag.fail := bne_iff_ne.mp hall
  exact hne (beq_iff_eq.mp htag)

/-- At the cut, H1's inertness does not apply to the root: no halt, no queue, no published exit. -/
theorem m6_not_inert : ¬ H1Shapes.CodeInert m6 [] (.fiber Api.root) := by
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
    (hni : ¬ H1Shapes.CodeInert m q p) (hlen : x.stack.length = 0)
    (hstale : staleFail x.current = true) :
    ¬ H1Shapes.SavedPosition (prog : ProgramSource) w m q p ty x := by
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

/-- **H1's typed state fails at the cut machine, at every world** (the empty queue is what its
`decision_preserves` and `typedState_reachable` read). -/
theorem window_untyped (w : W) : ¬ H1Shapes.TypedState (prog : ProgramSource) ty w m6 := by
  intro typed
  obtain ⟨f, hf, hid, _, _, hlen, hstale⟩ := m6_root_running
  have declared : expectOf w (.fiber f.id) = some ty := by
    change w.Γ f.id = some ty
    rw [hid]
    exact typed.1.root
  have hni : ¬ H1Shapes.CodeInert m6 [] (.fiber f.id) := by rw [hid]; exact m6_not_inert
  exact stale_not_saved w m6 [] _ f.frame hni hlen hstale (((typed.2.1.c0 f hf).c0).c0 ty declared)

/-- H1's `typedState_reachable` proposition, refuted at the cut. -/
theorem capstone_false_window : ¬ (Api.typeOf prog [] = some ty →
    RReachable (prog : ProgramSource) 6 m6 → ∃ w, H1Shapes.TypedState (prog : ProgramSource) ty w m6) := by
  intro h
  obtain ⟨w, hw⟩ := h typed_source reach6
  exact window_untyped w hw

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

/-- H1's `decision_preserves` proposition, at this program and budget. -/
def DecisionPreserves (fuel : Nat) : Prop :=
  ∀ (d : Api.Decision) (w : W) (m : RState), H1Shapes.TypedState (prog : ProgramSource) ty w m →
    AnswerOk w m d → ∃ w', w.leHost w' ∧ H1Shapes.TypedState (prog : ProgramSource) ty w'
      (letI := termEvaluatorFor prog
       stepDecisionState (interpR prog) fuel m d).1

/-- H1's `typedState_load` conclusion, at this program and budget. -/
def Loads (fuel : Nat) : Prop := ∃ w, H1Shapes.TypedState (prog : ProgramSource) ty w (loadR prog fuel fuel)

/-- **H1's M5 and M6b cannot both hold at this program** (budget 6), through the tree's own
replay lift. -/
theorem ledger_jointly_false_window : ¬ (Loads 6 ∧ DecisionPreserves 6) := by
  rintro ⟨⟨w0, h0⟩, pres⟩
  letI := termEvaluatorFor prog
  obtain ⟨w, _, hw⟩ := Effect4.Machine.Lift.replayEval_lift hostOrder
    (fun w m => H1Shapes.TypedState (prog : ProgramSource) ty w m) (fun w m d => AnswerOk w m d)
    (interpR prog) 6 (fun w m d _ ht ha => pres d w m ht ha) tape w0 (loadR prog 6 6) h0
    (admitted_noAnswer _ 6 tape answerFree _)
  exact window_untyped w hw

/-! ## Historical: the finished run is covered by H1's published-exit disjunct -/

theorem m7_root_published : ∃ f ∈ m7.fibers, f.id = Api.root ∧ f.exit.isSome = true := by
  decide +kernel

theorem m9_root_published : ∃ f ∈ m9.fibers, f.id = Api.root ∧ f.exit.isSome = true := by
  decide +kernel

theorem m7_root_inert : H1Shapes.CodeInert m7 [] (.fiber Api.root) := by
  obtain ⟨f, hf, hid, hex⟩ := m7_root_published
  exact Or.inr (Or.inr ⟨f, hf, hid, hex⟩)

theorem m9_root_inert : H1Shapes.CodeInert m9 [] (.fiber Api.root) := by
  obtain ⟨f, hf, hid, hex⟩ := m9_root_published
  exact Or.inr (Or.inr ⟨f, hf, hid, hex⟩)

/-! ## The proofs seat's split against the tree's decision lift -/

/-- A stale `Fail` over an empty stack is not `SavedOk` at the root's type (error `never`). -/
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

/-- A queued `finish` for this fiber. -/
def finishFor (id : FiberId) : RCmd → Prop
  | .finish target _ => target = id
  | _ => False

/-- The proofs seat's configuration code clause (row 133 as the seat states it). -/
def SeatCode (w : W) (m : RState) (q : List RCmd) : Prop :=
  ∀ f ∈ m.fibers, f.exit = none → (∀ c ∈ q, ¬ finishFor f.id c) →
    ∀ t, w.Γ f.id = some t →
      Contracts.SavedOk (TypedProg (prog : ProgramSource)) ExitOk (frameProtocols prog) w t f.frame

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

/-- Code typing for every fiber that is neither exited nor running (machine-only). -/
def RunningCode (w : W) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, f.exit = none → f.running = false →
    ∀ t, w.Γ f.id = some t →
      Contracts.SavedOk (TypedProg (prog : ProgramSource)) ExitOk (frameProtocols prog) w t f.frame

/-- **The running-keyed clause holds at the window, at every world.** -/
theorem running_clause_vacuous_at_m6 (w : W) : RunningCode w m6 := by
  intro f hf _ hrun
  rw [(m6_only_root f hf).2.1] at hrun
  exact Bool.noConfusion hrun

/-- The commands that run a fiber's current code: `loop`, `deliver`. -/
def continues (id : FiberId) : RCmd → Bool
  | .loop target _ => target == id
  | .deliver target _ => target == id
  | _ => false

def positionId : Expect → Option FiberId
  | .root => some Api.root
  | .fiber id => some id
  | .hook _ => none

/-- H1's inertness, extended: a running fiber whose code no queued command runs. -/
def CodeInertRun (m : RState) (q : List RCmd) (p : Expect) : Prop :=
  H1Shapes.CodeInert m q p ∨ ∃ id, positionId p = some id ∧
    (∃ f ∈ m.fibers, f.id = id ∧ f.running = true) ∧ q.all (fun c => !continues id c) = true

theorem running_exempt_at_m6 : CodeInertRun m6 [] (.fiber Api.root) := by
  obtain ⟨f, hf, hid, hrun, _⟩ := m6_root_running
  exact Or.inr ⟨Api.root, rfl, ⟨f, hf, hid, hrun⟩, rfl⟩

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
  | failure c =>
    have interrupts : ∀ r ∈ c.reasons, r.tag = .interrupt := fun r hr =>
      beq_iff_eq.mp (List.all_eq_true.mp hc r hr)
    exact fitsExit_of_clean w t c (cleanExit_of_interrupts c interrupts)
      (noShapeDefect_of_interrupts t c interrupts)

theorem exitsTyped6 : ExitsTyped (initialWorld ty) m6 := exitsTyped_of m6 _ only_root6
theorem exitsTyped7 : ExitsTyped (initialWorld ty) m7 := exitsTyped_of m7 _ only_root7

/-! ## The typed state is not upward closed -/

theorem worldValid_not_upward_closed :
    ∃ (w w' : W) (m : RState), w.leHost w' ∧ WorldValid ty w m ∧ ¬ WorldValid ty w' m := by
  let w := initialWorld ty
  let m := loadR prog 3 3
  have fresh : w.Γ ⟨1⟩ = none := rfl
  obtain ⟨le, here, _⟩ := fork_extension w ⟨1⟩ ty fresh
  refine ⟨w, w.addFiber ⟨1⟩ ty, m, ⟨le, fun _ _ h => h⟩, initial_world_valid ty prog 3 3, ?_⟩
  intro valid
  have hmem := (valid.fibers ⟨1⟩).mp (by rw [here]; rfl)
  revert hmem
  decide

/-! ## Historical: probe C under H1 (`E4-TYPED-CE-014`)

`RunMachine.halt` sets only `stuck` (`Machine/Fibers.lean:665-667`); H1's typed state reads
`stuck` only through its `CodeInert`, which makes every current code inert on a halted machine.
So halting keeps it at every queue, a halting command meets H1's `StepPreserves` conclusion at
the same world, and H1's typed state never excludes a stuck machine. -/

namespace H1

/-! ### Transport through the generated skeleton

Two instances of the merged bundle `statePreds root m q` differ only in `SavedOk`: every other
field is `preds root`'s. The generated structures take the bundle as a parameter, so their types
differ while their fields agree (the probe author's lesson, `proofs/note.md` §5, probe C). These
lemmas move each generated clause between two instances; `FinNameOk`'s foreign-capture arm is a
structure over the bundle, so finalizer names and scope states are taken by cases. -/

section Transport
variable {root : ProgramSource} {m m' : RState} {q q' : List RCmd} {w : W} {e : Expect}

theorem finNameOk_tr (x : FinName) (h : FinNameOk (H1Shapes.statePreds root m q) w e x) :
    FinNameOk (H1Shapes.statePreds root m' q') w e x := by
  cases x with
  | foreign capture =>
    change CaptureOk (H1Shapes.statePreds root m q) w e capture at h
    exact ⟨h.c0⟩
  | interruptFiber fiber skipSelf => trivial
  | closeChildScope scope => trivial
  | detachFromParent parent key => trivial
  | release label fails => trivial
  | awaitNewChildren snapshot => trivial
  | parkThen slot => trivial
  | closeChildOnFailure scope => trivial
  | memoEntry layer memoMap => trivial
  | memoDone layer memoMap => trivial

theorem scopeStateOk_tr (x : Effect4.ScopeState Nat FinName Val Err Defect FiberId Ann)
    (h : ScopeStateOk (H1Shapes.statePreds root m q) w e x) : ScopeStateOk (H1Shapes.statePreds root m' q') w e x := by
  cases x with
  | empty => trivial
  | openEmpty => trivial
  | openInline key finalizer => exact ⟨h.1, finNameOk_tr finalizer h.2⟩
  | openMap entries => exact ⟨h.1, fun v hv => finNameOk_tr v.2 (h.2 v hv)⟩
  | closed exit => exact h

theorem storesOk_tr (x : Stores) (h : StoresOk (H1Shapes.statePreds root m q) w e x) :
    StoresOk (H1Shapes.statePreds root m' q') w e x :=
  ⟨h.c0, h.c1, ⟨h.c2.c0⟩,
    ⟨fun entry member => ⟨⟨scopeStateOk_tr entry.scope.state ((h.c3.c0 entry member).c0.c0)⟩⟩⟩,
    fun memo member => ⟨fun v hv => ⟨finNameOk_tr v.2.finalizer (((h.c4 memo member).c0 v hv).c0)⟩⟩,
    h.c5⟩

theorem dispatcherOk_tr (x : Dispatcher EffName EffThunk Val Err Defect FiberId Ann RProgram)
    (h : DispatcherOk (H1Shapes.statePreds root m q) w e x) : DispatcherOk (H1Shapes.statePreds root m' q') w e x :=
  ⟨fun bucket hb => ⟨fun task ht => ((h.c0 bucket hb).c0 task ht)⟩⟩

theorem runFiberOk_tr (x : RFiber)
    (hs : ∀ w e x, (H1Shapes.statePreds root m q).SavedOk w e x → (H1Shapes.statePreds root m' q').SavedOk w e x)
    (h : RunFiberOk (H1Shapes.statePreds root m q) w e x) : RunFiberOk (H1Shapes.statePreds root m' q') w e x :=
  ⟨⟨hs _ _ _ h.c0.c0⟩, h.c1, h.c2, h.c3, dispatcherOk_tr x.dispatcher h.c4, h.c5⟩

end Transport

/-- `halt` sets only `stuck`: the fiber and race lookups are unchanged. -/
theorem halt_fiber? (m : RState) (why : Stuck) (id : FiberId) : (m.halt why).fiber? id = m.fiber? id := rfl
theorem halt_race? (m : RState) (why : Stuck) (raceId : Nat) : (m.halt why).race? raceId = m.race? raceId := rfl

/-- H1's countdown clause reads the waiter and its pending record, which `halt` leaves alone. -/
theorem countdownAt_halt {w : W} {m : RState} {why : Stuck} {waiter : FiberId} {token : Nat}
    {incoming : Ty → Ty → Prop} (h : CountdownAt w m waiter token incoming) :
    CountdownAt w (m.halt why) waiter token incoming := by
  unfold CountdownAt at h ⊢
  rw [halt_fiber?]
  cases hf : m.fiber? waiter with
  | none => trivial
  | some fiber =>
    rw [hf] at h
    dsimp only at h ⊢
    cases hp : fiber.pending.find? (fun pending => pending.token = token) with
    | none => trivial
    | some pending =>
      rw [hp] at h
      dsimp only at h
      obtain ⟨answer, error, tokenTy, payload, incomingOk⟩ := h
      exact ⟨answer, error, tokenTy,
        ⟨payload.token, payload.collected, payload.targets, payload.resume⟩, incomingOk⟩

theorem storedObserverOk_halt {root : ProgramSource} {w : W} {m : RState} {why : Stuck}
    {source : FiberId} (o : Observer) (h : StoredObserverOk root w m source o) :
    StoredObserverOk root w (m.halt why) source o := by
  cases o with
  | resumeAwait waiter token mode => exact h
  | countdown waiter token => exact countdownAt_halt h
  | raceCallback raceId =>
    unfold StoredObserverOk at h ⊢
    dsimp only at h ⊢
    rw [halt_race?]
    exact h
  | untrackChild parent => trivial
  | dropScopeFinalizer scope key => exact h
  | callback key => trivial

/-- Halting changes no clause the merged typed state checks: H1's `CodeInert` makes every current
code inert on a halted machine, and the rest reads fields `halt` leaves alone. -/
theorem typedState_halt (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (q : List RCmd) (why : Stuck) (h : H1Shapes.TypedState root rootTy w m q) :
    H1Shapes.TypedState root rootTy w (m.halt why) q := by
  obtain ⟨valid, ok, deliv, sched, obsv, reg⟩ := h
  have saved : ∀ w e x, (H1Shapes.statePreds root m q).SavedOk w e x →
      (H1Shapes.statePreds root (m.halt why) q).SavedOk w e x := by
    intro w e x hx t ht
    obtain ⟨tin, _, stack, prov⟩ := hx t ht
    exact ⟨tin, fun live => False.elim (live (Or.inl rfl)), stack, prov⟩
  refine ⟨{ ids := valid.ids, fibers := valid.fibers, heap := valid.heap,
            promises := valid.promises, tokens := valid.tokens, tokenBound := valid.tokenBound,
            tokenTargets := valid.tokenTargets, state := valid.state, wf := valid.wf,
            cells := valid.cells, root := valid.root, timers := valid.timers, waiters := valid.waiters,
            children := valid.children },
    ⟨fun f hf => runFiberOk_tr f saved (ok.c0 f hf), ok.c1, storesOk_tr m.state ok.c2⟩,
    activeDelivery_races (m := m) rfl (racesKept_of_eq fun _ => rfl) deliv, ?_, ?_,
    registrationState_races (m := m) rfl (racesKept_of_eq fun _ => rfl) reg⟩
  · exact { fiberIds := sched.fiberIds, fibersBelow := sched.fibersBelow, raceIds := sched.raceIds,
            racesBelow := sched.racesBelow, raceHosts := sched.raceHosts, keysBelow := sched.keysBelow,
            requestsBelow := sched.requestsBelow, requestsOwned := sched.requestsOwned,
            pendingShape := sched.pendingShape, parkedIdle := sched.parkedIdle,
            parkedBelow := sched.parkedBelow, exited := sched.exited, exitedStack := sched.exitedStack,
            deferredCause := sched.deferredCause, raceObservers := sched.raceObservers,
            liveBelow := sched.liveBelow, targetsBelow := sched.targetsBelow,
            observersBelow := sched.observersBelow }
  · exact ⟨obsv.pendingOwner, fun f hf o ho => storedObserverOk_halt o (obsv.observers f hf o ho)⟩

/-- The empty residue is typed. -/
theorem queueOk_nil (root : ProgramSource) (w : W) (m : RState) : QueueOk root w m [] :=
  { payload := fun _ h => (nomatch h), authority := fun _ h => (nomatch h),
    delivery := fun _ h => (nomatch h), owners := List.nodup_nil, registration := trivial,
    keys := ⟨fun _ h => (nomatch h), fun _ _ _ _ h => (nomatch h)⟩,
    observer := fun _ _ _ h => (nomatch h), enroll := fun _ _ h => (nomatch h),
    noRaceAfterInterrupt := fun _ _ _ h => (nomatch h), links := fun _ _ _ _ _ h => (nomatch h),
    raceObservers := fun _ _ _ h => (nomatch h) }

/-- A command whose result is `(m.halt why, [])` (for example `linkScope` on an unknown scope,
`Machine/Fibers.lean:1010`) meets the conclusion `StepPreserves` asks for, at the same world. -/
theorem halting_result_typed (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (why : Stuck) (h : H1Shapes.TypedState root rootTy w m) :
    ∃ w', w.leHost w' ∧ H1Shapes.TypedState root rootTy w' (m.halt why) [] ∧
      QueueOk root w' (m.halt why) [] :=
  ⟨w, leHost_refl w, typedState_halt root rootTy w m [] why h, queueOk_nil root w (m.halt why)⟩

/-- Hence the typed state does not imply that the machine is not stuck. -/
theorem typed_not_imply_running (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (why : Stuck) (h : H1Shapes.TypedState root rootTy w m) :
    ∃ m', H1Shapes.TypedState root rootTy w m' ∧ m'.stuck = some why :=
  ⟨m.halt why, typedState_halt root rootTy w m [] why h, rfl⟩

end H1

/-! ## Row 134's split at probe A's machines (positive)

`J` is `MachineTyped`. At the cut the root is running, so `J`'s code clause does not read its
stale slot; at the finished run the root has exited. Both machines hold one quiet root over
empty stores, so one builder, over facts checked by `decide +kernel`, gives `J` at an explicit
world. -/

/-- `J`'s code clause at the cut, at every world: the window fiber is running. -/
theorem liveCode_m6 (w : W) : LiveCode (prog : ProgramSource) w m6 := by
  intro f hf _ idle
  rw [(m6_only_root f hf).2.1] at idle
  cases idle

/-- The world a quiet root machine is typed at: the root at `ty`, the machine's store. -/
def rootWorld (m : RState) : W := { initialWorld ty with state := m.state }

/-- One quiet fiber: the root, not parked, nothing pending, an empty stack, no observers or
tasks, the empty context, recorded causes interrupts, no race marker, running or exited, and an
exit (if any) that is an interrupt-only failure. -/
abbrev QuietFiber (f : RFiber) : Prop :=
  f.id = Api.root ∧ f.parked = .notParked ∧ f.pending.isEmpty = true ∧
    f.finalizing.isNone = true ∧ f.frame.stack.isEmpty = true ∧ f.observers.isEmpty = true ∧
    f.dispatcher.buckets.isEmpty = true ∧ f.context = emptyCtx ∧
    f.frame.deferredInterrupt = false ∧ raceRegistrationR f.frame.current = none ∧
    (f.frame.interruptedCause.all fun c => c.reasons.all (·.tag == .interrupt)) = true ∧
    (f.running || f.exit.isSome) = true ∧ (!f.exit.isSome || !f.running) = true ∧
    (f.exit.all fun ex => match ex with
      | .success _ => false
      | .failure c => c.reasons.all (·.tag == .interrupt)) = true ∧ f.children.isEmpty = true

/-- A machine of one quiet root over empty stores. Every field is decidable. -/
structure QuietRoot (m : RState) : Prop where
  ids : m.fibers.map (·.id) = [Api.root]
  races : m.races.isEmpty = true
  stuck : m.stuck = none
  refs : m.state.refs.isEmpty = true
  cells : m.state.deferreds.cells.isEmpty = true
  due : m.state.deferreds.due.isEmpty = true
  scopes : m.state.scopes.entries.isEmpty = true
  memo : m.state.memo.isEmpty = true
  wf : m.state.WF
  keys : (Guard.internalKeys m).isEmpty = true
  nextId : 1 ≤ m.nextId
  fibers : ∀ f ∈ m.fibers, QuietFiber f

theorem interrupts_of_all {c : CauseV} (h : c.reasons.all (·.tag == .interrupt) = true) :
    ∀ r ∈ c.reasons, r.tag = .interrupt :=
  fun r hr => beq_iff_eq.mp (List.all_eq_true.mp h r hr)

/-- `QuietFiber` with its facts named. -/
structure QuietFacts (f : RFiber) : Prop where
  id : f.id = Api.root
  parked : f.parked = .notParked
  pending : f.pending = []
  finalizing : f.finalizing = none
  stack : f.frame.stack = []
  observers : f.observers = []
  buckets : f.dispatcher.buckets = []
  context : f.context = emptyCtx
  deferred : f.frame.deferredInterrupt = false
  marker : raceRegistrationR f.frame.current = none
  recorded : ∀ c, f.frame.interruptedCause = some c → ∀ r ∈ c.reasons, r.tag = .interrupt
  live : f.running = true ∨ f.exit.isSome = true
  idle : f.exit.isSome = true → f.running = false
  exitClean : ∀ ex, f.exit = some ex → ∃ c, ex = .failure c ∧ ∀ r ∈ c.reasons, r.tag = .interrupt
  children : f.children = []

theorem quietFacts {f : RFiber} (h : QuietFiber f) : QuietFacts f := by
  obtain ⟨fid, parked, pending, finalizing, stack, observers, buckets, context, deferred, marker,
    recorded, live, idle, exitClean, children⟩ := h
  refine ⟨fid, parked, List.isEmpty_iff.mp pending, Option.isNone_iff_eq_none.mp finalizing,
    List.isEmpty_iff.mp stack, List.isEmpty_iff.mp observers, List.isEmpty_iff.mp buckets, context,
    deferred, marker, ?_, Bool.or_eq_true_iff.mp live, ?_, ?_, List.isEmpty_iff.mp children⟩
  · intro c hc
    rw [hc] at recorded
    exact interrupts_of_all recorded
  · intro hexit
    rw [hexit] at idle
    cases hrun : f.running
    · rfl
    · rw [hrun] at idle
      cases idle
  · intro ex hex
    rw [hex] at exitClean
    cases ex with
    | success v => cases exitClean
    | failure c => exact ⟨c, rfl, interrupts_of_all exitClean⟩

/-- A quiet root machine is in `J` at its root world. -/
theorem machineTyped_of_quiet (m : RState) (q : QuietRoot m) :
    MachineTyped (prog : ProgramSource) ty (rootWorld m) m := by
  have old := initial_world_valid ty prog 6 6
  have facts : ∀ f ∈ m.fibers, QuietFacts f := fun f hf => quietFacts (q.fibers f hf)
  have races : m.races = [] := List.isEmpty_iff.mp q.races
  have refs : m.state.refs = [] := List.isEmpty_iff.mp q.refs
  have cells : m.state.deferreds.cells = [] := List.isEmpty_iff.mp q.cells
  have due : m.state.deferreds.due = [] := List.isEmpty_iff.mp q.due
  have entries : m.state.scopes.entries = [] := List.isEmpty_iff.mp q.scopes
  have memo : m.state.memo = [] := List.isEmpty_iff.mp q.memo
  have keys : Guard.internalKeys m = [] := List.isEmpty_iff.mp q.keys
  have noRequests : ∀ fiber token, requestOfR m fiber token = none := by
    intro fiber token
    unfold requestOfR
    cases found : m.fiber? fiber with
    | none => rfl
    | some f =>
      have parked := (facts f (List.mem_of_find?_eq_some found)).parked
      show (guard (f.parked = .withGuard token) >>= fun _ => externalRequestR f.frame.current) = none
      rw [parked]
      rfl
  have valid : WorldValid ty (rootWorld m) m :=
    { ids := q.ids.symm
      fibers := fun id => by rw [q.ids]; exact old.fibers id
      heap := fun key => by
        change ((initialWorld ty).Ρ key).isSome = true ↔ key.index < m.state.refs.length
        rw [refs]
        exact old.heap key
      promises := fun key => by
        change ((initialWorld ty).«Π» key).isSome = true ↔ key.index < m.state.deferreds.cells.length
        rw [cells]
        exact old.promises key
      tokens := fun f hf token parked => by
        rw [(facts f hf).parked] at parked
        cases parked
      tokenBound := fun _ _ _ h => nomatch h
      tokenTargets := fun _ _ _ h => nomatch h
      state := rfl
      wf := q.wf
      cells := ⟨fun i v hv => (by
          change m.state.refs[i]? = some v at hv
          rw [refs] at hv
          cases hv),
        fun i v hv => (by
          change m.state.deferreds.cells[i]? = some v at hv
          rw [cells] at hv
          cases hv)⟩
      root := old.root
      timers := fun k hk => by
        have h : k ∈ Guard.internalKeys m := List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ hk)))
        rw [keys] at h
        cases h
      waiters := fun key cell hc => by
        unfold DeferredStore.cellAt at hc
        rw [cells] at hc
        cases hc
      children := fun f hf c hc => by
        rw [(facts f hf).children] at hc
        cases hc }
  refine ⟨⟨valid, ⟨fun f hf => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, rfl, ?_,
    ⟨q.stuck, fun o ho => ?_⟩, ⟨rfl, .of_nil rfl⟩⟩
  · have fact := facts f hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro t _
      refine ⟨t, ?_, ⟨fact.recorded, fun deferred => ?_⟩⟩
      · rw [fact.stack]
        exact .nil _
      · rw [fact.deferred] at deferred
        cases deferred
    · intro p hp
      rw [fact.pending] at hp
      cases hp
    · intro v hv
      rw [fact.finalizing] at hv
      cases hv
    · intro ex hex t _
      obtain ⟨c, rfl, interrupts⟩ := fact.exitClean ex hex
      exact ⟨fitsExit_of_clean _ t c (cleanExit_of_interrupts c interrupts)
        (noShapeDefect_of_interrupts t c interrupts), noShapeDefect_of_interrupts t c interrupts⟩
    · intro b hb
      rw [fact.buckets] at hb
      cases hb
    · rw [fact.context]
      exact servicesFit_empty _
  · intro r hr
    rw [races] at hr
    cases hr
  · refine ⟨⟨fun o ho => ?_, fun p hp => ?_⟩, fun i v hv => ?_, ⟨fun i v hv => ?_⟩,
      ⟨fun e he => ?_⟩, fun v hv => ?_, trivial⟩
    · rw [due] at ho; cases ho
    · rw [memo] at hp; cases hp
    · change m.state.refs[i]? = some v at hv
      rw [refs] at hv; cases hv
    · change m.state.deferreds.cells[i]? = some v at hv
      rw [cells] at hv; cases hv
    · rw [entries] at he; cases he
    · rw [memo] at hv; cases hv
  · intro f hf token parked
    rw [(facts f hf).parked] at parked
    cases parked
  · exact
      { fiberIds := by rw [q.ids]; exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
        fibersBelow := fun f hf => by
          rw [(facts f hf).id]
          exact q.nextId
        raceIds := by rw [races]; exact List.nodup_nil
        racesBelow := fun r hr => by rw [races] at hr; cases hr
        raceHosts := fun r hr => by rw [races] at hr; cases hr
        keysBelow := fun key hk => by rw [keys] at hk; cases hk
        requestsBelow := fun fiber token request hr => by rw [noRequests] at hr; cases hr
        requestsOwned := fun fiber token request hr => by rw [noRequests] at hr; cases hr
        pendingShape := fun f hf => by
          unfold Guard.PendingShape
          rw [(facts f hf).parked]
          exact (facts f hf).pending
        parkedIdle := fun f hf parked => absurd (facts f hf).parked parked
        parkedBelow := fun f hf token parked => by
          rw [(facts f hf).parked] at parked
          cases parked
        exited := fun f hf hexit => ⟨(facts f hf).parked, (facts f hf).idle hexit⟩
        exitedStack := fun f hf _ => (facts f hf).stack
        deferredCause := fun f hf deferred => by
          rw [(facts f hf).deferred] at deferred
          cases deferred
        raceObservers := fun r race hr => by
          unfold RunMachine.race? at hr
          rw [races] at hr
          cases hr
        liveBelow := fun r race hr => by
          unfold RunMachine.race? at hr
          rw [races] at hr
          cases hr
        targetsBelow := fun f hf p hp => by
          rw [(facts f hf).pending] at hp
          cases hp
        observersBelow := fun f hf o ho => by
          rw [(facts f hf).observers] at ho
          cases ho }
  · refine ⟨fun f hf p hp => ?_, fun f hf o ho => ?_⟩
    · rw [(facts f hf).pending] at hp
      cases hp
    · rw [(facts f hf).observers] at ho
      cases ho
  · intro f hf raceId marker
    rw [(facts f hf).marker] at marker
    cases marker
  · intro f hf hexit idle
    rcases (facts f hf).live with running | exited
    · rw [idle] at running
      cases running
    · rw [hexit] at exited
      cases exited
  · rw [due] at ho
    cases ho

theorem quiet6 : QuietRoot m6 :=
  { ids := by decide +kernel, races := by decide +kernel, stuck := m6_stuck_none,
    refs := by decide +kernel, cells := by decide +kernel, due := by decide +kernel,
    scopes := by decide +kernel, memo := by decide +kernel, wf := by decide +kernel,
    keys := by decide +kernel, nextId := by decide +kernel, fibers := by decide +kernel }

theorem quiet9 : QuietRoot m9 :=
  { ids := by decide +kernel, races := by decide +kernel, stuck := by decide +kernel,
    refs := by decide +kernel, cells := by decide +kernel, due := by decide +kernel,
    scopes := by decide +kernel, memo := by decide +kernel, wf := by decide +kernel,
    keys := by decide +kernel, nextId := by decide +kernel, fibers := by decide +kernel }

/-- **`J` holds at the cut** where H1's typed state failed (`window_untyped`). -/
theorem machineTyped_m6 : MachineTyped (prog : ProgramSource) ty (rootWorld m6) m6 :=
  machineTyped_of_quiet m6 quiet6

/-- **`J` holds on the finished run**, the root's stale slot outside the code clause. -/
theorem machineTyped_m9 : MachineTyped (prog : ProgramSource) ty (rootWorld m9) m9 :=
  machineTyped_of_quiet m9 quiet9

/-- The amended capstone's conclusion at the cut: probe A does not refute it. -/
theorem capstone_window_holds :
    LawfulSource (prog : ProgramSource) → Api.typeOf prog [] = some ty →
      RReachable (prog : ProgramSource) 6 m6 → ∃ w, MachineTyped (prog : ProgramSource) ty w m6 :=
  fun _ _ _ => ⟨rootWorld m6, machineTyped_m6⟩

/-- The decision lift's loop entry at the cut: `J` gives `I` at the evaluate queue. -/
theorem evaluate_entry_m6 :
    ConfigTyped (prog : ProgramSource) ty (rootWorld m6) m6 [Cmd.evaluate Api.root, Cmd.drainDue] :=
  evaluate_entry _ _ _ _ _ machineTyped_m6

/-! ## M7 at probe A's program (positive)

The frame machine's replay of the same tape (`Api.replay`) is in the book with the reference
replay (`replay_rel`), so `J` at the reference machine types the frame machine's observation:
M7a's and M7c's conclusions at the cut and on the finished run. -/

-- Term mode, through lemmas stated for a variable program: unifying projections of a concrete
-- replay made the elaborator evaluate it (killed at 5.7 GB; the probe authors' trap).
theorem m7_exits_at_cut : ExitsFit ty (rootWorld m6) (obs (Api.replay prog 6 tape).machine) :=
  Eq.mpr (congrArg (ExitsFit ty (rootWorld m6)) (run_eq_ref prog 6 tape).2)
    (obsTyped_of_machineTyped machineTyped_m6).1

theorem m7_exits_finished : ExitsFit ty (rootWorld m9) (obs (Api.replay prog 9 tape).machine) :=
  Eq.mpr (congrArg (ExitsFit ty (rootWorld m9)) (run_eq_ref prog 9 tape).2)
    (obsTyped_of_machineTyped machineTyped_m9).1

theorem m7_no_halt_at_cut : (Api.replay prog 6 tape).machine.stuck = none :=
  (replay_stuck_eq prog 6 tape).trans machineTyped_m6.live.running

/-- R4's bridge at the cut: the reference machine is in the book with a native reachable one. -/
theorem cut_native_reachable :
    ∃ m₁, Guard.Reachable prog [] 6 [] m₁ ∧ BMeans prog m₁ m6 :=
  replayR_bmeans_reachable prog 6 tape

/-! ## Row 139 beside probe C

The generated part with its correlations still tolerates a halt: `TypedState` reads no `stuck`,
and with the bundle independent of the machine its clauses carry over by the fields `halt`
leaves alone. `J` carries `stuck = none` and excludes every halted machine. -/

theorem typedState_halt (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (why : Stuck) (h : TypedState root rootTy w m) : TypedState root rootTy w (m.halt why) := by
  obtain ⟨valid, ok, deliv, sched, obsv, reg⟩ := h
  exact ⟨{ ids := valid.ids, fibers := valid.fibers, heap := valid.heap,
           promises := valid.promises, tokens := valid.tokens, tokenBound := valid.tokenBound,
           tokenTargets := valid.tokenTargets, state := valid.state, wf := valid.wf,
           cells := valid.cells, root := valid.root, timers := valid.timers, waiters := valid.waiters,
            children := valid.children },
    ⟨ok.c0, ok.c1, ok.c2⟩, activeDelivery_races (m := m) rfl (racesKept_of_eq fun _ => rfl) deliv,
    { fiberIds := sched.fiberIds, fibersBelow := sched.fibersBelow, raceIds := sched.raceIds,
      racesBelow := sched.racesBelow, raceHosts := sched.raceHosts, keysBelow := sched.keysBelow,
      requestsBelow := sched.requestsBelow, requestsOwned := sched.requestsOwned,
      pendingShape := sched.pendingShape, parkedIdle := sched.parkedIdle,
      parkedBelow := sched.parkedBelow, exited := sched.exited, exitedStack := sched.exitedStack,
      deferredCause := sched.deferredCause, raceObservers := sched.raceObservers,
      liveBelow := sched.liveBelow, targetsBelow := sched.targetsBelow,
      observersBelow := sched.observersBelow },
    ⟨obsv.pendingOwner, fun f hf o ho => H1.storedObserverOk_halt o (obsv.observers f hf o ho)⟩,
    registrationState_races (m := m) rfl (racesKept_of_eq fun _ => rfl) reg⟩

/-- Probe C's `typedState_halt` read at `J`: false at every halted machine. -/
theorem machineTyped_not_halted_here (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (why : Stuck) : ¬ MachineTyped root rootTy w (m.halt why) :=
  machineTyped_not_halted root rootTy w m why

/-- Probe C's `halting_result_typed` read at `I`: a command whose result halts never meets
`StepPreserves`'s conclusion. -/
theorem halting_result_outside (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (why : Stuck) (rest : List RCmd) : ¬ ConfigTyped root rootTy w (m.halt why) rest :=
  fun typed => machineTyped_not_halted root rootTy w m why typed.machine

end Test.Counterexamples.Machine.Semantics.StaleCode

open Test.Counterexamples.Machine.Semantics.StaleCode
