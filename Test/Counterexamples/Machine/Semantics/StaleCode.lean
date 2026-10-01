import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Machine.Lift

/-!
# `E4-TYPED-CE-011`: the saved-code clause at a budget cut (row 134's red control)

The formal pass's probe A (`docs/research/2026-10-01-formal-pass/proofs/probes/StaleCode.lean`),
its verifier's `verify-probes/VerifySplit.lean` and probe C (`probes/HaltTyped.lean`), restated
against the merged typed state (`0c534f06`: H1's `CodeInert`, the scheduler facts, H2's
`ExitOk`). The synthesis seat's port at `dceae006`
(`docs/research/2026-10-01-landing/ports-at-dceae006/HeadCut.lean`) is the base of the cut and
split sections.

The program is `E4-SCHED-CE-008`'s preempted catch with a one-millisecond timer in place of the
deferred answer (the tape has no host answer, as `RReachable` requires) and one pure bind (so a
uniform command budget can stop between the walk that finishes the root and its queued `finish`).
After the signed divergence `U-01` the root's exit is the recorded interrupt with no `Fail`
reason, which fits `⟨nat, never, ∅⟩`; its code slot still holds the escaped `Fail 42`.

What this file proves, at the merged head:
* the window (budget 6): the cut lands between the finishing walk and its `finish`; the root
  is running, not exited, not halted, and the machine the capstone receives carries no queue,
  so H1's clause types its stale code and fails at every world (`window_untyped`); the ledger's
  `typedState_reachable` is false there (`capstone_false_window`), and `typedState_load` and
  `decision_preserves` are jointly false at this program (`ledger_jointly_false_window`);
* the finished run (budgets 7 and 9): H1's published-exit disjunct makes the stale slot inert
  (`m7_root_inert`, `m9_root_inert`), so `E4-TYPED-CE-011` claims the cut only (the coordinator's
  correction, decisions row 134); the earlier note's finished-run refutations are not restated;
* the split: a `J` true at the cut with an `I` keyed on a queued `finish` cannot instantiate
  `DecisionLift` (`seat_split_not_decisionLift`, red); a clause keyed on `running` holds at the
  window (`running_clause_vacuous_at_m6`, `running_exempt_at_m6`, positive); the
  observation-level clause holds at both machines (`exitsTyped6`, `exitsTyped7`, positive);
* halting keeps the typed state (`typedState_halt`, `halting_result_typed`,
  `typed_not_imply_running`), so the typed state cannot yield "never halts" (`E4-TYPED-CE-014`);
* `WorldValid` is not upward closed along `leHost` (`worldValid_not_upward_closed`).

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

/-- An exit that is a failure with no `Fail` reason; `none` is vacuously fine. -/
def exitFailClean : Option ExitV → Bool
  | none => true
  | some (.failure c) => cleanExit (.failure c)
  | some (.success _) => false

abbrev RR := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit
def isFinished : RR → Bool | .finished _ => true | _ => false
def isFuel : RR → Bool | .frontier .fuel _ => true | _ => false

/-! ## Reachability and the machines -/

theorem typed_source : Api.typeOf prog = some ty := by rfl'

theorem closed_ty : ClosedEff ty := ⟨rfl, rfl⟩

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

/-! ## The merged typed state fails at the cut -/

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

/-- **The merged typed state fails at the cut machine, at every world** (the empty queue is
what `decision_preserves` and `typedState_reachable` read). -/
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

/-- `decision_preserves`'s proposition at the merged head, at this program and budget. -/
def DecisionPreserves (fuel : Nat) : Prop :=
  ∀ (d : Api.Decision) (w : W) (m : RState), TypedState (prog : ProgramSource) ty w m →
    AnswerOk w m d → ∃ w', w.leHost w' ∧ TypedState (prog : ProgramSource) ty w'
      (letI := termEvaluatorFor prog
       stepDecisionState (interpR prog) fuel m d).1

/-- `typedState_load`'s conclusion at the merged head, at this program and budget. -/
def Loads (fuel : Nat) : Prop := ∃ w, TypedState (prog : ProgramSource) ty w (loadR prog fuel fuel)

/-- **The merged ledger's M5 and M6b cannot both hold at this program** (budget 6), through the
tree's own replay lift. -/
theorem ledger_jointly_false_window : ¬ (Loads 6 ∧ DecisionPreserves 6) := by
  rintro ⟨⟨w0, h0⟩, pres⟩
  letI := termEvaluatorFor prog
  obtain ⟨w, _, hw⟩ := Effect4.Machine.Lift.replayEval_lift hostOrder
    (fun w m => TypedState (prog : ProgramSource) ty w m) (fun w m d => AnswerOk w m d)
    (interpR prog) 6 (fun w m d _ ht ha => pres d w m ht ha) tape w0 (loadR prog 6 6) h0
    (admitted_noAnswer _ 6 tape answerFree _)
  exact window_untyped w hw

/-! ## The finished run: covered by H1's published-exit disjunct at the merged head -/

theorem m7_root_published : ∃ f ∈ m7.fibers, f.id = Api.root ∧ f.exit.isSome = true := by
  decide +kernel

theorem m9_root_published : ∃ f ∈ m9.fibers, f.id = Api.root ∧ f.exit.isSome = true := by
  decide +kernel

theorem m7_root_inert : CodeInert m7 [] (.fiber Api.root) := by
  obtain ⟨f, hf, hid, hex⟩ := m7_root_published
  exact Or.inr (Or.inr ⟨f, hf, hid, hex⟩)

theorem m9_root_inert : CodeInert m9 [] (.fiber Api.root) := by
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
  CodeInert m q p ∨ ∃ id, positionId p = some id ∧
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
  | failure c => exact fitsExit_of_clean w t c hc

theorem exitsTyped6 : ExitsTyped (initialWorld ty) m6 := exitsTyped_of m6 _ only_root6
theorem exitsTyped7 : ExitsTyped (initialWorld ty) m7 := exitsTyped_of m7 _ only_root7

/-! ## The typed state is not upward closed -/

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

/-! ## Probe C at the merged head: halting keeps the typed state (`E4-TYPED-CE-014`)

`RunMachine.halt` sets only `stuck` (`Machine/Fibers.lean:665-667`); the merged `TypedState`
reads `stuck` only through H1's `CodeInert`, which makes every current code inert on a halted
machine. So halting keeps it at every queue, a halting command meets `StepPreserves`'s
conclusion at the same world, and the typed state never excludes a stuck machine. -/

/-! ### Transport through the generated skeleton

Two instances of the merged bundle `statePreds root m q` differ only in `SavedOk`: every other
field is `preds root`'s. The generated structures take the bundle as a parameter, so their types
differ while their fields agree (the probe author's lesson, `proofs/note.md` §5, probe C). These
lemmas move each generated clause between two instances; `FinNameOk`'s foreign-capture arm is a
structure over the bundle, so finalizer names and scope states are taken by cases. -/

section Transport
variable {root : ProgramSource} {m m' : RState} {q q' : List RCmd} {w : W} {e : Expect}

theorem finNameOk_tr (x : FinName) (h : FinNameOk (statePreds root m q) w e x) :
    FinNameOk (statePreds root m' q') w e x := by
  cases x with
  | foreign capture =>
    change CaptureOk (statePreds root m q) w e capture at h
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
    (h : ScopeStateOk (statePreds root m q) w e x) : ScopeStateOk (statePreds root m' q') w e x := by
  cases x with
  | empty => trivial
  | openEmpty => trivial
  | openInline key finalizer => exact finNameOk_tr finalizer h
  | openMap entries => exact fun v hv => finNameOk_tr v.2 (h v hv)
  | closed exit => trivial

theorem storesOk_tr (x : Stores) (h : StoresOk (statePreds root m q) w e x) :
    StoresOk (statePreds root m' q') w e x :=
  ⟨h.c0, h.c1, ⟨h.c2.c0⟩,
    ⟨fun entry member => ⟨⟨scopeStateOk_tr entry.scope.state ((h.c3.c0 entry member).c0.c0)⟩⟩⟩,
    fun memo member => ⟨fun v hv => ⟨finNameOk_tr v.2.finalizer (((h.c4 memo member).c0 v hv).c0)⟩⟩,
    h.c5⟩

theorem dispatcherOk_tr (x : Dispatcher EffName EffThunk Val Err Defect FiberId Ann RProgram)
    (h : DispatcherOk (statePreds root m q) w e x) : DispatcherOk (statePreds root m' q') w e x :=
  ⟨fun bucket hb => ⟨fun task ht => ((h.c0 bucket hb).c0 task ht)⟩⟩

theorem runFiberOk_tr (x : RFiber)
    (hs : ∀ w e x, (statePreds root m q).SavedOk w e x → (statePreds root m' q').SavedOk w e x)
    (h : RunFiberOk (statePreds root m q) w e x) : RunFiberOk (statePreds root m' q') w e x :=
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
  | dropScopeFinalizer scope key => trivial
  | callback key => trivial


/-- Halting changes no clause the merged typed state checks: H1's `CodeInert` makes every current
code inert on a halted machine, and the rest reads fields `halt` leaves alone. -/
theorem typedState_halt (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (q : List RCmd) (why : Stuck) (h : TypedState root rootTy w m q) :
    TypedState root rootTy w (m.halt why) q := by
  obtain ⟨valid, ok, deliv, sched, obsv, reg⟩ := h
  have saved : ∀ w e x, (statePreds root m q).SavedOk w e x →
      (statePreds root (m.halt why) q).SavedOk w e x := by
    intro w e x hx t ht
    obtain ⟨tin, _, stack, prov⟩ := hx t ht
    exact ⟨tin, fun live => False.elim (live (Or.inl rfl)), stack, prov⟩
  refine ⟨{ ids := valid.ids, fibers := valid.fibers, heap := valid.heap,
            promises := valid.promises, tokens := valid.tokens, tokenBound := valid.tokenBound,
            tokenTargets := valid.tokenTargets, state := valid.state, wf := valid.wf,
            cells := valid.cells, fiberClosed := valid.fiberClosed, heapClosed := valid.heapClosed,
            promiseClosed := valid.promiseClosed, tokenClosed := valid.tokenClosed,
            root := valid.root },
    ⟨fun f hf => runFiberOk_tr f saved (ok.c0 f hf), ok.c1, storesOk_tr m.state ok.c2⟩,
    deliv, ?_, ?_, reg⟩
  · exact { fiberIds := sched.fiberIds, fibersBelow := sched.fibersBelow, raceIds := sched.raceIds,
            racesBelow := sched.racesBelow, raceHosts := sched.raceHosts, keysBelow := sched.keysBelow,
            requestsBelow := sched.requestsBelow, requestsOwned := sched.requestsOwned,
            pendingShape := sched.pendingShape, parkedIdle := sched.parkedIdle,
            parkedBelow := sched.parkedBelow, exited := sched.exited,
            deferredCause := sched.deferredCause }
  · exact ⟨obsv.pendingOwner, fun f hf o ho => storedObserverOk_halt o (obsv.observers f hf o ho)⟩

/-- The empty residue is typed. -/
theorem queueOk_nil (root : ProgramSource) (w : W) (m : RState) : QueueOk root w m [] :=
  { payload := fun _ h => (nomatch h), authority := fun _ h => (nomatch h),
    delivery := fun _ h => (nomatch h), owners := List.nodup_nil, registration := trivial,
    keys := ⟨fun _ h => (nomatch h), fun _ _ _ _ h => (nomatch h)⟩,
    observer := fun _ _ _ h => (nomatch h), enroll := fun _ _ h => (nomatch h),
    noRaceAfterInterrupt := fun _ _ _ h => (nomatch h) }

/-- A command whose result is `(m.halt why, [])` (for example `linkScope` on an unknown scope,
`Machine/Fibers.lean:1010`) meets the conclusion `StepPreserves` asks for, at the same world. -/
theorem halting_result_typed (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (why : Stuck) (h : TypedState root rootTy w m) :
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' (m.halt why) [] ∧
      QueueOk root w' (m.halt why) [] :=
  ⟨w, leHost_refl w, typedState_halt root rootTy w m [] why h, queueOk_nil root w (m.halt why)⟩

/-- Hence the typed state does not imply that the machine is not stuck. -/
theorem typed_not_imply_running (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (why : Stuck) (h : TypedState root rootTy w m) :
    ∃ m', TypedState root rootTy w m' ∧ m'.stuck = some why :=
  ⟨m.halt why, typedState_halt root rootTy w m [] why h, rfl⟩

end Test.Counterexamples.Machine.Semantics.StaleCode

open Test.Counterexamples.Machine.Semantics.StaleCode

#print axioms typed_source
#print axioms answerFree
#print axioms reach6
#print axioms reach7
#print axioms reach9
#print axioms window6
#print axioms m6_stuck_none
#print axioms m6_root_running
#print axioms m6_only_root
#print axioms finished7m
#print axioms budget7_is_fuel_frontier
#print axioms budget7_not_finished
#print axioms finished7
#print axioms finished9
#print axioms m9_root_stale
#print axioms only_root6
#print axioms only_root7
#print axioms residue6_shape
#print axioms residue6_machine
#print axioms any_fail_not_clean
#print axioms m6_not_inert
#print axioms stale_not_saved
#print axioms window_untyped
#print axioms capstone_false_window
#print axioms admitted_noAnswer
#print axioms ledger_jointly_false_window
#print axioms m7_root_published
#print axioms m9_root_published
#print axioms m7_root_inert
#print axioms m9_root_inert
#print axioms stale_not_savedOk
#print axioms seat_split_not_decisionLift
#print axioms running_clause_vacuous_at_m6
#print axioms running_exempt_at_m6
#print axioms exitsTyped_of
#print axioms exitsTyped6
#print axioms exitsTyped7
#print axioms worldValid_not_upward_closed
#print axioms finNameOk_tr
#print axioms scopeStateOk_tr
#print axioms storesOk_tr
#print axioms dispatcherOk_tr
#print axioms runFiberOk_tr
#print axioms halt_fiber?
#print axioms halt_race?
#print axioms countdownAt_halt
#print axioms storedObserverOk_halt
#print axioms typedState_halt
#print axioms queueOk_nil
#print axioms halting_result_typed
#print axioms typed_not_imply_running
