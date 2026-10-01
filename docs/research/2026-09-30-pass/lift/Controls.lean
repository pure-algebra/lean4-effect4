import Effect4.Laws.Program.Guard.Decision
import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Api.TraceOrigin

/-!
# Research.Pass.Lift.Controls — red controls for the lift probe (`Lift.lean`)

Each control shows that a premise of the lift, or a choice in its statement, is not vacuous.
The `#guard`s are finite checks on one concrete machine each; the theorems are kernel facts.

- C1: the guard's queue invariant is false at `[resume, drainDue]` for an answer to a live
  request, so the answer premise must hold after that `resume`, as `DecisionLift.answer` says.
- C2: the frame law's halting disjunct occurs: an evaluator whose iteration halts drops the
  suffix. The lift is generic in the evaluator; the native one reaches the same `settle` arm
  through a join on an unknown fiber (`Machine/Fibers.lean:1108`).
- C3: with today's `RunFiber.origin`, an edit outside the loop (`yieldVerdict`'s modify) breaks
  the trace agreement on a machine whose fiber ids repeat. So the agreement is a `Keeps` of
  every machine only once the record is off the fiber (the ledger), or under a distinct-ids
  premise.
- C4: M6's current capstone is false (the plan review's counterexample, copied from
  `docs/research/2026-09-30-origin-plan-review/Probe.lean`); its tape applies a host answer.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.Pass.Lift.Controls

open Effect4 Effect4.Machine Effect4.Program

/-! ## C1: the guard's queue refuses an answer's `resume` at the loop entry -/

open Effect4.Program.Guard in
theorem guardQueue_refuses_live_answer (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (id : FiberId) (token : Nat) (code : NCode) (request : NativeOp × Val)
    (live : requestOf m id token = some request) :
    ¬ GuardQueue p table m [.resume id token code, .drainDue] :=
  fun q => q.keys.disjoint id token request live (List.mem_append_left _ (List.mem_singleton_self _))

/-! ## C2: the frame law's halting disjunct is not vacuous -/

/-- An instance of the generic machine whose every iteration halts. -/
@[reducible] def haltingEvaluator :
    FiberEvaluator EffName EffThunk Val Err Defect FiberId Ann Ctx Stores
      (Prim EffName EffThunk Val Err Defect FiberId Ann) (FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
      (FrameEvent EffName EffThunk Val Err Defect FiberId Ann) where
  evaluate := fun _ m f yielding => ⟨m, f, yielding, Outcome.stuck (Stuck.unknownFiber ⟨7⟩), []⟩

def trivialProg : NativeEff := .succeed (.lit .unit)
def loaded : NativeMachine := Api.load trivialProg 20 []

-- With `rest := []` the residue is empty; with `rest := [drainDue]` it is still empty: the
-- suffix is dropped, and the machine is halted.
#guard (letI := haltingEvaluator
  (driveStep (interpOf trivialProg) loaded (.loop Api.root false) []).2).isEmpty
#guard (letI := haltingEvaluator
  (driveStep (interpOf trivialProg) loaded (.loop Api.root false) [Cmd.drainDue]).2).isEmpty
#guard (letI := haltingEvaluator
  (driveStep (interpOf trivialProg) loaded (.loop Api.root false) []).1).stuck.isSome
-- The naive frame law would need `[] ++ [drainDue]` here, which is not empty.
#guard !(([] : List (Cmd EffName EffThunk Val Err Defect FiberId Ann)) ++ [Cmd.drainDue]).isEmpty

/-! ## C3: today's origin field; an edit outside the loop breaks the agreement -/

open Effect4.Api.TraceFacts in
/-- The loaded root, plus a copy of it recorded as forked by itself: two fibers, one id. -/
def dupMachine : NativeMachine :=
  match loaded.fibers with
  | [f] => { loaded with
      fibers := [f, { f with origin := .forked f.id false [] }]
      trace := [.forked f.id f.id false] }
  | _ => loaded

def dupYield : NativeMachine :=
  dupMachine.modify Api.root fun f => { f with yieldOverride := some true }

open Effect4.Api.TraceFacts in
#guard forkedOf dupMachine.trace == originForks dupMachine
open Effect4.Api.TraceFacts in
#guard !(forkedOf dupYield.trace == originForks dupYield)
#guard !(decide (dupMachine.fibers.map (·.id)).Nodup)

/-! ## C4: M6's current capstone is false on a tape that applies a host answer -/

open Effect4.Program.Sched Effect4.Program.Typed

def sleeper : NativeEff := .perform .sleep (.lit (.nat 1))
def badTape : List Api.Decision :=
  [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (.nat 42)))]
def bad : RState := (replayR sleeper 80 badTape).machine

#guard Api.typeOf sleeper = some (EffTy.pure .unit)
#guard ((bad.fiber? Api.root).bind RunFiber.exit) == some (.success (.nat 42))

theorem bad_reachable : RReachable (sleeper : ProgramSource) 80 bad := ⟨badTape, rfl⟩

theorem bad_has_bad_exit : ∃ f ∈ bad.fibers,
    f.id = Api.root ∧ f.exit = some (.success (.nat 42)) := by decide

theorem bad_not_typed (w : Typed.World) :
    ¬ TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w bad := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := bad_has_bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → StrongExit w ty (.success (.nat 42)) at he
  have hs := he (EffTy.pure .unit) (by rw [hid]; exact h.1.root)
  exact Bool.noConfusion hs.1

/-- The capstone as the ledger states it (`Typed/Assembly.lean:225-227`) is false here. -/
theorem current_capstone_false : ¬ (
    Api.typeOf sleeper [] = some (EffTy.pure .unit) →
    ClosedEff (EffTy.pure .unit) →
    RReachable (sleeper : ProgramSource) 80 bad →
    ∃ w, TypedState (sleeper : ProgramSource) (EffTy.pure .unit) w bad) := by
  intro h
  obtain ⟨w, hw⟩ := h (by rfl') ⟨rfl, rfl⟩ bad_reachable
  exact bad_not_typed w hw

/-- The refuting tape applies a host answer (its second decision). The repaired reachability of
`Lift.lean` (`RReachableNoAnswer`) admits only tapes with none. -/
theorem badTape_applies_answer :
    ∃ d ∈ badTape, ∃ id token answer, d = .answerAsync id token answer :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Api.root, 0, _, rfl⟩

-- The same with the probe's own `isAnswer` spelled out here (a copy of `Lift.lean`'s):
#guard badTape.any (fun d => match d with | .answerAsync _ _ _ => true | _ => false)

end Research.Pass.Lift.Controls

#print axioms Research.Pass.Lift.Controls.guardQueue_refuses_live_answer
#print axioms Research.Pass.Lift.Controls.bad_reachable
#print axioms Research.Pass.Lift.Controls.bad_has_bad_exit
#print axioms Research.Pass.Lift.Controls.bad_not_typed
#print axioms Research.Pass.Lift.Controls.current_capstone_false
#print axioms Research.Pass.Lift.Controls.badTape_applies_answer
