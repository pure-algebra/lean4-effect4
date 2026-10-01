import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Guard.Core

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SideAudit.BadDefectCurrent
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def program : NativeEff := .succeed (.lit .unit)
def malformed : NativeEff := .succeed (.var 99)
def ty : EffTy := EffTy.pure .unit
-- A convenient concrete machine whose only current code is pure(badName).
-- The source being typed remains the independently checked `program` above.
def m0 : RState := loadR malformed 20 20

def badDefect (ty : EffTy) : Reason Err Defect FiberId Ann → Bool
  | .die d _ => d == .badName || d == .notImplemented ||
      (d == .missingService && ty.requires == Env.Requirement.empty)
  | _ => false

def NoShapeDefect (ty : EffTy) : ExitV → Prop
  | .success _ => True
  | .failure c => c.reasons.any (badDefect ty) = false

def predsH (root : ProgramSource) : Preds W :=
  { preds root with
    exit := fun w e ex => ∀ ty, expectOf w e = some ty →
      StrongExit w ty ex ∧ NoShapeDefect ty ex }

def TypedStateH (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (predsH root) w m ∧
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      Contracts.StackAccepts (TypedProg root) StrongExit (frameProtocols root) w tin final f.frame.stack ∧
      Contracts.InterruptProvenance f.frame

#guard Api.typeOf program [] == some ty
#guard ((m0.fiber? Api.root).bind RunFiber.exit) == none
#guard m0.nextToken == 0

theorem loaded_code (w : W) : TypedProg (program : ProgramSource) w ty
    (denoteR malformed malformed (rootPoint 20)) := by
  change TypedProg (program : ProgramSource) w ty (.pure (.failure (Cause.die .badName)))
  exact .pure (strongExit_of_clean w ty (Cause.die .badName) rfl)

theorem strengthened_input : ∃ w, TypedStateH (program : ProgramSource) ty w m0 := by
  refine ⟨initialWorld ty, initial_world_valid _ malformed 20 20 ⟨rfl, rfl⟩,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty' hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root ty Api.root =
          some ty := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root ty Api.root =
        some ty' at hty
      rw [h0] at hty
      cases hty
      exact ⟨ty, loaded_code _, .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro q hq
      cases hq
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro r hr
    cases hr
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hq
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hq


def mEnd : RState :=
  (letI := termEvaluatorFor program
   driveState (interpR program) 20 m0 [.evaluate Api.root]).1

#guard ((mEnd.fiber? Api.root).bind RunFiber.exit) == some (.failure (Cause.die .badName))

theorem bad_exit : ∃ f ∈ mEnd.fibers,
    f.id = Api.root ∧ f.exit = some (.failure (Cause.die .badName)) := by decide

theorem strengthened_output_false (w : W) : ¬ TypedStateH (program : ProgramSource) ty w mEnd := by
  intro typed
  obtain ⟨f, hf, hid, hex⟩ := bad_exit
  have exits := (typed.2.1.c0 f hf).c3 _ hex
  change ∀ t, w.Γ f.id = some t → StrongExit w t (.failure (Cause.die .badName)) ∧
    NoShapeDefect t (.failure (Cause.die .badName)) at exits
  have safe := (exits ty (by rw [hid]; exact typed.1.root)).2
  exact Bool.noConfusion safe

-- The stronger generated command predicate exposes the same problem one iteration earlier.
def firstStep : RState × List RCmd :=
  letI := termEvaluatorFor program
  driveStep (interpR program) m0 (.loop Api.root false) []

theorem firstStep_queue : firstStep.2 = [.finish Api.root (.failure (Cause.die .badName))] := rfl

theorem produced_queue_refused (w : W) (rootDecl : w.Γ Api.root = some ty) :
    ¬ (∀ cmd ∈ firstStep.2, RCmdOk (predsH (program : ProgramSource)) w cmd) := by
  intro queue
  have h := queue (.finish Api.root (.failure (Cause.die .badName))) (by
    rw [firstStep_queue]
    exact List.mem_singleton_self _)
  have safe := (h ty rootDecl).2
  exact Bool.noConfusion safe

#print axioms firstStep_queue
#print axioms loaded_code
#print axioms strengthened_input
#print axioms bad_exit
#print axioms strengthened_output_false
#print axioms produced_queue_refused
def taskKeysR : Task EffName EffThunk Val Err Defect FiberId Ann RProgram → List Guard.GuardKey
  | .resume fiber token _ => [(fiber, token)]
  | _ => []

def commandKeysR : RCmd → List Guard.GuardKey
  | .resume fiber token _ => [(fiber, token)]
  | .observe _ _ observer => Guard.observerKeys observer
  | _ => []

def internalKeysR (m : RState) : List Guard.GuardKey :=
  Guard.wakeKeys m.state.timers.wake ++
    m.state.deferreds.cells.flatMap (fun c => Guard.wakeKeys c.wake) ++
    m.state.deferreds.due.map (fun d => (d.waiter, d.token)) ++
    m.races.map (fun r => (r.host, r.token)) ++
    m.fibers.flatMap (fun f =>
      f.observers.flatMap Guard.observerKeys ++
      f.dispatcher.buckets.flatMap fun b => b.tasks.flatMap taskKeysR)

def InternalKeysBelowR (m : RState) : Prop := ∀ k ∈ internalKeysR m, k.2 < m.nextToken

def QueueFresh (m : RState) (cmds : List RCmd) : Prop :=
  ∀ k ∈ cmds.flatMap commandKeysR, k.2 < m.nextToken

theorem input_keys_below : InternalKeysBelowR m0 := by
  intro k hk
  cases hk

theorem evaluate_fresh : QueueFresh m0 [.evaluate Api.root] := by
  intro k hk
  cases hk

theorem evaluate_admitted (w : W) : RCmdOk (predsH (program : ProgramSource)) w (.evaluate Api.root) := by
  trivial

#print axioms input_keys_below
#print axioms evaluate_fresh
#print axioms evaluate_admitted

end SideAudit.BadDefectCurrent
