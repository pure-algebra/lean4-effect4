import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Guard.Core

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SideAudit.TokenFinish
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed

abbrev W := Effect4.Program.Typed.World

def program : NativeEff := .succeed (.lit .unit)
def ty : EffTy := EffTy.pure .unit
def m0 : RState := loadR program 20 20
def bad : RCmd := .finish Api.root (.success (.nat 42))
def m1 : RState :=
  (letI := termEvaluatorFor program
   driveStep (interpR program) m0 bad []).1

#guard Api.typeOf program [] == some ty
#guard m0.nextToken == 0
#guard ((m1.fiber? Api.root).bind RunFiber.exit) == some (.success (.nat 42))

theorem loaded_code (w : W) : TypedProg (program : ProgramSource) w ty
    (denoteR program program (rootPoint 20)) := by
  change TypedProg (program : ProgramSource) w ty (.pure (.success .unit))
  apply TypedProg.pure
  refine ⟨rfl, ?_, ?_⟩
  · intro v heq
    cases heq
    exact ⟨rfl, trivial, fun _ h => nomatch h⟩
  · intro c heq
    cases heq

theorem loaded_typed : ∃ w, TypedState (program : ProgramSource) ty w m0 := by
  refine ⟨initialWorld ty, initial_world_valid _ program 20 20 ⟨rfl, rfl⟩,
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

theorem bad_queue (w : W) : QueueOk (program : ProgramSource) w [bad] := by
  intro cmd hcmd
  simp only [List.mem_singleton] at hcmd
  subst cmd
  trivial

theorem bad_exit : ∃ f ∈ m1.fibers, f.id = Api.root ∧ f.exit = some (.success (.nat 42)) := by
  decide

theorem after_untyped (w : W) : ¬ TypedState (program : ProgramSource) ty w m1 := by
  intro h
  obtain ⟨f, hf, hid, hex⟩ := bad_exit
  have he := (h.2.1.c0 f hf).c3 _ hex
  change ∀ ty, w.Γ f.id = some ty → StrongExit w ty (.success (.nat 42)) at he
  have hs := he ty (by rw [hid]; exact h.1.root)
  exact Bool.noConfusion hs.1

/-- The present step_finish obligation is false even for the loaded pure-unit program. -/
theorem step_finish_false : ¬ StepPreserves (program : ProgramSource) ty bad := by
  intro step
  obtain ⟨w, hw⟩ := loaded_typed
  obtain ⟨w', _, after, _⟩ := step w m0 [] hw (bad_queue w)
  exact after_untyped w' after

-- The pending-token question has a positive answer already implied by present fields.
theorem pending_below (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (typed : TypedState root rootTy w m) (f : RFiber) (hf : f ∈ m.fibers)
    (p : Pending EffName Val Err Defect FiberId Ann) (hp : p ∈ f.pending) :
    p.token < m.nextToken := by
  obtain ⟨id, declared⟩ := (typed.2.1.c0 f hf).c1 p hp
  cases h : w.Θ id p.token with
  | none => rw [h] at declared; cases declared
  | some tokenTy => exact typed.1.tokenBound id p.token tokenTy h

-- Generalize exactly the guard key lists over the RProgram code carrier, as the proposal asks.
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

theorem loaded_keys_below : InternalKeysBelowR m0 := by
  intro k hk
  cases hk

theorem bad_queue_fresh : QueueFresh m0 [bad] := by
  intro k hk
  cases hk

/-- The exact proposed StepPreserves' shape from lift/verify.md section 3. -/
def StepPreservesFresh (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, TypedState root rootTy w m → InternalKeysBelowR m →
    QueueOk root w (cmd :: rest) → QueueFresh m (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' r.1 ∧ InternalKeysBelowR r.1 ∧
      QueueOk root w' r.2 ∧ QueueFresh r.1 r.2

theorem proposed_step_finish_false : ¬ StepPreservesFresh (program : ProgramSource) ty bad := by
  intro step
  obtain ⟨w, hw⟩ := loaded_typed
  obtain ⟨w', _, after, _⟩ := step w m0 [] hw loaded_keys_below (bad_queue w) bad_queue_fresh
  exact after_untyped w' after

-- The generated command judgment already has the missing finish exit clause.
theorem bad_generated_command_rejected (w : W) (valid : WorldValid ty w m0) :
    ¬ RCmdOk (preds (program : ProgramSource)) w bad := by
  intro h
  have hs := h ty valid.root
  exact Bool.noConfusion hs.1

#print axioms loaded_keys_below
#print axioms bad_queue_fresh
#print axioms proposed_step_finish_false
#print axioms bad_generated_command_rejected
#print axioms loaded_code
#print axioms loaded_typed
#print axioms bad_queue
#print axioms bad_exit
#print axioms after_untyped
#print axioms step_finish_false
#print axioms pending_below
end SideAudit.TokenFinish
