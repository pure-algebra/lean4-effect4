import Effect4.Laws.Program.Typed.Edits
import Test.Counterexamples.Machine.Semantics.M6Capstone

/-!
Seat D3 refutation probe: `StepPreserves` for `exitDone` and for `finish` (`M6Ledger.step_exitDone`,
`M6Ledger.step_finish`) is false as stated: both clear a fiber's saved stack while its current code
may be a race registration marker, and `RegistrationState` reads that stack.

A typed configuration (`I`) whose root's current code is the marker of race 0 (host the root,
token 0, declared at `number`), over a saved stack `[answer (fun _ => succeed void)]` that takes
`number` to the root's declared `void`, so `RegistrationState`'s `StackReply` holds. Nothing in `I`
keeps an exited fiber's or a finishing fiber's current code off the marker: `LiveCode` reads only
idle unexited fibers, `ReadCode` only fibers a queued `loop` or `deliver` reads.

* `exitDone`: the root has exited (`succeed void`); `exitDone` clears it (`RunFiber.cleared`).
* `finish`: the root is running with a queued `finish root (succeed void)`; with no observer and
  no middleware, `exitStore` publishes and clears it.

After either step the marker sits over the empty stack, and `StackReply` at the race's type
(`number`, pinned by the token at every later world) over the empty stack needs the root declared
at `number`; it is declared at `void`. Run: `LEAN_NUM_THREADS=2 lake env lean
docs/research/2026-10-01-landing/seat-D3/probes/MarkerStack.lean`.
-/

namespace Effect4.Program.Typed.SeatD3.MarkerStack
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

def rootProgram : NativeEff := .succeed (.lit .unit)
def unitTy : EffTy := EffTy.pure .unit
def natTy : EffTy := EffTy.pure .nat

def marker : RProgram := .vis (.inr (.raceRegister 0)) Effects.Program.pure
def answer : ExitV → RProgram := fun _ => .pure (.success .unit)

def frame : RSaved :=
  { current := marker, stack := [.answer answer], interruptible := true,
    interruptedCause := none, deferredInterrupt := false }

/-- The root as `exitDone` finds it: exited, idle, the marker over the answer frame. -/
def exitedFiber : RFiber :=
  { RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx with
    running := false, exit := some (.success .unit), frame := frame }

/-- The root as `finish` finds it: running, the marker over the answer frame. -/
def runningFiber : RFiber :=
  { RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx with
    running := true, frame := frame }

def race : RRace :=
  { id := 0, host := Api.root, token := 0, state := Supervision.RaceAllState.initial [],
    settled := false, programs := [], registering := false }

def machineOf (f : RFiber) : RState :=
  { loadR rootProgram 20 20 with fibers := [f], races := [race], nextToken := 1, nextRace := 1 }

def world : W :=
  { initialWorld unitTy with Θ := fun id t => if id = Api.root ∧ t = 0 then some natTy else none }

/-- The two fibers this probe uses share every field `J` reads but the flags. -/
inductive Shape : RFiber → Prop
  | exited : Shape exitedFiber
  | running : Shape runningFiber

theorem shape_id {f : RFiber} (h : Shape f) : f.id = Api.root := by cases h <;> rfl
theorem shape_frame {f : RFiber} (h : Shape f) : f.frame = frame := by cases h <;> rfl
theorem shape_parked {f : RFiber} (h : Shape f) : f.parked = .notParked := by cases h <;> rfl
theorem shape_pending {f : RFiber} (h : Shape f) : f.pending = [] := by cases h <;> rfl
theorem shape_observers {f : RFiber} (h : Shape f) : f.observers = [] := by cases h <;> rfl
theorem shape_finalizing {f : RFiber} (h : Shape f) : f.finalizing = none := by cases h <;> rfl
theorem shape_exit {f : RFiber} (h : Shape f) : f.exit = none ∨ f.exit = some (.success .unit) := by
  cases h
  · exact Or.inr rfl
  · exact Or.inl rfl
theorem shape_exited {f : RFiber} (h : Shape f) : f.exit.isSome = true → f.running = false := by
  cases h
  · intro _; rfl
  · intro hx; cases hx
theorem shape_dispatcher {f : RFiber} (h : Shape f) :
    f.dispatcher = (RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx).dispatcher := by
  cases h <;> rfl
theorem shape_context {f : RFiber} (h : Shape f) : f.context = emptyCtx := by cases h <;> rfl

theorem member {f g : RFiber} (hg : g ∈ (machineOf f).fibers) : g = f := by
  change g ∈ [f] at hg
  exact List.mem_singleton.mp hg

theorem stack_typed : StackAccepts (TypedProg (rootProgram : ProgramSource)) ExitOk
    (frameProtocols (rootProgram : ProgramSource)) world natTy unitTy frame.stack :=
  .cons (.answer (tin := natTy) (tout := unitTy) answer
    (fun _ _ _ _ => TypedProg.pure (ty := unitTy) ⟨trivial, trivial⟩)) (.nil unitTy)

theorem provenance : InterruptProvenance frame := ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩

theorem valid {f : RFiber} (h : Shape f) : WorldValid unitTy world (machineOf f) := by
  have old := initial_world_valid_at unitTy nativeServiceTy rootProgram 20 20 ⟨rfl, rfl⟩
  refine
    { ids := ?_, fibers := ?_, heap := old.heap, promises := old.promises,
      tokens := ?_, tokenBound := ?_, tokenTargets := ?_, state := rfl, wf := old.wf,
      cells := old.cells, fiberClosed := old.fiberClosed, heapClosed := old.heapClosed,
      promiseClosed := old.promiseClosed, tokenClosed := ?_, root := old.root }
  · cases h <;> rfl
  · intro id
    cases h <;> exact old.fibers id
  · intro g hg token hp
    rw [member hg, shape_parked h] at hp
    cases hp
  · intro id token ty hΘ
    change (if id = Api.root ∧ token = 0 then some natTy else none) = some ty at hΘ
    by_cases c : id = Api.root ∧ token = 0
    · rw [c.2]
      exact Nat.zero_lt_one
    · rw [if_neg c] at hΘ
      cases hΘ
  · intro id token ty hΘ
    change (if id = Api.root ∧ token = 0 then some natTy else none) = some ty at hΘ
    by_cases c : id = Api.root ∧ token = 0
    · rw [c.1]
      rfl
    · rw [if_neg c] at hΘ
      cases hΘ
  · intro id token ty hΘ
    change (if id = Api.root ∧ token = 0 then some natTy else none) = some ty at hΘ
    by_cases c : id = Api.root ∧ token = 0
    · rw [if_pos c] at hΘ
      cases hΘ
      exact ⟨rfl, rfl⟩
    · rw [if_neg c] at hΘ
      cases hΘ

theorem internalKeys_machine {f : RFiber} (h : Shape f) :
    Guard.internalKeys (machineOf f) = [(Api.root, 0)] := by
  cases h <;> rfl

theorem no_requests {f : RFiber} (h : Shape f) (id : FiberId) (token : Nat) :
    requestOfR (machineOf f) id token = none := by
  unfold requestOfR
  cases hf : (machineOf f).fiber? id with
  | none => rfl
  | some found =>
    have same := member (List.mem_of_find?_eq_some hf)
    subst same
    cases h <;> rfl

theorem raceId_machine {f : RFiber} : (machineOf f).race? 0 = some race := rfl

theorem racePayload : RacePayload (rootProgram : ProgramSource) world race natTy :=
  ⟨rfl, ⟨failureFits_of_cause (fun _ h => nomatch h) (fun _ h => nomatch h),
      (fun _ h => nomatch h)⟩, (fun _ h => nomatch h), (fun _ h => nomatch h),
    (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

theorem typedState {f : RFiber} (h : Shape f) :
    TypedState (rootProgram : ProgramSource) unitTy world (machineOf f) := by
  refine ⟨valid h, ⟨?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro g hg
    rw [member hg]
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty declared
      change world.Γ f.id = some ty at declared
      rw [shape_id h] at declared
      have root : world.Γ Api.root = some unitTy := rfl
      rw [root] at declared
      cases declared
      rw [shape_frame h]
      exact ⟨natTy, stack_typed, provenance⟩
    · intro p hp
      rw [shape_pending h] at hp
      cases hp
    · intro v hv
      rw [shape_finalizing h] at hv
      cases hv
    · intro v hv ty declared
      change world.Γ f.id = some ty at declared
      rw [shape_id h] at declared
      have root : world.Γ Api.root = some unitTy := rfl
      rw [root] at declared
      cases declared
      rcases shape_exit h with e | e <;> rw [e] at hv <;> cases hv
      exact ⟨trivial, trivial⟩
    · intro b hb
      rw [shape_dispatcher h] at hb
      cases hb
    · intro key value ty lookup
      rw [shape_context h] at lookup
      change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
      rw [Env.Context.getV_empty] at lookup
      cases lookup
  · intro r hr
    change r ∈ [race] at hr
    rw [List.mem_singleton.mp hr]
    exact ⟨natTy, racePayload⟩
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro g hg token hp
    rw [member hg, shape_parked h] at hp
    cases hp
  · constructor
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro g hg
      rw [member hg, shape_id h]
      exact Nat.zero_lt_one
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro r hr
      change r ∈ [race] at hr
      rw [List.mem_singleton.mp hr]
      exact Nat.zero_lt_one
    · intro r hr
      change r ∈ [race] at hr
      rw [List.mem_singleton.mp hr]
      exact ⟨f, by cases h <;> rfl⟩
    · intro key hk
      rw [internalKeys_machine h, List.mem_singleton] at hk
      rw [hk]
      exact Nat.zero_lt_one
    · intro id token request hr
      rw [no_requests h] at hr
      cases hr
    · intro id token request hr
      rw [no_requests h] at hr
      cases hr
    · intro g hg
      rw [member hg]
      unfold Guard.PendingShape
      rw [shape_parked h, shape_pending h]
    · intro g hg hp
      rw [member hg, shape_parked h] at hp
      exact False.elim (hp rfl)
    · intro g hg token hp
      rw [member hg, shape_parked h] at hp
      cases hp
    · intro g hg hx
      rw [member hg] at hx ⊢
      exact ⟨shape_parked h, shape_exited h hx⟩
    · intro g hg hd
      rw [member hg, shape_frame h] at hd
      cases hd
  · intro g hg p hp
    rw [member hg, shape_pending h] at hp
    cases hp
  · intro g hg o ho
    rw [member hg, shape_observers h] at ho
    cases ho
  · intro g hg raceId hm
    rw [member hg] at hm ⊢
    rw [shape_frame h] at hm
    change some 0 = some raceId at hm
    cases hm
    refine ⟨race, natTy, raceId_machine, shape_id h ▸ rfl, rfl, unitTy, ?_, ?_, ?_⟩
    · rw [shape_id h]
      rfl
    · rw [shape_frame h]
      exact stack_typed
    · rw [shape_frame h]
      exact provenance

theorem machine_typed {f : RFiber} (h : Shape f) :
    MachineTyped (rootProgram : ProgramSource) unitTy world (machineOf f) := by
  refine ⟨typedState h, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩⟩
  intro g hg _ _ marker' ty _
  rw [member hg, shape_frame h] at marker'
  cases marker'

/-- After the step, no later world types a machine whose root keeps the marker over an empty
stack: the race's token pins its type at `number`, and the empty stack replies only at the
root's declared `void`. -/
theorem untyped (w' : W) (ord : world.leHost w') (m : RState) (g : RFiber)
    (hg : g ∈ m.fibers) (gid : g.id = Api.root) (current : g.frame.current = marker)
    (empty : g.frame.stack = []) (races : m.race? 0 = some race) :
    ¬ MachineTyped (rootProgram : ProgramSource) unitTy w' m := by
  intro typed
  have registration := typed.typed.2.2.2.2.2 g hg 0 (by rw [current]; rfl)
  obtain ⟨r, resultTy, found, host, token, reply⟩ := registration
  rw [races] at found
  cases found
  have pinned : w'.Θ Api.root 0 = some natTy := ord.1.2.2.2.2.2.1 Api.root 0 natTy rfl
  change w'.Θ Api.root 0 = some resultTy at token
  rw [pinned] at token
  cases token
  have declared := Test.Counterexamples.Machine.Semantics.M6Capstone.H1.stackReply_empty_declared
    (rootProgram : ProgramSource) w' g natTy empty reply
  have root : w'.Γ Api.root = some unitTy := ord.1.2.1 Api.root unitTy rfl
  rw [gid, root] at declared
  cases declared

/-! ### `exitDone` -/

def exitDoneResult :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) (machineOf exitedFiber) (.exitDone Api.root) []

theorem exitDone_config : ConfigTyped (rootProgram : ProgramSource) unitTy world
    (machineOf exitedFiber) [.exitDone Api.root] := by
  refine ⟨machine_typed .exited, ?_, ?_⟩
  · intro f _ _ reads
    obtain ⟨_, r⟩ := reads
    rcases r with r | r <;> (rw [List.mem_singleton] at r; cases r)
  · refine ⟨?_, ?_, ?_, List.nodup_nil, ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨exitedFiber, rfl, rfl⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro k member
      cases member
    · intro fiber token request _ member
      cases member
    · intro source exit observer member
      rw [List.mem_singleton] at member
      cases member
    · intro race child member
      rw [List.mem_singleton] at member
      cases member
    · intro host yielding race member
      rw [List.mem_singleton] at member
      cases member
    · intro mode scope target interruptor extra member
      rw [List.mem_singleton] at member
      cases member

/-- **`exitDone` does not keep `I`.** -/
theorem exitDone_false :
    ¬ StepPreserves (rootProgram : ProgramSource) unitTy (.exitDone Api.root) := by
  intro step
  obtain ⟨w', ord, typed⟩ := step world (machineOf exitedFiber) [] rfl exitDone_config
  exact untyped w' ord exitDoneResult.1 _ (List.mem_singleton_self _) rfl rfl rfl rfl
    typed.machine

/-! ### `finish` -/

def finishResult :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) (machineOf runningFiber) (.finish Api.root (.success .unit)) []

theorem finish_config : ConfigTyped (rootProgram : ProgramSource) unitTy world
    (machineOf runningFiber) [.finish Api.root (.success .unit)] := by
  refine ⟨machine_typed .running, ?_, ?_⟩
  · intro f _ _ reads
    obtain ⟨_, r⟩ := reads
    rcases r with r | r <;> (rw [List.mem_singleton] at r; cases r)
  · refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      intro ty declared
      have root : world.Γ Api.root = some unitTy := rfl
      change world.Γ Api.root = some ty at declared
      rw [root] at declared
      cases declared
      exact ⟨trivial, trivial⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨runningFiber, rfl, rfl, rfl⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro k member
      cases member
    · intro fiber token request _ member
      cases member
    · intro source exit observer member
      rw [List.mem_singleton] at member
      cases member
    · intro race child member
      rw [List.mem_singleton] at member
      cases member
    · intro host yielding race member
      rw [List.mem_singleton] at member
      cases member
    · intro mode scope target interruptor extra member
      rw [List.mem_singleton] at member
      cases member

/-- **`finish` does not keep `I`.** -/
theorem finish_false :
    ¬ StepPreserves (rootProgram : ProgramSource) unitTy (.finish Api.root (.success .unit)) := by
  intro step
  obtain ⟨w', ord, typed⟩ := step world (machineOf runningFiber) [] rfl finish_config
  exact untyped w' ord finishResult.1 _ (List.mem_singleton_self _) rfl rfl rfl rfl
    typed.machine

end Effect4.Program.Typed.SeatD3.MarkerStack

#print axioms Effect4.Program.Typed.SeatD3.MarkerStack.exitDone_config
#print axioms Effect4.Program.Typed.SeatD3.MarkerStack.exitDone_false
#print axioms Effect4.Program.Typed.SeatD3.MarkerStack.finish_config
#print axioms Effect4.Program.Typed.SeatD3.MarkerStack.finish_false
