import Effect4.Laws.Program.Typed.Edits

/-!
UNCOMPILED candidate against 4c219956e9fa952a34bb37cb5f89ab0ce657f74c.
Concept 4; M6Ledger.step_launch, ConfigTyped closure under the actual driveStep.
Reuses seat-D3 Races.Launch's finite construction and contradiction, with the missing id
moved from the now-bounded stored live list to a queued enrollRace. Two registration hosts
keep the existing queue-owner uniqueness premise. No current predicate is redefined.
This is not a reachable-machine witness, runtime counterexample, progress or host claim.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace LaunchQueuedFuture
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World
abbrev RaceR := Effect4.Program.Typed.RRace

def rootProgram : NativeEff := .succeed (.lit (.nat 0))
def natTy : EffTy := EffTy.pure .nat
def stringTy : EffTy := EffTy.pure .string
def other : FiberId := ⟨1⟩
def fresh : FiberId := ⟨2⟩
def marker (r : Nat) : RProgram := .vis (.inr (.raceRegister r)) Effects.Program.pure
def entrant : RProgram := .pure (.success (.nat 0))
def host (id : FiberId) (r : Nat) : RFiber :=
  { RunFiber.make id (marker r) true (stores.budgetOf emptyCtx) emptyCtx with running := true }
def fiber0 := host Api.root 0
def fiber1 := host other 1

def race0 : RaceR :=
  { id := 0, host := Api.root, token := 0, state := Supervision.RaceAllState.initial [],
    settled := false, programs := [entrant], registering := true }
def race1 : RaceR :=
  { id := 1, host := other, token := 1, state := Supervision.RaceAllState.initial [],
    settled := false, programs := [], registering := true }
def machine : RState :=
  { loadR rootProgram 20 20 with
    fibers := [fiber0, fiber1], races := [race0, race1],
    nextId := 2, nextToken := 2, nextRace := 2 }
def world : W :=
  { initialWorld natTy with
    ids := [Api.root, other]
    Γ := fun id => if id = Api.root then some natTy else if id = other then some stringTy else none
    Θ := fun id t => if id = Api.root ∧ t = 0 then some natTy
      else if id = other ∧ t = 1 then some stringTy else none }
def rest : List RCmd := [.enrollRace 1 fresh, .registrationDone 0 false, .registrationDone 1 false]
def commands : List RCmd := .launch 0 :: rest

theorem provenance (f : RSaved) (h1 : f.interruptedCause = none) (h2 : f.deferredInterrupt = false) :
    InterruptProvenance f := by
  refine ⟨fun c hc => ?_, fun hd => ?_⟩
  · rw [h1] at hc
    cases hc
  · rw [h2] at hd
    cases hd

theorem member {f : RFiber} (h : f ∈ machine.fibers) : f = fiber0 ∨ f = fiber1 := by
  change f ∈ [fiber0, fiber1] at h
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem raceMember {r : RaceR} (h : r ∈ machine.races) : r = race0 ∨ r = race1 := by
  change r ∈ [race0, race1] at h
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem gamma {id : FiberId} {ty : EffTy} (h : world.Γ id = some ty) :
    (id = Api.root ∧ ty = natTy) ∨ (id = other ∧ ty = stringTy) := by
  change (if id = Api.root then some natTy else if id = other then some stringTy else none) = some ty at h
  by_cases h0 : id = Api.root
  · rw [if_pos h0] at h
    cases h
    exact Or.inl ⟨h0, rfl⟩
  · rw [if_neg h0] at h
    by_cases h1 : id = other
    · rw [if_pos h1] at h
      cases h
      exact Or.inr ⟨h1, rfl⟩
    · rw [if_neg h1] at h
      cases h

theorem theta {id : FiberId} {t : Nat} {ty : EffTy} (h : world.Θ id t = some ty) :
    (id = Api.root ∧ t = 0 ∧ ty = natTy) ∨ (id = other ∧ t = 1 ∧ ty = stringTy) := by
  change (if id = Api.root ∧ t = 0 then some natTy
    else if id = other ∧ t = 1 then some stringTy else none) = some ty at h
  by_cases h0 : id = Api.root ∧ t = 0
  · rw [if_pos h0] at h
    cases h
    exact Or.inl ⟨h0.1, h0.2, rfl⟩
  · rw [if_neg h0] at h
    by_cases h1 : id = other ∧ t = 1
    · rw [if_pos h1] at h
      cases h
      exact Or.inr ⟨h1.1, h1.2, rfl⟩
    · rw [if_neg h1] at h
      cases h

theorem valid : WorldValid natTy world machine := by
  have old := initial_world_valid_at natTy nativeServiceTy rootProgram 20 20 ⟨rfl, rfl⟩
  refine
    { ids := rfl, fibers := ?_, heap := old.heap, promises := old.promises,
      tokens := ?_, tokenBound := ?_, tokenTargets := ?_, state := rfl, wf := old.wf,
      cells := old.cells, fiberClosed := ?_, heapClosed := old.heapClosed,
      promiseClosed := old.promiseClosed, tokenClosed := ?_, root := rfl,
      timers := WakeTyped.empty _ _, waiters := ?_ }
  · intro id
    change (if id = Api.root then some natTy else if id = other then some stringTy else none).isSome = true ↔
      id ∈ [Api.root, other]
    rw [List.mem_cons, List.mem_singleton]
    by_cases h0 : id = Api.root
    · rw [if_pos h0]
      exact ⟨fun _ => Or.inl h0, fun _ => rfl⟩
    · rw [if_neg h0]
      by_cases h1 : id = other
      · rw [if_pos h1]
        exact ⟨fun _ => Or.inr h1, fun _ => rfl⟩
      · rw [if_neg h1]
        exact ⟨fun h => Bool.noConfusion h, fun h => (h.elim h0 h1).elim⟩
  · intro f hf t hp
    rcases member hf with rfl | rfl <;> cases hp
  · intro id t ty h
    rcases theta h with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
    · exact Nat.zero_lt_two
    · exact Nat.one_lt_two
  · intro id t ty h
    rcases theta h with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> rfl
  · intro id ty h
    rcases gamma h with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩
  · intro id t ty h
    rcases theta h with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact ⟨rfl, rfl⟩
  · intro key cell hc
    cases hc

theorem no_requests (id : FiberId) (t : Nat) : requestOfR machine id t = none := by
  unfold requestOfR
  cases hf : machine.fiber? id with
  | none => rfl
  | some f =>
    rcases member (List.mem_of_find?_eq_some hf) with rfl | rfl <;> rfl

theorem internalKeys_machine : Guard.internalKeys machine = [(Api.root, 0), (other, 1)] := rfl

theorem emptyPayload (w : W) (r : RaceR) (ty : EffTy) (token : w.Θ r.host r.token = some ty)
    (failures : r.state.failures = []) (winner : r.state.winner = none)
    (accepted : r.state.accepted = none) (cleanup : r.state.cleanup = none)
    (live : r.state.live = [])
    (programs : ∀ code ∈ r.programs, ∃ childTy, TypedProg (rootProgram : ProgramSource) w childTy code ∧
      Ty.subN childTy.answer ty.answer = true ∧ Ty.subN childTy.error ty.error = true) :
    RacePayload (rootProgram : ProgramSource) w r ty := by
  refine ⟨token, ?_, ?_, ?_, ?_, ?_, programs⟩
  · rw [failures]
    exact ⟨failureFits_of_cause (fun _ h => nomatch h) (fun _ h => nomatch h), fun _ h => nomatch h⟩
  · intro pair hp
    rw [winner] at hp
    cases hp
  · intro ex hx
    rw [accepted] at hx
    cases hx
  · intro wait hw
    rw [cleanup] at hw
    cases hw
  · intro id hi
    rw [live] at hi
    cases hi

theorem entrant_typed (w : W) : TypedProg (rootProgram : ProgramSource) w natTy entrant :=
  TypedProg.pure ⟨trivial, trivial⟩

theorem scheduler : SchedulerState machine := by
  constructor
  · decide +kernel
  · intro f hf
    rcases member hf with rfl | rfl <;> decide +kernel
  · decide +kernel
  · intro r hr
    rcases raceMember hr with rfl | rfl <;> decide +kernel
  · intro r hr
    rcases raceMember hr with rfl | rfl
    · exact ⟨fiber0, rfl⟩
    · exact ⟨fiber1, rfl⟩
  · intro key hk
    rw [internalKeys_machine, List.mem_cons, List.mem_singleton] at hk
    rcases hk with rfl | rfl <;> decide +kernel
  · intro id token request hr
    rw [no_requests] at hr
    cases hr
  · intro id token request hr
    rw [no_requests] at hr
    cases hr
  · intro f hf
    rcases member hf with rfl | rfl <;> rfl
  · intro f hf hp
    rcases member hf with rfl | rfl <;> exact False.elim (hp rfl)
  · intro f hf token hp
    rcases member hf with rfl | rfl <;> cases hp
  · intro f hf hx
    rcases member hf with rfl | rfl <;> cases hx
  · intro f hf hx
    rcases member hf with rfl | rfl <;> cases hx
  · intro f hf hd
    rcases member hf with rfl | rfl <;> cases hd
  · intro raceId r hr f hf o ho
    rcases member hf with rfl | rfl <;> cases ho
  · intro raceId r hr id hi
    rcases raceMember (List.mem_of_find?_eq_some hr) with rfl | rfl <;> cases hi
  · intro f hf p hp
    rcases member hf with rfl | rfl <;> cases hp
  · intro f hf o ho
    rcases member hf with rfl | rfl <;> cases ho

theorem typedState : TypedState (rootProgram : ProgramSource) natTy world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, scheduler, ⟨?_, ?_⟩, ?_⟩
  · intro f hf
    rcases member hf with rfl | rfl
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty _
        exact ⟨ty, .nil ty, provenance _ rfl rfl⟩
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup
        cases lookup
    · refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
      · intro ty _
        exact ⟨ty, .nil ty, provenance _ rfl rfl⟩
      · intro p hp; cases hp
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro v hv; cases hv
      · intro key value ty lookup
        change (Env.Context.empty : Env.Ctx).getV key = some value at lookup
        rw [Env.Context.getV_empty] at lookup
        cases lookup
  · intro r hr
    rcases raceMember hr with rfl | rfl
    · refine ⟨natTy, emptyPayload world race0 natTy rfl rfl rfl rfl rfl rfl ?_⟩
      intro code hc
      rw [List.mem_singleton.mp hc]
      exact ⟨natTy, entrant_typed world, Ty.subN_refl _, Ty.subN_refl _⟩
    · exact ⟨stringTy, emptyPayload world race1 stringTy rfl rfl rfl rfl rfl rfl (fun _ h => nomatch h)⟩
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩,
      (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    rcases member hf with rfl | rfl <;> cases hp
  · intro f hf p hp
    rcases member hf with rfl | rfl <;> cases hp
  · intro f hf o ho
    rcases member hf with rfl | rfl <;> cases ho
  · intro f hf r hm
    rcases member hf with rfl | rfl
    · change some 0 = some r at hm
      cases hm
      exact ⟨race0, natTy, rfl, rfl, rfl, natTy, rfl, .nil natTy, provenance _ rfl rfl⟩
    · change some 1 = some r at hm
      cases hm
      exact ⟨race1, stringTy, rfl, rfl, rfl, stringTy, rfl, .nil stringTy, provenance _ rfl rfl⟩

theorem machine_typed : MachineTyped (rootProgram : ProgramSource) natTy world machine := by
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩⟩
  intro f hf _ idle
  rcases member hf with rfl | rfl <;> cases idle

theorem config_typed : ConfigTyped (rootProgram : ProgramSource) natTy world machine commands := by
  refine ⟨machine_typed, ?_, ?_⟩
  · intro f _ _ reads
    obtain ⟨_, h⟩ := reads
    rcases h with h | h <;>
      simp only [commands, rest, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at h
  · refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      simp only [commands, rest, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> trivial
    · intro c hc
      simp only [commands, rest, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact ⟨race0, rfl, fiber0, rfl, rfl, rfl⟩
      · exact ⟨race1, rfl, fiber1, rfl, rfl, rfl⟩
      · exact ⟨race0, fiber0, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨race1, fiber1, rfl, rfl, rfl, rfl, rfl⟩
    · intro c hc
      simp only [commands, rest, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;> trivial
    · change ([Api.root, other] : List FiberId).Nodup
      decide +kernel
    · refine ⟨⟨false, ?_⟩, ⟨⟨false, ?_⟩, trivial, trivial, trivial⟩⟩
      · simp only [rest, List.mem_cons, reduceCtorEq, true_or, or_true]
      · simp only [List.mem_cons, true_or, or_true]
    · intro key hk
      change key ∈ ([] : List Guard.GuardKey) at hk
      cases hk
    · intro id token request _ hk
      change (id, token) ∈ ([] : List Guard.GuardKey) at hk
      cases hk
    · intro source exit observer hc
      simp only [commands, rest, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hc
    · intro r child hc
      simp only [commands, rest, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h | h | h
      · cases h
      · cases h
        trivial
      · cases h
      · cases h
    · intro host yielding race hc
      simp only [commands, rest, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hc
    · intro mode scope target interruptor extra hc
      simp only [commands, rest, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hc
    · intro source exit observer hc
      simp only [commands, rest, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hc

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.launch 0) rest

/-- The second race and stale enrollment are retained when child 2 appears. -/
theorem launched : ∃ a b g r0, result.1.fibers = [a, b, g] ∧ result.1.races = [r0, race1] ∧
    g.id = fresh ∧ g.exit = none ∧ g.running = false ∧ g.frame.current = entrant ∧ g.frame.stack = [] :=
  ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem retained_enroll : Cmd.enrollRace 1 fresh ∈ result.2 := by
  change Cmd.enrollRace 1 fresh ∈ [Cmd.evaluate fresh, Cmd.enrollRace 0 fresh, Cmd.launch 0,
    Cmd.enrollRace 1 fresh, Cmd.registrationDone 0 false, Cmd.registrationDone 1 false]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- The exact current obligation, with no extra premise and no predicate replacement. -/
theorem launch_false : ¬ StepPreserves (rootProgram : ProgramSource) natTy (.launch 0) := by
  intro step
  obtain ⟨w', ord, typed⟩ := step world machine rest rfl config_typed
  change ConfigTyped (rootProgram : ProgramSource) natTy w' result.1 result.2 at typed
  obtain ⟨a, b, g, r0, fibers, races, gid, gexit, grunning, gcurrent, gstack⟩ := launched
  have hg : g ∈ result.1.fibers := by
    rw [fibers]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have lookup : result.1.fiber? fresh = some g := by
    rw [← gid]
    exact rfiber?_of_mem typed.machine.typed.2.2.2.1.fiberIds hg
  have raceLookup : result.1.race? 1 = some race1 := rfl
  have enroll := typed.queue.enroll 1 fresh retained_enroll
  unfold EnrollRaceOk at enroll
  rw [raceLookup, lookup] at enroll
  obtain ⟨resultTy, payload, childTy, declared, below, _⟩ := enroll
  have pinned : w'.Θ other 1 = some stringTy := ord.1.2.2.2.2.2.1 other 1 stringTy rfl
  have token := payload.token
  change w'.Θ other 1 = some resultTy at token
  rw [pinned] at token
  cases token
  have saved := typed.machine.code g hg gexit grunning (by rw [gcurrent]; rfl) childTy declared
  obtain ⟨tin, code, stack, _⟩ := saved
  rw [gstack] at stack
  cases stack
  rw [gcurrent] at code
  have fits := (TypedProg.pure_inv code).1
  exact fits_subN w' below _ fits

#print axioms config_typed
#print axioms launch_false
end LaunchQueuedFuture
