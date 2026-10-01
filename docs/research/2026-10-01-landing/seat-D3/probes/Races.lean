import Effect4.Laws.Program.Typed.Edits
import Test.Counterexamples.Machine.Semantics.M6Capstone

/-!
Seat D3 refutation probe: `StepPreserves` for `registrationDone` and for `launch`
(`M6Ledger.step_registrationDone`, `M6Ledger.step_launch`) is false as stated.

* `registrationDone` (no buffered answer, no deferred interrupt): the host parks on the race's
  token with a `void` pending record (`Machine/Fibers.lean:1925-1929`). A stored countdown
  observer on that same key, `(host, token)`, which `I` allows (with no pending record at the
  waiter `CountdownAt` holds vacuously; the scheduler clauses read keys only as below the counter
  and unrequested), then reads the new record: `CountdownPayload` demands the token declared at
  `void`, and it is declared at the race's type, `number`.
* `launch`: the entrant is spawned at the next fiber id (`spawn`, `:948-966`). A second race whose
  live set already names that id, which `I` allows (`RacePayload.live` reads only declared fibers),
  then constrains the new fiber: its declared columns must sit below that race's type (`string`),
  while its code, `succeed 0`, is typed only at a number.

Run: `LEAN_NUM_THREADS=2 lake env lean docs/research/2026-10-01-landing/seat-D3/probes/Races.lean`.
-/

namespace Effect4.Program.Typed.SeatD3.Races
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

def rootProgram : NativeEff := .succeed (.lit (.nat 0))
def natTy : EffTy := EffTy.pure .nat
def unitTy : EffTy := EffTy.pure .unit
def stringTy : EffTy := EffTy.pure .string

def marker : RProgram := .vis (.inr (.raceRegister 0)) Effects.Program.pure
theorem provenance (f : RSaved) (h1 : f.interruptedCause = none) (h2 : f.deferredInterrupt = false) :
    InterruptProvenance f := by
  refine ⟨fun c hc => ?_, fun hd => ?_⟩
  · rw [h1] at hc
    cases hc
  · rw [h2] at hd
    cases hd

theorem emptyPayload (w : W) (r : RRace) (ty : EffTy) (token : w.Θ r.host r.token = some ty)
    (failures : r.state.failures = []) (winner : r.state.winner = none)
    (accepted : r.state.accepted = none) (cleanup : r.state.cleanup = none)
    (live : ∀ id ∈ r.state.live, ∀ childTy, w.Γ id = some childTy →
      Ty.subN childTy.answer ty.answer = true ∧ Ty.subN childTy.error ty.error = true)
    (programs : ∀ code ∈ r.programs, ∃ childTy, TypedProg (rootProgram : ProgramSource) w childTy code ∧
      Ty.subN childTy.answer ty.answer = true ∧ Ty.subN childTy.error ty.error = true) :
    RacePayload (rootProgram : ProgramSource) w r ty := by
  refine ⟨token, ?_, fun pair hp => ?_, fun e he => ?_, fun wait hw => ?_, live, programs⟩
  · rw [failures]
    exact ⟨failureFits_of_cause (fun _ h => nomatch h) (fun _ h => nomatch h),
      (fun _ h => nomatch h)⟩
  · rw [winner] at hp
    cases hp
  · rw [accepted] at he
    cases he
  · rw [cleanup] at hw
    cases hw

/-! ## `registrationDone` -/

namespace Registration

def fiber : RFiber :=
  { RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx with
    running := true, observers := [.countdown Api.root 0] }

def race : RRace :=
  { id := 0, host := Api.root, token := 0, state := Supervision.RaceAllState.initial [],
    settled := false, programs := [], registering := true }

def machine : RState :=
  { loadR rootProgram 20 20 with fibers := [fiber], races := [race], nextToken := 1, nextRace := 1 }

def world : W :=
  { initialWorld natTy with Θ := fun id t => if id = Api.root ∧ t = 0 then some natTy else none }

theorem member {f : RFiber} (hf : f ∈ machine.fibers) : f = fiber := by
  change f ∈ [fiber] at hf
  exact List.mem_singleton.mp hf

theorem theta {id : FiberId} {t : Nat} {ty : EffTy} (h : world.Θ id t = some ty) :
    id = Api.root ∧ t = 0 ∧ ty = natTy := by
  change (if id = Api.root ∧ t = 0 then some natTy else none) = some ty at h
  by_cases c : id = Api.root ∧ t = 0
  · rw [if_pos c] at h
    cases h
    exact ⟨c.1, c.2, rfl⟩
  · rw [if_neg c] at h
    cases h

theorem valid : WorldValid natTy world machine := by
  have old := initial_world_valid_at natTy nativeServiceTy rootProgram 20 20 ⟨rfl, rfl⟩
  refine
    { ids := rfl, fibers := old.fibers, heap := old.heap, promises := old.promises,
      tokens := ?_, tokenBound := ?_, tokenTargets := ?_, state := rfl, wf := old.wf,
      cells := old.cells, fiberClosed := old.fiberClosed, heapClosed := old.heapClosed,
      promiseClosed := old.promiseClosed, tokenClosed := ?_, root := old.root }
  · intro f hf token hp
    rw [member hf] at hp
    cases hp
  · intro id token ty h
    obtain ⟨_, rfl, _⟩ := theta h
    exact Nat.zero_lt_one
  · intro id token ty h
    obtain ⟨rfl, _, _⟩ := theta h
    rfl
  · intro id token ty h
    obtain ⟨_, _, rfl⟩ := theta h
    exact ⟨rfl, rfl⟩

theorem no_requests (id : FiberId) (token : Nat) : requestOfR machine id token = none := by
  unfold requestOfR
  cases hf : machine.fiber? id with
  | none => rfl
  | some found =>
    rw [member (List.mem_of_find?_eq_some hf)]
    rfl

theorem internalKeys_machine : Guard.internalKeys machine = [(Api.root, 0), (Api.root, 0)] := rfl

theorem typedState : TypedState (rootProgram : ProgramSource) natTy world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro f hf
    rw [member hf]
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
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
    change r ∈ [race] at hr
    rw [List.mem_singleton.mp hr]
    exact ⟨natTy, emptyPayload world race natTy rfl rfl rfl rfl rfl (fun _ h => nomatch h)
      (fun _ h => nomatch h)⟩
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    rw [member hf] at hp
    cases hp
  · constructor
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro f hf
      rw [member hf]
      exact Nat.zero_lt_one
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro r hr
      change r ∈ [race] at hr
      rw [List.mem_singleton.mp hr]
      exact Nat.zero_lt_one
    · intro r hr
      change r ∈ [race] at hr
      rw [List.mem_singleton.mp hr]
      exact ⟨fiber, rfl⟩
    · intro key hk
      rw [internalKeys_machine] at hk
      rcases List.mem_cons.mp hk with h | h
      · rw [h]; exact Nat.zero_lt_one
      · rw [List.mem_singleton.mp h]; exact Nat.zero_lt_one
    · intro id token request hr
      rw [no_requests] at hr
      cases hr
    · intro id token request hr
      rw [no_requests] at hr
      cases hr
    · intro f hf
      rw [member hf]
      rfl
    · intro f hf hp
      rw [member hf] at hp
      exact False.elim (hp rfl)
    · intro f hf token hp
      rw [member hf] at hp
      cases hp
    · intro f hf hx
      rw [member hf] at hx
      cases hx
    · intro f hf hd
      rw [member hf] at hd
      cases hd
  · intro f hf p hp
    rw [member hf] at hp
    cases hp
  · intro f hf o ho
    rw [member hf] at ho ⊢
    rw [List.mem_singleton.mp ho]
    exact trivial
  · intro f hf raceId hm
    rw [member hf] at hm ⊢
    change some 0 = some raceId at hm
    cases hm
    exact ⟨race, natTy, rfl, rfl, rfl, natTy, rfl, .nil natTy, provenance _ rfl rfl⟩

theorem machine_typed : MachineTyped (rootProgram : ProgramSource) natTy world machine := by
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩⟩
  intro f hf _ idle
  rw [member hf] at idle
  cases idle

theorem config_typed : ConfigTyped (rootProgram : ProgramSource) natTy world machine
    [.registrationDone 0 false] := by
  refine ⟨machine_typed, ?_, ?_⟩
  · intro f _ _ reads
    obtain ⟨_, r⟩ := reads
    rcases r with r | r <;> (rw [List.mem_singleton] at r; cases r)
  · refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨race, fiber, rfl, rfl, rfl, rfl, rfl⟩
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

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.registrationDone 0 false) []

/-- The host after the step: parked on the race's token with a `void` record, its stale
countdown observer still stored. -/
theorem parked : ∃ g, result.1.fibers = [g] ∧ result.1.fiber? Api.root = some g ∧ g.id = Api.root ∧
    g.pending = [⟨0, none, [], [], .void, false⟩] ∧ g.observers = [.countdown Api.root 0] :=
  ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- **`registrationDone` does not keep `I`.** -/
theorem registrationDone_false :
    ¬ StepPreserves (rootProgram : ProgramSource) natTy (.registrationDone 0 false) := by
  intro step
  obtain ⟨w', ord, typed⟩ := step world machine [] rfl config_typed
  obtain ⟨g, fibers, look, gid, pending, observers⟩ := parked
  have hg : g ∈ result.1.fibers := by rw [fibers]; exact List.mem_singleton_self _
  have stored := typed.machine.typed.2.2.2.2.1.2 g hg (.countdown Api.root 0)
    (by rw [observers]; exact List.mem_singleton_self _)
  have stored' : CountdownAt w' result.1 Api.root 0 (FiberColumnsBelow w' g.id) := stored
  unfold CountdownAt at stored'
  rw [look] at stored'
  dsimp only at stored'
  rw [pending] at stored'
  obtain ⟨_, _, tokenTy, payload, _⟩ := stored'
  have declared := payload.token
  have pinned : w'.Θ Api.root 0 = some natTy := ord.1.2.2.2.2.2.1 Api.root 0 natTy rfl
  change w'.Θ Api.root 0 = some tokenTy at declared
  rw [pinned] at declared
  cases declared
  have resume := payload.resume
  change natTy = EffTy.pure .unit at resume
  cases resume

end Registration

/-! ## `launch` -/

namespace Launch

def entrant : RProgram := .pure (.success (.nat 0))

def fiber : RFiber :=
  { RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx with running := true }

/-- The race being launched: one unlaunched entrant, typed at its number. -/
def race0 : RRace :=
  { id := 0, host := Api.root, token := 0, state := Supervision.RaceAllState.initial [],
    settled := false, programs := [entrant], registering := true }

/-- A second race whose live set names the next fiber id, not yet a fiber. -/
def race1 : RRace :=
  { id := 1, host := Api.root, token := 1,
    state := { Supervision.RaceAllState.initial [] with live := [⟨1⟩] },
    settled := false, programs := [], registering := false }

def machine : RState :=
  { loadR rootProgram 20 20 with
    fibers := [fiber], races := [race0, race1], nextToken := 2, nextRace := 2 }

def world : W :=
  { initialWorld natTy with
    Θ := fun id t => if id = Api.root ∧ t = 0 then some natTy
      else if id = Api.root ∧ t = 1 then some stringTy else none }

theorem member {f : RFiber} (hf : f ∈ machine.fibers) : f = fiber := by
  change f ∈ [fiber] at hf
  exact List.mem_singleton.mp hf

theorem theta {id : FiberId} {t : Nat} {ty : EffTy} (h : world.Θ id t = some ty) :
    id = Api.root ∧ ((t = 0 ∧ ty = natTy) ∨ (t = 1 ∧ ty = stringTy)) := by
  change (if id = Api.root ∧ t = 0 then some natTy
    else if id = Api.root ∧ t = 1 then some stringTy else none) = some ty at h
  by_cases c0 : id = Api.root ∧ t = 0
  · rw [if_pos c0] at h
    cases h
    exact ⟨c0.1, Or.inl ⟨c0.2, rfl⟩⟩
  · rw [if_neg c0] at h
    by_cases c1 : id = Api.root ∧ t = 1
    · rw [if_pos c1] at h
      cases h
      exact ⟨c1.1, Or.inr ⟨c1.2, rfl⟩⟩
    · rw [if_neg c1] at h
      cases h

theorem valid : WorldValid natTy world machine := by
  have old := initial_world_valid_at natTy nativeServiceTy rootProgram 20 20 ⟨rfl, rfl⟩
  refine
    { ids := rfl, fibers := old.fibers, heap := old.heap, promises := old.promises,
      tokens := ?_, tokenBound := ?_, tokenTargets := ?_, state := rfl, wf := old.wf,
      cells := old.cells, fiberClosed := old.fiberClosed, heapClosed := old.heapClosed,
      promiseClosed := old.promiseClosed, tokenClosed := ?_, root := old.root }
  · intro f hf token hp
    rw [member hf] at hp
    cases hp
  · intro id token ty h
    obtain ⟨_, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := theta h
    · exact Nat.zero_lt_two
    · exact Nat.one_lt_two
  · intro id token ty h
    obtain ⟨rfl, _⟩ := theta h
    rfl
  · intro id token ty h
    obtain ⟨_, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ := theta h
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

theorem no_requests (id : FiberId) (token : Nat) : requestOfR machine id token = none := by
  unfold requestOfR
  cases hf : machine.fiber? id with
  | none => rfl
  | some found =>
    rw [member (List.mem_of_find?_eq_some hf)]
    rfl

theorem internalKeys_machine : Guard.internalKeys machine = [(Api.root, 0), (Api.root, 1)] := rfl

theorem entrant_typed (w : W) : TypedProg (rootProgram : ProgramSource) w natTy entrant :=
  TypedProg.pure ⟨trivial, trivial⟩

theorem typedState : TypedState (rootProgram : ProgramSource) natTy world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro f hf
    rw [member hf]
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
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
    change r ∈ [race0, race1] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine ⟨natTy, emptyPayload world race0 natTy rfl rfl rfl rfl rfl (fun _ h => nomatch h) ?_⟩
      intro code hc
      rw [List.mem_singleton.mp hc]
      exact ⟨natTy, entrant_typed world, Ty.subN_refl _, Ty.subN_refl _⟩
    · rw [List.mem_singleton.mp hr]
      refine ⟨stringTy, emptyPayload world race1 stringTy rfl rfl rfl rfl rfl ?_
        (fun _ h => nomatch h)⟩
      intro id hid childTy declared
      rw [List.mem_singleton.mp hid] at declared
      change (tableInsert (fun _ => none) Api.root natTy ⟨1⟩) = some childTy at declared
      simp only [tableInsert] at declared
      cases declared
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v hv => nomatch hv)⟩, (fun v hv => nomatch hv), trivial⟩
  · intro f hf token hp
    rw [member hf] at hp
    cases hp
  · constructor
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro f hf
      rw [member hf]
      exact Nat.zero_lt_one
    · decide
    · intro r hr
      change r ∈ [race0, race1] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact Nat.zero_lt_two
      · rw [List.mem_singleton.mp hr]
        exact Nat.one_lt_two
    · intro r hr
      change r ∈ [race0, race1] at hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨fiber, rfl⟩
      · rw [List.mem_singleton.mp hr]
        exact ⟨fiber, rfl⟩
    · intro key hk
      rw [internalKeys_machine] at hk
      rcases List.mem_cons.mp hk with h | h
      · rw [h]; exact Nat.zero_lt_two
      · rw [List.mem_singleton.mp h]; exact Nat.one_lt_two
    · intro id token request hr
      rw [no_requests] at hr
      cases hr
    · intro id token request hr
      rw [no_requests] at hr
      cases hr
    · intro f hf
      rw [member hf]
      rfl
    · intro f hf hp
      rw [member hf] at hp
      exact False.elim (hp rfl)
    · intro f hf token hp
      rw [member hf] at hp
      cases hp
    · intro f hf hx
      rw [member hf] at hx
      cases hx
    · intro f hf hd
      rw [member hf] at hd
      cases hd
  · intro f hf p hp
    rw [member hf] at hp
    cases hp
  · intro f hf o ho
    rw [member hf] at ho
    cases ho
  · intro f hf raceId hm
    rw [member hf] at hm ⊢
    change some 0 = some raceId at hm
    cases hm
    exact ⟨race0, natTy, rfl, rfl, rfl, natTy, rfl, .nil natTy, provenance _ rfl rfl⟩

theorem machine_typed : MachineTyped (rootProgram : ProgramSource) natTy world machine := by
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩⟩
  intro f hf _ idle
  rw [member hf] at idle
  cases idle

theorem config_typed : ConfigTyped (rootProgram : ProgramSource) natTy world machine
    [.launch 0, .registrationDone 0 false] := by
  refine ⟨machine_typed, ?_, ?_⟩
  · intro f _ _ reads
    obtain ⟨_, r⟩ := reads
    rcases r with r | r <;>
      (simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at r)
  · refine ⟨?_, ?_, ?_, ?_, ⟨⟨false, List.mem_singleton_self _⟩, trivial, trivial⟩, ⟨?_, ?_⟩,
      ?_, ?_, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> trivial
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨race0, rfl, fiber, rfl, rfl, rfl⟩
      · exact ⟨race0, fiber, rfl, rfl, rfl, rfl, rfl⟩
    · intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> trivial
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro k member
      simp only [List.flatMap_cons, List.flatMap_nil, Guard.commandKeys, List.append_nil,
        List.not_mem_nil] at member
    · intro fiber token request _ member
      simp only [List.flatMap_cons, List.flatMap_nil, Guard.commandKeys, List.append_nil,
        List.not_mem_nil] at member
    · intro source exit observer member
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member
    · intro race child member
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member
    · intro host yielding race member
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member
    · intro mode scope target interruptor extra member
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.launch 0) [.registrationDone 0 false]

/-- After the launch: the entrant is a fiber at id 1, idle, unexited, its code the entrant over
the empty stack; the second race is unchanged. -/
theorem launched : ∃ a g r0, result.1.fibers = [a, g] ∧ result.1.races = [r0, race1] ∧
    g.id = ⟨1⟩ ∧ g.exit = none ∧ g.running = false ∧ g.frame.current = entrant ∧
    g.frame.stack = [] :=
  ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`launch` does not keep `I`.** -/
theorem launch_false : ¬ StepPreserves (rootProgram : ProgramSource) natTy (.launch 0) := by
  intro step
  obtain ⟨w', ord, typed⟩ := step world machine [.registrationDone 0 false] rfl config_typed
  obtain ⟨a, g, r0, fibers, races, gid, gexit, grunning, gcurrent, gstack⟩ := launched
  have wide := typed.machine.wide
  have hg : g ∈ result.1.fibers := by rw [fibers]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain ⟨cty, declared⟩ := Option.isSome_iff_exists.mp
    ((wide.fibers g.id).mpr (List.mem_map_of_mem hg))
  have hr : race1 ∈ result.1.races := by rw [races]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  obtain ⟨resultTy, payload⟩ := wide.races race1 hr
  have pinned : w'.Θ Api.root 1 = some stringTy := ord.1.2.2.2.2.2.1 Api.root 1 stringTy rfl
  have token := payload.token
  change w'.Θ Api.root 1 = some resultTy at token
  rw [pinned] at token
  cases token
  have below := (payload.live ⟨1⟩ (List.mem_singleton_self _) cty (by rw [← gid]; exact declared)).1
  have saved := typed.machine.code g hg gexit grunning (by rw [gcurrent]; rfl) cty declared
  obtain ⟨tin, code, stack, _⟩ := saved
  rw [gstack] at stack
  cases stack
  rw [gcurrent] at code
  have fits := (TypedProg.pure_inv code).1
  exact fits_subN w' below _ fits

end Launch

end Effect4.Program.Typed.SeatD3.Races

#print axioms Effect4.Program.Typed.SeatD3.Races.Registration.config_typed
#print axioms Effect4.Program.Typed.SeatD3.Races.Registration.registrationDone_false
#print axioms Effect4.Program.Typed.SeatD3.Races.Launch.config_typed
#print axioms Effect4.Program.Typed.SeatD3.Races.Launch.launch_false
