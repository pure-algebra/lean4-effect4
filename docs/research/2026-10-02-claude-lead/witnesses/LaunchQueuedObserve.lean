import Test.Program.RegistrationColumn

/-!
# Falsifier: `M6Ledger.step_launch` with a queued `observe` naming the next fiber id

Checked at the head after decisions rows 134 (e) and 188 landed (`96415122`). The payload clause
of a queued `observe source exit o` (`RCmdOk`, `Typed/Residual.lean`'s generated bundle) reads
`∀ ty, Γ source = some ty → ExitOk ty exit`: vacuous while `source` is undeclared. A queued
`observe` whose source is the next unallocated fiber id is therefore admitted with any exit. The
race's launch allocates that id; the launch's own enrollment pins the child below the race's
`nat` column, so the retained observe's `"x"` exit fits no declaration of the child at any later
world. Same family as `E4-TYPED-CE-032` (a queued command naming a future fiber id); the bound
there covered only `enrollRace`. A constructed configuration: `observe` is queued only by the
source's own `finish` on reachable machines; no runtime claim.
-/

set_option autoImplicit false

namespace LaunchQueuedObserve
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

def rootProgram : NativeEff := .succeed (.lit (.nat 0))
def natTy : EffTy := EffTy.pure .nat

def marker : RProgram := .vis (.inr (.raceRegister 0)) Effects.Program.pure
theorem provenance (f : RSaved) (h1 : f.interruptedCause = none) (h2 : f.deferredInterrupt = false) :
    InterruptProvenance f := by
  refine ⟨fun c hc => ?_, fun hd => ?_⟩
  · rw [h1] at hc
    cases hc
  · rw [h2] at hd
    cases hd

theorem emptyPayload (w : W) (r : Effect4.Program.Typed.RRace) (ty : EffTy) (token : w.Θ r.host r.token = some ty)
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

def fiber : RFiber :=
  { RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx with
    running := true }

def entrant : RProgram := .pure (.success (.nat 0))

def race : Effect4.Program.Typed.RRace :=
  { id := 0, host := Api.root, token := 0, state := Supervision.RaceAllState.initial [],
    settled := false, programs := [entrant], registering := true }

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
      promiseClosed := old.promiseClosed, tokenClosed := ?_, root := old.root,
      timers := WakeTyped.empty _ _, waiters := fun _ _ h => by cases h }
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

theorem internalKeys_machine : Guard.internalKeys machine = [(Api.root, 0)] := rfl

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
    refine ⟨natTy, emptyPayload world race natTy rfl rfl rfl rfl rfl (fun _ h => nomatch h) ?_⟩
    intro code hc
    change code ∈ [entrant] at hc
    rw [List.mem_singleton.mp hc]
    exact ⟨natTy, TypedProg.pure ⟨trivial, trivial⟩, Ty.subN_refl _, subN_never _⟩
  · refine ⟨⟨(fun o ho => nomatch ho), (fun _ hp => nomatch hp)⟩,
      (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
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
      rw [List.mem_singleton.mp hk]
      exact Nat.zero_lt_one
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
    · intro f hf hx
      rw [member hf] at hx
      cases hx
    · intro f hf hd
      rw [member hf] at hd
      cases hd
    · intro raceId r hr f hf o ho
      rw [member hf] at ho
      cases ho
    · intro raceId r hr id hi
      have mem : r ∈ machine.races := List.mem_of_find?_eq_some hr
      change r ∈ [race] at mem
      rw [List.mem_singleton.mp mem] at hi
      cases hi
    · intro f hf p hp
      rw [member hf] at hp
      cases hp
    · intro f hf o ho
      rw [member hf] at ho
      cases ho
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
    exact ⟨race, natTy, rfl, rfl, rfl, natTy, rfl, .nil natTy, provenance _ rfl rfl⟩

theorem machine_typed : MachineTyped (rootProgram : ProgramSource) natTy world machine := by
  refine ⟨typedState, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩⟩
  intro f hf _ idle
  rw [member hf] at idle
  cases idle

def fresh : FiberId := ⟨1⟩
def obsExit : ExitV := .success (.str "x")
def rest : List RCmd := [.observe fresh obsExit (.untrackChild Api.root), .registrationDone 0 false]
def commands : List RCmd := .launch 0 :: rest

/-- The input: the race's marker current, one unlaunched entrant, and a queued `observe` whose
source is the next fiber id (its payload clause is vacuous: that id is undeclared). -/
theorem config_typed : ConfigTyped (rootProgram : ProgramSource) natTy world machine commands := by
  refine ⟨machine_typed, ?_, ?_⟩
  · intro f _ _ reads
    obtain ⟨_, r⟩ := reads
    rcases r with r | r <;>
      (change _ ∈ [Cmd.launch 0, Cmd.observe fresh obsExit (.untrackChild Api.root),
        Cmd.registrationDone 0 false] at r
       simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at r)
  · refine ⟨?_, ?_, ?_, ?_, ⟨⟨false, by simp only [rest, List.mem_cons, true_or, or_true]⟩,
      trivial, trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      change c ∈ [Cmd.launch 0, Cmd.observe fresh obsExit (.untrackChild Api.root),
        Cmd.registrationDone 0 false] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · trivial
      rcases List.mem_cons.mp hc with rfl | hc
      · intro ty declared
        change (initialWorld natTy).Γ fresh = some ty at declared
        cases declared
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro c hc
      change c ∈ [Cmd.launch 0, Cmd.observe fresh obsExit (.untrackChild Api.root),
        Cmd.registrationDone 0 false] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨race, rfl, fiber, rfl, rfl, rfl⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · trivial
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨race, fiber, rfl, rfl, rfl, rfl, rfl⟩
    · intro c hc
      change c ∈ [Cmd.launch 0, Cmd.observe fresh obsExit (.untrackChild Api.root),
        Cmd.registrationDone 0 false] at hc
      rcases List.mem_cons.mp hc with rfl | hc
      · trivial
      rcases List.mem_cons.mp hc with rfl | hc
      · trivial
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro k member
      change k ∈ ([] : List Guard.GuardKey) at member
      cases member
    · intro fiber token request _ member
      change (fiber, token) ∈ ([] : List Guard.GuardKey) at member
      cases member
    · intro source exit observer member
      change _ ∈ [Cmd.launch 0, Cmd.observe fresh obsExit (.untrackChild Api.root),
        Cmd.registrationDone 0 false] at member
      rcases List.mem_cons.mp member with h | h
      · cases h
      rcases List.mem_cons.mp h with h | h
      · cases h
        trivial
      rw [List.mem_singleton] at h
      cases h
    · intro race child member
      change _ ∈ [Cmd.launch 0, Cmd.observe fresh obsExit (.untrackChild Api.root),
        Cmd.registrationDone 0 false] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member
    · intro host yielding race member
      change _ ∈ [Cmd.launch 0, Cmd.observe fresh obsExit (.untrackChild Api.root),
        Cmd.registrationDone 0 false] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member
    · intro mode scope target interruptor extra member
      change _ ∈ [Cmd.launch 0, Cmd.observe fresh obsExit (.untrackChild Api.root),
        Cmd.registrationDone 0 false] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member
    · intro source exit observer member raceId race hr
      change _ ∈ [Cmd.launch 0, Cmd.observe fresh obsExit (.untrackChild Api.root),
        Cmd.registrationDone 0 false] at member
      rcases List.mem_cons.mp member with h | h
      · cases h
      rcases List.mem_cons.mp h with h | h
      · cases h
        intro hk
        cases hk
      rw [List.mem_singleton] at h
      cases h

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.launch 0) rest

/-- The actual launch: the child at the next id, the race's entrant consumed. -/
theorem launched : ∃ a g r0, result.1.fibers = [a, g] ∧ result.1.race? 0 = some r0 ∧
    r0.host = Api.root ∧ r0.token = 0 ∧ g.id = fresh :=
  ⟨_, _, _, rfl, rfl, rfl, rfl, rfl⟩

theorem queued : result.2 = [.evaluate fresh, .enrollRace 0 fresh, .launch 0,
    .observe fresh obsExit (.untrackChild Api.root), .registrationDone 0 false] := rfl

/-- **The frozen obligation is false**: no later world types the launch's result. -/
theorem launch_false : ¬ StepPreserves (rootProgram : ProgramSource) natTy (.launch 0) := by
  intro step
  obtain ⟨w', ord, typed⟩ := step world machine rest rfl config_typed
  change ConfigTyped (rootProgram : ProgramSource) natTy w' result.1 result.2 at typed
  obtain ⟨a, g, r0, fibers, raceLookup, host, token0, gid⟩ := launched
  have hg : g ∈ result.1.fibers := by
    rw [fibers]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have lookup : result.1.fiber? fresh = some g := by
    rw [← gid]
    exact rfiber?_of_mem typed.machine.typed.2.2.2.1.fiberIds hg
  have enrollMem : Cmd.enrollRace 0 fresh ∈ result.2 := by
    rw [queued]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have enroll := (typed.queue.enroll 0 fresh enrollMem).2
  rw [raceLookup, lookup] at enroll
  obtain ⟨resultTy, payload, childTy, declared, below, _⟩ := enroll
  have pinned : w'.Θ Api.root 0 = some natTy := ord.1.2.2.2.2.2.1 Api.root 0 natTy rfl
  have token := payload.token
  rw [host, token0, pinned] at token
  cases token
  have obsMem : Cmd.observe fresh obsExit (.untrackChild Api.root) ∈ result.2 := by
    rw [queued]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have observed := typed.queue.payload _ obsMem
  have exitOk : ExitOk w' childTy obsExit :=
    observed childTy (by rw [← gid]; exact declared)
  exact fits_subN w' below _ exitOk.1

end LaunchQueuedObserve

#print axioms LaunchQueuedObserve.config_typed
#print axioms LaunchQueuedObserve.launch_false
