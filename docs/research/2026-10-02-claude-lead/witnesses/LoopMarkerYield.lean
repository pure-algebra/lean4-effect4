import Effect4.Laws.Program.Typed.Commands.Registration

/-!
UNCOMPILED source-only falsifier candidate at 4c219956.
Concept 4: ConfigTyped closure; M6Ledger.step_loop, unchanged.
Reuses RegistrationColumn's input, with only scheduler-budget fields adjusted
and a loop head. No judgment or ledger statement is changed. Marker current
code remains exempt from ReadCode until the actual loop injects a yield wrapper.
The resulting saved success callback returns that untypable marker.
This constructed invariant input is not asserted reachable; no runtime,
progress, liveness, host, or full M6 correctness claim is made.
-/

set_option autoImplicit false

namespace LoopMarkerYield
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

#print axioms emptyPayload

def fiber : RFiber :=
  { RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx with
    running := true, currentOpCount := 0, maxOpsBeforeYield := 0, preventYield := false }

def race : Effect4.Program.Typed.RRace :=
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
    exact ⟨natTy, emptyPayload world race natTy rfl rfl rfl rfl rfl (fun _ h => nomatch h)
      (fun _ h => nomatch h)⟩
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

theorem config_typed : ConfigTyped (rootProgram : ProgramSource) natTy world machine
    [.loop Api.root false] := by
  refine ⟨machine_typed, ?_, ?_⟩
  · intro f hf _ _ hm
    rw [member hf] at hm
    change some 0 = none at hm
    cases hm
  · refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨fiber, rfl, rfl, rfl⟩
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
    · intro source exit observer member
      rw [List.mem_singleton] at member
      cases member

/-- The callback saved by the injected success guard. -/
def yieldNext (ex : ExitV) : RProgram := seqR (fun _ => marker) ex

/-- The body reached by evaluating the injected guard, before Yield itself runs. -/
def yieldCurrent : RProgram :=
  .vis (.inr (.yieldNow 0)) fun v =>
    .vis (.inr (.unguard (.success v))) yieldNext

def outputFiber : RFiber :=
  { countOp fiber with
    yieldOverride := none
    frame := { fiber.frame with
      current := yieldCurrent
      stack := [.resume .onSuccess yieldNext] } }

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) machine (.loop Api.root false) []

/-- Exact actual loop result; no model evaluator is substituted. -/
theorem result_eq : result =
    ((machine.emit [.yieldInjected Api.root 1]).update outputFiber,
      [.loop Api.root true]) := rfl

/-- Direct registration markers are deliberately outside TypedProg. -/
theorem marker_not_typed (w : W) (ty : EffTy) :
    ¬ TypedProg (rootProgram : ProgramSource) w ty marker := by
  intro h
  have absent := raceRegistrationR_typed h
  change some 0 = none at absent
  cases absent

/-- A typed injected yield body must type its real success-unit payload. -/
theorem yieldCurrent_unit {w : W} {ty : EffTy}
    (h : TypedProg (rootProgram : ProgramSource) w ty yieldCurrent) :
    ExitOk w ty (.success Val.unit) := by
  obtain ⟨_, _, next⟩ := TypedProg.fiber_inv h
    (fun _ he => nomatch he) (fun _ he => nomatch he)
    (fun _ he => nomatch he) (fun _ _ _ he => nomatch he)
  have unit := next w (leHost_refl w) Val.unit rfl
  exact unguard_payload_inv (rootProgram : ProgramSource) w ty
    (.success Val.unit) yieldNext unit

/-- The saved success arm would require typing the registration marker.
The intermediate type cannot avoid this obligation: the yield body proves
that the concrete unit success inhabits it. -/
theorem output_saved_false (w : W) (ty : EffTy) :
    ¬ SavedOk (TypedProg (rootProgram : ProgramSource)) ExitOk
      (frameProtocols (rootProgram : ProgramSource)) w ty outputFiber.frame := by
  intro saved
  obtain ⟨tin, code, stack, _⟩ := saved
  have payload : ExitOk w tin (.success Val.unit) := yieldCurrent_unit code
  change StackAccepts (TypedProg (rootProgram : ProgramSource)) ExitOk
    (frameProtocols (rootProgram : ProgramSource)) w tin ty
      [.resume .onSuccess yieldNext] at stack
  cases stack with
  | cons head tail =>
    cases head with
    | resume kind next run skip =>
      have impossible := run w (leHost_refl w) (.success Val.unit) payload rfl
      exact marker_not_typed w _ impossible

/-- The output is running with a queued loop and a non-marker head, so ReadCode
must type its saved frame. Unlike the input, there is no marker exemption. -/
theorem result_not_configTyped (w : W) :
    ¬ ConfigTyped (rootProgram : ProgramSource) natTy w result.1 result.2 := by
  intro typed
  have memberOut : outputFiber ∈ result.1.fibers := by
    rw [result_eq]
    exact List.mem_singleton_self _
  have reads : ReadsCode outputFiber.id result.2 := by
    refine ⟨true, Or.inl ?_⟩
    rw [result_eq]
    exact List.mem_singleton_self _
  have saved := typed.code outputFiber memberOut rfl reads rfl natTy
    typed.machine.wide.rootDeclared
  exact output_saved_false w natTy saved

/-- Proposed refutation of the unchanged ledger statement. UNCOMPILED. -/
theorem step_loop_false :
    ¬ StepPreserves (rootProgram : ProgramSource) natTy (.loop Api.root false) := by
  intro keeps
  obtain ⟨w', _, output⟩ := keeps world machine [] rfl config_typed
  exact result_not_configTyped w' output

#print axioms LoopMarkerYield.config_typed
#print axioms LoopMarkerYield.result_eq
#print axioms LoopMarkerYield.output_saved_false
#print axioms LoopMarkerYield.step_loop_false

end LoopMarkerYield
