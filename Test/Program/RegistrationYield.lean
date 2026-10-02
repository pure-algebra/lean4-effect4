import Effect4.Laws.Program.Typed.Commands.Registration

/-!
# Test.Program.RegistrationYield — a registration marker under an injected yield

Placement: semantics Concept 4 (the configuration invariant `I`), question `M6Ledger.step_loop`;
decisions row 188 (b), `E4-TYPED-CE-033`. The historical refutation is pinned unchanged at
`docs/research/2026-10-02-claude-lead/witnesses/LoopMarkerYield.lean` (checked at `53caad0f`):
`beginRace` leaves a race's registration marker current with `loop` queued; at a reached budget
`injectYield` saves the marker in a success callback around `Yield`, where `ReadCode`'s
current-marker exemption no longer applies and no frame types the callback.

Row 188 (b) types a host stack as a path with correlated registration arrows (`HostStack`), the
reply consumers read it (`StackReply`), and the generated position clause reads its machine-free
shape (`PositionStack`). This battery copies the witness's input and its exact step, and adds the
two adjacent cases Codex's review raised before landing:

1. `config_typed`, `result_eq`, `output_not_saved`: the input is typed, the actual loop result is
   the injected wrapper's output, and that output frame is still no `SavedOk` at any world (the
   historical refutation's core, kept).
2. `Single.result_typed`: the output is a typed configuration at the same world, the callback
   a registration arrow at the race token's `nat`.
3. `Interrupt.result_typed`: typed code above a stored callback (`interruptAll []`) pushes its
   answer slot and queues `afterInterrupt`, whose reply stack (`StackReply`) carries the arrow.
4. `Double.result_typed`: a marker current over a stored callback is injected again; the two
   callbacks compose as two arrows.

Constructed-configuration controls; no reachability, progress or `step_loop` claim.
-/

set_option autoImplicit false

namespace Test.Program.RegistrationYield
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

/-- **The historical core, kept**: the output frame is no `SavedOk` at any world and type. -/
theorem output_not_saved (w : W) (ty : EffTy) :
    ¬ SavedOk (TypedProg (rootProgram : ProgramSource)) ExitOk
      (frameProtocols (rootProgram : ProgramSource)) w ty outputFiber.frame :=
  output_saved_false w ty

/-! ## One root fiber over the witness's race and world -/

/-- The witness's root fiber with a chosen current code, stack and op count. -/
def baseOf (c : RProgram) : RFiber := RunFiber.make Api.root c true (stores.budgetOf emptyCtx) emptyCtx

def fiberOf (c : RProgram) (s : List ScopeFrame) (n : Nat) : RFiber :=
  { baseOf c with
    running := true, currentOpCount := n, maxOpsBeforeYield := 0, preventYield := false,
    frame := { (baseOf c).frame with stack := s } }

def machineOf (g : RFiber) : RState :=
  { loadR rootProgram 20 20 with fibers := [g], races := [race], nextToken := 1, nextRace := 1 }

section Fixture
variable (c : RProgram) (s : List ScopeFrame) (n : Nat)

theorem member_of {f : RFiber} (hf : f ∈ (machineOf (fiberOf c s n)).fibers) : f = fiberOf c s n := by
  change f ∈ [fiberOf c s n] at hf
  exact List.mem_singleton.mp hf

theorem valid_of : WorldValid natTy world (machineOf (fiberOf c s n)) := by
  have old := initial_world_valid_at natTy nativeServiceTy rootProgram 20 20 ⟨rfl, rfl⟩
  refine
    { ids := rfl, fibers := old.fibers, heap := old.heap, promises := old.promises,
      tokens := ?_, tokenBound := ?_, tokenTargets := ?_, state := rfl, wf := old.wf,
      cells := old.cells, fiberClosed := old.fiberClosed, heapClosed := old.heapClosed,
      promiseClosed := old.promiseClosed, tokenClosed := ?_, root := old.root,
      timers := WakeTyped.empty _ _, waiters := fun _ _ h => by cases h }
  · intro f hf token hp
    rw [member_of c s n hf] at hp
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

theorem no_requests_of (id : FiberId) (token : Nat) :
    requestOfR (machineOf (fiberOf c s n)) id token = none := by
  unfold requestOfR
  cases hf : (machineOf (fiberOf c s n)).fiber? id with
  | none => rfl
  | some found =>
    rw [member_of c s n (List.mem_of_find?_eq_some hf)]
    rfl

theorem internalKeys_of : Guard.internalKeys (machineOf (fiberOf c s n)) = [(Api.root, 0)] := rfl

/-- The typed state of the one-fiber machine, given its stack's position path and its marker's
registration reply stack. -/
theorem typedState_of
    (position : ∀ ty, ∃ tin, PositionStack (rootProgram : ProgramSource) world tin ty s)
    (registration : ∀ raceId, raceRegistrationR c = some raceId → raceId = 0 ∧
      HostStack (rootProgram : ProgramSource) world (machineOf (fiberOf c s n)) Api.root natTy natTy s) :
    TypedState (rootProgram : ProgramSource) natTy world (machineOf (fiberOf c s n)) := by
  refine ⟨valid_of c s n, ⟨?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro f hf
    rw [member_of c s n hf]
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty _
      obtain ⟨tin, path⟩ := position ty
      exact ⟨tin, path, provenance _ rfl rfl⟩
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
    rw [member_of c s n hf] at hp
    cases hp
  · constructor
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro f hf
      rw [member_of c s n hf]
      exact Nat.zero_lt_one
    · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
    · intro r hr
      change r ∈ [race] at hr
      rw [List.mem_singleton.mp hr]
      exact Nat.zero_lt_one
    · intro r hr
      change r ∈ [race] at hr
      rw [List.mem_singleton.mp hr]
      exact ⟨fiberOf c s n, rfl⟩
    · intro key hk
      rw [internalKeys_of c s n] at hk
      rw [List.mem_singleton.mp hk]
      exact Nat.zero_lt_one
    · intro id token request hr
      rw [no_requests_of c s n] at hr
      cases hr
    · intro id token request hr
      rw [no_requests_of c s n] at hr
      cases hr
    · intro f hf
      rw [member_of c s n hf]
      rfl
    · intro f hf hp
      rw [member_of c s n hf] at hp
      exact False.elim (hp rfl)
    · intro f hf token hp
      rw [member_of c s n hf] at hp
      cases hp
    · intro f hf hx
      rw [member_of c s n hf] at hx
      cases hx
    · intro f hf hx
      rw [member_of c s n hf] at hx
      cases hx
    · intro f hf hd
      rw [member_of c s n hf] at hd
      cases hd
    · intro raceId r hr f hf o ho
      rw [member_of c s n hf] at ho
      cases ho
    · intro raceId r hr id hi
      have mem : r ∈ (machineOf (fiberOf c s n)).races := List.mem_of_find?_eq_some hr
      change r ∈ [race] at mem
      rw [List.mem_singleton.mp mem] at hi
      cases hi
    · intro f hf p hp
      rw [member_of c s n hf] at hp
      cases hp
    · intro f hf o ho
      rw [member_of c s n hf] at ho
      cases ho
  · intro f hf p hp
    rw [member_of c s n hf] at hp
    cases hp
  · intro f hf o ho
    rw [member_of c s n hf] at ho
    cases ho
  · intro f hf raceId hm
    rw [member_of c s n hf] at hm ⊢
    obtain ⟨rfl, stack⟩ := registration raceId hm
    exact ⟨race, natTy, rfl, rfl, rfl, natTy, rfl, stack, provenance _ rfl rfl⟩

theorem machineTyped_of'
    (position : ∀ ty, ∃ tin, PositionStack (rootProgram : ProgramSource) world tin ty s)
    (registration : ∀ raceId, raceRegistrationR c = some raceId → raceId = 0 ∧
      HostStack (rootProgram : ProgramSource) world (machineOf (fiberOf c s n)) Api.root natTy natTy s) :
    MachineTyped (rootProgram : ProgramSource) natTy world (machineOf (fiberOf c s n)) := by
  refine ⟨typedState_of c s n position registration, rfl, ?_, ⟨rfl, fun o ho => nomatch ho⟩⟩
  intro f hf _ idle
  rw [member_of c s n hf] at idle
  cases idle

/-- The queue `[loop root b]`, its code read through `CodeOk` (or exempt at a marker). -/
theorem config_loop (b : Bool) (machine : MachineTyped (rootProgram : ProgramSource) natTy world
      (machineOf (fiberOf c s n)))
    (code : raceRegistrationR c = none →
      CodeOk (rootProgram : ProgramSource) world (machineOf (fiberOf c s n)) Api.root natTy
        (fiberOf c s n).frame) :
    ConfigTyped (rootProgram : ProgramSource) natTy world (machineOf (fiberOf c s n))
      [.loop Api.root b] := by
  refine ⟨machine, ?_, ?_⟩
  · intro f hf _ _ hm ty declared
    rw [member_of c s n hf] at hm declared ⊢
    change world.Γ Api.root = some ty at declared
    rw [(valid_of c s n).root] at declared
    cases declared
    exact code hm
  · refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro c' hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro c' hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨fiberOf c s n, rfl, rfl, rfl⟩
    · intro c' hc
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

end Fixture

/-- The registration arrow of the witness's callback, from `tin` to the race token's `nat`. -/
theorem arrow {tin final : EffTy} {m : RState} {s : List ScopeFrame} (found : m.race? 0 = some race)
    (errors : tin.error = natTy.error)
    (rest : HostStack (rootProgram : ProgramSource) world m Api.root natTy final s) :
    HostStack (rootProgram : ProgramSource) world m Api.root tin final
      (.resume .onSuccess yieldNext :: s) :=
  .cons (.inr (.mk (fun _ => rfl) (fun _ _ _ hc => strongExit_failure_of_error errors hc) found rfl rfl))
    rest

/-- The position skip from a `never`-error type to any type. -/
theorem neverSkip {tin : EffTy} (errors : tin.error = Ty.never) (ty : EffTy) :
    ∀ w', world.leHost w' → ∀ c, ExitOk w' tin (.failure c) → ExitOk w' ty (.failure c) :=
  fun _ _ _ hc => exitOk_failure_of_errorN (by rw [errors]; exact subN_never _) hc

/-- The witness's callback as an answer slot's neighbour: `interruptAll`'s unit answer slot. -/
def iaNext : ExitV → RProgram := seqR fun v => .pure (.success v)

theorem iaSlot (w : W) : FrameAccepts (TypedProg (rootProgram : ProgramSource)) ExitOk
    (frameProtocols (rootProgram : ProgramSource)) w (EffTy.pure .unit) (EffTy.pure .unit)
    (.answer iaNext) :=
  .answer iaNext fun _ _ ex hex => by
    cases ex with
    | success v => exact TypedProg.pure hex
    | failure c => exact TypedProg.pure hex

/-- The injected `Yield` body is typed at `unit`: `Yield` answers `unit`, and the closing marker
carries it. -/
theorem yieldCurrent_typed (w : W) :
    TypedProg (rootProgram : ProgramSource) w (EffTy.pure .unit) yieldCurrent :=
  TypedProg.fiber (op := .yieldNow 0) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => by
      change ans = Val.unit at post
      subst post
      exact TypedProg.unguard (ty := EffTy.pure .unit) ⟨trivial, trivial⟩)

/-! ### 1. The witness's single injected yield -/

namespace Single

def out : RFiber := fiberOf yieldCurrent [.resume .onSuccess yieldNext] 1

theorem out_eq : outputFiber = out := rfl

theorem output_typed : ConfigTyped (rootProgram : ProgramSource) natTy world (machineOf out)
    [.loop Api.root true] :=
  config_loop yieldCurrent _ 1 true
    (machineTyped_of' yieldCurrent _ 1
      (fun ty => ⟨EffTy.pure .unit, .cons (.inr (.mk (fun _ => rfl) (neverSkip rfl ty))) (.nil ty)⟩)
      (fun _ hm => by cases hm))
    (fun _ => ⟨EffTy.pure .unit, yieldCurrent_typed world, arrow rfl rfl (.nil natTy),
      provenance _ rfl rfl⟩)

/-- **The repaired step**: the actual loop result is a typed configuration at the input's world. -/
theorem result_typed : ∃ w', world.leHost w' ∧
    ConfigTyped (rootProgram : ProgramSource) natTy w' result.1 result.2 := by
  refine ⟨world, leHost_refl world, ?_⟩
  rw [result_eq, out_eq]
  exact configTyped_congr (m := machineOf out) rfl rfl rfl rfl rfl rfl rfl output_typed

end Single

/-! ### 2. Typed code above a stored callback (Codex's adjacent case) -/

namespace Interrupt

def iaCode : RProgram := fiberValR (.interruptAll [] none) rfl

theorem iaCode_typed (w : W) :
    TypedProg (rootProgram : ProgramSource) w (EffTy.pure .unit) iaCode :=
  TypedProg.fiber (op := .interruptAll [] none) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial (fun w' _ ans post => by
      change ans = Val.unit at post
      subst post
      exact TypedProg.pure (ty := EffTy.pure .unit) ⟨trivial, trivial⟩)

def input : RFiber := fiberOf iaCode [.resume .onSuccess yieldNext] 0

/-- The input: `interruptAll []` typed at `unit` over a stored registration callback, with the
latch set so no yield is injected. -/
theorem config_typed : ConfigTyped (rootProgram : ProgramSource) natTy world (machineOf input)
    [.loop Api.root true] :=
  config_loop iaCode _ 0 true
    (machineTyped_of' iaCode _ 0
      (fun ty => ⟨EffTy.pure .unit, .cons (.inr (.mk (fun _ => rfl) (neverSkip rfl ty))) (.nil ty)⟩)
      (fun _ hm => by cases hm))
    (fun _ => ⟨EffTy.pure .unit, iaCode_typed world, arrow rfl rfl (.nil natTy),
      provenance _ rfl rfl⟩)

def out : RFiber := fiberOf iaCode [.answer iaNext, .resume .onSuccess yieldNext] 1

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) (machineOf input) (.loop Api.root true) []

/-- The actual step: the answer slot is pushed and `afterInterrupt` queued, the operation still
current. -/
theorem result_eq : result =
    ((machineOf input).update out, [.afterInterrupt Api.root true (.awaitAll [])]) := rfl

theorem output_typed : ConfigTyped (rootProgram : ProgramSource) natTy world (machineOf out)
    [.afterInterrupt Api.root true (.awaitAll [])] := by
  have stack : HostStack (rootProgram : ProgramSource) world (machineOf out) Api.root
      (EffTy.pure .unit) natTy [.answer iaNext, .resume .onSuccess yieldNext] :=
    .cons (.inl (iaSlot world)) (arrow rfl rfl (.nil natTy))
  refine ⟨machineTyped_of' iaCode _ 1
      (fun ty => ⟨EffTy.pure .unit,
        .cons (.inl (iaSlot world)) (.cons (.inr (.mk (fun _ => rfl) (neverSkip rfl ty))) (.nil ty))⟩)
      (fun _ hm => by cases hm), ?_, ?_⟩
  · intro f _ _ reads
    obtain ⟨_, r⟩ := reads
    rcases r with r | r <;> (rw [List.mem_singleton] at r; cases r)
  · refine ⟨?_, ?_, ?_, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
      ⟨trivial, trivial⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      trivial
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      exact ⟨out, rfl, rfl, rfl⟩
    · intro c hc
      rw [List.mem_singleton] at hc
      subst hc
      intro f found
      change some out = some f at found
      cases found
      -- the reply consumer reads the correlated stack (`StackReply`)
      exact ⟨EffTy.pure .unit, ⟨.unit, .never, (fun _ h => nomatch h), rfl⟩, natTy,
        (valid_of iaCode [.answer iaNext, .resume .onSuccess yieldNext] 1).root, stack,
        provenance _ rfl rfl⟩
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

theorem result_typed : ∃ w', world.leHost w' ∧
    ConfigTyped (rootProgram : ProgramSource) natTy w' result.1 result.2 := by
  refine ⟨world, leHost_refl world, ?_⟩
  rw [result_eq]
  exact configTyped_congr (m := machineOf out) rfl rfl rfl rfl rfl rfl rfl output_typed

end Interrupt

/-! ### 3. A second injection over a stored callback (Codex's composition case) -/

namespace Double

def input : RFiber := fiberOf marker [.resume .onSuccess yieldNext] 0

/-- The input: the race's marker current over a stored callback of the same race, budget
reached, latch clear. -/
theorem config_typed : ConfigTyped (rootProgram : ProgramSource) natTy world (machineOf input)
    [.loop Api.root false] :=
  config_loop marker _ 0 false
    (machineTyped_of' marker _ 0
      (fun ty => ⟨natTy, .cons (.inr (.mk (fun _ => rfl) (neverSkip rfl ty))) (.nil ty)⟩)
      (fun raceId hm => by
        change some 0 = some raceId at hm
        cases hm
        exact ⟨rfl, arrow rfl rfl (.nil natTy)⟩))
    (fun hm => by cases hm)

def out : RFiber :=
  fiberOf yieldCurrent [.resume .onSuccess yieldNext, .resume .onSuccess yieldNext] 1

def result :=
  letI := termEvaluatorFor rootProgram
  driveStep (interpR rootProgram) (machineOf input) (.loop Api.root false) []

/-- The actual step injects a second callback above the stored one. -/
theorem result_eq : result =
    (((machineOf input).emit [.yieldInjected Api.root 1]).update out, [.loop Api.root true]) := rfl

/-- The two callbacks compose as two registration arrows. -/
theorem output_typed : ConfigTyped (rootProgram : ProgramSource) natTy world (machineOf out)
    [.loop Api.root true] :=
  config_loop yieldCurrent _ 1 true
    (machineTyped_of' yieldCurrent _ 1
      (fun ty => ⟨EffTy.pure .unit, .cons (.inr (.mk (fun _ => rfl) (neverSkip rfl ty)))
        (.cons (.inr (.mk (fun _ => rfl) (fun _ _ _ hc => hc))) (.nil ty))⟩)
      (fun _ hm => by cases hm))
    (fun _ => ⟨EffTy.pure .unit, yieldCurrent_typed world,
      arrow rfl rfl (arrow rfl rfl (.nil natTy)), provenance _ rfl rfl⟩)

theorem result_typed : ∃ w', world.leHost w' ∧
    ConfigTyped (rootProgram : ProgramSource) natTy w' result.1 result.2 := by
  refine ⟨world, leHost_refl world, ?_⟩
  rw [result_eq]
  exact configTyped_congr (m := machineOf out) rfl rfl rfl rfl rfl rfl rfl output_typed

end Double

end Test.Program.RegistrationYield

#print axioms Test.Program.RegistrationYield.config_typed
#print axioms Test.Program.RegistrationYield.result_eq
#print axioms Test.Program.RegistrationYield.output_not_saved
#print axioms Test.Program.RegistrationYield.yieldCurrent_typed
#print axioms Test.Program.RegistrationYield.typedState_of
#print axioms Test.Program.RegistrationYield.Single.output_typed
#print axioms Test.Program.RegistrationYield.Single.result_typed
#print axioms Test.Program.RegistrationYield.Interrupt.config_typed
#print axioms Test.Program.RegistrationYield.Interrupt.result_eq
#print axioms Test.Program.RegistrationYield.Interrupt.output_typed
#print axioms Test.Program.RegistrationYield.Interrupt.result_typed
#print axioms Test.Program.RegistrationYield.Double.config_typed
#print axioms Test.Program.RegistrationYield.Double.result_eq
#print axioms Test.Program.RegistrationYield.Double.output_typed
#print axioms Test.Program.RegistrationYield.Double.result_typed
