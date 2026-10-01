/-! Frozen addendum-3 observer falsifier. The free noRace parameter belongs only to this
historical statement; the repaired production predicate does not pretend it is an exact scan. -/
namespace OldObserve
abbrev W := Effect4.Program.Typed.World

-- These three copies stand in for the code-generalized Guard.Core definitions.
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

def InternalKeysBelowR (m : RState) : Prop :=
  ∀ key ∈ internalKeysR m, key.2 < m.nextToken

def ActiveAtR (m : RState) (fiber : FiberId) : Prop :=
  ∃ f, m.fiber? fiber = some f ∧ f.running = true ∧ f.parked = .notParked

def commandOwnerR (m : RState) : RCmd → Option FiberId
  | .loop fiber _ | .deliver fiber _ | .finish fiber _ => some fiber
  | .afterInterrupt fiber _ _ | .closeParAwait fiber _ _ | .raceCancel _ fiber _ _ _ => some fiber
  | .registrationDone raceId _ => (m.race? raceId).map Race.host
  | _ => none

/-- The reference evaluator recognizes this operation directly; interpR.parkOf is unused. -/
def raceRegistrationR : RProgram → Option Nat
  | .vis (.inr (.raceRegister raceId)) _ => some raceId
  | _ => none

def CommandAuthorityR (m : RState) : RCmd → Prop
  | .loop fiber _ | .deliver fiber _ | .finish fiber _ => ActiveAtR m fiber
  | .afterInterrupt fiber _ _ | .closeParAwait fiber _ _ | .raceCancel _ fiber _ _ _ => ActiveAtR m fiber
  | .registrationDone raceId _ =>
    ∃ race f, m.race? raceId = some race ∧ m.fiber? race.host = some f ∧
      f.running = true ∧ f.parked = .notParked ∧
      raceRegistrationR f.frame.current = some raceId
  | .launch raceId | .enrollRace raceId _ =>
    ∃ race, m.race? raceId = some race ∧ ActiveAtR m race.host
  | .exitDone fiber => ∃ f, m.fiber? fiber = some f ∧ f.exit.isSome = true
  | _ => True

structure ReservedKeysR (m : RState) (keys : List Guard.GuardKey) : Prop where
  below : ∀ key ∈ keys, key.2 < m.nextToken
  disjoint : ∀ fiber token request, requestOfR m fiber token = some request → (fiber, token) ∉ keys

/-- The native commandRaceSites conditions, with the unresolved reference continuation scan
as an explicit parameter. Pure-code scanning is not needed to admit this probe's input. -/
def commandCodeSites (noRace : RProgram → Prop) : RCmd → Prop
  | .resume _ _ code => noRace code
  | .afterInterrupt _ _ (.race _) => False
  | _ => True

structure ReviewedQueueOk (noRace : RProgram → Prop) (root : ProgramSource) (w : W)
    (m : RState) (commands : List RCmd) : Prop where
  payload : ∀ command ∈ commands, RCmdOk (H1.reviewedPreds root) w command
  authority : ∀ command ∈ commands, CommandAuthorityR m command
  owners : (commands.filterMap (commandOwnerR m)).Nodup
  keys : ReservedKeysR m (commands.flatMap commandKeysR)
  codeSites : ∀ command ∈ commands, commandCodeSites noRace command

def ReviewedStepPreserves (noRace : RProgram → Prop) (root : ProgramSource)
    (rootTy : EffTy) (command : RCmd) : Prop :=
  ∀ w m rest, H1.ReviewedTypedState root rootTy w m → InternalKeysBelowR m →
    ReviewedQueueOk noRace root w m (command :: rest) →
    let result := (letI := termEvaluatorFor root.program
                   driveStep (interpR root.program) m command rest)
    ∃ w', w.leHost w' ∧ H1.ReviewedTypedState root rootTy w' result.1 ∧ InternalKeysBelowR result.1 ∧
      ReviewedQueueOk noRace root w' result.1 result.2

-- A typed unit program. The machine has a historical declared token, but no active park.
def program : NativeEff := .succeed (.lit .unit)
def ty : EffTy := EffTy.pure .unit
def base : RState := loadR program 20 20
def machine : RState := { base with nextToken := 1 }
def world : W :=
  { initialWorld ty with
    Θ := fun id token => if id = Api.root ∧ token = 0 then some ty else none }
def command : RCmd := .observe Api.root (.success .unit) (.resumeAwait Api.root 0 .awaitValue)
def emitted : RCmd := .resume Api.root 0 (.pure (.success (reifyExitVal (.success .unit))))
def result : RState × List RCmd :=
  letI := termEvaluatorFor program
  driveStep (interpR program) machine command []

#guard Api.typeOf program [] == some ty
#guard machine.nextToken == 1
#guard world.Θ Api.root 0 == some ty

theorem loaded_code (w : W) : TypedProg (program : ProgramSource) w ty
    (denoteR program program (rootPoint 20)) := by
  change TypedProg (program : ProgramSource) w ty (.pure (.success .unit))
  exact TypedProg.pure trivial

theorem valid : WorldValid ty world machine := by
  have old := initial_world_valid ty program 20 20 ⟨rfl, rfl⟩
  refine {
    ids := old.ids
    fibers := old.fibers
    heap := old.heap
    promises := old.promises
    tokens := ?_
    tokenBound := ?_
    tokenTargets := ?_
    state := old.state
    wf := old.wf
    cells := old.cells
    fiberClosed := old.fiberClosed
    heapClosed := old.heapClosed
    promiseClosed := old.promiseClosed
    tokenClosed := ?_
    root := old.root }
  · intro f hf token hp
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hp
  · intro id token tokenTy h
    change (if id = Api.root ∧ token = 0 then some ty else none) = some tokenTy at h
    split at h
    · rename_i hkey
      rw [hkey.2]
      decide
    · cases h
  · intro id token tokenTy h
    change (if id = Api.root ∧ token = 0 then some ty else none) = some tokenTy at h
    split at h
    · rename_i hkey
      rw [hkey.1]
      rfl
    · cases h
  · intro id token tokenTy h
    change (if id = Api.root ∧ token = 0 then some ty else none) = some tokenTy at h
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · cases h

theorem typed : H1.ReviewedTypedState (program : ProgramSource) ty world machine := by
  refine ⟨valid, ⟨?_, ?_, ?_⟩, ?_⟩
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
  · intro f hf token hp
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hp

theorem internal_below : InternalKeysBelowR machine := by
  intro key hk
  cases hk

theorem no_requests (fiber : FiberId) (token : Nat) : requestOfR machine fiber token = none := by
  unfold requestOfR
  cases hf : machine.fiber? fiber with
  | none => rfl
  | some f =>
    have member : f ∈ machine.fibers := List.mem_of_find?_eq_some hf
    change f ∈ [_] at member
    rw [List.mem_singleton] at member
    subst member
    rfl

theorem command_payload : RCmdOk (H1.reviewedPreds (program : ProgramSource)) world command := by
  change ∀ outTy, world.Γ Api.root = some outTy → FitsExit world outTy (.success .unit)
  intro outTy h
  have hroot : world.Γ Api.root = some ty := valid.root
  rw [hroot] at h
  cases h
  trivial

theorem queue (noRace : RProgram → Prop) :
    ReviewedQueueOk noRace (program : ProgramSource) world machine [command] := by
  refine ⟨?_, ?_, List.nodup_nil, ⟨?_, ?_⟩, ?_⟩
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact command_payload
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    trivial
  · intro key hk
    change key ∈ [(Api.root, 0)] at hk
    rw [List.mem_singleton] at hk
    subst hk
    decide
  · intro fiber token request hr
    rw [no_requests] at hr
    cases hr
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    trivial

theorem result_queue : result.2 = [emitted] := rfl

/-- Even moving to a later world cannot change the historical token's unit declaration. -/
theorem emitted_refused (w' : W) (ordered : world.leHost w') :
    ¬ RCmdOk (H1.reviewedPreds (program : ProgramSource)) w' emitted := by
  intro h
  change ∀ tokenTy, w'.Θ Api.root 0 = some tokenTy →
    TypedProg (program : ProgramSource) w' tokenTy
      (.pure (.success (reifyExitVal (.success .unit)))) at h
  have declared : world.Θ Api.root 0 = some ty := rfl
  have declared' := ordered.1.2.2.2.2.2 Api.root 0 ty declared
  have hex := TypedProg.pure_inv (h ty declared')
  change False at hex
  exact hex

theorem result_queue_refused (noRace : RProgram → Prop) (w' : W) (ordered : world.leHost w') :
    ¬ ReviewedQueueOk noRace (program : ProgramSource) w' result.1 result.2 := by
  intro h
  apply emitted_refused w' ordered
  apply h.payload emitted
  rw [result_queue]
  exact List.mem_singleton_self _

/-- This depends on no choice of reference code-site scan: observe itself has no code field. -/
theorem proposed_step_observe_false (noRace : RProgram → Prop) :
    ¬ ReviewedStepPreserves noRace (program : ProgramSource) ty command := by
  intro step
  obtain ⟨w', ordered, _, _, queue'⟩ := step world machine [] typed internal_below (queue noRace)
  exact result_queue_refused noRace w' ordered queue'

#print axioms loaded_code
#print axioms valid
#print axioms typed
#print axioms internal_below
#print axioms no_requests
#print axioms command_payload
#print axioms queue
#print axioms result_queue
#print axioms emitted_refused
#print axioms result_queue_refused
#print axioms proposed_step_observe_false

end OldObserve
