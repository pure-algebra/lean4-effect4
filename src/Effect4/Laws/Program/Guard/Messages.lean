import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Interference
import Effect4.Laws.Machine.EditWords

/-!
Concept: reactive-scheduling, R11, the reachable guard-token ownership claim.
These instances consume the shared ordered-edit path at its actual prefix states.
NativeState supplies observer-key admission; NativeAssembly consumes settlement preservation.
Arbitrary messages carry no source provenance, progress, or host agreement.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.NativeState
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

abbrev filteredFiber (keep : Observer → Bool) (f : NFiber) : NFiber :=
  {f with observers := f.observers.filter keep}

abbrev filteredMachine (keep : Observer → Bool) (m : NativeMachine) : NativeMachine :=
  {m with fibers := m.fibers.map (filteredFiber keep)}

theorem filtered_lookup (keep : Observer → Bool) (m : NativeMachine) (fiber : FiberId) :
    (filteredMachine keep m).fiber? fiber = (m.fiber? fiber).map (filteredFiber keep) := by
  simp only [RunMachine.fiber?, List.find?_map, Function.comp_def]

theorem filtered_request (keep : Observer → Bool) (m : NativeMachine) (fiber : FiberId) (token : Nat) :
    requestOf (filteredMachine keep m) fiber token = requestOf m fiber token := by
  unfold requestOf
  rw [filtered_lookup]
  cases hf : m.fiber? fiber <;> rfl

theorem filtered_fiberKeys (keep : Observer → Bool) (f : NFiber) :
    fiberKeys (filteredFiber keep f) ⊆ fiberKeys f := by
  intro key hk
  rcases List.mem_append.mp hk with hk | hk
  · obtain ⟨obs, ho, hk⟩ := List.mem_flatMap.mp hk
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨obs, (List.mem_filter.mp ho).1, hk⟩)
  · exact List.mem_append_right _ hk

theorem filtered_internalKeys (keep : Observer → Bool) (m : NativeMachine) :
    internalKeys (filteredMachine keep m) ⊆ internalKeys m := by
  intro key hk
  rw [internalKeys_store_decomposition] at hk ⊢
  rcases List.mem_append.mp hk with hk | hk
  · exact List.mem_append_left _ hk
  · obtain ⟨f, hf, hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨old, hm, rfl⟩ := List.mem_map.mp hf
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨old, hm, filtered_fiberKeys keep old hk⟩)

theorem guardState_filterObservers_at {active : Option FiberId} {m : NativeMachine} (state : GuardState m active) (keep : Observer → Bool) :
    GuardState (filteredMachine keep m) active := by
  have hall (P : NFiber → Prop) (old : ∀ f ∈ m.fibers, P (filteredFiber keep f)) :
      ∀ f ∈ (filteredMachine keep m).fibers, P f := by
    intro f hf
    obtain ⟨oldf, hm, rfl⟩ := List.mem_map.mp hf
    exact old oldf hm
  constructor
  · simpa only [List.map_map, Function.comp_def] using state.fiberIds
  · exact hall _ state.fibersBelow
  · exact state.raceIds
  · exact state.racesBelow
  · intro race hr
    obtain ⟨f, hf⟩ := state.raceHosts race hr
    exact ⟨filteredFiber keep f, by rw [filtered_lookup, hf]; rfl⟩
  · exact fun key hk => state.keysBelow key (filtered_internalKeys keep m hk)
  · intro fiber token request hr
    rw [filtered_request] at hr
    exact state.requestsBelow fiber token request hr
  · intro fiber token request hr hk
    rw [filtered_request] at hr
    exact state.requestsOwned fiber token request hr (filtered_internalKeys keep m hk)
  · exact hall _ state.pendingShape
  · exact hall _ state.parkedIdle
  · exact hall _ state.parkedBelow
  · exact hall _ state.exited
  · exact hall _ state.deferredCause
  · exact hall _ state.frameCodes
  · exact ⟨hall _ state.internalCodes.1, state.internalCodes.2⟩

end Effect4.Program.Guard.NativeState

namespace Effect4.Program.Guard.Messages
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

/-- The actual observer message carries no key, or the newly minted internal owner key.
The source head proves the returned code cannot offer that key as an external request. -/
def MessageKeys (before : NativeMachine) (next : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) : Prop :=
  ∀ target observer, FiberEdit.observe target observer ∈ next.edits →
    observerKeys observer = [] ∨
      (observerKeys observer = [(next.fiber.id, before.nextToken)] ∧
        before.nextToken < next.machine.nextToken ∧
        externalRequest next.fiber.frame.current = none)

/-- Callback keys contributed by the addressed observer messages. -/
def editKeys (edits : List (FiberEdit Err Defect FiberId Ann)) : List GuardKey :=
  edits.flatMap fun edit => match edit with
    | .observe _ observer => observerKeys observer
    | _ => []

/-- Every keyed observer message uses the actual new owner token.
Consumer: its reservation after the local owner is installed. -/
theorem MessageKeys.key {before : NativeMachine} {next : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores}
    (admitted : MessageKeys before next) {key : GuardKey} (member : key ∈ editKeys next.edits) :
    key = (next.fiber.id, before.nextToken) ∧ before.nextToken < next.machine.nextToken ∧
      externalRequest next.fiber.frame.current = none := by
  obtain ⟨message, occurs, member⟩ := List.mem_flatMap.mp member
  cases message with
  | observe target observer =>
    change key ∈ observerKeys observer at member
    rcases admitted target observer occurs with empty | ⟨keys, fresh, internal⟩
    · rw [empty] at member; cases member
    · rw [keys] at member
      exact ⟨List.mem_singleton.mp member, fresh, internal⟩
  | dropToken token => cases member
  | interrupt target cause => cases member

/-- The actual local install reserves every key contributed by its deferred messages.
The source-head premise excludes a new external request at the installed owner. -/
theorem reserved_editKeys_install {before : NativeMachine} {next : Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores}
    (admitted : MessageKeys before next)
    {old : NFiber} (lookup : next.machine.fiber? next.fiber.id = some old) :
    ReservedKeys (next.machine.update next.fiber) (editKeys next.edits) := by
  constructor
  · intro key member
    obtain ⟨same, fresh, _⟩ := admitted.key member
    rw [same]
    exact fresh
  · intro fiber token request offered member
    obtain ⟨same, fresh, internal⟩ := admitted.key member
    have owner : next.fiber.id = fiber := (congrArg Prod.fst same).symm
    have found := fiber_lookup_update_self lookup next.fiber rfl
    obtain ⟨held, heldLookup, _, code⟩ := requestOf_shape offered
    rw [owner] at found
    have equal : held = next.fiber := Option.some.inj (heldLookup.symm.trans found)
    rw [equal, internal] at code
    cases code

/-- An existing primitive edit with its actual message-prefix payload premise. -/
def GuardEdge (keys : List GuardKey) (before after : NativeMachine)
    (edit : Edit EffName EffThunk Val Err Defect FiberId Ann Ctx Stores NCode (FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)) : Prop :=
  after = edit.apply before ∧
    match edit with
    | .observe _ observer => observerKeys observer ⊆ keys
    | .update next => ∃ target held fresh,
        before.fiber? target = some held ∧ next = (interruptWithCause fresh held).1
    | .dropToken _ => True
    | _ => False

/-- One message edit retains the guard state and reservations, and introduces no request.
The update case reads its payload from that edit's actual prefix lookup. -/
theorem guardEdge_transfer {active : Option FiberId} {keys : List GuardKey}
    {before after : NativeMachine} {edit : Edit EffName EffThunk Val Err Defect FiberId Ann Ctx Stores NCode (FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)}
    (edge : GuardEdge keys before after edit) :
    (GuardState before active → ReservedKeys before keys → GuardState after active) ∧
    (ReservedKeys before keys → ReservedKeys after keys) ∧
    (∀ fiber token request, requestOf after fiber token = some request →
      requestOf before fiber token = some request) := by
  obtain ⟨rfl, allowed⟩ := edge
  cases edit with
  | observe target observer =>
    exact ⟨fun state reserved => guardState_addObserver_at state target observer
      (reservedKeys_subset reserved allowed), fun reserved => reservedKeys_addObserver reserved target observer,
      fun fiber token request offered => (requestOf_addObserver before target observer fiber token).symm.trans offered⟩
  | update next =>
    obtain ⟨target, held, fresh, lookup, rfl⟩ := allowed
    have selected : before.fiber? held.id = some held := by
      simpa only [fiber_id_of_lookup lookup] using lookup
    exact ⟨fun state _ => guardState_interruptWithCause_at state selected fresh,
      fun reserved => reservedKeys_of_requests_subset reserved (Nat.le_refl _)
        (requestOf_interruptWithCause_subset selected fresh),
      requestOf_interruptWithCause_subset selected fresh⟩
  | dropToken token =>
    let keep : Observer → Bool := fun observer => match observer with
      | .resumeAwait _ held _ => held ≠ token
      | .countdown _ held => held ≠ token
      | _ => true
    change (GuardState before active → ReservedKeys before keys →
      GuardState (NativeState.filteredMachine keep before) active) ∧
      (ReservedKeys before keys → ReservedKeys (NativeState.filteredMachine keep before) keys) ∧
      (∀ fiber offered request, requestOf (NativeState.filteredMachine keep before) fiber offered = some request →
        requestOf before fiber offered = some request)
    refine ⟨fun state _ => NativeState.guardState_filterObservers_at state keep, ?_, ?_⟩
    · intro reserved
      exact ⟨reserved.below, fun fiber offered request found member =>
        reserved.disjoint fiber offered request
          ((NativeState.filtered_request keep before fiber offered).symm.trans found) member⟩
    · intro fiber offered request found
      exact (NativeState.filtered_request keep before fiber offered).symm.trans found
  | _ => exact False.elim allowed

/-- The shared word carries the actual lookup premise of every resolved update. -/
theorem fiberWords_guardPath (edits : List (FiberEdit Err Defect FiberId Ann)) (m : NativeMachine) :
    Contracts.Path (GuardEdge (editKeys edits)) m (applyFiberEdits edits m).1 (Edits.fiberWords edits m) := by
  apply Edits.fiberWords_path
  intro message member held
  cases message with
  | observe target observer =>
    apply Contracts.Path.cons (middle := (applyFiberEdit (.observe target observer) held).1)
    · refine ⟨rfl, ?_⟩
      intro key found
      exact List.mem_flatMap.mpr ⟨.observe target observer, member, found⟩
    · exact .nil _
  | dropToken token =>
    exact .cons ⟨rfl, True.intro⟩ (.nil _)
  | interrupt target fresh =>
    cases lookup : held.fiber? target with
    | none =>
      simp only [Edits.fiberWord, applyFiberEdit, lookup]
      exact .nil held
    | some fiber =>
      simp only [Edits.fiberWord, applyFiberEdit, lookup]
      exact .cons ⟨rfl, target, fiber, fresh, lookup, rfl⟩ (.nil _)

/-- Addressed messages retain an admitted guard phase through the shared edit path. -/
theorem guardState_fiberEdits_at {active : Option FiberId} (edits : List (FiberEdit Err Defect FiberId Ann))
    {m : NativeMachine} (state : GuardState m active) (reserved : ReservedKeys m (editKeys edits)) :
    GuardState (applyFiberEdits edits m).1 active ∧ ReservedKeys (applyFiberEdits edits m).1 (editKeys edits) := by
  have preserved := Edits.run_preserves_at (Edge := GuardEdge (editKeys edits)) (fun _ _ _ edge => edge.1)
    (fun held => GuardState held active ∧ ReservedKeys held (editKeys edits))
    (fun _ _ _ edge initial => ⟨(guardEdge_transfer (active := active) edge).1 initial.1 initial.2,
      (guardEdge_transfer (active := active) edge).2.1 initial.2⟩)
    (fiberWords_guardPath edits m) ⟨state, reserved⟩
  simpa only [← Edits.fiber_words] using preserved

/-- Raw messages introduce no external request; source admission is needed only for new callback keys. -/
theorem requestOf_fiberEdits_subset (edits : List (FiberEdit Err Defect FiberId Ann))
    (m : NativeMachine) (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (offered : requestOf (applyFiberEdits edits m).1 fiber token = some request) :
    requestOf m fiber token = some request := by
  have preserved := Edits.run_preserves_at (Edge := GuardEdge (editKeys edits)) (fun _ _ _ edge => edge.1)
    (fun held => ∀ id key answer, requestOf held id key = some answer → requestOf m id key = some answer)
    (fun _ _ _ edge previous id key answer found =>
      previous id key answer ((guardEdge_transfer (active := none) edge).2.2 id key answer found))
    (fiberWords_guardPath edits m) (fun _ _ _ found => found)
  rw [← Edits.fiber_words] at preserved
  exact preserved fiber token request offered

/-- Addressed messages retain the command tail's active/exited observations.
The existing interference word supplies each actual stored record. -/
theorem commandControls_fiberEdits (edits : List (FiberEdit Err Defect FiberId Ann)) (m : NativeMachine) :
    CommandControlsPreserved m (applyFiberEdits edits m).1 := by
  have changed := Moves.InterferesWithLookup.fiberEdits edits m
  constructor
  · intro fiber f found running park
    obtain ⟨g, lookup, word⟩ := changed.lookup fiber f found
    have fields := word.controls (Or.inl running)
    exact ⟨g, lookup, fields.2.2.2 running, fields.2.1.trans park, fields.1, fun empty => word.stack.trans empty⟩
  · intro fiber f found exited
    obtain ⟨g, lookup, word⟩ := changed.lookup fiber f found
    exact ⟨g, lookup, word.exit ▸ exited⟩

end Effect4.Program.Guard.Messages
