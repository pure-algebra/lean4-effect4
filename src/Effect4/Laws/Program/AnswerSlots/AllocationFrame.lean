import Effect4.Laws.Program.AnswerSlots.AllocationSync
import Effect4.Laws.Machine.AnswerFlowHooks

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual initializer frame transitions preserve the older ordered saved suffix.
Reach: one real frame step or native sync answer, with the exact boundary hook explicit.
Consumer: the common bare-prefix history producer and its numeric entry activation.
These frame facts do not assert queue ownership or scheduler progress.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.AllocationAdapter
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts

/-- The structured initializer and stable callbacks retain their actual saved frame in a future world. -/
theorem edge_future (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (first last : World) (future : Future first last) (input output : Kind spec.stable.Kind) (frame : NCode)
    (held : Edge spec fragment first input output frame) : Edge spec fragment last input output frame := by
  apply AnswerFlow.FamilyEmbedding.edge_future_over (embedding spec [])
    (Semantic spec) (spec.laws fragment).Edge (semantic_future spec) ?_ first last future input output frame held
  intro before after _ incoming outgoing code owned
  cases before
  cases after
  exact owned

/-- Native heap growth retains the same ordered saved suffix and answer endpoints. -/
theorem path_future (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (first last : World) (future : Future first last) (input output : Kind spec.stable.Kind) (frames : List NCode)
    (held : Effect4.Contracts.Path (Edge spec fragment first) input output frames) : Effect4.Contracts.Path (Edge spec fragment last) input output frames :=
  held.map (edge_future spec fragment first last future)

/-- Actual mask restoration is an identity saved edge for every initializer answer class. -/
theorem mask_edge (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (kind : Kind spec.stable.Kind) (flag : Bool) : Edge spec fragment world kind kind (.setInterruptible flag) :=
  .saved (.saved ⟨(fun view => AnswerFlow.saved_mask (model spec view)
    (interpAt spec.root view spec.table).toPrimInterp world kind flag),
    (by intro name cursor equal; cases equal), (by intro name cursor equal; cases equal)⟩ (Or.inr (Or.inl ⟨rfl, flag, rfl⟩)))

/-- The actual entry hook changes only the independent world flag and preserves the entire saved suffix. -/
theorem activate_frame (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (world : World) (point : Point) (output : Kind spec.stable.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (entry : Entry spec world point) (current : fiber.current = resolve spec.root point)
    (saved : Effect4.Contracts.Path (Edge spec fragment world) (.stable spec.stable.rootKind) output fiber.stack) :
    let after : World := {world with entered := true}
    Future world after ∧ Ready spec after ∧
      AnswerFlow.FamilyResult (model spec []) (Edge spec fragment) after output fiber.current fiber.stack := by
  obtain ⟨future, ready, owned⟩ := activate_entry spec fragment world point entry
  refine ⟨future, ready, .stable spec.stable.rootKind, ?_, path_future spec fragment world _ future _ _ _ saved⟩
  rw [current]
  exact owned

/-- An actual allocation answer retains its current input and actual older saved suffix.
An entry marker remains explicit for joint application activation before the operation. -/
theorem sync_frame_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (world : World) (input output : Kind spec.stable.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (thunk : EffThunk)
    (state : Stores) (value : Val) (current : fiber.current = .sync thunk)
    (owned : CodeAt spec world input fiber.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment world) input output fiber.stack)
    (ran : (interpAt spec.root view spec.table).syncState thunk world.state = some (state, value)) :
    AnswerFlow.FamilyResult (model spec view) (Edge spec fragment) ⟨world.owner, state, world.entered⟩ output
      (.success value) fiber.stack ∨
    ∃ point, input = .stable spec.stable.rootKind ∧ fiber.current = resolve spec.root point ∧ Entry spec world point := by
  rcases sync_or_entry spec view world input thunk state value (current ▸ owned) ran with good | entry
  · exact .inl ⟨input, .success good,
      path_future spec fragment world _ (sync_future spec view world thunk state value ran) input output _ saved⟩
  · obtain ⟨point, kind, code, stage⟩ := entry
    exact .inr ⟨point, kind, current.trans code, stage⟩

/-- An ordinary nonterminal frame uses the shared head step or exposes its exact source entry. -/
theorem nonterminal_step_or_entry (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (view : List (FiberId × ExitV)) (world : World) (input output : Kind spec.stable.Kind)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (owned : CodeAt spec world input fiber.current)
    (saved : Effect4.Contracts.Path (Edge spec fragment world) input output fiber.stack)
    (noSuccess : ∀ value, fiber.current ≠ .success value)
    (noFailure : ∀ cause, fiber.current ≠ .failure cause)
    (noSync : ∀ thunk, fiber.current ≠ .sync thunk) :
    AnswerFlow.FamilyStep (model spec view) (Edge spec fragment) world output
      (fiber.step (interpAt spec.root view spec.table).toPrimInterp).1 ∨
    ∃ point, input = .stable spec.stable.rootKind ∧ fiber.current = resolve spec.root point ∧ Entry spec world point := by
  rcases head_or_entry spec fragment view world input fiber.current owned noSync with head | entry
  · apply Or.inl
    apply AnswerFlow.frame_step (model spec view) (interpAt spec.root view spec.table).toPrimInterp
      (Edge spec fragment) world input output fiber head saved
    · intro value provided actual good
      rcases actual with ⟨current, supplied⟩ | ⟨thunk, current, valueEq, supplied⟩
      · exact (noSuccess value current).elim
      · exact (noSync thunk current).elim
    · intro cause current good
      exact (noFailure cause current).elim
  · exact .inr entry

/-- A native captured scoped callback is admitted only after actual prefix entry. -/
theorem scoped_edge_ready (spec : Spec) (fragment : SourceScope.Fragment spec.root) (world : World)
    (input output : Kind spec.stable.Kind) (body : NCode) (previous : Ctx) (scope : Nat) (flag : Bool)
    (held : Edge spec fragment world input output (.onExit body (.scopedExit previous scope) flag)) : Ready spec world := by
  generalize same : Prim.onExit body (.scopedExit previous scope) flag = frame at held
  cases held with
  | saved held =>
    cases held with
    | saved held scopeReady =>
      rcases scopeReady with ready | shape
      · exact ready
      · rcases shape with ⟨kinds, flag, mask⟩ | ⟨refs, deferred, priority, next, input, wrapper⟩
        · cases mask.symm.trans same.symm
        · cases wrapper.symm.trans same.symm
    | allocation => cases same
    | gate => cases same
  | mapped ready held => exact ready

end Effect4.Program.AnswerSlots.AllocationAdapter
