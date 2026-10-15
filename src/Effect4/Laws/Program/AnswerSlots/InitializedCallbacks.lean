import Effect4.Laws.Program.AnswerSlots.Initialized

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual initializer callbacks enter the checked protected stable source graph.
Reach: the certified reference prefix and gate, actual returned allocation keys and current store lengths.
Limit: native command preservation and root exclusivity remain separate producers.
Consumer: the initialized native head and crew history invariant.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- An actual reference allocation extends the existing initializer's environment and store phase. -/
theorem allocation_callback (spec : Spec) (world nextWorld : World) (index : Nat) (point : Point)
    (small : index < spec.initialization.width) (stage : RootStage spec world index point)
    (future : Future world nextWorld) (view : List (FiberId × ExitV)) (answer : Val)
    (good : ValueAt spec nextWorld (.allocated index) answer) :
    CodeAt spec nextWorld (.stable .root) ((interpAt spec.root view spec.table).contA (.cont point) answer) := by
  obtain ⟨bound, owner, path, env, refs, deferred, source⟩ := stage
  obtain ⟨phase, rfl, afterRefs, afterDeferred⟩ := good
  obtain ⟨tail, found⟩ := spec.initialization.head index small
  rw [← path] at found
  have next := SourceScope.next_of_at spec.root point _ 1 1 found source rfl
  have extension := spec.initialization.next index small
  rw [spec.bindings_eq] at extension
  apply CodeAt.initial
  refine ⟨by omega, future.1.symm.trans owner, ?_, ?_, afterRefs, afterDeferred, ?_⟩
  · change point.path ++ [1] = List.replicate (index + 1) 1
    rw [path, List.replicate_succ']
  · change point.env ++ [.cell ⟨index⟩] = spec.bindings.take (index + 1)
    rw [env]
    exact extension
  · exact SourceScope.childWith_at spec.root _ 1 _ next

/-- The actual gate allocation enters the protected stable graph with all initialized bindings. -/
theorem gate_callback (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (world nextWorld : World) (point : Point)
    (stage : RootStage spec world spec.initialization.width point)
    (view : List (FiberId × ExitV)) (answer : Val) (good : ValueAt spec nextWorld .gate answer) :
    CodeAt spec nextWorld (.stable .root) ((interpAt spec.root view spec.table).contA (.cont point) answer) := by
  obtain ⟨bound, owner, path, env, refs, deferred, source⟩ := stage
  obtain ⟨rfl, ready⟩ := good
  obtain ⟨tail, found⟩ := spec.gate_head
  rw [← path] at found
  have next := SourceScope.next_of_at spec.root point _ 1 1 found source rfl
  apply CodeAt.stable ready
  apply Typed.resolve_source spec.toSpec fragment
  refine ⟨SourceScope.childWith_at spec.root _ 1 _ next, ?_, .inl ?_⟩
  · change (point.env ++ [Val.promise ⟨0⟩]).take spec.bindings.length = spec.bindings
    rw [env, spec.gate_next, List.take_length]
  · apply cont_ordinary spec.root spec.toSpec.acquisitions (Typed.sites spec.toSpec) _ _
    exact ⟨next, .perform (.deferredMakeOf spec.gateValue spec.gateError) (.lit .unit), tail, found⟩

/-- A positive child budget exposes the actual gate allocation operation. -/
theorem gate_operation (spec : Spec) (point : Point) (fuel : Nat) (amount : point.fuel = fuel + 1) :
    compileEff (.perform (.deferredMakeOf spec.gateValue spec.gateError) (.lit .unit)) point =
      .sync (.op .deferredMake) := by
  rw [Agreement.compileEff_perform_sync _ _ amount rfl]
  rfl
end Effect4.Program.AnswerSlots.Initialized
