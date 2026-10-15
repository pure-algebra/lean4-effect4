import Test.Dogfood.Proofs.QueueWorkersNotificationEmbedding
import Test.Dogfood.Proofs.QueueWorkersTakeTailSites
import Effect4.Laws.Machine.AnswerFlowIndexedFamily

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the actual stack across both notification regions.
The common stack retains the member source family and the exact captured option of each edge.
Actual callbacks use their existing family proofs; this instance adds no source traversal.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersJobFamilies
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open Test.Dogfood.Scenario

/-- Each notification frame retains its own concrete region, prefix and request option. -/
abbrev Index (total : Nat) := Option (Nat × Val × List Val ×
  QueueWorkersNotificationFlow.Spec (Programs.queueProgram total))

/-- Semantic worker binders and source notification frames share one actual stack relation. -/
def member (total : Nat) (table : RowTable) (owner : FiberId) :
    Index total → QueueWorkersCustodyFlow.World → QueueWorkersCustodyFlow.Kind →
      QueueWorkersCustodyFlow.Kind → NCode → Prop
  | none => QueueWorkersJobGraph.Semantic total table owner
  | some (token, option, bindings, spec) =>
      QueueWorkersNotificationEmbedding.Edge total table owner token option spec bindings

/-- Every actual mixed stack edge retains its original classified input and output. -/
abbrev Edge (total : Nat) (table : RowTable) (owner : FiberId) :=
  IndexedEdge (member total table owner)

/-- Existing per-region callback proofs assemble once into the worker's mixed saved family. -/
theorem family (total : Nat) (table : RowTable) (owner : FiberId) (view : List (FiberId × ExitV)) :
    SavedFamily (QueueWorkersJobGraph.model total table owner view)
      (interpAt (Programs.queueProgram total) view table).toPrimInterp (Edge total table owner) := by
  apply indexed_family
  intro index
  cases index with
  | none => exact QueueWorkersJobGraph.semantic_family total table owner view
  | some selected =>
    obtain ⟨token, option, bindings, spec⟩ := selected
    exact QueueWorkersNotificationEmbedding.family total table owner token option spec bindings view

/-- A real notification head enters the common mixed stack without changing its captured option. -/
theorem notification_head (total : Nat) (table : RowTable) (owner : FiberId) (token : Nat) (option : Val)
    (spec : QueueWorkersNotificationFlow.Spec (Programs.queueProgram total)) (bindings : List Val)
    (view : List (FiberId × ExitV)) (world : QueueWorkersCustodyFlow.World) (code : NCode)
    (phase : QueueWorkersCustodyFlow.Owns world owner token ∧ QueueWorkersCustody.OptionAt world.requests.custody token option)
    (owned : QueueWorkersNotificationFlow.Code spec bindings code) :
    HeadAt (QueueWorkersJobGraph.model total table owner view)
      (interpAt (Programs.queueProgram total) view table).toPrimInterp
      (Edge total table owner) world (.snapshot owner token option) code :=
  indexed_head _ _ (member total table owner) (some (token, option, bindings, spec)) world _ code
    (QueueWorkersNotificationEmbedding.head total table owner token option spec bindings view world code phase owned)

/-- The actual notification bind executes its certified body before consuming the captured option. -/
theorem notification_bind (total : Nat) (table : RowTable) (owner : FiberId) (token : Nat) (option : Val)
    (spec : QueueWorkersNotificationFlow.Spec (Programs.queueProgram total))
    (world : QueueWorkersCustodyFlow.World) (point : Point) (first rest : NativeEff)
    (found : Node.at_ (.eff (Programs.queueProgram total)) point.path = some (.eff (.bind first rest)))
    (inside : spec.origin.IsPrefix (point.child 0).path)
    (phase : QueueWorkersCustodyFlow.Owns world owner token ∧ QueueWorkersCustody.OptionAt world.requests.custody token option)
    (output : QueueWorkersCustodyFlow.Kind)
    (callback : ∀ nextWorld, QueueWorkersCustodyFlow.Future world nextWorld → ∀ view answer,
      QueueWorkersCustodyFlow.ValueAt nextWorld (.snapshot owner token option) answer →
      QueueWorkersJobGraph.CodeAt total table owner nextWorld output
        ((interpAt (Programs.queueProgram total) view table).contA (.cont point) answer)) :
    QueueWorkersJobGraph.CodeAt total table owner world output (resolve (Programs.queueProgram total) point) := by
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ available =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .snapshot owner token option)
    · exact .notification spec phase (QueueWorkersNotificationFlow.compile_at spec point.env first
        (point.child 0) (Agreement.at_child found 0) ⟨inside, List.take_length⟩)
    · exact callback

/-- Both actual notification prefixes retain the captured tuple before the actual option branch. -/
theorem take_notifications (total worker : Nat) (member : worker ∈ [1, 2])
    (table : RowTable) (owner : FiberId) (token : Nat) (option : Val)
    (world : QueueWorkersCustodyFlow.World) (point : Point)
    (source : SourceScope.At (Programs.queueProgram total) point)
    (path : point.path = QueueWorkersTakeTailSites.tailPath worker)
    (phase : QueueWorkersCustodyFlow.Owns world owner token ∧ QueueWorkersCustody.OptionAt world.requests.custody token option)
    (output : QueueWorkersCustodyFlow.Kind)
    (branch : ∀ nextWorld nextPoint,
      SourceScope.At (Programs.queueProgram total) nextPoint →
      AnswerSlots.Prefix point.env nextPoint.env → nextPoint.path = QueueWorkersTakeTailSites.optionPath worker →
      QueueWorkersCustodyFlow.Owns nextWorld owner token ∧ QueueWorkersCustody.OptionAt nextWorld.requests.custody token option →
      QueueWorkersJobGraph.CodeAt total table owner nextWorld output (resolve (Programs.queueProgram total) nextPoint)) :
    QueueWorkersJobGraph.CodeAt total table owner world output (resolve (Programs.queueProgram total) point) := by
  have found := QueueWorkersTakeTailSites.source total worker member
  rw [← path] at found
  refine notification_bind total table owner token option (QueueWorkersTakeTailSites.firstSpec total worker member)
    world point _ _ found ?_ phase output ?_
  · change (QueueWorkersTakeTailSites.tailPath worker ++ [0]).IsPrefix (point.path ++ [0])
    rw [path]
    exact List.prefix_refl _
  · intro nextWorld future view answer good
    have nextPhase : QueueWorkersCustodyFlow.Owns nextWorld owner token ∧
        QueueWorkersCustody.OptionAt nextWorld.requests.custody token option := good
    have nextSource := SourceScope.childWith_at (Programs.queueProgram total)
      {point with completed := view} 1 answer
      (SourceScope.next_of_at _ _ _ 1 1 found source rfl)
    refine notification_bind total table owner token option (QueueWorkersTakeTailSites.secondSpec total worker member)
      nextWorld ({point with completed := view}.childWith 1 answer) _ _ (Agreement.at_childWith found 1 answer) ?_ nextPhase output ?_
    · change (QueueWorkersTakeTailSites.tailPath worker ++ [1, 0]).IsPrefix ((point.path ++ [1]) ++ [0])
      simp only [path, List.append_assoc, List.cons_append, List.nil_append]
      exact List.prefix_refl _
    · intro lastWorld later lastView lastAnswer lastGood
      apply branch lastWorld _ ?_ ?_ ?_ lastGood
      · exact SourceScope.childWith_at (Programs.queueProgram total)
          {{point with completed := view}.childWith 1 answer with completed := lastView} 1 lastAnswer
          (SourceScope.next_of_at _ _ _ 1 1 (Agreement.at_childWith found 1 answer) nextSource rfl)
      · exact ((show AnswerSlots.Prefix point.env point.env from List.take_length).append [answer]).append [lastAnswer]
      · change (point.path ++ [1]) ++ [1] = QueueWorkersTakeTailSites.tailPath worker ++ [1, 1]
        simp only [path, List.append_assoc, List.cons_append, List.nil_append]
end Test.Dogfood.Proofs.QueueWorkersJobFamilies
