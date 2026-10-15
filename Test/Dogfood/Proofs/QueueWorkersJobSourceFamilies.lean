import Test.Dogfood.Proofs.QueueWorkersJobFamilies
import Effect4.Laws.Machine.AnswerFlowEmbedding

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, whose actual saved stack includes ordinary and postoffer source callbacks.
Existing unit source families enter the same classified model at its ordinary input.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersJobSourceFamilies
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open Test.Dogfood.Scenario
open QueueWorkersCustodyFlow

/-- The ordinary and postoffer leaves retain their respective source predicates. -/
def sourcePoint (total : Nat) (bindings : Option (List Val)) : Point → Prop :=
  match bindings with
  | none => QueueWorkersReadonly.PointAt total
  | some values => QueueWorkersOfferTail.PointAt values (QueueWorkersOfferSites.path.dropLast ++ [1])

def sourceEnv (bindings : Option (List Val)) : List Val → Prop :=
  match bindings with
  | none => AnswerSlots.Prefix QueueWorkers.InitialSlots.bindings
  | some values => AnswerSlots.Prefix values

def sourceWrites (total : Nat) (bindings : Option (List Val)) : SyncOp → Prop :=
  match bindings with
  | none => QueueWorkersReadonly.Writes
  | some values => QueueWorkersOfferTail.Writes total values (QueueWorkersOfferSites.path.dropLast ++ [1])

/-- These source families share their actual root, interpreter and broad unit answer class. -/
def sourceSpec (total : Nat) (table : RowTable) (bindings : Option (List Val)) :=
  CodeClosure.Qualified.prefixSpec (Programs.queueProgram total) table
    (sourcePoint total bindings) (sourceEnv bindings) (sourceWrites total bindings)

/-- The ordinary input has no custody permission to mint from a broad source answer. -/
theorem embedding (total : Nat) (table : RowTable) (owner : FiberId) (bindings : Option (List Val)) (view) :
    FamilyEmbedding ((sourceSpec total table bindings).model view) (QueueWorkersJobGraph.model total table owner view)
      (fun _ => ()) (fun _ => Kind.ordinary) (fun _ => True) := by
  cases bindings with
  | none =>
    exact { ready_future := fun _ _ _ _ => trivial
            future := fun _ _ _ _ => trivial
            value_read := fun _ _ _ _ _ => trivial
            value_write := fun _ _ _ _ _ => trivial
            cause_read := fun _ _ _ _ _ => trivial
            cause_write := fun _ _ _ _ _ => trivial
            code := fun _ _ _ _ owned => .ordinary owned
            finalizer := fun _ _ _ _ => rfl }
  | some values =>
    exact { ready_future := fun _ _ _ _ => trivial
            future := fun _ _ _ _ => trivial
            value_read := fun _ _ _ _ _ => trivial
            value_write := fun _ _ _ _ _ => trivial
            cause_read := fun _ _ _ _ _ => trivial
            cause_write := fun _ _ _ _ _ => trivial
            code := fun _ _ _ _ owned => .postOffer owned
            finalizer := fun _ _ _ _ => rfl }

/-- The existing source law supplies its original uniform saved edge. -/
def sourceLaws (total : Nat) (table : RowTable) (bindings : Option (List Val)) :
    AnswerSlots.StableLaws (sourceSpec total table bindings) :=
  match bindings with
  | none => QueueWorkersReadonly.laws total (SourceFragment.queue_fragment total) table
  | some values => QueueWorkersOfferTail.laws total values (QueueWorkersOfferSites.path.dropLast ++ [1]) table

abbrev SourceEdge (total : Nat) (table : RowTable) (owner : FiberId) (bindings : Option (List Val)) :=
  EmbeddedEdgeOver (fun _ => ()) (fun _ => Kind.ordinary) (fun _ => True)
    (QueueWorkersJobGraph.Semantic total table owner) (sourceLaws total table bindings).Edge

/-- The shared embedding retains actual arm results and pushed paths for each source family. -/
theorem sourceFamily (total : Nat) (table : RowTable) (owner : FiberId)
    (bindings : Option (List Val)) (view) :
    SavedFamily (QueueWorkersJobGraph.model total table owner view)
      (interpAt (Programs.queueProgram total) view table).toPrimInterp (SourceEdge total table owner bindings) :=
  (embedding total table owner bindings view).family_over _ _ _
    (QueueWorkersJobGraph.semantic_family total table owner view) ((sourceLaws total table bindings).family view)

abbrev Index := Sum Unit (Option (List Val))

def member (total : Nat) (table : RowTable) (owner : FiberId) :
    Index → QueueWorkersCustodyFlow.World → Kind → Kind → NCode → Prop
  | .inl _ => QueueWorkersJobFamilies.Edge total table owner
  | .inr bindings => SourceEdge total table owner bindings

abbrev Edge (total : Nat) (table : RowTable) (owner : FiberId) := IndexedEdge (member total table owner)

/-- The actual mixed stack uses the existing indexed family assembly once. -/
theorem family (total : Nat) (table : RowTable) (owner : FiberId) (view) :
    SavedFamily (QueueWorkersJobGraph.model total table owner view)
      (interpAt (Programs.queueProgram total) view table).toPrimInterp (Edge total table owner) := by
  apply indexed_family
  intro index
  cases index with
  | inl _ => exact QueueWorkersJobFamilies.family total table owner view
  | inr bindings => exact sourceFamily total table owner bindings view

/-- The previously checked worker and notification edges retain their actual endpoints in future worlds. -/
theorem worker_edge_future (total : Nat) (table : RowTable) (owner : FiberId)
    (world nextWorld : QueueWorkersCustodyFlow.World) (future : Future world nextWorld)
    (input output : Kind) (frame : NCode)
    (held : QueueWorkersJobFamilies.Edge total table owner world input output frame) :
    QueueWorkersJobFamilies.Edge total table owner nextWorld input output frame := by
  obtain ⟨index, owned⟩ := held
  refine ⟨index, ?_⟩
  cases index with
  | none =>
    exact ViewSavedAt.future (QueueWorkersJobGraph.model total table owner)
      (fun view => (interpAt (Programs.queueProgram total) view table).toPrimInterp) (fun _ => future) owned
  | some selected =>
    obtain ⟨kind, bindings, spec⟩ := selected
    exact (QueueWorkersNotificationEmbedding.embedding_at total table owner kind.val kind.property spec bindings []).edge_future_over
      (QueueWorkersJobGraph.Semantic total table owner)
      (CodeClosure.PredicateFamily.edge (QueueWorkersNotificationFlow.Code spec bindings))
      (fun _ _ later _ _ _ saved => ViewSavedAt.future (QueueWorkersJobGraph.model total table owner)
      (fun view => (interpAt (Programs.queueProgram total) view table).toPrimInterp) (fun _ => later) saved)
      (fun first last _ _ _ _ saved => by cases first; cases last; exact saved) world nextWorld future input output frame owned

/-- All saved families advance under the same custody order, even when an old successful input becomes empty. -/
theorem edge_future (total : Nat) (table : RowTable) (owner : FiberId)
    (world nextWorld : QueueWorkersCustodyFlow.World) (future : Future world nextWorld)
    (input output : Kind) (frame : NCode) (held : Edge total table owner world input output frame) :
    Edge total table owner nextWorld input output frame := by
  obtain ⟨index, owned⟩ := held
  refine ⟨index, ?_⟩
  cases index with
  | inl _ => exact worker_edge_future total table owner world nextWorld future input output frame owned
  | inr bindings =>
    exact (embedding total table owner bindings []).edge_future_over
      (QueueWorkersJobGraph.Semantic total table owner) (sourceLaws total table bindings).Edge
      (fun _ _ later _ _ _ saved => ViewSavedAt.future (QueueWorkersJobGraph.model total table owner)
      (fun view => (interpAt (Programs.queueProgram total) view table).toPrimInterp) (fun _ => later) saved)
      (fun first last _ _ _ _ saved => by cases first; cases last; exact saved) world nextWorld future input output frame owned

/-- An actual saved suffix transports without changing its classes or frames. -/
theorem path_future (total : Nat) (table : RowTable) (owner : FiberId)
    (world nextWorld : QueueWorkersCustodyFlow.World) (future : Future world nextWorld)
    {input output : Kind} {frames : List NCode}
    (held : Contracts.Path (Edge total table owner world) input output frames) :
    Contracts.Path (Edge total table owner nextWorld) input output frames :=
  held.map (fun first last frame saved => edge_future total table owner world nextWorld future first last frame saved)

/-- The actual ordinary source head enters the common stack without creating a job class. -/
theorem sourceHead (total : Nat) (table : RowTable) (owner : FiberId)
    (bindings : Option (List Val)) (view) (world : QueueWorkersCustodyFlow.World) (code : NCode)
    (owned : (sourceSpec total table bindings).code () code) :
    HeadAt (QueueWorkersJobGraph.model total table owner view)
      (interpAt (Programs.queueProgram total) view table).toPrimInterp (Edge total table owner) world .ordinary code := by
  apply indexed_head (QueueWorkersJobGraph.model total table owner view) _ (member total table owner) (.inr bindings)
  exact (embedding total table owner bindings view).head_over _ _ _ world True.intro () code
    ((sourceLaws total table bindings).head view () code owned)
end Test.Dogfood.Proofs.QueueWorkersJobSourceFamilies
