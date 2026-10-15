import Effect4.Laws.Program.AnswerSlots.Points
import Test.Dogfood.Proofs.QueueWorkersCustody
import Effect4.Laws.Program.CodeClosure.Qualified.Stable

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.jobs_step, between an actual attempt and its protected result callback.
Notification segments use the existing qualified compiler, callback and stable-family proofs.
Their source certificate excludes reference writers and the feeder's offer-entry event.
The request-phase filter and typed boundary callbacks remain separate consumers.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersCustodySegments
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario.QueueWorkers

/-- A selected notification subtree only posts deferred answers. -/
structure Spec (root : NativeEff) where
  origin : List Nat
  rows : ∀ path row request, origin.IsPrefix path →
    Node.at_ (.eff root) path = some (.eff (.perform row request)) → row = .deferredSucceed
  noFeed : ¬ origin.IsPrefix offerEntryPath

/-- A notification point keeps its entire captured prefix inside the selected source subtree. -/
def PointAt {root : NativeEff} (spec : Spec root) (bindings : List Val) (point : Point) : Prop :=
  spec.origin.IsPrefix point.path ∧ AnswerSlots.Prefix bindings point.env

/-- The existing point transport preserves this source region and all captured payload slots. -/
theorem transport {root : NativeEff} (spec : Spec root) (bindings : List Val) :
    CodeClosure.Qualified.Transport (PointAt spec bindings) (AnswerSlots.Prefix bindings) where
  environment := fun held => held.2
  child := fun held _ => ⟨List.prefix_append_of_prefix held.1, held.2⟩
  childWith := fun held _ value => ⟨List.prefix_append_of_prefix held.1, held.2.append [value]⟩
  capture := fun held value _ => ⟨held.1, held.2.append [value]⟩

/-- Every actual operation of this source region satisfies the reference-writer exclusion. -/
theorem operation {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (point : Point) (row : NativeOp) (request : Term) (value : Val) (op : SyncOp)
    (found : Node.at_ (.eff root) point.path = some (.eff (.perform row request)))
    (held : PointAt spec bindings point) (selected : row.syncOpOf point.env value = some op) :
    CodeClosure.Qualified.OpAt (PointAt spec bindings) (AnswerSlots.Prefix bindings) (fun _ => False) op := by
  have rowEq := spec.rows point.path row request held.1 found
  fun_cases NativeOp.syncOpOf row point.env value
  all_goals aesop (add norm simp [NativeOp.syncOpOf, CodeClosure.Qualified.OpAt])

/-- The common compiler and callback contract supplies the notification source graph. -/
theorem contract {root : NativeEff} (spec : Spec root) (bindings : List Val) :
    CodeClosure.Qualified.Contract root (PointAt spec bindings) (AnswerSlots.Prefix bindings) (fun _ => False) where
  compilation := CodeClosure.Qualified.compile_contract _ _ _ _ (transport spec bindings)
    (fun point row request value op found held _ selected => operation spec bindings point row request value op found held selected)
  child := (transport spec bindings).child
  childWith := (transport spec bindings).childWith
  capture := (transport spec bindings).capture

/-- Completed-fiber views change neither notification paths nor immutable payload slots. -/
theorem view_stable {root : NativeEff} (spec : Spec root) (bindings : List Val) :
    CodeClosure.Qualified.ViewStable (PointAt spec bindings) := fun _ held _ => held

/-- Notification segments instantiate the existing stable family without another code traversal. -/
def laws {root : NativeEff} (spec : Spec root) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (table : RowTable) :
    AnswerSlots.StableLaws (CodeClosure.Qualified.prefixSpec root table (PointAt spec bindings)
      (AnswerSlots.Prefix bindings) (fun _ => False)) :=
  CodeClosure.Qualified.prefixLaws root fragment _ _ _ (contract spec bindings) (view_stable spec bindings) table

/-- An actual source entry seeds the notification graph at the full captured environment. -/
theorem entry {root : NativeEff} (spec : Spec root) (fragment : SourceScope.Fragment root)
    (point : Point) (inside : spec.origin.IsPrefix point.path) :
    CodeClosure.Qualified.CodeAt (PointAt spec point.env) (AnswerSlots.Prefix point.env) (fun _ => False)
      (resolve root point) :=
  CodeClosure.Qualified.resolve_at root fragment _ _ _ (contract spec point.env) point
    ⟨inside, List.take_length⟩

/-- A source notification segment cannot smuggle a queue modify into a broad callback class. -/
theorem no_modify {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (cell : RefKey) (term : Term) (env : List Val) :
    ¬ CodeClosure.Qualified.CodeAt (PointAt spec bindings) (AnswerSlots.Prefix bindings) (fun _ => False)
      (.sync (.op (.refModify cell term env))) := fun impossible => impossible

/-- A source notification segment cannot append an assignment through its broad callback class. -/
theorem no_update {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (cell : RefKey) (term : Term) (env : List Val) :
    ¬ CodeClosure.Qualified.CodeAt (PointAt spec bindings) (AnswerSlots.Prefix bindings) (fun _ => False)
      (.sync (.op (.refUpdate cell term env))) := fun impossible => impossible

/-- A retained source callback in the segment cannot emit an offer-entry feeding event. -/
theorem no_feed {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (fiber : FiberId) (body : NCode) (point : Point) (held : PointAt spec bindings point) :
    fedAt (.frame fiber (.pushed (.onSuccess body (.cont point)))) = none := by
  have different : point.path ≠ offerEntryPath := fun same => spec.noFeed (same ▸ held.1)
  change (if point.path == offerEntryPath then point.env[10]? else none) = none
  exact if_neg (fun same => different (beq_iff_eq.mp same))

/-- The actual current notification bind emits no feeding observation when it pushes its saved callback. -/
theorem no_feed_code {root : NativeEff} (spec : Spec root) (bindings : List Val)
    (fiber : FiberId) (body : NCode) (point : Point)
    (owned : CodeClosure.Qualified.CodeAt (PointAt spec bindings) (AnswerSlots.Prefix bindings) (fun _ => False)
      (.onSuccess body (.cont point))) :
    fedAt (.frame fiber (.pushed (.onSuccess body (.cont point)))) = none :=
  no_feed spec bindings fiber body point owned.2

end Test.Dogfood.Proofs.QueueWorkersCustodySegments
