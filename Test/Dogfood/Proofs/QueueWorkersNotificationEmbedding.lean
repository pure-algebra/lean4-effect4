import Test.Dogfood.Proofs.QueueWorkersJobFamily

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, between an actual take and its option/retry branch.
The existing strict notification family preserves the captured option at its classified input.
Failures unwind without asserting that a waiting or held request still exists.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace Test.Dogfood.Proofs.QueueWorkersNotificationEmbedding
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open Test.Dogfood.Scenario
open QueueWorkersCustodyFlow

/-- One actual source notification region supplies the old unit-class model. -/
def oldSpec (total : Nat) (table : RowTable) (spec : QueueWorkersNotificationFlow.Spec (Programs.queueProgram total))
    (bindings : List Val) :=
  CodeClosure.PredicateFamily.spec (Programs.queueProgram total) table (QueueWorkersNotificationFlow.Code spec bindings)
    (QueueWorkersNotificationFlow.rules spec (SourceFragment.queue_fragment total) bindings table)

/-- The current input supplies its literal request and option; a failure supplies no such fact. -/
theorem embedding (total : Nat) (table : RowTable) (owner : FiberId) (token : Nat) (option : Val)
    (spec : QueueWorkersNotificationFlow.Spec (Programs.queueProgram total)) (bindings : List Val)
    (view : List (FiberId × ExitV)) :
    ClassifiedInputEmbedding ((oldSpec total table spec bindings).model view)
      (QueueWorkersJobGraph.model total table owner view) (fun _ => ())
      (fun _ => Kind.snapshot owner token option)
      (fun world => Owns world owner token ∧ QueueWorkersCustody.OptionAt world.requests.custody token option) where
  future _ _ _ := trivial
  value_ready _ _ _ good := good
  value_read _ _ _ _ _ := trivial
  value_write _ _ _ ready _ := ready
  cause_read _ _ _ _ _ := trivial
  cause_write _ _ _ _ _ := trivial
  code _ _ _ ready owned := .notification spec ready owned
  finalizer _ _ _ _ := rfl

/-- Existing semantic binders and source notification edges share the same actual answer classes. -/
def Edge (total : Nat) (table : RowTable) (owner : FiberId) (token : Nat) (option : Val)
    (spec : QueueWorkersNotificationFlow.Spec (Programs.queueProgram total)) (bindings : List Val) :=
  ClassifiedEdgeOver (fun _ => ()) (fun _ => Kind.snapshot owner token option)
    (QueueWorkersJobGraph.Semantic total table owner)
    (CodeClosure.PredicateFamily.edge (QueueWorkersNotificationFlow.Code spec bindings))

/-- The conditional-family adapter consumes the actual classified option and the existing saved arms. -/
theorem family (total : Nat) (table : RowTable) (owner : FiberId) (token : Nat) (option : Val)
    (spec : QueueWorkersNotificationFlow.Spec (Programs.queueProgram total)) (bindings : List Val)
    (view : List (FiberId × ExitV)) :
    SavedFamily (QueueWorkersJobGraph.model total table owner view)
      (interpAt (Programs.queueProgram total) view table).toPrimInterp
      (Edge total table owner token option spec bindings) :=
  (embedding total table owner token option spec bindings view).family_over
    (interpAt (Programs.queueProgram total) view table).toPrimInterp
    (QueueWorkersJobGraph.Semantic total table owner)
    (CodeClosure.PredicateFamily.edge (QueueWorkersNotificationFlow.Code spec bindings))
    (QueueWorkersJobGraph.semantic_family total table owner view)
    (CodeClosure.PredicateFamily.family (Programs.queueProgram total) table _
      (QueueWorkersNotificationFlow.rules spec (SourceFragment.queue_fragment total) bindings table) view)
    (QueueWorkersNotificationFlow.cause_transfer spec bindings _ _ _ _ (fun _ _ => trivial))

/-- The actual notification head retains the same captured option while its helper bodies run. -/
theorem head (total : Nat) (table : RowTable) (owner : FiberId) (token : Nat) (option : Val)
    (spec : QueueWorkersNotificationFlow.Spec (Programs.queueProgram total)) (bindings : List Val)
    (view : List (FiberId × ExitV)) (world : QueueWorkersCustodyFlow.World) (code : NCode)
    (phase : Owns world owner token ∧ QueueWorkersCustody.OptionAt world.requests.custody token option)
    (owned : QueueWorkersNotificationFlow.Code spec bindings code) :
    HeadAt (QueueWorkersJobGraph.model total table owner view)
      (interpAt (Programs.queueProgram total) view table).toPrimInterp
      (Edge total table owner token option spec bindings) world (.snapshot owner token option) code :=
  (embedding total table owner token option spec bindings view).head_over
    (interpAt (Programs.queueProgram total) view table).toPrimInterp
    (QueueWorkersJobGraph.Semantic total table owner) _ world phase () code
    (CodeClosure.PredicateFamily.head (Programs.queueProgram total) table _
      (QueueWorkersNotificationFlow.rules spec (SourceFragment.queue_fragment total) bindings table) view code owned)
end Test.Dogfood.Proofs.QueueWorkersNotificationEmbedding
