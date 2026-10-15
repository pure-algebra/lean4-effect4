import Effect4.Laws.Program.AnswerSlots.InitializedFrame
import Effect4.Laws.Program.NativeActionRows

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the initialized crew model supplies the common native action facts.
Reach: the ready stable root class, actual administrative programs and uniform saved edges.
Limit: actual source-action and captured-scope ownership remain producer premises.
Consumer: the shared native action evaluation in both crew history proofs.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- The broad stable class supplies every administrative answer and actual action control edge. -/
theorem action_facts (spec : Spec) (view : List (FiberId × ExitV)) (world : World)
    (ready : Ready spec world) :
    SourceScope.ActionFlowFacts (model spec view) (Edge spec view)
      spec.root view spec.table world (.stable .root) where
  value := fun _ => ⟨ready, trivial⟩
  cause := fun _ => .inr ready
  interrupt := fun _ => .stable ready ⟨rfl, trivial, trivial, trivial⟩
  interruptAs := fun _ _ => .stable ready ⟨rfl, trivial, trivial, trivial⟩
  park := fun _ => .stable ready ⟨rfl, trivial, trivial, trivial⟩
  mask := mask_edge_flag spec view world (.stable .root)
  cancel := fun _ _ => .mapped ready (Typed.async_edge spec.toSpec view _)

end Effect4.Program.AnswerSlots.Initialized
