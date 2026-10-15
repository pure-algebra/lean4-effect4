import Effect4.Laws.Program.CodeClosure.Compile
import Effect4.Laws.Program.NativeScope

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumers: Qualified.suspend_at and QueueWorkers' classified notification callbacks.
One local constructor contract shares the existing direct-fragment source-body proof.
Stored thunk programs and wider generator or invocation profiles remain caller obligations.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure
open Effect4 Effect4.Machine Effect4.Program

/-- Actual source-body decisions use these existing compiled bodies and constructor results. -/
structure BodyContract (root : NativeEff) (point : Point → Prop) (code : NCode → Prop) : Prop where
  compiled : ∀ e p, Node.at_ (.eff root) p.path = some (.eff e) → point p → code (compileEff e p)
  frontier : ∀ p, point p → code (frontier p)
  child : ∀ p, point p → code (resolve root (p.child 0))
  selected : ∀ p first bound, point p → code (resolve root (p.childBind (cond first 0 1) bound))
  loop : ∀ p cursor, point p → code (.whileLoop (.loop p) cursor)
  badShape : code badShape

/-- The direct source body's actual interpreter decisions consume one local constructor contract. -/
theorem suspend_body_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (code : NCode → Prop) (contract : BodyContract root point code)
    (p : Point) (held : point p) : code (suspendBodyAt root (.body p)) := by
  revert held
  generalize argument : EffThunk.body p = thunk
  revert p
  fun_cases suspendBodyAt root thunk
  all_goals intro p argument held
  all_goals cases argument
  all_goals aesop (add norm simp [SourceScope.directHead]) (add safe apply [contract.compiled, contract.frontier, contract.child, contract.selected, contract.loop, contract.badShape]) (add safe forward [SourceScope.Fragment.at])

end Effect4.Program.CodeClosure
