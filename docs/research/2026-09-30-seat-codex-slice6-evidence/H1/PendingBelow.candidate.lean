import Effect4.Laws.Program.Typed.Assembly

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program.Sched

/-- Every pending token is below the machine allocator. The generated pending predicate
supplies a token declaration; WorldValid bounds every such declaration, even though the
pending predicate does not receive its enclosing fiber. No extra pending-token clause is
needed in the typed state. -/
theorem pending_below (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (typed : TypedState root rootTy w m) (f : RFiber) (hf : f ∈ m.fibers)
    (p : Pending EffName Val Err Defect FiberId Ann) (hp : p ∈ f.pending) :
    p.token < m.nextToken := by
  obtain ⟨id, declared⟩ := (typed.2.1.c0 f hf).c1 p hp
  cases h : w.Θ id p.token with
  | none => rw [h] at declared; cases declared
  | some tokenTy => exact typed.1.tokenBound id p.token tokenTy h

#print axioms pending_below
end Effect4.Program.Typed
