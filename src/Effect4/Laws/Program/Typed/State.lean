import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Auto.TypedStateDecl
import Effect4.Laws.Auto.PositionGate

/-!
The reference machine's typed-state skeleton. Lean derives the declarations during
elaboration; the source table is the only hand-maintained input. The position gate covers
all four census roots, including interpreter hooks; the skeleton covers stored state and
command residue. Refused source rows remain explicit debt, not proved invariant clauses.
-/
namespace Effect4.Program.Typed

/-- Where a position's expected type comes from, as data the predicates read. -/
inductive Expect
  | root
  | fiber (id : Effect4.FiberId)
  | promise (cell : Effect4.Machine.DeferredKey)
  | refColumn
  | row (op : Effect4.Program.NativeOp)
  | checker (point : Effect4.Program.Point)
  | const (ty : Effect4.Program.EffTy)
  | hook (name : String)


#position_gate Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
  Effect4.Program.Sched.RInterp Effect4.Program.Sched.RIter

#typed_state Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
  using Effect4.Program.Typed.sources columns Effect4.Machine.Stores

/-- The named bank assembles a saved-frame invariant from its three clauses. -/
theorem saved_from_clauses {W : Type} (P : Preds W) (w : W) (e : Expect)
    (x : Effect4.Program.Sched.RSaved)
    (current : P.program w e x.current) (stack : P.StackOk w e x.stack)
    (interrupted : P.InterruptOnly w e x.interruptedCause) : RSavedOk P w e x := by
  aesop (rule_sets := [Effect4.TypedState])

end Effect4.Program.Typed
