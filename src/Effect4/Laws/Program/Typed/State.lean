import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Program.Typed.TypedStateDecl
import Effect4.Laws.Program.Typed.PositionGate

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
  | hook (name : String)


#position_gate Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
  Effect4.Program.Sched.RInterp Effect4.Program.Sched.RIter

/-- info: typed state: 17 predicates, 10 carrier predicates, 2 refusals -/
#guard_msgs in
#typed_state Effect4.Program.Sched.RState Effect4.Program.Sched.RCmd
  using Effect4.Program.Typed.sources columns Effect4.Machine.Stores

end Effect4.Program.Typed
