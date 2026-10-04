import Lean

/-!
The axioms a declaration reaches, memoized across declarations. `Lean.collectAxioms` walks the
dependency graph afresh on every call; the whole-library gate (`Test/Audit/AxiomGate.lean`) and
the semantics report (`tools/Tools/Semantics.lean`) ask the question for thousands of
declarations that share most of their dependencies, so the memo is what makes them linear in the
graph instead of quadratic. The traversal is `Lean.CollectAxioms.collect`'s: a declaration's type
and value, an inductive's type and its constructors, an axiom itself. A constant that `stop`
selects is a leaf: the walk reports it among the axioms and does not enter it. The planned goals
are such leaves (`ProofGraph.Goal`, decisions row 203), so a theorem that rests on a goal reaches
the goal's name and not its `sorry`. One memo serves one `stop`. The walk runs on an explicit
stack, since a proof's dependency chain is thousands deep and the interpreter's native stack is
not; the step budget is a loop bound, and running out of it is an answered `none`, never an
empty set.
-/
namespace ProofGraph
open Lean

abbrev AxiomMemo := Std.HashMap Name (Array Name)

private def union (acc : Array Name) (xs : Array Name) : Array Name :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) acc

/-- The constants a declaration's own content names, as `collectAxioms` reads it. -/
def usedConstantsOf : ConstantInfo → Array Name
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .quotInfo _ => #[]
  | .axiomInfo _ => #[]

private def deps (env : Environment) (stop : Name → Bool) (c : Name) : Array Name :=
  if stop c then #[] else
  match env.find? c with
  | some ci => usedConstantsOf ci
  | none => #[]

private def selfAxiom (env : Environment) (stop : Name → Bool) (c : Name) : Array Name :=
  if stop c then #[c] else
  match env.find? c with
  | some (.axiomInfo _) => #[c]
  | _ => #[]

/-- Steps the traversal may take in one call: more than the edges of any environment. -/
def axiomBudget : Nat := 1000000000

/-- A frame of the explicit stack: the constant, its dependencies, the next one to visit, and
the axioms gathered so far. -/
private abbrev Frame := Name × Array Name × Nat × Array Name

/-- The axioms `root` reaches, and the `stop` leaves, with the memo threaded through; `none` only
if the step budget ran out, which no finite environment reaches. -/
def reachedAxioms (env : Environment) (root : Name) (stop : Name → Bool := fun _ => false) :
    StateM AxiomMemo (Option (Array Name)) := do
  if let some known := (← get)[root]? then return some known
  let mut stack : Array Frame := #[(root, deps env stop root, 0, selfAxiom env stop root)]
  let mut result : Option (Array Name) := none
  for _ in [0:axiomBudget] do
    if stack.isEmpty then break
    let (c, ds, i, acc) := stack.back!
    if h : i < ds.size then
      let d := ds[i]
      stack := stack.set! (stack.size - 1) (c, ds, i + 1, acc)
      match (← get)[d]? with
      | some known => stack := stack.set! (stack.size - 1) (c, ds, i + 1, union acc known)
      | none =>
        -- the environment's constants form a DAG; a provisional entry only guards a cycle
        modify (·.insert d #[])
        stack := stack.push (d, deps env stop d, 0, selfAxiom env stop d)
    else
      modify (·.insert c acc)
      stack := stack.pop
      if stack.isEmpty then result := some acc
      else
        let (p, pds, pi, pacc) := stack.back!
        stack := stack.set! (stack.size - 1) (p, pds, pi, union pacc acc)
  return result

/-- `reachedAxioms` for every root, in order, with the memo threaded through: one loop for a whole
list of declarations, which runs natively when this module is precompiled. -/
def reachedAxiomsMany (env : Environment) (roots : Array Name) (memo : AxiomMemo)
    (stop : Name → Bool := fun _ => false) : Array (Option (Array Name)) × AxiomMemo :=
  roots.foldl (init := (#[], memo)) fun (out, memo) root =>
    let (reached, memo) := (reachedAxioms env root stop).run memo
    (out.push reached, memo)

end ProofGraph
