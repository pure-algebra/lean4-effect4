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

**Cycles.** The dependencies are not a DAG: an inductive type names its constructors, and each
constructor's type names the inductive. The walk finds these cycles as strongly connected
components (Tarjan's algorithm, on the explicit stack) and stores no answer for a constant until
its whole component has closed. It then stores the component root's answer for every member,
since every member of a component reaches the same constants. An earlier walk stored a member as
soon as its own frame closed. A member closed inside an open component read an empty
placeholder for the open part, and its short answer stayed in the memo: a constructor whose
sibling's type reached `Classical.choice` was stored with no axiom. The control is in
`Test/Audit/ProofGraph.lean`.
-/
namespace AxiomTypeCandidate
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
  | .axiomInfo v => v.type.getUsedConstants

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

/-- A frame of the explicit stack: the constant, its dependencies, the next one to visit, the
axioms gathered so far, its discovery index, and the least discovery index of an unfinished
component member its walk met (Tarjan's low link). -/
private structure Frame where
  name : Name
  deps : Array Name
  next : Nat
  acc : Array Name
  index : Nat
  low : Nat

/-- The axioms `root` reaches, and the `stop` leaves, with the memo threaded through; `none` only
if the step budget ran out, which no finite environment reaches. Each constant's answer enters
the memo when its component closes, and not before. -/
def reachedAxioms (env : Environment) (root : Name) (stop : Name → Bool := fun _ => false) :
    StateM AxiomMemo (Option (Array Name)) := do
  if let some known := (← get)[root]? then return some known
  -- the members of the components still open, by discovery index, and the order they were found
  let mut pending : Std.HashMap Name Nat := ({} : Std.HashMap Name Nat).insert root 0
  let mut found : Array Name := #[root]
  let mut counter := 1
  let mut stack : Array Frame :=
    #[{ name := root, deps := deps env stop root, next := 0, acc := selfAxiom env stop root,
        index := 0, low := 0 }]
  let mut result : Option (Array Name) := none
  for _ in [0:axiomBudget] do
    let some f := stack.back? | break
    if h : f.next < f.deps.size then
      let d := f.deps[f.next]
      let f := { f with next := f.next + 1 }
      if let some j := pending[d]? then
        -- a member of an open component: its answer arrives when the component closes
        stack := stack.set! (stack.size - 1) { f with low := min f.low j }
      else
        match (← get)[d]? with
        | some known => stack := stack.set! (stack.size - 1) { f with acc := union f.acc known }
        | none =>
          stack := stack.set! (stack.size - 1) f
          pending := pending.insert d counter
          found := found.push d
          stack := stack.push
            { name := d, deps := deps env stop d, next := 0, acc := selfAxiom env stop d,
              index := counter, low := counter }
          counter := counter + 1
    else
      stack := stack.pop
      if f.low == f.index then
        -- `f` roots its component: every member found since it reaches what `f` reaches
        for _ in [0:found.size] do
          let some m := found.back? | break
          found := found.pop
          pending := pending.erase m
          modify (·.insert m f.acc)
          if m == f.name then break
      match stack.back? with
      | none => result := some f.acc
      | some p =>
        stack := stack.set! (stack.size - 1)
          { p with acc := union p.acc f.acc, low := min p.low f.low }
  return result

/-- **The axioms one declaration reaches, exactly**: this walk with a fresh memo. Use it where
`Lean.collectAxioms` would serve. Lean 4.33's collector caches an answer for a constant closed
inside an open cycle, as this walk once did, and exports those answers in each module's `.olean`;
on 713 declarations of the law graph it omits `propext` that a plain search reaches (measured
2026-10-09). `none` only if the step budget ran out. -/
def exactAxioms (env : Environment) (name : Name) : Option (Array Name) :=
  ((reachedAxioms env name).run {}).1

/-- `reachedAxioms` for every root, in order, with the memo threaded through: one loop for a whole
list of declarations, which runs natively when this module is precompiled. -/
def reachedAxiomsMany (env : Environment) (roots : Array Name) (memo : AxiomMemo)
    (stop : Name → Bool := fun _ => false) : Array (Option (Array Name)) × AxiomMemo :=
  roots.foldl (init := (#[], memo)) fun (out, memo) root =>
    let (reached, memo) := (reachedAxioms env root stop).run memo
    (out.push reached, memo)

end AxiomTypeCandidate

open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let base ← getEnv
  let env ← match base.addDeclCore 0 1000 (.axiomDecl {
      name := `LocalAudit.A, levelParams := [], type := mkSort (.succ .zero), isUnsafe := false }) none with
    | .ok env => pure env
    | .error _ => throwError "synthetic type creation failed"
  let env ← match env.addDeclCore 0 1000 (.axiomDecl {
      name := `LocalAudit.a, levelParams := [], type := mkConst `LocalAudit.A, isUnsafe := false }) none with
    | .ok env => pure env
    | .error _ => throwError "synthetic value creation failed"
  let some got := AxiomTypeCandidate.exactAxioms env `LocalAudit.a | throwError "candidate budget"
  let expected ← withEnv env <| Lean.collectAxioms `LocalAudit.a
  unless got.qsort Name.lt == expected do throwError "type dependency mismatch: {got} versus {expected}"
  let (stopped, _) := (AxiomTypeCandidate.reachedAxioms env `LocalAudit.a (· == `LocalAudit.a)).run {}
  unless stopped == some #[`LocalAudit.a] do throwError "stopping leaf must hide its body and type dependencies"
  for name in [``propext, ``Quot.sound, ``Classical.choice] do
    let expected ← Lean.collectAxioms name
    let some actual := AxiomTypeCandidate.exactAxioms base name | throwError "candidate budget"
    unless actual.qsort Name.lt == expected do throwError "permitted-leaf mismatch: {name}: {actual} versus {expected}"
  unless ((← getEnv).find? `LocalAudit.A).isNone do throwError "synthetic environment escaped"
  logInfo "PASS: one-case extractor repair includes axiom-type dependencies, preserves stop leaves, and matches all three policy leaves."
