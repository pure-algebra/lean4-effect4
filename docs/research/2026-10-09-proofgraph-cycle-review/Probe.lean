import ProofGraph.Axioms
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0


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
namespace CycleCandidate
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

end CycleCandidate


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
namespace OldLimited
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
def axiomBudget : Nat := 4

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

end OldLimited


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
namespace NewLimited
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
def axiomBudget : Nat := 4

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

end NewLimited


namespace CycleAudit
open Lean Elab Command

def leafOne : Nat := 1
def leafTwo : Nat := 2
inductive Sibling where
  | quiet : Sibling
  | loud : Fin (leafOne + 1) → Sibling
def entry : Type := Sibling

inductive TwoLeaves where
  | quiet : TwoLeaves
  | one : Fin (leafOne + 1) → TwoLeaves
  | two : Fin (leafTwo + 1) → TwoLeaves

mutual
  inductive LeftCycle where
    | quiet : LeftCycle
    | right : RightCycle → LeftCycle
  inductive RightCycle where
    | left : LeftCycle → RightCycle
    | loud : Fin (leafTwo + 1) → RightCycle
end

noncomputable def choiceSize : Nat := Classical.choice (show Nonempty Nat from ⟨1⟩)
inductive ChoiceCycle where
  | quiet : ChoiceCycle
  | loud : Fin (choiceSize + 1) → ChoiceCycle
def choiceEntry : Type := ChoiceCycle

/-- Fresh reachability, with no shared per-root answers or cycle summaries.
The edge policy is the landed extractor, except that axiom types are visited. -/
def fresh (env : Environment) (root : Name) (stop : Name → Bool) : Option (Array Name) := Id.run do
  let mut todo := #[root]
  let mut visited : Std.HashSet Name := {}
  let mut out : Array Name := #[]
  for _ in [0:1000000] do
    let some name := todo.back? | return some out
    todo := todo.pop
    if !visited.contains name then
      visited := visited.insert name
      if stop name then
        if !out.contains name then out := out.push name
      else
        match env.find? name with
        | some (.axiomInfo info) =>
          if !out.contains name then out := out.push name
          todo := todo ++ info.type.getUsedConstants
        | some info => todo := todo ++ ProofGraph.usedConstantsOf info
        | none => pure ()
  return none

def same (a b : Array Name) : Bool := a.all b.contains && b.all a.contains

def checkMemo (env : Environment) (stop : Name → Bool) (memo : ProofGraph.AxiomMemo) : Bool :=
  memo.toArray.all fun (name, got) =>
    match fresh env name stop with
    | none => false
    | some want => same got want

run_cmd do
  let env ← getEnv
  let stop := fun name => name == ``leafOne || name == ``leafTwo
  let groups := #[
    #[``entry, ``Sibling.quiet, ``Sibling.loud],
    #[``Sibling.quiet, ``entry, ``Sibling.loud],
    #[``TwoLeaves, ``TwoLeaves.quiet, ``TwoLeaves.one, ``TwoLeaves.two],
    #[``LeftCycle, ``LeftCycle.quiet, ``RightCycle.left, ``RightCycle.loud],
    #[``Nat.zero, ``Nat, ``leafOne]]
  let mut count := 0
  for roots in groups do
    let (got, memo) := CycleCandidate.reachedAxiomsMany env roots {} stop
    for i in [0:roots.size] do
      let some expected := fresh env roots[i]! stop | throwError "oracle budget"
      let some actual := got[i]! | throwError "candidate budget"
      unless same actual expected do
        throwError "candidate mismatch {roots[i]!}: {actual} versus {expected}"
      count := count + 1
    unless checkMemo env stop memo do throwError "candidate memo contains an incomplete answer"
  let (old, _) := ProofGraph.reachedAxiomsMany env #[``entry, ``Sibling.quiet] {} stop
  unless old[1]! == some #[] do throwError "landed negative control no longer reproduces: {old}"
  logInfo m!"PASS: {count} selected-leaf roots and all retained candidate memo entries; landed cycle misses leafOne."

run_cmd do
  let env ← getEnv
  let stop := fun _ => false
  let roots := #[``choiceEntry, ``ChoiceCycle.quiet, ``ChoiceCycle.loud]
  let (old, _) := ProofGraph.reachedAxiomsMany env roots {}
  let (got, memo) := CycleCandidate.reachedAxiomsMany env roots {}
  for i in [0:roots.size] do
    let some expected := fresh env roots[i]! stop | throwError "oracle budget"
    let some actual := got[i]! | throwError "candidate budget"
    unless same actual expected && actual.contains ``Classical.choice do
      throwError "choice mismatch {roots[i]!}: {actual} versus {expected}"
  let some oldQuiet := old[1]! | throwError "landed budget"
  if oldQuiet.contains ``Classical.choice then throwError "landed choice control no longer reproduces"
  unless checkMemo env stop memo do throwError "candidate choice memo contains an incomplete answer"
  logInfo m!"PASS: 3 axiom-bearing roots and their memo; landed quiet constructor misses Classical.choice."

run_cmd do
  let env ← getEnv
  let stop := fun name => name == ``leafOne
  let (old, oldMemo) := (OldLimited.reachedAxioms env ``entry stop).run {}
  let (got, memo) := (NewLimited.reachedAxioms env ``entry stop).run {}
  unless old.isNone && got.isNone do throwError "budget control must interrupt both walks"
  if checkMemo env stop oldMemo then throwError "landed interrupted memo control failed"
  unless checkMemo env stop memo do throwError "candidate interrupted memo contains a false answer"
  let (resumed, resumedMemo) := CycleCandidate.reachedAxiomsMany env #[``entry, ``Sibling.quiet] memo stop
  for (name, actual) in #[``entry, ``Sibling.quiet].zip resumed do
    let some actual := actual | throwError "candidate resume budget"
    let some expected := fresh env name stop | throwError "oracle budget"
    unless same actual expected do throwError "candidate resume mismatch"
  unless checkMemo env stop resumedMemo do throwError "resumed memo contains a false answer"
  logInfo m!"PASS: reduced-budget interruption refuses an answer, preserves valid memo, and safely resumes. Old memo is incomplete."

-- Construct local environment data. No declaration is added to the compiling environment.
run_cmd do
  let base ← getEnv
  let env ← match base.addDeclCore 0 1000 (.axiomDecl {
      name := `CycleSynthetic.A, levelParams := [], type := mkSort (.succ .zero), isUnsafe := false }) none with
    | .ok env => pure env
    | .error _ => throwError "synthetic type creation failed"
  let env ← match env.addDeclCore 0 1000 (.axiomDecl {
      name := `CycleSynthetic.a, levelParams := [], type := mkConst `CycleSynthetic.A, isUnsafe := false }) none with
    | .ok env => pure env
    | .error _ => throwError "synthetic value creation failed"
  let some got := CycleCandidate.exactAxioms env `CycleSynthetic.a | throwError "candidate budget"
  let expected ← withEnv env <| Lean.collectAxioms `CycleSynthetic.a
  unless same expected #[`CycleSynthetic.A, `CycleSynthetic.a] do
    throwError "Lean oracle differs: {expected}"
  unless same got #[`CycleSynthetic.a] do throwError "candidate axiom-type omission no longer reproduces: {got}"
  unless ((← getEnv).find? `CycleSynthetic.A).isNone do throwError "synthetic environment escaped"
  logInfo m!"PASS: pre-existing axiom-type omission reproduced. Candidate {got}; pinned Lean {expected}. Synthetic declarations did not escape."
end CycleAudit
