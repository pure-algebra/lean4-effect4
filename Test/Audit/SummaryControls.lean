import ProofGraph.AxiomAudit
import Tools.View.FlowReach

/-!
# Controls of the checked summaries

The battery of `dependency-summary-exact` (`tools/Tools/Graph/Summary.lean`), of its consumer at
the axiom walk (`tools/ProofGraph/Summary.lean`), and of `view-reachability-summary-exact`
(`tools/Tools/View/FlowReach.lean`). Each line is a reader of a law at a real graph, a control
that shows where `check` refuses, or a finite evaluation that no theorem covers (decisions
row 301). The controls port the research probe's
(`docs/research/2026-10-09-openai-math-probe/Reachability.lean`, `ProofGraphProbe.lean` and
`FlowReachability.lean`).
-/

namespace Test.Audit.SummaryControls

open Tools.Graph.Summary

/-! ## The summary law -/

/-- Two nodes on a cycle; only the second seeds the label. -/
def cycleWithSeed : Graph 2 1 :=
  { seeds := ⟨#[[], [0]], rfl⟩, children := ⟨#[[1], [0]], rfl⟩ }

/-- The shortest distances of `cycleWithSeed`. -/
def good : Distances 2 1 := ⟨#[⟨#[some 1], rfl⟩, ⟨#[some 0], rfl⟩], rfl⟩

/-- Large stored distances: `check` compares them and searches nothing below them. -/
def largeDistances : Distances 2 1 :=
  ⟨#[⟨#[some 1000000000], rfl⟩, ⟨#[some 999999999], rfl⟩], rfl⟩

/-- The first node leaves out the label its child holds. -/
def missing : Distances 2 1 := ⟨#[⟨#[none], rfl⟩, ⟨#[some 0], rfl⟩], rfl⟩

/-- The same cycle with no seed. -/
def seedlessCycle : Graph 2 1 :=
  { seeds := ⟨#[[], []], rfl⟩, children := ⟨#[[1], [0]], rfl⟩ }

/-- A label that the cycle supports only by itself. -/
def invented : Distances 2 1 := ⟨#[⟨#[some 1], rfl⟩, ⟨#[some 1], rfl⟩], rfl⟩

/-- No entry at all. -/
def empty : Distances 2 1 := ⟨#[⟨#[none], rfl⟩, ⟨#[none], rfl⟩], rfl⟩

/-- Two labels on one cycle, each seeded at a different node. -/
def twoSeeds : Graph 2 2 :=
  { seeds := ⟨#[[0], [1]], rfl⟩, children := ⟨#[[1], [0]], rfl⟩ }

/-- Distances per node and label: the two labels descend in opposite directions. -/
def twoDistances : Distances 2 2 :=
  ⟨#[⟨#[some 0, some 1], rfl⟩, ⟨#[some 1, some 0], rfl⟩], rfl⟩

/-- One distance per node, the same for both labels. -/
def nodeRank : Distances 2 2 :=
  ⟨#[⟨#[some 0, some 0], rfl⟩, ⟨#[some 1, some 1], rfl⟩], rfl⟩

-- reader: `check_summary_exact` at a cyclic graph gives a path from the reported label
example : Reaches cycleWithSeed 0 0 :=
  (check_summary_exact (by decide : check cycleWithSeed good = true) 0 0).mp (by decide)

-- reader: the same law at large distances
example : Reaches cycleWithSeed 0 0 :=
  (check_summary_exact (by decide : check cycleWithSeed largeDistances = true) 0 0).mp (by decide)

-- reader: an accepted empty table proves that the seedless cycle reaches no label
example : ¬ Reaches seedlessCycle 0 0 := fun path =>
  (by decide : ¬ Present empty 0 0)
    ((check_summary_exact (by decide : check seedlessCycle empty = true) 0 0).mpr path)

-- red: an omitted label is refused
#guard !check cycleWithSeed missing

-- red: the first two conditions alone accept the invented label, and the descending distance
-- refuses it
example : (∀ u l, l ∈ seedlessCycle.seeds[u] → Present invented u l) ∧
    (∀ u v, v ∈ seedlessCycle.children[u] → ∀ l, Present invented v l → Present invented u l) := by
  decide
#guard !check seedlessCycle invented

-- green: distances per node and label accept opposite directions on one cycle; red: one distance
-- per node is refused there
#guard check twoSeeds twoDistances
#guard !check twoSeeds nodeRank

-- finite evaluation: the breadth-first table is accepted and holds the shortest distances
#guard (summarize cycleWithSeed).isSome
#guard distances cycleWithSeed == good
#guard distances twoSeeds == twoDistances
#guard (summarize seedlessCycle).isSome && distances seedlessCycle == empty

/-! ## The axiom walk's answers -/

/-- A leaf of the walk, selected by `stop`, as a planned goal is. -/
def memoLeaf : Nat := 0

/-- An inductive type names its constructors, and each constructor names the type: a cycle. -/
inductive MemoCycle where
  | quiet : MemoCycle
  | loud : Fin (memoLeaf + 1) → MemoCycle

def memoEntry : Type := MemoCycle

open Lean ProofGraph in
-- green: the walk's answers over the cycle are accepted, and `quiet` reports the leaf through
-- `MemoCycle` and `loud`; red: the same table without `quiet`'s answer, and with a label at
-- `Nat`, which reaches no leaf, are refused
#guard_msgs in
run_cmd do
  let env ← getEnv
  let stop := (· == ``memoLeaf)
  let .ok c := checkDependencies env #[``memoEntry, ``MemoCycle.quiet] stop
    | throwError "the walk's answers over the cycle were refused"
  let names := c.snapshot.names
  let some qi := names.idxOf? ``MemoCycle.quiet | throwError "quiet was not captured"
  let some ni := names.idxOf? ``Nat | throwError "Nat was not captured"
  if h : qi < names.size then
    unless c.reported ⟨qi, h⟩ == #[``memoLeaf] do throwError "quiet's answer changed"
  else throwError "quiet's position is out of range"
  unless c.snapshot.labels == #[``memoLeaf] do throwError "the labels changed"
  let table := c.summary.table
  let edit (at_ : Nat) (entry : Option Nat) : Distances names.size c.snapshot.labels.size :=
    Vector.ofFn fun v => Vector.ofFn fun l =>
      if v.val == at_ then entry else distance table v l
  if check c.snapshot.graph (edit qi none) then throwError "an omitted answer was accepted"
  if check c.snapshot.graph (edit ni (some 0)) then throwError "an invented answer was accepted"

open Lean ProofGraph in
-- red: an exhausted capture and a constant with no declaration are refused, never an empty graph
#guard_msgs in
run_cmd do
  let env ← getEnv
  let stop := (· == ``memoLeaf)
  unless (captureDependencies env #[``memoEntry] stop 0).toOption.isNone do
    throwError "an exhausted capture was accepted"
  unless (captureDependencies env #[`Test.Audit.SummaryControls.absent] stop).toOption.isNone do
    throwError "a constant with no declaration was accepted"

-- green: the checked mode of `#axiom_audit` accepts the walk's answers over a real module
/--
info: #axiom_audit: 52 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals; checked: the walk's answers at 197 constants agree with their captured graph, over the labels [propext]
-/
#guard_msgs in
#axiom_audit checked Tools.Graph.Path

/-! ## The flow's directed reachability -/

open Tools.View.Flow

def directed : List Edge := [{ fr := 0, to := 1 }, { fr := 1, to := 2 }]
def directedAnswers : Distances 3 3 :=
  ⟨#[⟨#[some 0, some 1, some 2], rfl⟩, ⟨#[none, some 0, some 1], rfl⟩,
     ⟨#[none, none, some 0], rfl⟩], rfl⟩
def reversedAnswer : Distances 3 3 :=
  ⟨#[⟨#[some 0, some 1, some 2], rfl⟩, ⟨#[none, some 0, some 1], rfl⟩,
     ⟨#[some 1, none, some 0], rfl⟩], rfl⟩

def flowCycle : List Edge := [{ fr := 0, to := 1 }, { fr := 1, to := 0 }]
def cycleAnswers : Distances 2 2 :=
  ⟨#[⟨#[some 0, some 1], rfl⟩, ⟨#[some 1, some 0], rfl⟩], rfl⟩

def badTarget : List Edge := [{ fr := 0, to := 2 }]
def badSource : List Edge := [{ fr := 2, to := 0 }]

/-- A path from 0 to 1 through position 2, outside the bound 2. -/
def missingIntermediate : List Edge := [{ fr := 0, to := 2 }, { fr := 2, to := 1 }]
def identities : Distances 2 2 := ⟨#[⟨#[some 0, none], rfl⟩, ⟨#[none, some 0], rfl⟩], rfl⟩

-- reader: `checkReach_exact` gives the directed path, and refuses the reversed one
example : Reach directed 0 2 :=
  (checkReach_exact (by decide : checkReach 3 directed directedAnswers = true) 0 2).mp (by decide)
example : ¬ Reach directed 2 0 := fun reversed =>
  (by decide : ¬ Present directedAnswers 2 0)
    ((checkReach_exact (by decide : checkReach 3 directed directedAnswers = true) 2 0).mpr
      reversed)

-- reader: on a cycle both directions hold
example : Reach flowCycle 1 0 :=
  (checkReach_exact (by decide : checkReach 2 flowCycle cycleAnswers = true) 1 0).mp (by decide)

-- red: a reversed answer is refused
#guard !checkReach 3 directed reversedAnswer

-- red: an end at or above the bound is refused, from either side of the edge
#guard !checkReach 2 badTarget cycleAnswers
#guard !checkReach 2 badSource cycleAnswers
#guard (ReachTable.build? 2 badTarget).isNone
#guard (ReachTable.build? 2 badSource).isNone

-- control of the bound premise: the reach graph drops both edges through position 2 and accepts
-- identities only, while `Reach` holds from 0 to 1; the endpoint test refuses that table
#guard check (reachGraph 2 missingIntermediate) identities
example : ¬ Present identities 0 1 := by decide
example : Reach missingIntermediate 0 1 :=
  .step { fr := 0, to := 2 } List.mem_cons_self
    (.step { fr := 2, to := 1 } (List.mem_cons_of_mem _ List.mem_cons_self) (.refl 1))
#guard !checkReach 2 missingIntermediate identities
#guard (ReachTable.build? 2 missingIntermediate).isNone

-- finite evaluation: the built table answers each directed query of `directed`
#guard (ReachTable.build? 3 directed).any fun t =>
  (List.finRange 3).all fun s => (List.finRange 3).all fun g =>
    t.reaches s g == decide (s.val ≤ g.val)

end Test.Audit.SummaryControls
