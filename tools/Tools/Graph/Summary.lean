/-!
# Checked summaries of cyclic dependencies

A summary answers, for each node of a finite graph, the labels that its paths reach. Each node
seeds some labels and names some children, and cycles are allowed. A summary is a distance table:
for each node and each label, no entry or a distance. `check` accepts a table when three things
hold at every node:

1. each label the node seeds has an entry;
2. each label of a child has an entry at the node;
3. each entry is a label the node seeds, or a child holds the label at a smaller distance.

The first two leave no reached label out. The third stops a cycle from inventing a label: a
descending distance ends at a seed. A distance belongs to a node and a label, not to a node
alone: two labels can need opposite directions on one cycle (`Test/Audit/SummaryControls.lean`).

`check_summary_exact` proves both directions: an accepted table holds an entry at a node and a
label if and only if a directed path from the node reaches a node that seeds the label (`Reaches`).
`distances` builds a table by breadth-first search against the references, and `summarize` runs
`check` on it, so a summary that `summarize` returns needs no trust in that search.

The technique adapts the reconstruction of openai/math's board-game note to cycles
(`docs/research/2026-10-09-openai-math-probe/README.md`). The graph is derived analysis data, not
a program representation, and the module introduces no program syntax.

Placement: concept `initial-algebras-folds` (`docs/core/semantics.md` §2.7), as a tool law. The
claim is `dependency-summary-exact`, with pointer `check_summary_exact`. Its consumers are the
axiom walk's summaries (`ProofGraph.checkDependencies`, `tools/ProofGraph/Summary.lean`) and the
flow's directed queries (`Tools.View.Flow.ReachTable`, `tools/Tools/View/FlowReach.lean`).

What it does not establish:

- that a graph holds every dependency of what it describes: extraction is its consumer's
  boundary;
- that `distances` builds an accepted table: `summarize` refuses a table that `check` refuses,
  and the battery's controls are finite;
- a speed bound: `check` visits each reference once for each label.
-/

namespace Tools.Graph.Summary

/-- A finite graph over `n` nodes and `m` labels: the labels that each node seeds and the nodes it
names, in order. Cycles, repeated references and nodes with no label are allowed. -/
structure Graph (n m : Nat) where
  seeds : Vector (List (Fin m)) n
  children : Vector (List (Fin n)) n

/-- A distance table: for each node and each label, no entry or a distance. -/
abbrev Distances (n m : Nat) := Vector (Vector (Option Nat) m) n

variable {n m : Nat}

/-- A graph from its two functions on the nodes. It reads through `List.ofFn`, so its index laws
rest on `propext` alone: `Vector.getElem_ofFn` reaches `Classical.choice`. -/
def Graph.ofFn (seeds : Fin n → List (Fin m)) (children : Fin n → List (Fin n)) : Graph n m where
  seeds := ⟨(List.ofFn seeds).toArray, by rw [List.size_toArray, List.length_ofFn]⟩
  children := ⟨(List.ofFn children).toArray, by rw [List.size_toArray, List.length_ofFn]⟩

/-- The seeds of a graph built from functions. A step of `dependency-summary-exact`'s consumers
that build a graph from functions. Its consumer is the flow's reach graph
(`Tools.View.Flow.reachGraph_seeds`). -/
theorem Graph.ofFn_seeds (seeds : Fin n → List (Fin m)) (children : Fin n → List (Fin n))
    (u : Fin n) : (Graph.ofFn seeds children).seeds[u] = seeds u := by
  simp only [Graph.ofFn, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_ofFn]

/-- The children of a graph built from functions. A step of `dependency-summary-exact`'s
consumers that build a graph from functions. Its consumer is the flow's reach graph
(`Tools.View.Flow.reachGraph_children`). -/
theorem Graph.ofFn_children (seeds : Fin n → List (Fin m)) (children : Fin n → List (Fin n))
    (u : Fin n) : (Graph.ofFn seeds children).children[u] = children u := by
  simp only [Graph.ofFn, Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_ofFn]

/-- The table's entry at node `u` and label `l`. -/
def distance (d : Distances n m) (u : Fin n) (l : Fin m) : Option Nat := d[u][l]

/-- The table reports label `l` at node `u`: its entry holds a distance. -/
def Present (d : Distances n m) (u : Fin n) (l : Fin m) : Prop :=
  (distance d u l).isSome = true

instance (d : Distances n m) (u : Fin n) (l : Fin m) : Decidable (Present d u l) :=
  inferInstanceAs (Decidable (_ = true))

/-- The nodes from which a directed path reaches a node that seeds the label. -/
inductive Reaches (g : Graph n m) : Fin n → Fin m → Prop where
  | seed {u : Fin n} {l : Fin m} : l ∈ g.seeds[u] → Reaches g u l
  | step {u v : Fin n} {l : Fin m} : v ∈ g.children[u] → Reaches g v l → Reaches g u l

/-- Child `v` holds label `l` at a distance below `k`. The stored distance is compared directly,
so a large distance costs no search. A step of `dependency-summary-exact`. Its consumer is
`Supported`. -/
def Below (d : Distances n m) (v : Fin n) (l : Fin m) (k : Nat) : Prop :=
  match distance d v l with
  | none => False
  | some j => j < k

/-- An entry is a seed of its node, or a child holds its label at a smaller distance. A step of
`dependency-summary-exact`. Its consumer is `Valid`. -/
def Supported (g : Graph n m) (d : Distances n m) (u : Fin n) (l : Fin m) : Prop :=
  match distance d u l with
  | none => True
  | some k => l ∈ g.seeds[u] ∨ ∃ v ∈ g.children[u], Below d v l k

/-- The three conditions on a table, as propositions. A step of `dependency-summary-exact`. Its
consumer is `summary_exact`. -/
structure Valid (g : Graph n m) (d : Distances n m) : Prop where
  seeds : ∀ u l, l ∈ g.seeds[u] → Present d u l
  children : ∀ u v, v ∈ g.children[u] → ∀ l, Present d v l → Present d u l
  supported : ∀ u l, Supported g d u l

/-- The test of `Below`. -/
def belowB (d : Distances n m) (v : Fin n) (l : Fin m) (k : Nat) : Bool :=
  match distance d v l with
  | none => false
  | some j => decide (j < k)

/-- The test of `Supported`: it visits the node's own references only. -/
def supportedB (g : Graph n m) (d : Distances n m) (u : Fin n) (l : Fin m) : Bool :=
  match distance d u l with
  | none => true
  | some k => decide (l ∈ g.seeds[u]) || g.children[u].any fun v => belowB d v l k

/-- The three conditions at one node. -/
def nodeOk (g : Graph n m) (d : Distances n m) (u : Fin n) : Bool :=
  g.seeds[u].all (fun l => (distance d u l).isSome) &&
    g.children[u].all (fun v => (List.finRange m).all fun l =>
      !(distance d v l).isSome || (distance d u l).isSome) &&
    (List.finRange m).all (supportedB g d u)

/-- Accept a table when every node meets the three conditions. It visits each reference once for
each label, never each pair of nodes. -/
def check (g : Graph n m) (d : Distances n m) : Bool :=
  (List.finRange n).all (nodeOk g d)

/-- A step of `dependency-summary-exact`. Its consumer is `check_valid`. -/
theorem below_of_belowB {d : Distances n m} {v : Fin n} {l : Fin m} {k : Nat}
    (h : belowB d v l k = true) : Below d v l k := by
  unfold belowB at h
  unfold Below
  cases stored : distance d v l with
  | none => simp only [stored] at h; cases h
  | some j => simp only [stored, decide_eq_true_eq] at h; exact h

/-- A table that `check` accepts meets the three conditions. A step of
`dependency-summary-exact`. Its consumer is `check_summary_exact`. -/
theorem check_valid {g : Graph n m} {d : Distances n m} (accepted : check g d = true) :
    Valid g d := by
  have node : ∀ u, nodeOk g d u = true :=
    fun u => List.all_eq_true.mp accepted u (List.mem_finRange u)
  refine ⟨fun u l seeded => ?_, fun u v edge l present => ?_, fun u l => ?_⟩
  · have h := node u
    simp only [nodeOk, Bool.and_eq_true] at h
    exact List.all_eq_true.mp h.1.1 l seeded
  · have h := node u
    simp only [nodeOk, Bool.and_eq_true] at h
    have entry := List.all_eq_true.mp (List.all_eq_true.mp h.1.2 v edge) l (List.mem_finRange l)
    unfold Present at present ⊢
    rw [present] at entry
    simpa only [Bool.not_true, Bool.false_or] using entry
  · have h := node u
    simp only [nodeOk, Bool.and_eq_true] at h
    have s := List.all_eq_true.mp h.2 l (List.mem_finRange l)
    unfold supportedB at s
    unfold Supported
    cases stored : distance d u l with
    | none => trivial
    | some k =>
      simp only [stored, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at s
      rcases s with seeded | ⟨v, edge, below⟩
      · exact Or.inl seeded
      · exact Or.inr ⟨v, edge, below_of_belowB below⟩

/-- No reached label is left out: every path to a seed has an entry. A step of
`dependency-summary-exact`. Its consumer is `summary_exact`. -/
theorem no_omissions {g : Graph n m} {d : Distances n m} (h : Valid g d) {u : Fin n} {l : Fin m}
    (path : Reaches g u l) : Present d u l := by
  induction path with
  | seed seeded => exact h.seeds _ _ seeded
  | step edge _ ih => exact h.children _ _ edge _ ih

/-- A descending distance ends at a seed, even on a cycle: by strong induction on the distance.
A step of `dependency-summary-exact`. Its consumer is `no_invented_labels`. -/
theorem distance_reaches {g : Graph n m} {d : Distances n m} (h : Valid g d) (k : Nat) :
    ∀ u l, distance d u l = some k → Reaches g u l := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro u l stored
    have support := h.supported u l
    simp only [Supported, stored] at support
    rcases support with seeded | ⟨v, edge, below⟩
    · exact .seed seeded
    · cases childStored : distance d v l with
      | none => simp only [Below, childStored] at below
      | some j =>
        have smaller : j < k := by simpa only [Below, childStored] using below
        exact .step edge (ih j smaller v l childStored)

/-- A cycle cannot invent a label: every entry lies on a path to a seed. A step of
`dependency-summary-exact`. Its consumer is `summary_exact`. -/
theorem no_invented_labels {g : Graph n m} {d : Distances n m} (h : Valid g d) {u : Fin n}
    {l : Fin m} (present : Present d u l) : Reaches g u l := by
  cases stored : distance d u l with
  | none => simp only [Present, stored, Option.isSome_none, Bool.false_eq_true] at present
  | some k => exact distance_reaches h k u l stored

/-- **Both directions**: a table that meets the three conditions holds an entry at a node and a
label if and only if a path from the node reaches a seed of the label. A step of
`dependency-summary-exact`. Its consumer is `check_summary_exact`. -/
theorem summary_exact {g : Graph n m} {d : Distances n m} (h : Valid g d) (u : Fin n)
    (l : Fin m) : Present d u l ↔ Reaches g u l :=
  ⟨no_invented_labels h, no_omissions h⟩

/-- **An accepted summary**: a table that `check` accepts holds an entry at a node and a label if
and only if a path from the node reaches a seed of the label. The pointer of the claim
`dependency-summary-exact`. Its consumers are `Checked.reports_iff`, the axiom walk's checked
summaries and the flow's directed queries. It certifies the supplied graph, not its extraction. -/
theorem check_summary_exact {g : Graph n m} {d : Distances n m} (accepted : check g d = true)
    (u : Fin n) (l : Fin m) : Present d u l ↔ Reaches g u l :=
  summary_exact (check_valid accepted) u l

/-- A table that `check` accepted for its graph. -/
structure Checked (g : Graph n m) where
  table : Distances n m
  accepted : check g table = true

/-- Run `check` on a supplied table; `none` refuses it. -/
def admit (g : Graph n m) (d : Distances n m) : Option (Checked g) :=
  if accepted : check g d = true then some ⟨d, accepted⟩ else none

/-- Whether the summary reports label `l` at node `u`. -/
def Checked.reports {g : Graph n m} (s : Checked g) (u : Fin n) (l : Fin m) : Bool :=
  (distance s.table u l).isSome

/-- An accepted summary reports a label at a node if and only if a path from the node reaches a
seed of the label. A consumer of `check_summary_exact`, for a caller that keeps a summary and
queries it. -/
theorem Checked.reports_iff {g : Graph n m} (s : Checked g) (u : Fin n) (l : Fin m) :
    s.reports u l = true ↔ Reaches g u l :=
  check_summary_exact s.accepted u l

/-- The nodes that name each node, once per reference. -/
def parents (g : Graph n m) : Vector (List (Fin n)) n :=
  (List.finRange n).foldl (init := Vector.replicate n []) fun acc u =>
    g.children[u].foldl (init := acc) fun acc v => acc.set v.val (u :: acc[v]) v.isLt

/-- The shortest distance from each node to a node that seeds `l`, by breadth-first search
against the references. Each node enters the queue once, so `n` steps empty it. -/
def labelDistances (g : Graph n m) (up : Vector (List (Fin n)) n) (l : Fin m) :
    Vector (Option Nat) n := Id.run do
  let mut table : Vector (Option Nat) n :=
    Vector.ofFn fun u => if l ∈ g.seeds[u] then some 0 else none
  let mut queue : Array (Fin n) := ((List.finRange n).filter fun u => l ∈ g.seeds[u]).toArray
  let mut next := 0
  for _ in [0:n] do
    let some v := queue[next]? | break
    next := next + 1
    let some k := table[v] | continue
    for p in up[v] do
      if table[p].isNone then
        table := table.set p.val (some (k + 1)) p.isLt
        queue := queue.push p
  return table

/-- A distance table built by breadth-first search, one label at a time. It is untrusted:
`summarize` runs `check` on it. -/
def distances (g : Graph n m) : Distances n m :=
  let up := parents g
  let columns : Vector (Vector (Option Nat) n) m := Vector.ofFn fun l => labelDistances g up l
  Vector.ofFn fun u => Vector.ofFn fun l => columns[l][u]

/-- Build a summary and run `check` on it. `none` is an unanswered summary, never an empty one. -/
def summarize (g : Graph n m) : Option (Checked g) :=
  admit g (distances g)

end Tools.Graph.Summary
