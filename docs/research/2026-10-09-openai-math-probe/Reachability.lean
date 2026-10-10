import ProofGraph.Proof

/-!
Research prototype for the proposed `dependency-summary-exact` tool claim.
Placement and consumers are recorded in `OPERATIONAL-PLAN.md`.
The observation is label membership in finite extracted dependency data.
The existing `reachedAxiomsMany` summaries are the proposed production consumer.
Extraction, missing declaration bodies, stopping policy and analysis budgets remain separate.
No theorem about Tarjan or represented programs is claimed here.
-/

namespace Research.DependencySummary

/-- A node carries local frontier labels and outgoing references. Both are finite data. -/
structure Row (nodes labels : Nat) where
  seeds : List (Fin labels)
  children : List (Fin nodes)
  deriving DecidableEq

/-- A finite dependency table. Cycles and repeated child occurrences are allowed. -/
structure Graph (nodes labels : Nat) where
  rows : Vector (Row nodes labels) nodes
  deriving DecidableEq

/-- Each node-label pair stores either no answer or its distance witness. -/
structure Certificate (nodes labels : Nat) where
  rows : Vector (Vector (Option Nat) labels) nodes
  deriving DecidableEq

variable {n m : Nat} {g : Graph n m} {c : Certificate n m}
  {u : Fin n} {label : Fin m}

def rank (c : Certificate n m) (u : Fin n) (label : Fin m) : Option Nat :=
  (c.rows[u])[label]

def Present (c : Certificate n m) (u : Fin n) (label : Fin m) : Prop :=
  (rank c u label).isSome = true

instance (c : Certificate n m) (u : Fin n) (label : Fin m) :
    Decidable (Present c u label) := inferInstanceAs (Decidable (_ = true))

/-- Read the child's stored distance once; the certificate's numeric distance is not a search bound.
This helper serves `summary_exact` through `Supported`. -/
def LowerRank (c : Certificate n m) (child : Fin n) (label : Fin m) (distance : Nat) : Prop :=
  match rank c child label with
  | none => False
  | some childDistance => childDistance < distance

instance (c : Certificate n m) (child : Fin n) (label : Fin m) (distance : Nat) :
    Decidable (LowerRank c child label distance) := by
  unfold LowerRank
  split <;> infer_instance

/-- A claimed answer is local, or follows a child with the same answer and a smaller distance.
This helper serves `summary_exact`; a rank belongs to a node-label pair, not a node. -/
def Supported (g : Graph n m) (c : Certificate n m) (u : Fin n) (label : Fin m) : Prop :=
  match rank c u label with
  | none => True
  | some distance => label ∈ g.rows[u].seeds ∨
      ∃ child : Fin n, child ∈ g.rows[u].children ∧ LowerRank c child label distance

instance (g : Graph n m) (c : Certificate n m) (u : Fin n) (label : Fin m) :
    Decidable (Supported g c u label) := by
  unfold Supported
  split <;> infer_instance

/-- Local seeds and every child's answers are included; every reported answer has support. -/
def Valid (g : Graph n m) (c : Certificate n m) : Prop :=
  (∀ u label, label ∈ g.rows[u].seeds → Present c u label) ∧
  (∀ u child, child ∈ g.rows[u].children →
    ∀ label, Present c child label → Present c u label) ∧
  (∀ u label, Supported g c u label)

instance (g : Graph n m) (c : Certificate n m) : Decidable (Valid g c) := by
  unfold Valid
  infer_instance

/-- Executable finite checker. It does not search for or certify the extraction boundary. -/
def check (g : Graph n m) (c : Certificate n m) : Bool := decide (Valid g c)

/-- The finite-path observation, ending at a local seed. -/
inductive Reaches (g : Graph n m) : Fin n → Fin m → Prop where
  | seed {source : Fin n} {answer : Fin m} :
      answer ∈ g.rows[source].seeds → Reaches g source answer
  | step {source child : Fin n} {answer : Fin m} : child ∈ g.rows[source].children →
      Reaches g child answer → Reaches g source answer

/-- Completeness helper for `summary_exact`: no path's label is omitted. -/
theorem no_omissions (h : Valid g c) (path : Reaches g u label) : Present c u label := by
  induction path with
  | seed seed => exact h.1 _ _ seed
  | step edge _ ih => exact h.2.1 _ _ edge _ ih

/-- Support helper for `summary_exact`: a decreasing distance ends at a seed, even on cycles. -/
theorem rank_reaches (h : Valid g c) (distance : Nat) :
    ∀ u label, rank c u label = some distance → Reaches g u label := by
  induction distance using Nat.strongRecOn with
  | ind distance ih =>
    intro u label same
    have support := h.2.2 u label
    simp only [Supported, same] at support
    rcases support with seedAt | ⟨child, edge, childLower⟩
    · exact .seed seedAt
    · cases childRank : rank c child label with
      | none => simp only [LowerRank, childRank] at childLower
      | some childDistance =>
        have smaller : childDistance < distance := by
          simpa only [LowerRank, childRank] using childLower
        exact .step edge (ih childDistance smaller child label childRank)

/-- Soundness helper for `summary_exact`: circular support cannot invent a label. -/
theorem no_invented_labels (h : Valid g c) (present : Present c u label) :
    Reaches g u label := by
  cases same : rank c u label with
  | none => simp only [Present, same, Option.isSome_none, Bool.false_eq_true] at present
  | some distance => exact rank_reaches h distance u label same

/-- Proposed claim `dependency-summary-exact`, concept `initial-algebras-folds`.
Consumer: the axiom and goal summaries of `reachedAxiomsMany`.
Membership agrees with finite paths to local frontier labels under all three certificate checks.
This theorem certifies the supplied graph, not the extraction of Lean's environment. -/
theorem summary_exact (h : Valid g c) (u : Fin n) (label : Fin m) :
    Present c u label ↔ Reaches g u label :=
  ⟨no_invented_labels h, no_omissions h⟩

/-- Operational connector: an accepted executable check supplies `summary_exact`'s premises. -/
theorem check_summary_exact (accepted : check g c = true) (u : Fin n) (label : Fin m) :
    Present c u label ↔ Reaches g u label :=
  summary_exact (of_decide_eq_true accepted) u label

/-- Kernel-checked pointers freeze the actual statements and enforce the axiom ceiling. -/
def summaryProof : ProofGraph.ProofRef := checked_theorem% summary_exact
def checkerProof : ProofGraph.ProofRef := checked_theorem% check_summary_exact

namespace Controls

/-- Both nodes form a cycle; only the second node has the local label. -/
def cycleWithSeed : Graph 2 1 :=
  { rows := ⟨#[{ seeds := [], children := [1] },
               { seeds := [0], children := [0] }], rfl⟩ }

def good : Certificate 2 1 :=
  { rows := ⟨#[⟨#[some 1], rfl⟩, ⟨#[some 0], rfl⟩], rfl⟩ }

-- Finite acceptance and a reader of the generic theorem at an actual cyclic table.
example : check cycleWithSeed good = true := by decide
example : Reaches cycleWithSeed 0 0 :=
  (check_summary_exact (by decide : check cycleWithSeed good = true) 0 0).mp (by decide)

/-- Large numeric distances do not increase the checker's search space. -/
def largeDistances : Certificate 2 1 :=
  { rows := ⟨#[⟨#[some 1000000000], rfl⟩,
               ⟨#[some 999999999], rfl⟩], rfl⟩ }

example : check cycleWithSeed largeDistances = true := by decide
example : Reaches cycleWithSeed 0 0 :=
  (check_summary_exact (by decide : check cycleWithSeed largeDistances = true) 0 0).mp (by decide)

/-- The first node omits the answer its child has. -/
def missing : Certificate 2 1 :=
  { rows := ⟨#[⟨#[none], rfl⟩, ⟨#[some 0], rfl⟩], rfl⟩ }

example : check cycleWithSeed missing = false := by decide

/-- With no local seed, the same cycle cannot justify any label. -/
def seedlessCycle : Graph 2 1 :=
  { rows := ⟨#[{ seeds := [], children := [1] },
               { seeds := [], children := [0] }], rfl⟩ }

def invented : Certificate 2 1 :=
  { rows := ⟨#[⟨#[some 1], rfl⟩, ⟨#[some 1], rfl⟩], rfl⟩ }

-- Merely closing answers along edges accepts the invention; the distance check rejects it.
example : (∀ u label, label ∈ seedlessCycle.rows[u].seeds → Present invented u label) ∧
    (∀ u child, child ∈ seedlessCycle.rows[u].children →
      ∀ label, Present invented child label → Present invented u label) := by decide
example : check seedlessCycle invented = false := by decide

/-- Empty answers are correct for a seedless cycle. -/
def empty : Certificate 2 1 :=
  { rows := ⟨#[⟨#[none], rfl⟩, ⟨#[none], rfl⟩], rfl⟩ }

example : check seedlessCycle empty = true := by decide
example : ¬ Reaches seedlessCycle 0 0 := by
  intro path
  have present := (check_summary_exact
    (by decide : check seedlessCycle empty = true) 0 0).mpr path
  exact (by decide : ¬ Present empty 0 0) present

/-- Different labels need opposite distance directions on the same cycle. -/
def twoSeeds : Graph 2 2 :=
  { rows := ⟨#[{ seeds := [0], children := [1] },
               { seeds := [1], children := [0] }], rfl⟩ }

def twoDistances : Certificate 2 2 :=
  { rows := ⟨#[⟨#[some 0, some 1], rfl⟩,
               ⟨#[some 1, some 0], rfl⟩], rfl⟩ }

example : check twoSeeds twoDistances = true := by decide

end Controls

-- Report the exact transitive proof dependencies; the checked pointers also enforce the ceiling.
run_cmd Lean.Elab.Command.liftTermElabM do
  for name in #[``no_omissions, ``rank_reaches, ``no_invented_labels,
      ``summary_exact, ``check_summary_exact] do
    let some axioms := ProofGraph.exactAxioms (← Lean.getEnv) name
      | Lean.throwError "dependency-summary proof audit exhausted its budget"
    Lean.logInfo m!"{name}: exact axioms {axioms}"

end Research.DependencySummary
