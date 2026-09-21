import Effect4.Laws.Machine.CompletionData
import Effect4.Laws.Machine.RefKernel
import Effect4.Laws.Auto.Obligations

/-!
The two representation-connection shapes from the observation packet §2.4, retained by
packet 2 §1. These are proof-side interfaces. Their instances and lifting proofs belong to
the corresponding representation slice; no historical store copy or decoding fallback is
part of either shape.
-/

set_option autoImplicit false

namespace Effect4.Machine.Refinement

universe u v w z

/-- A concrete step projects to one model step with the same answer, and retains the
concrete invariant needed by the next step. -/
structure Projects {C : Type u} {M : Type v} {Op : Type w} {Answer : Type z}
    (project : C → M)
    (stepC : Op → C → Option (C × Answer))
    (stepM : Op → M → Option (M × Answer))
    (WF : C → Prop) : Prop where
  step : ∀ o c, WF c →
    (stepC o c).map (fun (c', a) => (project c', a)) = stepM o (project c)
  keeps : ∀ o c c' a, WF c → stepC o c = some (c', a) → WF c'

/-- Related stores match successful steps and unanswered frontiers. Initialization and
any progress obligation for a machine lifting are supplied by that instance. -/
structure Refines {C : Type u} {M : Type v} {Op : Type w} {Answer : Type z}
    (related : C → M → Prop)
    (stepC : Op → C → Option (C × Answer))
    (stepM : Op → M → Option (M × Answer)) : Prop where
  step : ∀ o c m c' a, related c m → stepC o c = some (c', a) →
    ∃ m' a', stepM o m = some (m', a') ∧ a = a' ∧ related c' m'
  frontier : ∀ o c m, related c m → stepC o c = none → stepM o m = none

namespace CompositionObligations
universe x y
/-- C3 retains both concrete and intermediate validity. -/
theorem projects_compose : ProofGraph.Obligation (
    ∀ {Concrete : Type u} {Middle : Type v} {Model : Type w}
      {Op : Type x} {Answer : Type y}
      (first : Concrete → Middle) (second : Middle → Model)
      (stepConcrete : Op → Concrete → Option (Concrete × Answer))
      (stepMiddle : Op → Middle → Option (Middle × Answer))
      (stepModel : Op → Model → Option (Model × Answer))
      (concreteValid : Concrete → Prop) (middleValid : Middle → Prop),
      Projects first stepConcrete stepMiddle concreteValid →
      Projects second stepMiddle stepModel middleValid →
      Projects (second ∘ first) stepConcrete stepModel
        (fun concrete => concreteValid concrete ∧ middleValid (first concrete))) := ⟨⟩


/-- C4 retains concrete validity in the induced relation. -/
theorem projects_induces_refines : ProofGraph.Obligation (
    ∀ {Concrete : Type u} {Model : Type v} {Op : Type w} {Answer : Type x}
      (project : Concrete → Model)
      (stepConcrete : Op → Concrete → Option (Concrete × Answer))
      (stepModel : Op → Model → Option (Model × Answer))
      (valid : Concrete → Prop),
      Projects project stepConcrete stepModel valid →
      Refines (fun concrete model => valid concrete ∧ project concrete = model)
        stepConcrete stepModel) := ⟨⟩

end CompositionObligations
universe x y

/-- C3 composes exact one-step observations while retaining the validity domain required
by each projection. The operation and answer carriers are unchanged across both steps. -/
theorem projects_compose
    {Concrete : Type u} {Middle : Type v} {Model : Type w} {Op : Type x} {Answer : Type y}
    (first : Concrete → Middle) (second : Middle → Model)
    (stepConcrete : Op → Concrete → Option (Concrete × Answer))
    (stepMiddle : Op → Middle → Option (Middle × Answer))
    (stepModel : Op → Model → Option (Model × Answer))
    (concreteValid : Concrete → Prop) (middleValid : Middle → Prop)
    (one : Projects first stepConcrete stepMiddle concreteValid)
    (two : Projects second stepMiddle stepModel middleValid) :
    Projects (second ∘ first) stepConcrete stepModel
      (fun concrete => concreteValid concrete ∧ middleValid (first concrete)) := by
  constructor
  · intro op concrete valid
    change (stepConcrete op concrete).map (fun (next, answer) => (second (first next), answer)) =
      stepModel op (second (first concrete))
    rw [← two.step op (first concrete) valid.2, ← one.step op concrete valid.1, Option.map_map]
    rfl
  · intro op concrete next answer valid step
    refine ⟨one.keeps op concrete next answer valid.1 step, ?_⟩
    apply two.keeps op (first concrete) (first next) answer valid.2
    rw [← one.step op concrete valid.1, step]
    rfl

/-- C4 is a forward simulation on the graph of the projection, retaining concrete validity.
A concrete unanswered step yields an unanswered model step. No initialization or host
implementation instance is supplied by this generic connector. -/
theorem projects_induces_refines
    {Concrete : Type u} {Model : Type v} {Op : Type w} {Answer : Type x}
    (project : Concrete → Model)
    (stepConcrete : Op → Concrete → Option (Concrete × Answer))
    (stepModel : Op → Model → Option (Model × Answer))
    (valid : Concrete → Prop) (projection : Projects project stepConcrete stepModel valid) :
    Refines (fun concrete model => valid concrete ∧ project concrete = model)
      stepConcrete stepModel := by
  constructor
  · intro op concrete model next answer related step
    refine ⟨project next, answer, ?_, rfl, projection.keeps op concrete next answer related.1 step, rfl⟩
    rw [← related.2, ← projection.step op concrete related.1, step]
    rfl
  · intro op concrete model related step
    rw [← related.2, ← projection.step op concrete related.1, step]
    rfl

#obligation_proved CompositionObligations.projects_compose := @projects_compose
#obligation_proved CompositionObligations.projects_induces_refines := @projects_induces_refines
#typed_state_obligations Effect4.Machine.Refinement.CompositionObligations ceiling 0 using aesop (rule_sets := [Effect4.Stores])

end Effect4.Machine.Refinement

-- BEGIN M1 PHASE B Refinement
set_option autoImplicit false

namespace Effect4.Machine

open Effect4

variable {κ κ' κ'' : Type}

def DeferredCell.map (f : κ → κ') (cell : DeferredCell κ) : DeferredCell κ' :=
  ⟨cell.completion.map f, cell.wake⟩

def DeferredStore.map (f : κ → κ') (store : DeferredStore κ) : DeferredStore κ' :=
  ⟨store.cells.map (DeferredCell.map f), store.due.map (Owed.mapCode f)⟩

attribute [aesop norm simp (rule_sets := [Effect4.StoreKernel])] DeferredCell.map DeferredStore.map

namespace M1.DeferredWanted

variable (f : κ → κ') (g : κ' → κ'') (d : DeferredStore κ)

theorem cell_map_id (c : DeferredCell κ) : ProofGraph.Obligation
    (c.map id = c) := ⟨⟩

theorem cell_map_comp (c : DeferredCell κ) : ProofGraph.Obligation
    ((c.map f).map g = c.map (g ∘ f)) := ⟨⟩

theorem map_id : ProofGraph.Obligation (d.map id = d) := ⟨⟩

theorem map_comp : ProofGraph.Obligation ((d.map f).map g = d.map (g ∘ f)) := ⟨⟩

-- The ten operations, in the declaration order of Machine/Stores.lean.

theorem map_make : ProofGraph.Obligation
    ((d.map f).make = ((d.make).1, (d.make).2.map f)) := ⟨⟩

theorem map_cellAt (cell : DeferredKey) : ProofGraph.Obligation
    ((d.map f).cellAt cell = (d.cellAt cell).map (DeferredCell.map f)) := ⟨⟩

theorem map_setCell (cell : DeferredKey) (value : DeferredCell κ) : ProofGraph.Obligation
    ((d.map f).setCell cell (value.map f) = (d.setCell cell value).map f) := ⟨⟩

theorem map_isDone (cell : DeferredKey) : ProofGraph.Obligation
    ((d.map f).isDone cell = d.isDone cell) := ⟨⟩

theorem map_poll (cell : DeferredKey) : ProofGraph.Obligation
    ((d.map f).poll cell = (d.poll cell).map (Option.map f)) := ⟨⟩

theorem map_register (cell : DeferredKey) (waiter : FiberId) (token : Nat) : ProofGraph.Obligation
    ((d.map f).register cell waiter token =
      ((d.register cell waiter token).1.map f, (d.register cell waiter token).2.map f)) := ⟨⟩

theorem map_cancel (cell : DeferredKey) (waiter : FiberId) (token : Nat) : ProofGraph.Obligation
    ((d.map f).cancel cell waiter token = (d.cancel cell waiter token).map f) := ⟨⟩

theorem map_complete (cell : DeferredKey) (completion : κ) : ProofGraph.Obligation
    ((d.map f).complete cell (f completion) =
      ((d.complete cell completion).1.map f, (d.complete cell completion).2)) := ⟨⟩

theorem map_drainDue : ProofGraph.Obligation
    ((d.map f).drainDue =
      ((d.drainDue).1.map (Owed.mapCode f), (d.drainDue).2.map f)) := ⟨⟩

theorem map_wakeBatch (cell : DeferredKey) : ProofGraph.Obligation
    ((d.map f).wakeBatch cell = (d.wakeBatch cell).map f) := ⟨⟩

end M1.DeferredWanted

theorem M1.CellMapWanted.id_fun : ProofGraph.Obligation
    (DeferredCell.map (id : κ → κ) = id) := ⟨⟩

section DeferredMapLaws

variable (f : κ → κ') (g : κ' → κ'') (d : DeferredStore κ)

theorem DeferredCell.map_id (c : DeferredCell κ) :
    (c.map id = c) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredCell.map_id

theorem DeferredCell.map_comp (c : DeferredCell κ) :
    ((c.map f).map g = c.map (g ∘ f)) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredCell.map_comp

theorem DeferredCell.map_id_fun : DeferredCell.map (id : κ → κ) = id := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredCell.map_id_fun

theorem DeferredStore.map_id : (d.map id = d) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_id

theorem DeferredStore.map_comp : ((d.map f).map g = d.map (g ∘ f)) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_comp

-- The ten operations, in the declaration order of Machine/Stores.lean.

theorem DeferredStore.map_make :
    ((d.map f).make = ((d.make).1, (d.make).2.map f)) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_make

theorem DeferredStore.map_cellAt (cell : DeferredKey) :
    ((d.map f).cellAt cell = (d.cellAt cell).map (DeferredCell.map f)) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_cellAt

theorem DeferredStore.map_setCell (cell : DeferredKey) (value : DeferredCell κ) :
    ((d.map f).setCell cell (value.map f) = (d.setCell cell value).map f) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_setCell

theorem DeferredStore.map_isDone (cell : DeferredKey) :
    ((d.map f).isDone cell = d.isDone cell) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_isDone

theorem DeferredStore.map_poll (cell : DeferredKey) :
    ((d.map f).poll cell = (d.poll cell).map (Option.map f)) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_poll

theorem DeferredStore.map_register (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    ((d.map f).register cell waiter token =
      ((d.register cell waiter token).1.map f, (d.register cell waiter token).2.map f)) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_register

theorem DeferredStore.map_cancel (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    ((d.map f).cancel cell waiter token = (d.cancel cell waiter token).map f) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_cancel

theorem DeferredStore.map_complete (cell : DeferredKey) (completion : κ) :
    ((d.map f).complete cell (f completion) =
      ((d.complete cell completion).1.map f, (d.complete cell completion).2)) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_complete

theorem DeferredStore.map_drainDue :
    ((d.map f).drainDue =
      ((d.drainDue).1.map (Owed.mapCode f), (d.drainDue).2.map f)) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_drainDue

theorem DeferredStore.map_wakeBatch (cell : DeferredKey) :
    ((d.map f).wakeBatch cell = (d.wakeBatch cell).map f) := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredStore.map_wakeBatch

end DeferredMapLaws

#typed_state_obligations Effect4.Machine.M1.CellMapWanted ceiling 0 using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

#typed_state_obligations Effect4.Machine.M1.DeferredWanted ceiling 0 using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

/-! The image boundary lives in Laws, and never becomes a machine invariant again. -/
namespace Refinement

/-- Only actual completed cell values and actual due-code values need witnesses. -/
def DeferredOk (d : DeferredStore Program) : Prop :=
  (∀ cell ∈ d.cells, ∀ p, cell.completion = some p → ∃ c, p = completionPrim c) ∧
    ∀ owed ∈ d.due, ∃ c, owed.code = completionPrim c

end Refinement

namespace M1.DeferredWanted

-- These are exact embedding/image statements, not a total read on arbitrary Program.
theorem completionPrim_injective : ProofGraph.Obligation
    (Function.Injective completionPrim) := ⟨⟩

theorem deferredOk_iff_image (d : DeferredStore Program) : ProofGraph.Obligation
    (Refinement.DeferredOk d ↔ ∃ d' : DeferredStore, d = d'.map completionPrim) := ⟨⟩

end M1.DeferredWanted

/-! Concrete Projects instances. They instantiate the existing operations instead of
creating a second operation alphabet or a duplicate store interpreter. Specializing f to
completionPrim is the new-to-program-store connector. No inverse of the embedding exists
in this interface. The invariant for this direction is True: the concrete carrier is
already data. The image theorem above characterizes exactly the admissible target stores.

Missing cellAt/isDone/poll entries remain None frontiers in both steps. The other operations
retain their existing total/no-op behavior, including register on a missing key. -/
namespace M1.DeferredWanted

open Refinement

variable (f : κ → κ')

theorem projects_make : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some ((d.make).2, (d.make).1))
      (fun (_ : Unit) (d : DeferredStore κ') => some ((d.make).2, (d.make).1))
      (fun _ => True)) := ⟨⟩

theorem projects_cellAt (cell : DeferredKey) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => (d.cellAt cell).map fun c => (d, c.map f))
      (fun (_ : Unit) (d : DeferredStore κ') => (d.cellAt cell).map fun c => (d, c))
      (fun _ => True)) := ⟨⟩

theorem projects_setCell (cell : DeferredKey) (value : DeferredCell κ) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.setCell cell value, ()))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.setCell cell (value.map f), ()))
      (fun _ => True)) := ⟨⟩

theorem projects_isDone (cell : DeferredKey) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => (d.isDone cell).map fun done => (d, done))
      (fun (_ : Unit) (d : DeferredStore κ') => (d.isDone cell).map fun done => (d, done))
      (fun _ => True)) := ⟨⟩

theorem projects_poll (cell : DeferredKey) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => (d.poll cell).map fun c => (d, c.map f))
      (fun (_ : Unit) (d : DeferredStore κ') => (d.poll cell).map fun c => (d, c))
      (fun _ => True)) := ⟨⟩

theorem projects_register (cell : DeferredKey) (waiter : FiberId) (token : Nat) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) =>
        some ((d.register cell waiter token).1, (d.register cell waiter token).2.map f))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.register cell waiter token))
      (fun _ => True)) := ⟨⟩

theorem projects_cancel (cell : DeferredKey) (waiter : FiberId) (token : Nat) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.cancel cell waiter token, ()))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.cancel cell waiter token, ()))
      (fun _ => True)) := ⟨⟩

theorem projects_complete (cell : DeferredKey) (completion : κ) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.complete cell completion))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.complete cell (f completion)))
      (fun _ => True)) := ⟨⟩

theorem projects_drainDue : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) =>
        some ((d.drainDue).2, (d.drainDue).1.map (Owed.mapCode f)))
      (fun (_ : Unit) (d : DeferredStore κ') => some ((d.drainDue).2, (d.drainDue).1))
      (fun _ => True)) := ⟨⟩

theorem projects_wakeBatch (cell : DeferredKey) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.wakeBatch cell, ()))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.wakeBatch cell, ()))
      (fun _ => True)) := ⟨⟩

end M1.DeferredWanted

namespace Refinement

universe u v w

/-- The observation factors through the actual fine value. Adapted directly from the
observation packet's checked CritiqueContracts.Factors shape; no OldObs carrier. -/
def Factors {State : Type u} {Fine : Type v} {Coarse : Type w}
    (fine : State → Fine) (coarse : State → Coarse) : Prop :=
  ∃ forget : Fine → Coarse, ∀ s, coarse s = forget (fine s)

end Refinement

namespace M1.DeferredWanted

open Refinement

universe u v w z

/-- The packet's observation transfer uses these two shared laws, rather than
repeating a specialized factorization proof at each representation instance. -/
theorem factors_respects_eq {State : Type u} {Fine : Type v} {Coarse : Type w}
    (fine : State → Fine) (coarse : State → Coarse) (a b : State) :
    ProofGraph.Obligation
      (Factors fine coarse → fine a = fine b → coarse a = coarse b) := ⟨⟩

theorem factors_trans {State : Type u} {A : Type v} {B : Type w} {C : Type z}
    (a : State → A) (b : State → B) (c : State → C) : ProofGraph.Obligation
      (Factors a b → Factors b c → Factors a c) := ⟨⟩

theorem factors_deferreds {Observation : Type u} (observe : DeferredStore Program → Observation) :
    ProofGraph.Obligation
      (Factors Stores.deferreds (fun s => observe (s.deferreds.map completionPrim))) := ⟨⟩

/-- A surrounding observation need only retain the actual Deferred store projection. -/
theorem factors_through_deferreds {Fine : Type u} {Observation : Type v}
    (fine : Stores → Fine) (_h : Factors fine Stores.deferreds)
    (observe : DeferredStore Program → Observation) : ProofGraph.Obligation
      (Factors fine (fun s => observe (s.deferreds.map completionPrim))) := ⟨⟩

end M1.DeferredWanted

-- 30 statement obligations here: 4 functor + 10 naturality + 2 embedding/image +
-- 10 Projects + 4 Factors. Handles holds the separate memoEntry_keys goal.
-- The final ledger below checks all thirty statements at ceiling zero.
end Effect4.Machine

namespace Effect4.Machine

/-- The generic and model steps only change pair order to fit Projects' state-first API. -/
def arenaStepState {σ : Type} [Arena σ Val] (op : RefKey × RefKernel) (s : σ) :
    Option (σ × Val) :=
  (refStepOfA op.1 op.2 s).map Prod.swap

def listStepState (op : RefKey × RefKernel) (s : RefHeap) : Option (RefHeap × Val) :=
  (refStepOf op.1 op.2 s).map Prod.swap

namespace ArenaObligations

theorem projects {σ : Type} [Arena σ Val] [LawfulArena σ Val] : ProofGraph.Obligation (
    Refinement.Projects (@Arena.toList σ Val _ _) arenaStepState listStepState
      (fun _ : σ => True)) := ⟨⟩

end ArenaObligations
end Effect4.Machine
-- END M1 PHASE B Refinement

namespace Effect4.Machine.M1.DeferredImageSupportWanted

universe u v

theorem list_image_iff {α : Type u} {β : Type v} (f : α → β) (xs : List β) :
    ProofGraph.Obligation
      ((∀ x ∈ xs, ∃ y, x = f y) ↔ ∃ ys : List α, xs = ys.map f) := ⟨⟩

theorem cell_image_iff {κ κ' : Type} (f : κ → κ') (cell : DeferredCell κ') :
    ProofGraph.Obligation
      ((∀ p, cell.completion = some p → ∃ c, p = f c) ↔
        ∃ pre : DeferredCell κ, cell = pre.map f) := ⟨⟩

theorem owed_image_iff {κ : Type u} {κ' : Type v} (f : κ → κ') (owed : Owed κ') :
    ProofGraph.Obligation
      ((∃ c, owed.code = f c) ↔
        ∃ pre : Owed κ, owed = pre.mapCode f) := ⟨⟩

end Effect4.Machine.M1.DeferredImageSupportWanted


namespace Effect4.Machine
open Effect4
universe u v w z

attribute [aesop safe constructors (rule_sets := [Effect4.Stores])] Refinement.Projects
attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  doneWith_shared completeWith_non_exit Prim.ofExit_asExit?

/-- A finite list lies in an image exactly when each of its elements does. -/
theorem Refinement.list_image_iff {α : Type u} {β : Type v} (f : α → β) (xs : List β) :
    (∀ x ∈ xs, ∃ y, x = f y) ↔ ∃ ys : List α, xs = ys.map f := by
  induction xs with
  | nil => aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
  | cons x xs ih =>
    constructor
    · intro all
      obtain ⟨y, hy⟩ := all x List.mem_cons_self
      have tail : ∀ x ∈ xs, ∃ y, x = f y := by
        aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
      obtain ⟨ys, hys⟩ := ih.mp tail
      exact ⟨y :: ys, by simp only [List.map_cons, ← hy, ← hys]⟩
    · rintro ⟨ys, hys⟩ value member
      rw [hys] at member
      obtain ⟨y, _, hy⟩ := List.mem_map.mp member
      exact ⟨y, hy.symm⟩

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] Refinement.list_image_iff

/-- A cell needs a payload witness only when its completion is present. -/
theorem DeferredCell.image_iff {κ κ' : Type} (f : κ → κ') (cell : DeferredCell κ') :
    (∀ p, cell.completion = some p → ∃ c, p = f c) ↔
      ∃ pre : DeferredCell κ, cell = pre.map f := by
  constructor
  · intro all
    cases cell with
    | mk completion wake =>
      cases completion with
      | none => exact ⟨⟨none, wake⟩, rfl⟩
      | some p =>
        obtain ⟨c, hc⟩ := all p rfl
        exact ⟨⟨some c, wake⟩, by cases hc; rfl⟩
  · rintro ⟨pre, rfl⟩ p h
    obtain ⟨c, _, hc⟩ := Option.map_eq_some_iff.mp h
    exact ⟨c, hc.symm⟩

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] DeferredCell.image_iff

/-- An owed value changes only its payload under the map. -/
theorem Owed.image_iff {κ : Type u} {κ' : Type v} (f : κ → κ') (owed : Owed κ') :
    (∃ c, owed.code = f c) ↔ ∃ pre : Owed κ, owed = pre.mapCode f := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨⟨owed.waiter, owed.token, c, owed.mode⟩, ?_⟩
    cases owed
    aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
  · rintro ⟨pre, rfl⟩
    exact ⟨pre.code, rfl⟩

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] Owed.image_iff

/-- The exit/read distinction and exit readback make the completion spelling injective. -/
theorem Refinement.completionPrim_injective : Function.Injective completionPrim := by
  intro a b equal
  have observed := congrArg Prim.asExit? equal
  cases a with
  | ofExit ea =>
    cases b with
    | ofExit eb =>
      rw [doneWith_shared, doneWith_shared, Option.some.injEq] at observed
      rw [observed]
    | ofRefGet cb =>
      rw [doneWith_shared, completeWith_non_exit] at observed
      exact absurd observed (Option.some_ne_none ea)
  | ofRefGet ca =>
    cases b with
    | ofExit eb =>
      rw [completeWith_non_exit, doneWith_shared] at observed
      exact absurd observed.symm (Option.some_ne_none eb)
    | ofRefGet cb =>
      simp only [completionPrim] at equal
      cases equal
      rfl

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.completionPrim_injective

/-- Actual completed values and due payloads characterize the mapped-store image. -/
theorem Refinement.deferredOk_iff_image (d : DeferredStore Program) :
    Refinement.DeferredOk d ↔ ∃ d' : DeferredStore, d = d'.map completionPrim := by
  constructor
  · rintro ⟨hc, hd⟩
    have cells : ∀ cell ∈ d.cells, ∃ pre : DeferredCell, cell = pre.map completionPrim := by
      intro cell member
      exact (DeferredCell.image_iff completionPrim cell).mp (hc cell member)
    have dues : ∀ owed ∈ d.due, ∃ pre : Owed (Completion Val Err Defect FiberId Ann),
        owed = pre.mapCode completionPrim := by
      intro owed member
      exact (Owed.image_iff completionPrim owed).mp (hd owed member)
    obtain ⟨cells, hcells⟩ := (Refinement.list_image_iff _ _).mp cells
    obtain ⟨due, hdue⟩ := (Refinement.list_image_iff _ _).mp dues
    refine ⟨⟨cells, due⟩, ?_⟩
    cases d
    aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
  · rintro ⟨d', rfl⟩
    constructor
    · intro cell member
      obtain ⟨pre, _, rfl⟩ := List.mem_map.mp member
      exact (DeferredCell.image_iff completionPrim (pre.map completionPrim)).mpr ⟨pre, rfl⟩
    · intro owed member
      obtain ⟨pre, _, rfl⟩ := List.mem_map.mp member
      exact ⟨pre.code, rfl⟩

attribute [aesop norm simp (rule_sets := [Effect4.Stores])] Refinement.deferredOk_iff_image

section DeferredProjects
variable {κ κ' : Type} (f : κ → κ')

theorem Refinement.projects_make : (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some ((d.make).2, (d.make).1))
      (fun (_ : Unit) (d : DeferredStore κ') => some ((d.make).2, (d.make).1))
      (fun _ => True))  := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_make

theorem Refinement.projects_cellAt (cell : DeferredKey) : (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => (d.cellAt cell).map fun c => (d, c.map f))
      (fun (_ : Unit) (d : DeferredStore κ') => (d.cellAt cell).map fun c => (d, c))
      (fun _ => True))  := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_cellAt

theorem Refinement.projects_setCell (cell : DeferredKey) (value : DeferredCell κ) : (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.setCell cell value, ()))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.setCell cell (value.map f), ()))
      (fun _ => True))  := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_setCell

theorem Refinement.projects_isDone (cell : DeferredKey) : (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => (d.isDone cell).map fun done => (d, done))
      (fun (_ : Unit) (d : DeferredStore κ') => (d.isDone cell).map fun done => (d, done))
      (fun _ => True))  := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_isDone

theorem Refinement.projects_poll (cell : DeferredKey) : (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => (d.poll cell).map fun c => (d, c.map f))
      (fun (_ : Unit) (d : DeferredStore κ') => (d.poll cell).map fun c => (d, c))
      (fun _ => True))  := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_poll

theorem Refinement.projects_register (cell : DeferredKey) (waiter : FiberId) (token : Nat) : (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) =>
        some ((d.register cell waiter token).1, (d.register cell waiter token).2.map f))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.register cell waiter token))
      (fun _ => True))  := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_register

theorem Refinement.projects_cancel (cell : DeferredKey) (waiter : FiberId) (token : Nat) : (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.cancel cell waiter token, ()))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.cancel cell waiter token, ()))
      (fun _ => True))  := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_cancel

theorem Refinement.projects_complete (cell : DeferredKey) (completion : κ) : (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.complete cell completion))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.complete cell (f completion)))
      (fun _ => True))  := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_complete

theorem Refinement.projects_drainDue : (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) =>
        some ((d.drainDue).2, (d.drainDue).1.map (Owed.mapCode f)))
      (fun (_ : Unit) (d : DeferredStore κ') => some ((d.drainDue).2, (d.drainDue).1))
      (fun _ => True))  := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_drainDue

theorem Refinement.projects_wakeBatch (cell : DeferredKey) : (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.wakeBatch cell, ()))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.wakeBatch cell, ()))
      (fun _ => True))  := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_wakeBatch

end DeferredProjects

/-- Equality at the finer observation transfers through its explicit forgetting function. -/
theorem Refinement.factors_respects_eq {State : Type u} {Fine : Type v} {Coarse : Type w}
    (fine : State → Fine) (coarse : State → Coarse) (a b : State) :
    Factors fine coarse → fine a = fine b → coarse a = coarse b := by
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Refinement.Factors])

attribute [aesop safe forward (rule_sets := [Effect4.Stores])] Refinement.factors_respects_eq

/-- Compose the two explicit forgetting functions. This rule is used locally. -/
theorem Refinement.factors_trans {State : Type u} {A : Type v} {B : Type w} {C : Type z}
    (a : State → A) (b : State → B) (c : State → C) :
    Factors a b → Factors b c → Factors a c := by
  rintro ⟨ab, hab⟩ ⟨bc, hbc⟩
  refine ⟨bc ∘ ab, ?_⟩
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add norm simp [Function.comp_def])

/-- Observing the completion spelling uses only the actual deferred-store projection. -/
theorem Refinement.factors_deferreds {Observation : Type u}
    (observe : DeferredStore Program → Observation) :
    Factors Stores.deferreds (fun s => observe (s.deferreds.map completionPrim)) := by
  exact ⟨fun d => observe (d.map completionPrim), fun _ => rfl⟩

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.factors_deferreds

/-- A surrounding observation can use that same deferred-store factorization. -/
theorem Refinement.factors_through_deferreds {Fine : Type u} {Observation : Type v}
    (fine : Stores → Fine) (h : Factors fine Stores.deferreds)
    (observe : DeferredStore Program → Observation) :
    Factors fine (fun s => observe (s.deferreds.map completionPrim)) := by
  have deferred := Refinement.factors_deferreds observe
  aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add safe forward [Refinement.factors_trans])

attribute [aesop safe forward (rule_sets := [Effect4.Stores])] Refinement.factors_through_deferreds

/-- The established kernel projection supplies the state-first Projects interface. -/
theorem Refinement.projects_arena {σ : Type} [Arena σ Val] [LawfulArena σ Val] :
    Refinement.Projects (@Arena.toList σ Val _ _) arenaStepState listStepState
      (fun _ : σ => True) := by
  constructor
  · intro op s _
    have projected := congrArg (Option.map Prod.swap) (toList_refStepOf op.1 op.2 s)
    simpa only [arenaStepState, listStepState, Option.map_map, Function.comp_def,
      Prod.map, Prod.swap, id_eq] using projected
  · aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

attribute [aesop safe apply (rule_sets := [Effect4.Stores])] Refinement.projects_arena

end Effect4.Machine

#typed_state_obligations Effect4.Machine.M1.DeferredImageSupportWanted ceiling 0
  using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])

#typed_state_obligations Effect4.Machine.M1.DeferredWanted ceiling 0
  using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel]) (add safe forward [Effect4.Machine.Refinement.factors_trans])

#typed_state_obligations Effect4.Machine.ArenaObligations ceiling 0
  using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel])
