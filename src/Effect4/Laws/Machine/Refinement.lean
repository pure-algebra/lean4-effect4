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

namespace M1.DeferredWanted

variable (f : κ → κ') (g : κ' → κ'') (d : DeferredStore κ)

def cell_map_id (c : DeferredCell κ) : ProofGraph.Obligation
    (c.map id = c) := ⟨⟩
#proof_wanted cell_map_id

def cell_map_comp (c : DeferredCell κ) : ProofGraph.Obligation
    ((c.map f).map g = c.map (g ∘ f)) := ⟨⟩
#proof_wanted cell_map_comp

def map_id : ProofGraph.Obligation (d.map id = d) := ⟨⟩
#proof_wanted map_id

def map_comp : ProofGraph.Obligation ((d.map f).map g = d.map (g ∘ f)) := ⟨⟩
#proof_wanted map_comp

-- The ten operations, in the declaration order of Machine/Stores.lean.

def map_make : ProofGraph.Obligation
    ((d.map f).make = ((d.make).1, (d.make).2.map f)) := ⟨⟩
#proof_wanted map_make

def map_cellAt (cell : DeferredKey) : ProofGraph.Obligation
    ((d.map f).cellAt cell = (d.cellAt cell).map (DeferredCell.map f)) := ⟨⟩
#proof_wanted map_cellAt

def map_setCell (cell : DeferredKey) (value : DeferredCell κ) : ProofGraph.Obligation
    ((d.map f).setCell cell (value.map f) = (d.setCell cell value).map f) := ⟨⟩
#proof_wanted map_setCell

def map_isDone (cell : DeferredKey) : ProofGraph.Obligation
    ((d.map f).isDone cell = d.isDone cell) := ⟨⟩
#proof_wanted map_isDone

def map_poll (cell : DeferredKey) : ProofGraph.Obligation
    ((d.map f).poll cell = (d.poll cell).map (Option.map f)) := ⟨⟩
#proof_wanted map_poll

def map_register (cell : DeferredKey) (waiter : FiberId) (token : Nat) : ProofGraph.Obligation
    ((d.map f).register cell waiter token =
      ((d.register cell waiter token).1.map f, (d.register cell waiter token).2.map f)) := ⟨⟩
#proof_wanted map_register

def map_cancel (cell : DeferredKey) (waiter : FiberId) (token : Nat) : ProofGraph.Obligation
    ((d.map f).cancel cell waiter token = (d.cancel cell waiter token).map f) := ⟨⟩
#proof_wanted map_cancel

def map_complete (cell : DeferredKey) (completion : κ) : ProofGraph.Obligation
    ((d.map f).complete cell (f completion) =
      ((d.complete cell completion).1.map f, (d.complete cell completion).2)) := ⟨⟩
#proof_wanted map_complete

def map_drainDue : ProofGraph.Obligation
    ((d.map f).drainDue =
      ((d.drainDue).1.map (Owed.mapCode f), (d.drainDue).2.map f)) := ⟨⟩

def map_wakeBatch (cell : DeferredKey) : ProofGraph.Obligation
    ((d.map f).wakeBatch cell = (d.wakeBatch cell).map f) := ⟨⟩
#proof_wanted map_wakeBatch

end M1.DeferredWanted

/-! The image boundary lives in Laws, and never becomes a machine invariant again. -/
namespace Refinement

/-- Only actual completed cell values and actual due-code values need witnesses. -/
def DeferredOk (d : DeferredStore Program) : Prop :=
  (∀ cell ∈ d.cells, ∀ p, cell.completion = some p → ∃ c, p = completionPrim c) ∧
    ∀ owed ∈ d.due, ∃ c, owed.code = completionPrim c

end Refinement

namespace M1.DeferredWanted

-- These are exact embedding/image statements, not a total read on arbitrary Program.
def completionPrim_injective : ProofGraph.Obligation
    (Function.Injective completionPrim) := ⟨⟩
#proof_wanted completionPrim_injective

def deferredOk_iff_image (d : DeferredStore Program) : ProofGraph.Obligation
    (Refinement.DeferredOk d ↔ ∃ d' : DeferredStore, d = d'.map completionPrim) := ⟨⟩
#proof_wanted deferredOk_iff_image

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

def projects_make : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some ((d.make).2, (d.make).1))
      (fun (_ : Unit) (d : DeferredStore κ') => some ((d.make).2, (d.make).1))
      (fun _ => True)) := ⟨⟩
#proof_wanted projects_make

def projects_cellAt (cell : DeferredKey) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => (d.cellAt cell).map fun c => (d, c.map f))
      (fun (_ : Unit) (d : DeferredStore κ') => (d.cellAt cell).map fun c => (d, c))
      (fun _ => True)) := ⟨⟩
#proof_wanted projects_cellAt

def projects_setCell (cell : DeferredKey) (value : DeferredCell κ) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.setCell cell value, ()))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.setCell cell (value.map f), ()))
      (fun _ => True)) := ⟨⟩
#proof_wanted projects_setCell

def projects_isDone (cell : DeferredKey) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => (d.isDone cell).map fun done => (d, done))
      (fun (_ : Unit) (d : DeferredStore κ') => (d.isDone cell).map fun done => (d, done))
      (fun _ => True)) := ⟨⟩
#proof_wanted projects_isDone

def projects_poll (cell : DeferredKey) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => (d.poll cell).map fun c => (d, c.map f))
      (fun (_ : Unit) (d : DeferredStore κ') => (d.poll cell).map fun c => (d, c))
      (fun _ => True)) := ⟨⟩
#proof_wanted projects_poll

def projects_register (cell : DeferredKey) (waiter : FiberId) (token : Nat) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) =>
        some ((d.register cell waiter token).1, (d.register cell waiter token).2.map f))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.register cell waiter token))
      (fun _ => True)) := ⟨⟩
#proof_wanted projects_register

def projects_cancel (cell : DeferredKey) (waiter : FiberId) (token : Nat) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.cancel cell waiter token, ()))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.cancel cell waiter token, ()))
      (fun _ => True)) := ⟨⟩
#proof_wanted projects_cancel

def projects_complete (cell : DeferredKey) (completion : κ) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.complete cell completion))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.complete cell (f completion)))
      (fun _ => True)) := ⟨⟩
#proof_wanted projects_complete

def projects_drainDue : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) =>
        some ((d.drainDue).2, (d.drainDue).1.map (Owed.mapCode f)))
      (fun (_ : Unit) (d : DeferredStore κ') => some ((d.drainDue).2, (d.drainDue).1))
      (fun _ => True)) := ⟨⟩
#proof_wanted projects_drainDue

def projects_wakeBatch (cell : DeferredKey) : ProofGraph.Obligation
    (Projects (DeferredStore.map f)
      (fun (_ : Unit) (d : DeferredStore κ) => some (d.wakeBatch cell, ()))
      (fun (_ : Unit) (d : DeferredStore κ') => some (d.wakeBatch cell, ()))
      (fun _ => True)) := ⟨⟩
#proof_wanted projects_wakeBatch

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
def factors_respects_eq {State : Type u} {Fine : Type v} {Coarse : Type w}
    (fine : State → Fine) (coarse : State → Coarse) (a b : State) :
    ProofGraph.Obligation
      (Factors fine coarse → fine a = fine b → coarse a = coarse b) := ⟨⟩
#proof_wanted factors_respects_eq

def factors_trans {State : Type u} {A : Type v} {B : Type w} {C : Type z}
    (a : State → A) (b : State → B) (c : State → C) : ProofGraph.Obligation
      (Factors a b → Factors b c → Factors a c) := ⟨⟩
#proof_wanted factors_trans

def factors_deferreds {Observation : Type u} (observe : DeferredStore Program → Observation) :
    ProofGraph.Obligation
      (Factors Stores.deferreds (fun s => observe (s.deferreds.map completionPrim))) := ⟨⟩
#proof_wanted factors_deferreds

/-- A surrounding observation need only retain the actual Deferred store projection. -/
def factors_through_deferreds {Fine : Type u} {Observation : Type v}
    (fine : Stores → Fine) (_h : Factors fine Stores.deferreds)
    (observe : DeferredStore Program → Observation) : ProofGraph.Obligation
      (Factors fine (fun s => observe (s.deferreds.map completionPrim))) := ⟨⟩
#proof_wanted factors_through_deferreds

end M1.DeferredWanted

-- 30 statement obligations here: 4 functor + 10 naturality + 2 embedding/image +
-- 10 Projects + 4 Factors. Handles holds the separate memoEntry_keys goal.
-- These are declaration counts; the initial open count must be measured after elaboration.
-- #typed_state_obligations Effect4.Machine.M1.DeferredWanted ceiling 30
--   using aesop (rule_sets := [Effect4.Stores])
end Effect4.Machine

namespace Effect4.Machine

/-- The generic and model steps only change pair order to fit Projects' state-first API. -/
def arenaStepState {σ : Type} [Arena σ Val] (op : RefKey × RefKernel) (s : σ) :
    Option (σ × Val) :=
  (refStepOfA op.1 op.2 s).map Prod.swap

def listStepState (op : RefKey × RefKernel) (s : RefHeap) : Option (RefHeap × Val) :=
  (refStepOf op.1 op.2 s).map Prod.swap

namespace ArenaObligations

def projects {σ : Type} [Arena σ Val] [LawfulArena σ Val] : ProofGraph.Obligation (
    Refinement.Projects (@Arena.toList σ Val _ _) arenaStepState listStepState
      (fun _ : σ => True)) := ⟨⟩
#proof_wanted projects

end ArenaObligations
end Effect4.Machine
-- END M1 PHASE B Refinement

#typed_state_obligations Effect4.Machine.ArenaObligations ceiling 15 using aesop (rule_sets := [Effect4.Stores])
