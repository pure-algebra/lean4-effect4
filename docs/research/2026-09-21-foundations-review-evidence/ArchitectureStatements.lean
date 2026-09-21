import ProofGraph.Ledger
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Effects.Protocol
import Effect4.Laws.Machine.Refinement
import Effect4.Laws.Program.Typed.Contracts

/-!
# Foundations architecture: statement-only research packet

These are four candidate obligations, not proofs of the enclosed propositions. The empty
`ProofGraph.Obligation` constructor only retains a target statement; `#proof_wanted` records
that its mathematical proof remains absent. This file does not belong to the production
ledger. No evaluator, stored program representation, or concrete backend is introduced.

The candidates reuse the current operation definitions and proof-side interfaces. They do
not choose the still-open strong TypedProg/control judgment, identify shape admission with
live-handle typing, or assume a host/compiler implementation satisfies an interface.

Review base: 641a0feabe8ff7c3899396cd2144380d6d8cf53c.
-/

set_option autoImplicit false

namespace FoundationsArchitectureStatements
open Effect4 Effect4.Machine Effect4.Machine.Refinement Effect4.Program

universe u v w x y

/-- Candidate C1: completed-boundary shape/column transport with persistent heap declarations
and external lookup preservation. Equality of allocation tables is a sufficient specialization.
This does not establish handle liveness, nested declaration agreement, destination WF, or
that an actual transition establishes either premise. It generalizes the existing
`completionOk_extends` equality adapter using the already-proved value-admission transport. -/
theorem completion_transport : ProofGraph.Obligation (
    ∀ (before after : Typed.World) (types : Ty × Ty),
      Typed.TableExtends before.Ρ after.Ρ →
      Extends before.state.externals.allocated after.state.externals.allocated →
      ∀ completion : Completion Val Err Defect FiberId Ann,
        Typed.CompletionOk before types completion →
        Typed.CompletionOk after types completion) := ⟨⟩

#proof_wanted completion_transport

/-- Candidate C2: a heterogeneous heap property survives an actual reference-kernel row.
The row law constrains only the selected cell's predicate; every other index keeps its
actual lookup. `refMake` has no refKernel and remains a separate allocation obligation.
This is conditional on the row's Keeps proof, not on an invented replacement evaluator. -/
theorem indexed_ref_step_preserves : ProofGraph.Obligation (
    ∀ (P : Nat → Val → Prop) (Q : Val → Prop)
      (op : SyncOp) (cell : RefKey) (kernel : RefKernel)
      (before after : RefHeap) (answer : Val),
      op.refKernel = some (cell, kernel) →
      (∀ index value, refPeek before ⟨index⟩ = some value → P index value) →
      RefKernel.Keeps (P cell.index) Q kernel →
      refStep op before = some (answer, after) →
      Q answer ∧
      (∀ index value, refPeek after ⟨index⟩ = some value → P index value) ∧
      after.length = before.length ∧
      (∀ index, index ≠ cell.index →
        refPeek after ⟨index⟩ = refPeek before ⟨index⟩)) := ⟨⟩

#proof_wanted indexed_ref_step_preserves

/-- Candidate C3: compose two exact one-step projections, retaining both concrete-side
invariants. The paired domain makes the middle representation's validity requirement
explicit; initialization into that domain is a separate implementation obligation.
The operation and answer carriers remain identical along this particular interface. -/
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

#proof_wanted projects_compose

/-- Candidate C4: an exact projection supplies the existing relational interface when its
relation retains the concrete invariant. Successful steps retain the relation; a concrete
`none` yields model `none` at related states. No initialization, fairness, multi-step progress,
changed answer encoding, compiler correctness, or host implementation instance is supplied. -/
theorem projects_induces_refines : ProofGraph.Obligation (
    ∀ {Concrete : Type u} {Model : Type v} {Op : Type w} {Answer : Type x}
      (project : Concrete → Model)
      (stepConcrete : Op → Concrete → Option (Concrete × Answer))
      (stepModel : Op → Model → Option (Model × Answer))
      (valid : Concrete → Prop),
      Projects project stepConcrete stepModel valid →
      Refines (fun concrete model => valid concrete ∧ project concrete = model)
        stepConcrete stepModel) := ⟨⟩

#proof_wanted projects_induces_refines

end FoundationsArchitectureStatements

-- This gate reports open payloads; the declaration wrappers are not their proofs.
#typed_state_obligations FoundationsArchitectureStatements ceiling 4
  using aesop (rule_sets := [Effect4.Stores])

#check FoundationsArchitectureStatements.completion_transport
#check FoundationsArchitectureStatements.indexed_ref_step_preserves
#check FoundationsArchitectureStatements.projects_compose
#check FoundationsArchitectureStatements.projects_induces_refines
#print axioms FoundationsArchitectureStatements.completion_transport
#print axioms FoundationsArchitectureStatements.indexed_ref_step_preserves
#print axioms FoundationsArchitectureStatements.projects_compose
#print axioms FoundationsArchitectureStatements.projects_induces_refines
