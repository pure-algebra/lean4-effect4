---
name: lean-reification
description: Plan and coordinate correctness-oriented program reification in Lean. Use when turning programs into inspectable data, connecting stored syntax to effect semantics, or organizing an EffHOL-inspired development across contracts, proofs, generators, and execution. Ordinary isolated Lean proof work does not require this workflow.
---

# Lean program reification

Turn the requested connection between program data and behavior into named,
checkable obligations. Select the smallest stage that can finish the task.

## Establish the task

Read the current project's instructions and relevant ownership records. Record
the requested outcome, permitted edits, source/toolchain pins, current changes,
and existing evidence. Keep prior authorization; a stage transition does not
create permission to change a contract, publish, or install dependencies.

Distinguish three possible requests:

- **Reification:** construct inspectable program data from an admitted source.
- **Realizability:** relate programs to the logical specifications they realize.
- **Refinement or execution:** connect one program meaning to another model or
  an external implementation.

A task may involve all three. Name each connection separately. For a direct
EffHOL formalization, read [the adaptation boundary](references/effhol.md).
For work in Effect4 or Foldlab, read [project entry points](references/projects.md)
and then the live authority files, rather than treating this pack as policy.

## Resume from evidence

| Present need | Read and use | Entry evidence |
| --- | --- | --- |
| Intent, source coverage, observations, or public obligations are unsettled | [Contract](../lean-reification-contract/SKILL.md) | User request and existing decisions |
| Stored syntax, typing, effects, or a logic connection needs design | [Model](../lean-reification-model/SKILL.md) | Provisional contract with explicit unknowns |
| A proposed law or gate needs independent challenge | [Breaker](../lean-reification-breaker/SKILL.md) | Named claim and raw evidence |
| A model is ready to freeze, or a public statement must change | [Contract, freeze pass](../lean-reification-contract/SKILL.md) | Representation decisions and counterexamples |
| A frozen proof obligation needs implementation or repair | [Proof](../lean-reification-proof/SKILL.md) | Exact statement, definitions, imports, and edit fence |
| Serialization, source generation, lowering, or host behavior is involved | [Target](../lean-reification-target/SKILL.md) | Source/target domains and observation contract |
| Someone claims correctness, equivalence, coverage, or completion | [Audit](../lean-reification-audit/SKILL.md) | Claim and the artifacts cited for it |

Read only the selected skill and the references it needs. The usual sequence
is contract, model, independent challenge, freeze, implementation and proof,
then audit. Target work contributes obligations before freezing and evidence
after implementation. Re-enter upstream only for a demonstrated semantic change.
Do not require the full sequence for a passive finite label or a proof-body fix.

## Keep the chain explicit

For every claimed arrow, identify its input/output domains, partiality,
assumptions, observation, theorem or checker, and remaining external boundary.
Use [the evidence vocabulary](references/evidence.md). Reuse project records;
use [the work record](assets/work-record.md) only when none serves the task.

A Lean theorem establishes its stated judgment under its dependencies. A
generated file match, a finite run, and a paper theorem provide different
evidence. They cannot substitute for missing connections between artifacts.
State loss explicitly: a quotient, restricted language, or observation that
hides internal events changes the claim.

If a needed upstream fact is missing, do the useful analysis and record the
gap. Ask the user only when the unresolved choice changes intended meaning or
requires authority they have not given. Never invent approval or weaken an
obligation to make progress look complete.

## Finish

Deliver the stage's actual artifact and checks, the strongest supported claim,
and every required open obligation with its consequence. Preserve the edit
fence. A proposed design may finish with explicit open proofs; an implementation
or cutover claim may not hide them. Do not convert a research source or this
workflow into a claim that a program has been verified.
