---
name: lean-reification-contract
description: Define and freeze the contract for a Lean program representation or semantic connection. Use when deciding an admitted source profile, observables, ownership, theorem statements, or cutover obligations; use a separate proof workflow for unchanged proof bodies.
---

# Contract for a reified program

Make the intended claim precise enough that a wrong representation or
implementation can fail it. Use the project's existing contract format when
available; otherwise adapt [the contract record](assets/contract-record.md).

## Choose the pass

**Formation** establishes intent before implementation. **Freeze** validates
the chosen model and exact declarations before proof work. An existing approved
contract is input, not an invitation to redesign it. For project-specific
authority, use [the entry points](../lean-reification/references/projects.md).

## Formation

1. Identify the source language, source revision or package bytes, entry
   points, supported fragment, and intended consumers. For source extraction,
   inventory public aliases, overloads, constructor fields, recursive children,
   and export paths. Account for every in-scope row; an omitted row is unknown,
   not an exclusion. Use a second independent inventory when claiming closure.
2. State which artifact is canonical program content, which is a proof model,
   which is an interpreter, and which belongs to the host. Search existing
   owners before introducing a type. Record reuse, view, adapter, distinct
   calculus, derived form, foreign boundary, or explicit exclusion.
3. Name the observations: successful values, failure classes, state before and
   after failure, trace ordering, divergence, and pending interaction as needed.
   State the equality or refinement relation and its direction. Record any
   normalization, quotient, or hidden event. Do not infer the intended meaning
   from an API name or a successful typecheck.
4. Specify inputs and outcomes for each admission boundary. Separate parse
   errors, invalid references/types, unsupported profile forms, program
   failures, and unfinished execution. Distinguish checker soundness from
   accepting every valid source form; require the latter only if promised.
5. Give an inhabited positive case, a forbidden case, an important boundary
   case, and a counterexample to a tempting stronger claim. State environmental
   assumptions separately from facts to prove. A fairness assumption, hash
   assumption, or foreign-function contract must have an explicit owner.
6. Record obligations for each actual connection: admission, erasure,
   interpretation, composition, representation, target, and trust as applicable.
   Choose a small graph for semantic owners; use local receipts for passive
   leaves. A short or decidable admission function is still a semantic owner.

Read [obligation selection](references/obligations.md) when choosing theorem
directions or the assurance route. Read
[the EffHOL boundary](../lean-reification/references/effhol.md) when a paper rule
is proposed as a local law. Use prior art as reuse, adaptation, or a pattern,
with the mismatch recorded; the paper does not supply local proof evidence.

Formation finishes with a bounded contract, known decisions, unresolved model
questions, and falsifiers. Route unresolved representations to
[Model](../lean-reification-model/SKILL.md), then invite an independent
[Breaker](../lean-reification-breaker/SKILL.md) where the project requires one
or the claim warrants it. Do not start production implementation from sketches.

## Freeze

Compare the proposed declarations to the contract, model record, and attacks.
Check exact types, universe levels, implicit arguments, instances, operation
equations, semantic definitions, source profiles, and allowed trust dependencies.
When Lean statements exist, elaborate them at the target pin using the project's
statement-checking route. A red contract containing intentional missing names
must fail for those reasons; a parse failure is not a useful red battery.

Freeze the declaration and definition references, dependencies, imports,
applicable obligations, positive/negative cases, and builder edit fence. Retain
the contract/battery owner separately from the builder. A signature hash alone
does not protect the meaning of referenced definitions or local instances.

Before changing a frozen statement, record the old and new meaning, the
counterexample or requirement forcing the change, affected obligations, and
the required authority. Existing authorization can cover the change; never
manufacture a fresh approval hurdle or treat proof difficulty as permission.

Freeze finishes when the exact contract is reviewable, its acceptance checks
exercise the intended interfaces, and every unresolved issue has an explicit
consequence. Hand frozen obligations to [Proof](../lean-reification-proof/SKILL.md)
and transformation obligations to [Target](../lean-reification-target/SKILL.md).
