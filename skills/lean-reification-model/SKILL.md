---
name: lean-reification-model
description: Design Lean representations and semantics for inspectable effectful programs. Use for closure conversion, typed program graphs, effect handlers, evaluation modalities, state and failure, recursion, or decisions in a reified language, including EffHOL-inspired models.
---

# Model program data and behavior

Require a contract naming the admitted language and observations. If it is
missing, form a provisional one with
[Contract](../lean-reification-contract/SKILL.md); carry uncertainties as
questions rather than silently choosing a different language.

## Separate the representations

Identify raw input, checked program content, the semantic/proof carrier,
runtime configuration, specifications, and external realizations. Reuse the
canonical owners. For every additional view, name the erasure, embedding,
interpretation, or refusal relation and any information it loses.

When content must be stored, compared, transmitted, or generated, represent
its choices as data: operation tags, typed operands, named blocks, environments,
captures, and explicit exits. Higher-order source syntax can use first-order
binder syntax or closure-converted code; first-order content does not require
a first-order source language. Do not store host functions, promises, object
identity, or raw Lean `Expr` as the durable meaning.

A continuation-based free program can remain the proof carrier. An inductive
well-founded tree need not have finitely many nodes or a uniform depth bound
with infinitely many answers. A finite cyclic document may describe unbounded
behavior. Neither fact provides serialization or decidable semantic equality.
Use [representation decisions](references/representation.md) for binders,
cycles, universes, raw/checked boundaries, and higher-order effects.

## Define behavior before laws

Choose a relation or interpreter adequate for the stated observations. Name
the evaluation strategy, handler environment, answer history, choice owner,
state, and observations it carries. Use functions for a justified deterministic
fragment; use relations where unresolved external or scheduler decisions remain.

Keep unfinished computation distinct from typed failure, defects, interruption,
and input/profile refusal. A fuel limit witnesses an approximation, not
termination or divergence. Prove the relevant runner-to-relation connection;
state composition at the face where its hypotheses actually hold.

For stateful failure and scoped effects, check whether the carrier retains the
state that cleanup must observe. Record handler installation/removal, named
body and cleanup regions, resumption multiplicity, and interruption ownership.
Give success and failure examples before claiming a generic catch or finalizer.
Read [effects and logic](references/effects-and-logic.md) for these branches.

For open or concurrent execution, separate internal choice, external replies,
enabled scheduler moves, and the decisions actually selected. Determinism may
be conditional on one complete compatible decision stream. Safety, absence of
deadlock, termination, fairness, and eventual response are separate obligations.

## Connect programs and specifications

For a proposed modality or program logic, read
[the EffHOL adaptation record](../lean-reification/references/effhol.md).
Reuse an existing predicate transformer when it describes this fragment, then
prove its relationship to operational behavior. Record universal versus
existential choice and partial versus total correctness. A `Monad` instance
alone does not decide either or establish the modal rules.

When the task is actual proof-to-program extraction, keep the executable
witness in computational data and its certificate in `Prop`. An existence
theorem or an arbitrary Lean proof is not an executable reifier. List the
supported source proof rules, translations, typing/substitution obligations,
and the constructive extraction interface; leave unsupported rules explicit.

## Finish

Complete [the model record](assets/model-record.md): carriers, retained/lost
data, admission, semantics, logic, composition, observations, and required
connections. Include counterexamples that distinguish plausible alternatives.
Do not add a second public carrier or logic merely to avoid a difficult bridge.
Return the model and its unresolved obligations for independent challenge and
the contract's freeze pass. A design document finishes as a design; it does not
claim that the proposed theorems or host correspondence already exist.
