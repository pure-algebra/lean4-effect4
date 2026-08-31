# Effect4 source routing

This boundary contains the Lean library's semantic declarations and proofs.
The repository root rules remain in force; `docs/AGENT-ROUTING.md` defines how
these source rules connect to tests, host evidence, and generated closure.

## Before a declaration changes

Read `docs/ARCHITECTURE.md`, the relevant `PORT-MANIFEST.md` disposition, the
frozen contract, and every linked row in
`test/counterexamples/REGISTER.md`. Check the current per-type closure
snapshot when it exists.

Every public type must already have an authored existing-type row with one
owner, its semantic role, its source pin and digest when ported, and its proof
graph ID. A new native type names the contract that fixed its role.

Do not create a carrier because an implementation needs a convenient local
shape. Reuse the canonical owner, add a named view or adapter, or state that a
family is a separate calculus. A second representation requires an explicit
conversion, embedding, erasure, or refusal theorem and an annotation naming
the canonical carrier. Raw and checked forms, syntax and denotation, and
downstream compatibility views remain distinct for stated reasons; copied
constructors do not establish a distinction.

## Proof work

The builder does not edit the breaker-authored contract or red battery. Public
claims name the exact judgment and observation face. Bounded execution does
not replace relational or big-step meaning, and host execution does not prove
a Lean theorem.

For every changed public type, update or close only the proof-graph edges for
which evidence now exists: identity, construction, semantics, laws,
representation, counterexamples, bridges, targets, trust, and coverage. New
axioms or opaque trust boundaries require an explicit authored admission and
an axiom receipt. Compilation alone closes no semantic edge.

The narrow test, default Lake build, axiom inspection, and relevant generated
drift gate must run before a source handoff. Report open edges without
rounding them up to category completion.
