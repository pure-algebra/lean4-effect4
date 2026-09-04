# Effect4 source routing

This boundary contains the Lean library's semantic declarations and proofs.
The repository root rules remain in force; `docs/AGENT-ROUTING.md` defines how
these source rules connect to tests, host evidence, and generated assurance.

## Before a declaration changes

Read `docs/ARCHITECTURE.md`, the relevant `PORT-MANIFEST.md` disposition, the
frozen contract, and every linked row in
`test/counterexamples/REGISTER.md`. Check the current per-declaration assurance
snapshot when it exists.

Every public declaration must have a lightweight ownership, disposition, and
duplicate-prevention record. Every public type must already have an authored
existing-type row with one owner, its semantic role, and its source pin and
digest when ported. The row selects either a required proof graph or a local
receipt set marked `standalone` or linked to a named parent-graph edge. A new
native type names the contract that fixed its role. Empty source stubs with no
exported declarations need neither record nor graph.

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

Use `docs/AGENT-ROUTING.md`'s threshold. Admission or refusal, judgments,
denotation, interpreters or handlers, semantic reification or refinement,
generated-code relations, nontrivial composition or recursive invariants,
external semantic equivalence, and independently owned direct cutover
conditions require a proof graph. A passive finite leaf alphabet or value
record may instead close with its exact local theorem receipts. It is marked
standalone, or names the parent-graph edge to which it contributes. Escalate
the row before adding a graph-bearing claim, retaining every former receipt as
a graph obligation unless an explicit supersession ruling replaces it.

For a graph-bearing type, update or close only the edges for which evidence now
exists: identity, construction, semantics, laws, representation,
counterexamples, bridges, targets, trust, and coverage. For a leaf, update only
its declared signature, census, round-trip, separation, embedding, and axiom
receipts. New axioms or opaque trust boundaries require an explicit authored
admission and an axiom receipt. Compilation alone closes no semantic edge or
leaf theorem receipt.

A theorem written to witness an Effect runtime behaviour names the census row
id from `generated/effect-runtime-census.tsv` in its docstring and is joined
test-side in `Effect4Test/Audit/RuntimeCoverage.lean`; the theorem alone moves
no coverage number. A public declaration added under `Effect4/Concurrency/`
also moves the frozen surface census in
`Effect4Test/Concurrency/FiberAssurance.lean` and its generator counts, so
plan both edits in one packet. `docs/RUNTIME-COVERAGE.md` owns the rules.

The narrow test, default Lake build, axiom inspection, and relevant generated
drift gate must run before a source handoff. Report open graph edges and leaf
receipts without rounding them up to category completion.
