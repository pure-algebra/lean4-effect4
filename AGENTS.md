# Effect4 — agent operating rules

This file is the always-loaded router for work in this repository. Read it in
full, then open only the authority documents named for the current task.

## Authority map

| Path | Owns |
| --- | --- |
| `COORDINATION.md` | live claims between concurrent agents, and what past collisions cost |
| `PLAN.md` | extraction phases, entry and exit gates, current phase |
| `docs/ARCHITECTURE.md` | module boundaries, dependency direction, public API policy |
| `PORT-MANIFEST.md` | exact Foldlab source declarations, tests, pins, and destination dispositions |
| `test/contracts/` | breaker-authored algebraic contracts and executable falsifiers |
| `test/counterexamples/` | central counterexample register and durable witnesses |
| `Effect4/` | library declarations and proofs |
| `Effect4Test/` | Lean tests, attacks, examples, and proof receipts |
| `harness/` | host conformance, TypeScript, runtime, and language-service checks |
| `generated/` | deterministic projections only; never hand-edited |
| `docs/RUNTIME-COVERAGE.md` | definition, vocabulary, and the one report format of Effect runtime coverage |

If two files appear to own the same fact, stop and repair the ownership map.

More than one agent may edit this worktree at once. Direct messaging is not a
durable ownership record, so every agent reads `COORDINATION.md` before
writing and records a file claim there before freezing a packet or changing a
shared surface.

## Development order

1. Freeze the public declaration record, existing-type disposition, and
   assurance route.
2. A breaker, in a separate process, commits the contract and red battery.
3. The builder implements without editing that packet or battery.
4. Run the narrow test, the package build, axiom inspection, and the relevant
   host gate.
5. An independent reviewer checks model intent, proof trust, compatibility,
   and claim scope.
6. Close the required assurance route: a proof graph for semantic or
   cutover-bearing work, or local signature and theorem receipts for a trivial
   finite leaf. No category or full cutover may hide an open graph edge or
   leaf receipt.

Every exported declaration still receives a lightweight ownership,
disposition, and duplicate-prevention record. A proof graph is mandatory only
for admission or refusal, judgments or denotations, interpreters or handlers,
reification or generated-code relations, nontrivial composition or recursive
invariants, external semantic equivalence, and declarations that directly
gate cutover. Empty stubs have no declaration to record and need no graph.
`docs/AGENT-ROUTING.md` owns the full threshold and Schema examples.

Breadth precedes depth: every major category receives a frozen representative
contract before one category is developed far beyond the others.

## Representation rules

- Canonical program content is first-order data. Lean functions, `Expr`, host
  closures, promises, and runtime objects are not stored program syntax.
- Raw Lean `Expr` is allowed only at the metaprogramming boundary. Elaborated
  declarations must emit checked first-order rows before entering semantics.
- Fuel exhaustion and unanswered choices are live frontiers, never typed
  errors, causes, or refusals.
- Full meaning is relational over explicit decisions. Determinism is claimed
  only after fixing a complete compatible decision tape or proving a fragment
  contains no decision source.
- Fixed-fuel execution is not assigned a general bind law. Composition is
  proved at the big-step/interpreter face.
- State produced before failure remains available to finalization. Resource
  laws must not be encoded with a carrier that discards that state.
- Schema, Context/Service, Layer, Runtime, ManagedRuntime, Scope, Fiber,
  Channel/Stream, Schedule, and transactions are distinct calculi or layers
  with explicit embeddings; type mention alone does not make a primitive.
- Effect TypeScript is one target profile, not the identity or semantic owner.

## Reuse and compatibility

- This repository must not depend on Foldlab.
- The effect algebra (`Signature`, `Program`, `Handler`, their laws) is the
  `Effects` package, pinned by exact commit in `lakefile.toml`. Effect4
  depends on Effects, never conversely, and never re-declares its carriers.
  A change to the algebra goes through the Effects breaker process and a
  version bump here.
- Foldlab compatibility adapters depend on Effect4, never conversely.
- A moved declaration keeps a source digest and compatibility theorem before
  its Foldlab owner can be retired.
- Existing Foldlab CAS identity, bytes, refusal classification, and program
  spellings remain Foldlab-owned until their rows are explicitly closed.
- Experimental carriers that do not compose are evidence, not port sources.

## Counterexamples and claims

All counterexamples that can change a declaration or cutover decision have a
stable ID in `test/counterexamples/REGISTER.md`. Proof sources remain beside
the attacked code and are linked, not copied into prose.

Do not say “sound”, “equivalent”, “preserves”, “fully reified”, or “complete”
without naming the exact judgment, observation, theorem or gate, assumptions,
and remaining host boundary. A compiling finite probe is reported as a finite
probe.

Coverage of the Effect runtime is stated only in the block printed by
`scripts/report-effect-runtime-coverage.sh`, pasted verbatim with its commit,
after `scripts/check-effect-runtime-census.sh` passes. `docs/RUNTIME-COVERAGE.md`
defines the rows, the green criterion, and how the number may move; the
`runtime-coverage` skill is the procedure. No percentage is computed by hand.

## Generated facts and long-run continuity

Authored routers such as this file are never generated. Machine status,
surface rows, declaration digests, conditional obligation graphs, leaf receipts,
and proof receipts are generated from canonical inputs and checked for drift.
A fresh session resumes by reading, in order:

1. `PLAN.md` current-phase row;
2. `PORT-MANIFEST.md` source pin and open dispositions;
3. the current contract packet and counterexample rows;
4. the per-declaration assurance row;
5. the narrow verification command recorded by that row; and
6. `git status --short --branch` to attribute local changes.

## Handoff

Every handoff records base and head commits, file fence, changed files, exact
commands and results, public declarations, axiom output, open proof edges or
leaf receipts, counterexamples exercised, and whether any evidence is bounded
or host-only.
