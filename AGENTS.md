# Effect4 — agent operating rules

This file is the always-loaded router for work in this repository. Read it in
full, then open only the authority documents named for the current task.

## Authority map

| Path | Owns |
| --- | --- |
| `README.md` | what the product is, the application face, the source tree, how to build |
| `docs/ARCHITECTURE.md` | module boundaries, dependency direction, the API seam |
| `docs/DESIGN-BASIS.md` | the representation decisions (DB-01 … DB-07) and their sources |
| `docs/RUNTIME-COVERAGE.md` | the rc.112 runtime mechanism census, its rows, and the one coverage report format |
| `docs/SCHEMA-ANNOTATIONS.md` | the annotation data plane as the host defines it |
| `Test/contracts/` | frozen contract packets and their executable falsifiers |
| `Test/Counterexamples/REGISTER.md` | stable IDs of every declaration-changing counterexample |
| `src/Effect4/` | library declarations and proofs |
| `Test/` | batteries, attacks and proof receipts; `Audit/AxiomGate.lean` is the gate |
| `generated/` | deterministic projections only; never hand-edited |
| `docs/research/` (not tracked) | working notes, plans, the proof-graph ledgers and surveys; synced between machines directly |
| `COORDINATION.md` (not tracked) | live claims between concurrent sessions, and the parity steps for the other machine |

If two files appear to own the same fact, stop and repair the ownership map.

## What the tree is

The product is Effect codegen (`README.md`): `Eff` is the one program IR,
`Effect4.Api` the one module an application imports, the Deep machine the
semantics under it, Schema the data plane beside it. The Flow route of
earlier work lives on branch `archive/flow-route`; do not re-import it, and
do not write a second program representation.

## Representation rules

- Canonical program content is first-order data. Lean functions, `Expr`, host
  closures, promises, and runtime objects are not stored program syntax.
- Every rc.112 behaviour a declaration models names the line it transcribes
  (`vendor/effect-4.0.0-rc.112/src/…`); a theorem that witnesses a census row
  names the row id in its docstring and is joined in
  `Test/Audit/RuntimeCoverage.lean`. The theorem alone moves no number.
- Fuel exhaustion and unanswered choices are live frontiers, never typed
  errors, causes, or refusals.
- Full meaning is relational over explicit decisions. Determinism is claimed
  only after fixing a complete compatible decision tape or proving a fragment
  contains no decision source.
- State produced before failure remains available to finalization.
- Effect TypeScript is one target profile, not the identity or semantic owner.
- Names are data: an alphabet instantiated at a function type fails the
  separation gates at the foot of the machine modules.

## Trust

- No `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern`,
  `implemented_by`. The gate audits every `Effect4.*` and `Test.*`
  declaration at `[propext, Quot.sound]`; a rendering declaration that must
  traverse a `String` is admitted by exact name in `AxiomGate.lean`, never by
  module. A battery `def` over rendered text reaches `Classical.choice`: keep
  rendered bytes inside `#guard`s.
- Every battery file under `Test/` must be reachable from
  `Test/All.lean`, or the module-closure gate refuses the build.
- Do not say "sound", "equivalent", "preserves", "fully reified", or
  "complete" without naming the exact judgment, observation, theorem or gate,
  assumptions, and remaining host boundary. A compiling finite probe is
  reported as a finite probe.
- Coverage of the Effect runtime is stated only in the block printed by
  `scripts/report-effect-runtime-coverage.sh`, after
  `scripts/check-effect-runtime-census.sh` passes.

## Working

- Design first, land once: a change to the machine or the syntax starts as a
  grilled plan in `docs/research/`, then lands as one commit with the gate
  green. Mechanical pieces on disjoint files may be delegated; the coordinator
  reviews, adds the root imports, runs the build and commits. An agent never
  commits, never `git add`s, and never edits `src/Effect4.lean`,
  `Test/All.lean`, `Test/Audit/AxiomGate.lean` or `lakefile.toml`.
- One `lake` at a time in a working tree.
- On Windows the shell is PowerShell; the bash gate scripts run through WSL.
- A proof graph is mandatory only for admission or refusal, judgments or
  denotations, interpreters or handlers, reification or generated-code
  relations, nontrivial composition or recursive invariants, and external
  semantic equivalence; a passive finite alphabet closes with its local
  receipts.
- More than one session may edit this branch. Read `COORDINATION.md` before
  changing a shared surface and record a claim there; `git fetch` before a
  commit and never `git add -A` without reading `git status` first.
- A handoff records base and head commits, changed files, exact commands and
  results, axiom output, open obligations, and whether any evidence is bounded
  or host-only.
