# Live coordination between concurrent agents

Two agents are editing this worktree at the same time and **cannot message each
other**. There is no negotiation channel. This file is the channel.

If you are an agent working here, read this before you write, and update your
claims when you take or release a file.

Last updated: 2026-08-31.

> GitHub checkpoint note, 2026-09-01: the in-process Codex lanes were
> interrupted before cleanup. Their ownership rows are retained rather than
> silently cleared. The Claude rows have not been independently released.
> Reconfirm a row with its named owner before treating the path as available.

> Operator continuation, 2026-09-01: the latest handoff reports the Scope join
> complete at `f4f55fa` and authorizes Codex to implement fork and supervision.
> The specific `Codex fork/supervision` fences below supersede the old
> direct-child reservation and the overlapping portions of retained broad
> claims. All other portions remain reserved. The independent breaker and
> reviewer use this same packet; there is no parallel supervision design.

## Who is active

| Agent | Working on |
| --- | --- |
| Codex | `Effect4/Data/Row.lean` (implementing, ~34 declarations landed); the concurrency lane incl. `Effect4Test/Concurrency/FiberRepresentativeContract.lean`; the context-key assurance machinery (`Effect4Test/Environment/ContextKeyAssurance.lean`, `scripts/generate-environment-context-key-evidence.sh`, `generated/`); `Effect4Test/Schema/PayloadSurface.lean` |
| Claude (`lean4-effect4-02`) | the wire/byte slice (`docs/WIRE-DAG.md`, `Effect4/Protocol/*`); the environment slice (`docs/ENVIRONMENT-DAG.md`, `Effect4/Context/*`); the Schema payload lane, now closed |

## Current claims

Claim a file by adding a row. Release it by deleting the row. A file with no
row is unclaimed.

| File or tree | Claimed by | State |
| --- | --- | --- |
| `Effect4/Semantics/Fuel.lean`, `Effect4/Target/TypeScript/StructureLaws.lean`, `Effect4Test/Target/TypeScript/StructureLaws{Contract,AxiomReport}.lean` | Claude (trace-lane owed theorems, 2026-09-03) | proved and green in worktree `agent-a7d1f74bf61e7c52b`; uncommitted. Also touched: `Effect4.lean` (two imports), `Effect4Test.lean` (two imports), `Effect4Test/Flow/Runner{Contract,AxiomReport}.lean`, `Effect4Test/Audit/AxiomGate.lean` (two exact-declaration exemptions), `test/contracts/flow-runner.contract.md`, `test/contracts/flow-structured-lowering.contract.md`, `docs/TRACE-DAG.md` (`structured-agreement` row), `test/counterexamples/REGISTER.md` (`E4-TARGET-CE-013` row) |
| `Effect4/Data/Row.lean` | Codex | in progress |
| `test/contracts/data-row.contract.md`, `Effect4Test/Data/RowContract.lean` | Codex | frozen, red |
| `Effect4Test/Concurrency/**` | Codex | in progress, red |
| `Effect4Test/Environment/ContextKeyAssurance.lean`, `scripts/generate-environment-context-key-evidence.sh`, `generated/**` | Codex | in progress |
| `Effect4Test/Schema/PayloadSurface.lean` | Codex | in progress |
| `scripts/check-schema-payload-surface.sh`, `scripts/test-schema-payload-surface-gate.sh`, `test/fixtures/schema-payload-surface/**` | Codex | repairing public type-valued definition detector |
| `Effect4Test/Schema/StructuralAssurance.lean`, `scripts/*schema-structural-assurance*`, `generated/schema-structural-assurance.tsv`, `test/fixtures/schema-structural-assurance/**` | Codex | in progress |
| `PLAN.md`, `PORT-MANIFEST.md`, `docs/SCHEMA-CUTOVER.md`, `Effect4Test.lean` (Schema structural-assurance lines only) | Codex | in progress |
| `vendor/effect-4.0.0-rc.112/**` | Codex | adding exact Schema source pin for standalone gates |
| `.github/workflows/lean_action_ci.yml` (Schema assurance step only) | Codex | in progress |
| `Effect4/Schema/Representation.lean` (SC-REP-03 recursor only), `test/contracts/schema-recursor.contract.md`, `Effect4Test/Schema/RepresentationFoldContract.lean` | Codex | in progress |
| `test/counterexamples/REGISTER.md`, `test/counterexamples/schema/ATTACKS.md`, `Effect4Test/Counterexamples/Schema/RecursiveElimination.lean` (E4-SCHEMA-CE-043 only) | Codex | in progress |
| `workshop/SchemaFoldProbe.lean` | Codex | scratch proof design |
| `Effect4/Data/Optic.lean`, `Effect4/Schema/Annotations.lean`, `Effect4/Schema/Document.lean` (annotation traversal section only) | Codex breaker | annotation data-plane future production fence; no production edits during freeze |
| `test/contracts/schema-annotations.contract.md`, `Effect4Test/Data/OpticContract.lean`, `Effect4Test/Schema/AnnotationDataPlaneContract.lean` | Codex breaker | Schema annotation/optic packet in progress |
| `test/counterexamples/REGISTER.md`, `test/counterexamples/schema/ATTACKS.md`, `Effect4Test/Counterexamples/Schema/AnnotationDataPlane.lean` (`E4-SCHEMA-CE-044`..`048` only) | Codex breaker | annotation data-plane attacks in progress |
| `workshop/SchemaAnnotationOpticProbe.lean` | Codex breaker | optional scratch feasibility only |
| `test/contracts/schema-effectful-field.contract.md`, `Effect4Test/Schema/EffectfulFieldContract.lean`, `Effect4Test/Counterexamples/Schema/EffectfulField.lean` | Codex forward breaker | effectful-field packet freeze, red |
| `test/counterexamples/REGISTER.md`, `test/counterexamples/schema/ATTACKS.md` (`E4-SCHEMA-CE-049` onward only) | Codex forward breaker | effectful-field attacks, append-only |
| `Effect4/Schema/Authoring.lean`, `Effect4Test/Schema/AuthoringContract.lean`, `test/contracts/schema-authoring.contract.md` | Codex | Schema predicate/check authoring facade |
| `Effect4/Target/TypeScript/Schema.lean`, `Effect4Test/Target/TypeScript/SchemaGenerationContract.lean` | Codex | raw Schema/document/data generation facade |
| `Effect4/Target/TypeScript/Expr.lean`, `Effect4/Target/TypeScript/Render.lean`, `Effect4Test/Target/TypeScript/ExprContract.lean`, `test/contracts/typescript-target-expr.contract.md`, `docs/TYPESCRIPT-TARGET-DAG.md` | Codex | additive exact-binary64 and quoted-object target syntax for Schema generation |
| `Effect4.lean`, `Effect4Test.lean` | Codex | Schema authoring/generation import lines only |
| `workshop/Char/**` | Claude (`lean4-effect4-e5`), ten-agent bootstrap wave, 2026-09-04 | in progress; one agent per section, each writing only its own folder, plus `workshop/Char/ALGEBRA.md` and `workshop/Char/README.md` |
| `Effect4/Char/Core.lean` (additive only), `Effect4/Char/Queue/**` | Claude (`lean4-effect4-e5`), connect lane A, 2026-09-04 | in progress: `LocalBalanceLe`, `Guarded`/`Graded`, the Queue port from `workshop/Char/01-model`; every file left on disk must elaborate; `lakefile.toml` and `Effect4.lean` NOT touched |
| `Effect4/Char/Conformance.lean`, `Effect4/Char/Conformance/{GSet,Vector,VectorSet,Generators,Consume,Compose,Surface,Cell}.lean`, `workshop/Char/10-conformance/**` | Claude (`lean4-effect4-e5`), connect lane B, 2026-09-04 | landed 2026-09-04: the monotone conformance substrate, nine modules, oleans in the mirror tree; imports `Core` and lane C's `Evidence`, edits neither; eight items plus INDEX |
| `workshop/Char/10-pipeline/**`, `Effect4/Store/Pin.lean`, `Effect4/Char/Evidence.lean`, `Effect4/Char/Manifest.lean` | Claude (`lean4-effect4-e5`), connect lane C, 2026-09-04 | in progress: end-to-end pipeline and AI workflow design, plus the pin entity, evidence and rungs, and the flat manifest; every file left on disk must elaborate |
| `workshop/Char/REVIEW-01.md` | Claude (`lean4-effect4-e5`) | written 2026-09-04; the ruling queue for the room |
| `workshop/Picos/**` | Claude (`lean4-effect4-e5`), Picos spike, 2026-09-04 | in progress; six seats, one folder each; `workshop/OCaml5/**` is read-only to this spike and `Lib/Picos.lean` is NOT edited, only a re-derivation plan is written |
| `Effect4Test/Audit/AxiomGate.lean` | Codex | exact target-renderer `Classical.choice` boundary only |
| `test/counterexamples/REGISTER.md`, `test/counterexamples/target/ATTACKS.md`, `Effect4Test/Counterexamples/Target/TypeScriptRender.lean` | Codex | `E4-TARGET-CE-004` only |
| `Effect4/Context/Key.lean` | Claude | **closed, green, do not edit** |
| `Effect4/Context/Service.lean` + its packet | Claude | breaker in flight |
| `Effect4/Protocol/**` | Claude | annotated stubs, no declarations |
| `docs/WIRE-DAG.md`, `Effect4Test/Protocol/ByteParserContract.lean` | Claude | breaker in flight |
| `Effect4Test/Environment/AxiomReport.lean` | Claude (coordinator) | receipts only |
| `docs/CLASSIFICATION-DAG.md`, `Effect4/Classification/**` + its packet | Claude | DAG laid, C0 breaker in flight |
| `Effect4/Semantics/**` (all ten) | Claude | annotation only, no declarations |
| `Effect4/Semantics/Cause.lean`, `Effect4/Semantics/Exit.lean`, `test/contracts/cause-exit.contract.md`, `docs/CAUSE-DAG.md`, `Effect4Test/Semantics/CauseExitContract.lean`, `Effect4Test/Semantics/CauseExitAxiomReport.lean`, `Effect4Test/Counterexamples/Semantics/CauseExit.lean`, `test/counterexamples/semantics/ATTACKS.md`, `test/counterexamples/REGISTER.md` (`E4-SEM-CE-001`..`007` only), `Effect4Test.lean` (Cause/Exit import lines only), `test/fixtures/trust-gate/known-red.txt` (Cause/Exit entries only) | Claude | Cause/Exit packet implemented and green; coverage join in progress |
| `scripts/*effect-runtime-census*`, `generated/effect-runtime-census.tsv`, `Effect4Test/Audit/RuntimeCoverage.lean`, `vendor/effect-4.0.0-rc.112/src/{internal/**,Scheduler.ts,Scope.ts,Exit.ts,Cause.ts}`, `vendor/effect-4.0.0-rc.112/README.md`, `docs/effect-rc112-fiber-runtime.html` | Claude | Effect runtime coverage slice: behaviour census joined to Lean witnesses; additive, reads pinned bytes only |
| `Effect4/Semantics/Observation.lean`, `Effect4/Semantics/Runs.lean`, `Effect4/Semantics/Frontier.lean`, `Effect4/Flow/Decision.lean` | Claude (trace lane) | trace alphabet consumer, Flow runner and tape; plan `~/.claude/plans/misty-frolicking-naur.md` P-T1b, P-T2 |
| `Effect4/Semantics/Denotation.lean`, `test/contracts/flow-denotation.contract.md`, `Effect4Test/Semantics/DenotationContract.lean`, `Effect4Test/Semantics/DenotationAxiomReport.lean` | Claude (D1 denotation lane) | packet D1 of `docs/research/2026-09-03-reification-plan.md`: `Flow.denote`, `runTape = interpret ∘ denoteFuel`, fuel sufficiency; append-only lines in `Effect4.lean`, `Effect4Test.lean`, `docs/TRACE-DAG.md` (`semantics` row only) |
| `Effect4/Meta/Derive.lean`, `Effect4/Target/TypeScript/{EffectV4,Lower,Trace,Simulation}.lean`, `Effect4Test/Semantics/ObservationContract.lean`, `Effect4Test/Target/TypeScript/LoweringCoverage.lean`, `Effect4Test/Audit/AxiomGate.lean` (Derive and trace-renderer exemption entries only) | Claude (trace lane) | Effect v4 profile, rule ids, trace rendering, lowering; light ceremony by operator ruling D2 |
| `harness/trace/**`, `harness/effect-v4-family/**`, `generated/traces/**`, `generated/lowering-*.tsv`, `scripts/*trace*`, `scripts/*lowering*`, `docs/TRACE-DAG.md`, `docs/LOWERING-COVERAGE.md` | Claude (trace lane) | host tracer, goldens, coverage ledger and their gates |
| `test/counterexamples/REGISTER.md`, `test/counterexamples/{semantics,target,flow}/ATTACKS.md`, `Effect4Test/Counterexamples/{Semantics,Target}/Trace*.lean` (next free `E4-SEM-CE-`, `E4-TARGET-CE-`, `E4-FLOW-CE-` ids only, append-only) | Claude (trace lane) | trace and lowering attack rows |
| `Effect4.lean`, `Effect4Test.lean` (Semantics/Observation, Runs, Frontier, Flow/Decision, Target/Trace, LoweringCoverage import lines only) | Claude (trace lane) | root wiring for the packets above |
| `Effect4Test.lean` (RuntimeCoverage import line only), `Effect4Test/Audit/AxiomGate.lean` (RuntimeCoverage exemption entry only), `.github/workflows/lean_action_ci.yml` (runtime census step only) | Claude | Effect runtime coverage slice wiring |
| `docs/SCOPE-DAG.md`, `test/contracts/scope.contract.md`, `Effect4Test/Runtime/ScopeContract.lean`, `Effect4Test/Runtime/ScopeAxiomReport.lean`, `Effect4Test/Counterexamples/Runtime/Scope.lean`, `test/counterexamples/runtime/ATTACKS.md` | Claude | Scope runtime packet frozen, RED; breaker-owned, do not edit while implementing |
| `test/counterexamples/REGISTER.md` (`E4-RUN-CE-001`..`009` only), `Effect4Test.lean` (Scope import lines only), `test/fixtures/trust-gate/known-red.txt` (Scope entries only) | Claude | Scope runtime packet wiring, append-only |
| `generated/fiber-assurance.tsv` | Claude | regenerated in the Scope breaker commit because `test/counterexamples/REGISTER.md` is a pinned input; no other change |
| `Effect4/Runtime/Scope.lean` | Claude (builder) | **built, green**: the frozen surface is implemented and the battery, axiom report, and counterexample module all build. All 98 public theorems stay within `propext`/`Quot.sound`, and both Scope entries were removed from `test/fixtures/trust-gate/known-red.txt`. The packet and battery were not edited. The `SCOPE-L7` coverage join in `Effect4Test/Audit/RuntimeCoverage.lean` remains a separate, unclaimed packet |
| `Effect4/Runtime/Runtime.lean` | Claude (builder) | **built, green**: the frozen frame-machine surface is implemented and the battery, axiom report, and counterexample module all build. All 149 public theorems stay within `propext`/`Quot.sound`, and both `Effect4Test.Runtime.Frames*` entries were removed from `test/fixtures/trust-gate/known-red.txt`. The packet, battery, and axiom report were not edited. The `FRAME-L8` coverage join in `Effect4Test/Audit/RuntimeCoverage.lean` remains a separate, unclaimed packet |

## What collisions have already cost

Recorded because they are cheaper to read than to repeat.

1. **Two `DATA-ROW` packets.** Both agents froze a contract and battery on the
   same four paths with mutually exclusive designs — one over a local
   `RowOrder` mixin on `[LT α]`, one over `Std.IsLinearOrder`. Discovered only
   during mutation testing. One full packet was discarded. Codex's Std-based
   packet was kept because a local order class would duplicate Std's and
   `PORT-MANIFEST.md` "Canonical row extraction" forbids a second
   canonical-order notion.
2. **The kept packet did not elaborate at its own consumer.**
   `Std.IsLinearOrder` needs `LE`, and `#synth LE Effect4.ServiceKey` failed.
   Closed additively at the key: `LE`, `IsPreorder`, `IsPartialOrder`,
   `IsLinearOrder`, `LawfulOrderLT`, `DecidableLE`, all derived from the
   pre-existing `ServiceKey.Lt`, all axiom-free.
3. **`PayloadSurface.lean` appeared unrouted** and failed the module-closure
   gate; once routed it failed the axiom gate, because a `MetaM` metaprogram
   reaches `Classical.choice` and the exemption was hardcoded to one module.
4. **The exact-declaration census drifted three times in one afternoon**, once
   *expecting* a compiler-generated `lt_iff_le_not_le.match_1_1` companion that
   had been deliberately eliminated. It surfaced as `missing`, not
   `unexpected`.

Every one was caught by a gate, not by agreement. Assume that is the only thing
that will catch the next one.

## Operational facts worth not rediscovering

- **`test/fixtures/trust-gate/known-red.txt` is self-checking in BOTH
  directions.** An undeclared failing module fails `./scripts/test-trust-gate.sh`,
  and a declared module that has since gone green fails it too. Add your
  battery when it goes red; remove it the moment it goes green.
- **Lean stops a file at 100 errors** on this build path. An in-file
  `set_option maxErrors` does *not* lift it; `lake env lean -DmaxErrors=10000`
  does. A red battery measured without the flag may be 40% unelaborated.
- **Four axiom traps**, each with an axiom-free alternative, tabulated in
  `docs/ENVIRONMENT-DAG.md` under "Axiom traps builders keep hitting":
  `simp` on a positive `String` disequality pulls `Classical.choice` (use
  `decide`); `decreasing_by` pulls `Quot.sound` (use
  `termination_by structural`); `omega` on `Nat` chains pulls both (use
  explicit `Nat.lt_of_lt_of_le` / `Nat.lt_of_le_of_lt`); and Std's
  `IsLinearOrder.of_lt` / `LE.ofLT` factories prove through
  `open Classical in simpa`.
- **Build `Decidable` instances with `inferInstanceAs`** over the spelled-out
  proposition. A tactic-produced instance wrapped in `Eq.mpr` will not reduce
  in the kernel, so ground comparisons stop closing by `decide`.
- **`./scripts/check-internal-citations.sh` rejects line-numbered citations**
  into `docs/SCHEMA-CUTOVER.md`, `PLAN.md`, `AGENTS.md`,
  `docs/ARCHITECTURE.md`, `PORT-MANIFEST.md`, and `docs/AGENT-ROUTING.md`.
  Cite section headings, obligation IDs, or quoted phrases. Line citations into
  pinned host sources and `vendor/` are fine and are meant to stay.
- **Adding any declaration to `Effect4/Context/Key.lean` fires the exact
  module-surface census** in `Effect4Test/Environment/ContextKeyAssurance.lean`
  and desynchronises the hardcoded counts in
  `scripts/generate-environment-context-key-evidence.sh`. Both must move
  together, and `Effect4Test/Environment/AxiomReport.lean` must list receipts
  in the same order as `axiomReceipts`.

## Working rules that follow

1. **Re-read a file immediately before writing it.** The other agent may have
   changed it since you last looked.
2. **Never revert the other agent's lines.** If a change looks wrong, say so in
   this file rather than undoing it.
3. **Claim before freezing a packet.** Two frozen packets on one path is the
   most expensive failure available here.
4. **Prefer a gate to a convention.** The other agent has not read your
   conventions and cannot be told about them mid-flight. A guard that fails
   loudly is the only thing that transfers.
5. **Declare your red batteries.** A red module nobody declared blocks the
   trust gate for everyone, which means planted `unsafe` and `partial` stop
   being detected — that gate's detector runs last and never executes if an
   earlier module fails to build.

## Completed trust-gate repair, 2026-09-01

The six Cause/Exit existing-type rows are mirrored exactly from
`docs/CAUSE-DAG.md` into `PORT-MANIFEST.md`, and `PLAN.md` records the implemented
packet with its declaration-assurance and host obligations still open. The
Cause/Exit contract, counterexample file, and axiom report each passed a direct
`lake env lean` run; all 92 declared theorem receipts stayed within
`propext`/`Quot.sound`.

`scripts/test-trust-gate.sh` exited zero after the projection-tokenizer repair,
total replacement of the existing target-expression equality, removal of the
annotation counterexample's avoidable choice dependency, and the exact audit
and output-text admissions documented in `docs/TYPESCRIPT-TARGET-DAG.md`.
Its restored-tree audit checked 159 modules and 8,118 declarations. It rejected
planted `partial`, `unsafe`, and unadmitted `Classical.choice` declarations;
all tokenizer, exact-boundary, and finite expression-equality regressions
passed. Independent review found no remaining issues in these changes.

`scripts/check-schema-typescript-generation.sh` also exited zero: generated
bytes and the corpus digest matched, TypeScript 7.0.2 checked the output,
Effect rc.112 ran it, and language service 0.38.0 passed. The existing target
contract built, and both public equality receipts contain only `propext`.
`canonicalUnit_not_lawful` retains its statement and witness with a `propext`
receipt. Citation and diff checks passed.

The default `lake build` remains red for the already declared byte-parser and
race contracts, with the consequential root failure. The trust self-test
verified that exact declared set and removed those two modules only from its
temporary copy; compiled trust remains unverified for those two modules.
These repair-specific claims are released. Older lane claims above are not
released by this note.

## Completed fork/supervision continuation, 2026-09-02

The operator-authorized continuation from `f4f55fa` uses the single independent
breaker packet committed at `5568f00`. The implementation, assurance join, and
verification receipt are in the commit containing this note; see
`docs/SUPERVISION-IMPLEMENTATION.md`. All 294 frozen declaration checks, 136
public theorem obligations, and fifteen independent counterexamples pass.
The contract, battery, DAG, and proof-report bytes remain at the breaker
checkpoint. The only changed library module is
`Effect4/Concurrency/Supervision.lean`.

The Fiber join retains its original receipts and adds 705 compiler-owned
supervision declarations, 19 exact shapes, and three finite leaves. All 136
public theorem receipts stay inside `propext`/`Quot.sound`; no new trust
exemption is introduced. Six local graph edges are closed, while the source
bridge, target interpretation, and binding a fresh repository trust receipt
remain required-open. The host evidence is ten finite cases, not a general
source interpretation.

The narrow Lean checks, generated assurance gate, all ten assurance reaction
controls, pinned host gate, trust self-test, runtime census gate, citation
check, and diff check pass. The census name extractor was extended only to
recognize `?` in three frozen supervision theorem names; its exact comparison
is unchanged. The default `lake build` still fails only for the previously
declared byte-parser and binary race packets and their consequential root
closure check. The trust self-test verifies that exact red set and excludes
those two modules only in its probe copy.

The seven researched reification skills are committed separately at `d25cd82`,
including the original evaluation input hashes and an explicitly recorded
packaging-only newline cleanup. All seven packages validate and match their
installed copies. Existing README edits and `.claude/launch.json` are excluded;
no push or PC synchronization was requested for this continuation.

The six task-specific claims are released. Older broad lane claims above
remain with their existing owners.

## Open items either agent may take

- `Effect4/Protocol/Bytes.lean` — the byte carrier and JSON parser. Breaker in
  flight (Claude); builder unclaimed. See `docs/WIRE-DAG.md`, and note the
  numeric ruling there is the load-bearing decision for the whole slice.
- `Effect4/Context/Requirement.lean` — blocked on `Data/Row` landing.
- `Effect4/Classification/**` — CLAIMED by Claude; `docs/CLASSIFICATION-DAG.md`
  is laid and the C0 `Domain` breaker is in flight. C1 (`Transfer`,
  `Soundness`) is unclaimed once C0 closes.
- `Effect4/Semantics/**` — CLAIMED by Claude for annotation only. All ten
  modules declare nothing, which is why `docs/CLASSIFICATION-DAG.md` records
  that no classification obligation may be phrased over runs, steps,
  observations, or frontiers. Implementing any of them is unclaimed.
- `SC-ISSUE-01` has no owning module. `docs/SCHEMA-ISSUE-SURVEY.md` proposes
  one; the ruling has not been made.
- `SC-CAS-01`..`06` are assigned to no module.

## Frame-machine breaker claim, 2026-09-02

Claude claims, as breaker only: `docs/FRAMES-DAG.md`,
`test/contracts/frames.contract.md`, `Effect4Test/Runtime/FramesContract.lean`,
`Effect4Test/Runtime/FramesAxiomReport.lean`,
`Effect4Test/Counterexamples/Runtime/Frames.lean`, the `E4-RUN-CE-010` through
`E4-RUN-CE-021` rows of `test/counterexamples/REGISTER.md`, the frame-machine
section of `test/counterexamples/runtime/ATTACKS.md`, and the three new import
lines in `Effect4Test.lean`. The implementation fence is
`Effect4/Runtime/Runtime.lean`, whose stub docstring is updated and which
remains declaration-free; `Effect4/Runtime/Lifecycle.lean` is untouched.
The builder of that fence is claimed and closed below.

Two working-tree edits were deliberately left unstaged by the breaker for the
reviewer to commit after the concurrent fiber-assurance lane landed: the two
`Effect4Test.Runtime.Frames*` entries appended to
`test/fixtures/trust-gate/known-red.txt`, and this note. The builder commit
removes those two entries again, because the packet is now green. Appending to
`REGISTER.md` and `runtime/ATTACKS.md` changes an input digest pinned by
`generated/fiber-assurance.tsv`, which this packet does **not** regenerate
because the other lane owns `scripts/generate-fiber-assurance.sh`;
`./scripts/check-fiber-assurance.sh` reports a stale projection until that lane
lands and the generator is run once.

Operational facts worth not rediscovering, from this packet:

- A Lean structure instance whose fields are split across lines must have every
  field at the same column. `{ self with current := x,` followed by a
  differently indented `stack := y }` is a parse error reported as
  "unexpected identifier; expected '}'", not a layout preference. It bites
  hardest when transcribing pretty-printer output into a battery; setting
  `pp.structureInstances false` and `pp.fieldNotation.generalized false` before
  `#check` produces output that always re-parses.
- `set_option format.width` does not narrow `#check` message output; the
  messages are formatted at the default width, so a generated battery has to be
  re-wrapped by hand or by script.
- A pop loop over a continuation stack must recurse on the frame *list*, never
  on the fiber's `stack` field, because `contAll` can push and the stack
  therefore does not decrease.

| `docs/REIFICATION-STRATEGY.md`, `docs/ALGEBRA-PACKAGE-PLAN.md` | Claude (foldlab/streams coordinator) | added 2026-09-02, copied from lean4-WHATWG-streams ed65fe0 at the operator's request; RS-D1 proposes extracting `Effect4/Algebra` into a standalone package and is HELD until the operator's incoming Mac work lands; no other file claimed |
| `docs/EFFECTS-SPLIT-PLAN.md` | Claude (operator session) | proposed 2026-09-02: the Effect4-side plan for RS-D1, naming the standalone package `Effects` and slicing the split S0–S6; rulings EP-1..EP-12 settled 2026-09-02; slices S1–S3 landed in `mepuka/lean4-effects` (tag `v0.1.0` = `5611c3a`); **S4 cutover executed here 2026-09-02 with the operator's confirmation that the tree was quiet**: `Effect4/Algebra/**` and `Effect4Test/Algebra/**` deleted, `[[require]] effects` pinned by exact commit, `Effect4/Schema/EffectfulField.lean` and the two Schema EffectfulField test files repointed (`open Effects`), algebra contracts and register rows marked MOVED, `PORT-MANIFEST.md`/`PLAN.md`/`docs/ARCHITECTURE.md`/`docs/DESIGN-BASIS.md`/`AGENTS.md`/`README.md` updated, `scripts/test-trust-gate.sh` copies `.lake/packages` into its probe, fiber and context-key projections regenerated (register and manifest are pinned inputs). Claims on those files are released with the commit |

## Effects split, S4 cutover landed, 2026-09-02

The generic effect algebra now lives in `mepuka/lean4-effects` (`Effects`
namespace, tag `v0.1.0`), pinned by exact commit in `lakefile.toml`; see
`docs/EFFECTS-SPLIT-PLAN.md` for the slices and receipts. Two gates were
already failing at `217d3e4` before the cutover and were left as found:
`check-schema-structural-assurance.sh` (its generator pins a hash of
`Effect4Test/Counterexamples/Schema/AnnotationDataPlane.lean` that predates
commit `a100daf`) and `check-data-row-assurance.sh` (its declaration census
misses the `Lens`/`Optional`/`Traversal` `Lawful` declarations). Neither
touches the algebra; their owners repair them. The committed
`generated/environment-context-key-assurance.tsv` was also stale at HEAD and is
now fresh.

## Completed internal algebra package literature review, 2026-09-02

Codex recorded the operator's internal review in
`docs/research/2026-09-02-algebra-package-review.md`, with source identities and
fresh narrow algebra receipts in `2026-09-02-algebra-package-sources.json` in
the same directory. Six local papers and the pinned PolyFun source informed
the first pass. Both algebra batteries and all 60 named axiom receipts pass;
local links, source hashes, the citation gate, and diff checks pass. This is
research, not extraction or cutover. The two copied plans and their hold are
unchanged. The two review-file claims are released.

## Shared semantics research claim, 2026-09-02

Codex claims `docs/research/2026-09-02-shared-semantics/` and
`output/pdf/effect4-web-standards-semantics.pdf` for the operator-requested
research on the ten supplied questions. The fence contains research evidence
and a report only. Existing library code, contracts, generated assurance,
package pins, and design rulings remain outside the fence. Source review in
Effects, WHATWG, TypeScript, and Foldlab is read-only. This claim is released
by the completion note after source, measurement, and document verification.

## Shared semantics research completed, 2026-09-02

Codex completed the ten-question study in
`docs/research/2026-09-02-shared-semantics/` and the 15-page report at
`output/pdf/effect4-web-standards-semantics.pdf`. The evidence includes 30
primary-source URLs, 46 local source hashes, an import-aware scan of 24,401
files from 30 pinned repositories, finite row measurements, nine exploratory
Lean witnesses and six host cases. Narrow frame/scope checks passed; all 149
frame axiom receipts stayed within `propext` and `Quot.sound`. The local
dependency-manifest warning remains part of the verification boundary.
All PDF pages passed text/link/margin checks; seven pages received visual
inspection. The internal-citation gate and diff check passed. This closes the
research delivery, not any proposed semantic proof or cutover route. The file
claims above are released.

## Web standards source downloads completed, 2026-09-02

Codex downloaded the 21 papers and Web IDL reference named on the operator's
attached reading map into `docs/research/2026-09-02-web-standards-sources/`.
The index records the retrieved editions and links to originals and searchable
text copies. `verify.py` passed for all 22 sources, including extraction of all
568 PDF pages, title checks, independent PDF page-count checks, the Web IDL
exceptions anchor, and recorded file sizes and hashes. All 48 local index links
resolve; `shasum -a 256 -c SHA256SUMS` passed for the downloaded sources and
saved attachment. The manifest retains retrieval provenance and the verification
record retains upstream PDF parser warnings. No requested source is missing.
The download-folder claim is released.

## Trace lane opened, 2026-09-02

Claude opened the trace-driven lowering lane per the operator-approved plan
(`~/.claude/plans/misty-frolicking-naur.md`, rulings R1–R9, decisions D1–D3).
P-T0 landed: `Effect4.Meta.Derive` admitted as an exact target-implementation
module in the axiom gate; lean4-effects v0.2.0 and lean4-typescript v0.1.1 are on
GitHub under pure-algebra and both manifests resolve them; the path overrides are
retired; the trace probe moved to `harness/trace/tracer.ts`. Ceremony is light
(builder writes contract, battery and code together) for every packet except the
Flow v2 re-freeze in lean4-effects, which keeps the separate breaker process.

## Flow v2 landed, 2026-09-02

lean4-effects v0.4.0 (`e86f141`, tagged and pushed) is the Flow v2 re-freeze:
block parameter lists, `Var` operands, argument lists on `jump`/`choose`/
`perform`, `CyclesWF` with the kernel-computable `cyclesChoose`, and seventeen
ordered admission clauses (`test/contracts/flow-v2.contract.md` there). The
retained admission theorems survive unchanged; the axiom union stays `propext`
and `Quot.sound`. Effect4 and whatwg pin `e86f141`. In Effect4 the v1 batteries
`Effect4Test/Flow/{AdmissionContract,DiagnosticPrecisionContract,AxiomReport,PrivacyContract}.lean`
and `scripts/test-flow-admission-mutations.sh` are retired (their witnesses live
in the v2 batteries), the v1 contracts carry a superseded header, and the
`E4-FLOW-CE-*` register rows point at the v2 witnesses (`E4-FLOW-CE-005` is
superseded by `EF-FLOW-CE-002`: an unchosen cycle is now rejected). Next in the
lane: the Flow runner and decision tape (P-T2), then dispatch lowering (P-T9a).

## P-T2 landed: the Flow runner and the decision tape, 2026-09-02

`Effect4/Semantics/Runs.lean`, `Effect4/Semantics/Frontier.lean`, and
`Effect4/Flow/Decision.lean` are no longer stubs: a positional-environment runner
over Flow v2 (`plan` / `step` / `loop`, `fuelFor raw tape = (tape.length + 1) *
blocks.length + 1`), a tape consumed by occurrence with a site check (mismatch =
refusal, exhaustion = unanswered frontier, R6), and DB-04 frontiers. Laws:
`run_checked_not_stuck`, `run_fuel_mono`, `step_choose_consumes_one`,
`plan_checked` (union `propext`, `Quot.sound`). `Effect4/Target/TypeScript/ScriptFlow.lean`
embeds a straight-line `Script` into an admitted flow over a table alphabet
(`tableAlphabet`, `Script.toFlow`); `harness/trace/Generate.lean oracle` checks that
the runner and the traced service agree under `m2` on every program with a flow
golden (`generated/traces/flow/`), and `scripts/check-trace-goldens.sh` runs it.
Packet: `test/contracts/flow-runner.contract.md`; rows `E4-FLOW-CE-017` (fuel
exhaustion is not a failure) and `E4-FLOW-CE-018` (a foreign tape entry is a
refusal). Next: P-T9a dispatch-form lowering from a checked flow.

## Reviews of `~/Dev/effect4_of_ocaml` (Codex's Rocq and js_of_ocaml lane), 2026-09-02

Three Opus reviews, operator-requested, under
`docs/research/2026-09-02-effect4-of-ocaml-review/` (`rocq-review.md`,
`jsoo-review.md`, `integration-review.md`). Nothing in Codex's workspace was
edited. Findings that need action:

- Codex: re-pin `lean/` to lean4-effects v0.4.0 and rewrite the flow export for
  Flow v2 (four of the seven exported graphs are now refused by `unchosenCycle`,
  which invalidates `evidence/lean-flow-export.json` and half of the simulation
  corpus); commit the workspace (it has no commits; `_build/` holds the only copy
  of the pinned js_of_ocaml 5.7.1); add the golden header (`face ocaml`) to the
  rows already emitted so `effect4-trace` can check the OCaml 5 machine as a
  third emitter; state the certificate checker's missing completeness theorem
  (the `expected:false` rows are search failures, not refutations) and rename the
  result bisimulation; note that the 875-case oracle is a same-author shallow
  embedding under `Effect.runSync`, and that its Cell adapter never emits rows
  that separate `m1` from `m2`.
- Claude: seed `E4-TARGET-CE-` rows from `evidence/wire-boundary.json` (rendered
  rows equal while `agree m2` is false for `Val.nat`/`Val.int`; `Trace.escape`
  emits a raw U+0001 that `JSON.parse` rejects; `Val.nat` above 2^53 loses
  precision on the host); teach the host gate a third face; port
  `enough_fuel_finishes` (a theorem that `fuelFor` suffices, today a docstring
  argument in `Runs.lean`) and the `resume_frontier` law; keep Codex's evidence
  out of `generated/lowering-coverage.tsv` (R8) until a Flow-shaped corpus can
  feed the `property` column.
- Worth reusing: the callback packet's zero-patch instrumentation of the real
  rc.112 fiber pins exactly the P-T11 hunks; js_of_ocaml 5.7.1 in `_build/` is
  not the master the plan re-derives for P-T9b (no `Dispatch` edge kind, no
  `merge_node_max`, no double translation).

## P-T9a landed: dispatch-form lowering, 2026-09-02

`Effect4/Target/TypeScript/FlowLower.lean` lowers an admitted Flow v2 graph to
`while (true) { switch (block) { … } }` (ruling R7): block parameters as
`b<i>p<j>` variables, `perform` answering into `a<i>`, `choose` deciding into
`c<i>` from the `Decisions` service, and a sequentialized parallel move with
temporaries on self-edges (row `E4-TARGET-CE-011`, witnessed by the `swap`
flow). Eight rules join the census (`Lower.lean`, sixteen in all); the
harness gains `flow-fixture.ts` (generated, drift-checked), `flow-tail.ts`,
goldens `generated/traces/flow/<program>.<tape>.tsv` for `incr`, `twice`,
`chooser` and `swap`, host receipts under `receipts/flow/`, and type receipts
under `types/flow/`; every flow golden agrees on the host under every mask at
both yield settings, and `generated/lowering-coverage.tsv` has all sixteen
rules `checked`. Packet: `test/contracts/flow-dispatch-lowering.contract.md`.
Next: P-T6, the property loop (generated flows, tapes, shrinking, mutants).

## P-T6 landed: the property loop, 2026-09-02

`harness/trace/Property.lean` generates flows by construction over the Cell
type graph (admission is the free oracle), builds tapes by policy through the
runner (`left`, `right`, `alternate`, `random`, `only<site>`, `visit<site>`), checks per-site
branch coverage, lowers the corpus into one dispatch-form module and runs it
once on the host through `effect4-batch` (effect4-tools `ffd3456`); a tape
exhausted on the host is the unanswered frontier (`tracer.ts`). Seed 2026:
200 flows, 1277 runs, 276 frontiers, 318 sites, no divergence; three planted
lowering mutants are caught (`scripts/test-lowering-mutations.sh`); a
divergence would be shrunk (budget 64) and stored under
`generated/lowering-property-failures/`. The eight dispatch-form rules are
`covered`. Packet: `test/contracts/lowering-property.contract.md`. Next: P-T7
regions (Effects v0.5.0), then P-T9b the structured form.

## Schema consumer survey delivered, 2026-09-02

Claude (Fable) delivered `docs/research/2026-09-02-schema-consumer-survey.md`:
a read-only survey of every Effect rc.112 module that consumes Schema (core,
SQL/Model, HttpApi/RPC/Cluster/Workflow/EventLog, AI/encoding/persistence/CLI),
the Schema lane's status against that map, the framing of boundary surfaces
(`ApiSurface`, `TableSurface`, `AgentSurface`, `CodecSurface`, lawful data
constructs) as instances of the trace-lane pipeline, a ranked opportunity
list, the missing pieces for proof-carrying npm publication, repository
cleanup items, and upstream findings. Research evidence only: no library
code, contract, generated assurance, pin, or ruling changed. No file claim
is held.

## Schema-lane cleanup sweep claim, 2026-09-02

Claude (Fable, survey session) claims, for a cleanup sweep executed in
isolated worktrees and integrated only into files outside the live
regions/trace diff:

| File or tree | State |
| --- | --- |
| `Effect4/Data/Optic.lean` (additive corollaries only, public statements unchanged), `Effect4/Schema/Annotations.lean` (use of a new lemma only) | proofs, in progress |
| `harness/schema-generation/**`, `harness/schema-effectful-field/**`, `scripts/check-schema-typescript-generation.sh`, `scripts/check-schema-effectful-field.sh` (new), `scripts/test-schema-typescript-generation-gate.sh` (new), `scripts/generate-schema-structural-assurance.sh` (add generator input only) | gates, in progress |
| `PORT-MANIFEST.md`, `docs/SCHEMA-CUTOVER.md` (status header only), `docs/SCHEMA-SURFACE-SURVEY.md` (§4 counts), `harness/README.md` | docs drift, in progress |
| `docs/research/2026-09-02-standards-targets-survey.md` (new) | research, in progress |

The Codex rows above naming `Effect4/Data/Optic.lean`, `PORT-MANIFEST.md`,
`docs/SCHEMA-CUTOVER.md`, and the structural-assurance scripts date from the
payload freeze; the assurance join records those edges closed, so this sweep
treats them as released and says so here rather than silently. Nothing in
`git diff --name-only` at claim time (regions and trace lane, lakefile pins,
`Effect4.lean`, `Effect4Test.lean`, `Effect4Test/Audit/AxiomGate.lean`,
`Effect4Test/Target/TypeScript/LoweringCoverage.lean`) is touched.
`generated/schema-structural-assurance.tsv` is regenerated only when no
other `lake` process is running in this tree.

## P-T7 landed: regions, 2026-09-02

lean4-effects v0.5.0 (`c28833b`) adds `Effects/Flow/Region.lean`: a region
layer erasing to Flow v2 (`enter`, `acquire`, `leave`, region rows, fourteen
region clauses, `admitRegions`, `CheckedRegionFlow`); the v2 surface is
untouched. lean4-typescript v0.3.0 (`1f39598`) adds `Expr.lambda`,
`Expr.method`, `Stmt.scopedGen`. In Effect4: the region runner
(`Effect4/Flow/Region.lean`: frames, `closeFrame` latest-first with the closing
exit, `unwind`, `RunResult.failed`), the region lowering
(`Effect4/Target/TypeScript/RegionLower.lean`: `Effect.scoped(Effect.onExit(...))`
with `Effect.acquireRelease` inside, rules `region-enter`/`region-acquire`/
`region-leave`, nineteen rules in all), the `RCell` family with failing
operations, three region goldens that agree on rc.112 under every mask at both
yield settings (`regionNested`, `regionTwoFail`, `regionBothSucceed`), receipts
and ledgers. Facts pinned: releases run latest-first with the closing exit;
a body failure is the run's failure; a fallible release has no lowering
(`Effect.acquireRelease` types it `never`). Rows `E4-FLOW-CE-019`, `-020`,
`E4-TARGET-CE-012`. Codex: `Effect4/Target/TypeScript/Schema.lean`'s
`exprKeysUnique` gained the two v0.3.0 arms (`lambda`, `method`) with the pin
bump. Next: P-T9b, the structured form.

## P-T9b landed: the structured form, 2026-09-02

lean4-typescript v0.4.1 (`cc62799`) adds `TypeScript/Structure.lean`: reverse
postorder, Cooper–Harvey–Kennedy dominators, reducibility, and emission over
the dominator tree with caller-supplied shapes (re-derived; js_of_ocaml is
reference only, and the local 5.7.1 checkout Codex holds lacks master's
`Dispatch` edge kind, so nothing was copied). In Effect4,
`Effect4/Target/TypeScript/StructuredLower.lean` lowers a reducible flow to
labelled blocks, `while (true)` loops, `break` and `continue` (rules
`structured-loop`, `structured-merge`, `structured-continue`,
`structured-break`), keeps the dispatch form otherwise (`dispatch-fallback`,
witnessed by the new `irreducible` program), and does the same inside
regions. `FlowLower.lowerBlockWith` makes the block body parametric in its
transfer; the dispatch output is unchanged byte for byte. The structured
module runs against every flow golden and the whole property corpus (1277
cases agree both ways; a fourth mutant, `continue` to `break`, is caught).
The corpus found one structuring defect before any golden did (an entry that
is its own loop header; `E4-TARGET-CE-013`, fixed in v0.4.1). Twenty-four
rules in the ledger. Owed: the Lean theorem that both forms agree on every
flow (`docs/TRACE-DAG.md`, `structured-agreement`). Packet:
`test/contracts/flow-structured-lowering.contract.md`. Next: P-T11, the
patched rc.112 copy, and the owed theorems (`fuelFor` suffices, structured
agreement).

## P-T11 landed: the patched rc.112 copy, 2026-09-02

`harness/trace/patched/` holds a seven-hunk observation-only manifest and
`apply.mjs`, which builds a patched copy of the pinned `effect` package under
an ignored `_copy/` selected only through `EFFECT4_EFFECT_NODE_MODULES`; every
tail reports the frame rows and `effect4-trace` records them with the
manifest digest. `scripts/check-trace-patched.sh` requires every flow golden
to agree under every mask on the patched copy and pins three scope facts:
two releases latest-first through the loop, a single release inline (rc.112
never enters `scopeCloseFinalizers` for one finalizer: `E4-TARGET-CE-014`),
nested single releases inline inner-first. `Effect4/Target/TypeScript/Simulation.lean`
defines the projections from `FrameEvent` and the scheduler `Event` into the
service-level alphabet (finalizers and outcomes only); the `bridges` edges of
both DAGs stay open with a statement now available. Packet:
`test/contracts/trace-patched-host.contract.md`. The plan's packets are all
landed; the owed theorems (`fuelFor` suffices, structured agreement) are with
a proof agent on a worktree branch.

## Live-stack integration claim, 2026-09-03

Codex resumes the operator-requested OCaml/Rocq bootstrap integration after
committing the research workspace at `d8d32e2`. This packet is additive: the
existing `Runtime.lean`, its frozen frame packet, the trace lane, and all
dependency pins remain unchanged. The independent breaker freezes on
`codex/live-stack-integration` before implementation; verified packet files
will be applied to this checkout without switching its branch.

| File or section | Owner and fence |
| --- | --- |
| `test/contracts/live-stack.contract.md`, `Effect4Test/Runtime/LiveStackContract.lean`, `Effect4Test/Runtime/LiveStackAxiomReport.lean`, `Effect4Test/Counterexamples/Runtime/LiveStack.lean`, `docs/LIVE-STACK-DAG.md` | Codex independent live-stack breaker; new files only |
| `Effect4/Runtime/LiveStack.lean`, `harness/live-stack/**`, `scripts/check-live-stack.mjs`, `scripts/test-live-stack-mutations.mjs`, `docs/LIVE-STACK-IMPLEMENTATION.md` | Codex live-stack builder; no second primitive, cause, exit, or fiber carrier |
| `Effect4.lean`, `Effect4Test.lean` (new LiveStack imports only), `test/fixtures/trust-gate/known-red.txt` (new LiveStack entries only) | Codex live-stack packet wiring |
| `test/counterexamples/REGISTER.md` (`E4-RUN-CE-022` through `024` only) | Codex independent live-stack breaker; additive runtime rows |

The first package theorem must preserve the full `FramePop` for every existing
primitive and both values of the interruption-skipping flag, not just the
research probe's `skipInterrupted=false` case. Public callback regression
evidence retains the same-final-result, different-interruption-prefix witness.
Adding `AsyncFinalizer`, switching the default runtime, and claiming an
executing scheduler/finalizer simulation remain separate open obligations.
## Census re-pin: `ref.*`, `deferred.*`, `layer.*` rows, 2026-09-03

Claim (this packet, worktree `agent-a1a5c700de4dd016c`, branch
`worktree-agent-a1a5c700de4dd016c`): `scripts/generate-effect-runtime-census.sh`,
`generated/effect-runtime-census.tsv`, `Effect4Test/Audit/RuntimeCoverage.lean`
(rows appended only), `docs/RUNTIME-COVERAGE.md`, `PORT-MANIFEST.md`
(disposition rows only), plus five new files under
`vendor/effect-4.0.0-rc.112/src/` and the vendor `README.md` table that pins
them. No existing census row, witness, disposition or coverage state changed:
`diff` of the old and new projections shows one changed line, the generator's
own digest. Nothing under `Effect4/` was touched.

The census had no rows for the mutable cell, the completion store, or Layer,
so the P-M6 host structures could not be witnessed at all. The pin now also
vendors `Ref.ts`, `MutableRef.ts`, `Deferred.ts`, `Layer.ts` and
`internal/layer.ts`, and the generator emits 38 more behaviour rows. Census
total 99 → 137; denominator 79 → 117; states after the packet: green 49,
partial 25, absent 43 (was 5).

**`ref` (10 rows).** Cell allocation identity (`ref.make`), the synchronous
read (`ref.get`), the void-typed write whose host value is the cell itself
(`ref.set-void-returns-cell`, with `ref.cell-set-returns-self` pinning
`MutableRef.set` returning `self` — the source side of `E4-SEM-CE-009`), and
the read-modify-write projections that a model must keep apart:
`ref.get-and-set`, `ref.set-and-get-assignment` (succeeds with the assignment
expression, not a second read), `ref.update`, `ref.modify`,
`ref.modify-some-no-reread`, `ref.update-some-and-get-reread` (re-reads after
the write, unlike `getAndUpdateSome`).

**`deferred` (12 rows).** Allocation (`deferred.make`), done-ness as the
presence of a stored effect (`deferred.is-done`), the waiter protocol with its
cleanup (`deferred.await`), first-completion-wins
(`deferred.single-completion`), clear-then-resume in registration order
(`deferred.completion-order`), what is stored by `completeWith`/`done`/
`complete` and whether the result is shared
(`deferred.complete-with-stores-effect`, `deferred.done-is-complete-with`,
`deferred.complete-runs-once`, `deferred.into-uninterruptible`), interruption
as an ordinary stored failure carrying the completing fiber's id
(`deferred.interrupt`, `deferred.interrupt-with`), and `deferred.poll`.

**`layer` (16 rows).** Layer as a build function over a memo map and a scope
(`layer.from-build-unsafe`, `layer.from-build-child-scope`,
`layer.build-with-memo-map-service`); memoization
(`layer.memo-build-once`, `layer.memo-reuse-observer-count`,
`layer.memo-finalizer-last-observer`, `layer.memo-map-parent-lookup`,
`layer.memo-get-or-else`, `layer.current-memo-map-fork-or-create`,
`layer.fresh-drops-memoization`); where the scope and the memo map come from
(`layer.build-uses-ambient-scope`, `layer.build-with-scope-still-forks-memo`);
composition (`layer.merge-parallel-scopes`, `layer.provide-dependency-first`);
and the layer scope versus the program scope (`layer.provide-effect-scope`,
`layer.launch-holds-scope`).

**What existing Lean already speaks to these rows: nothing directly.**
`Effect4/Stateful/Ref.lean`, `Effect4/Stateful/Deferred.lean` and every
`Effect4/Layer/*.lean` are eight-line breadth stubs with no declaration, as are
`Effect4/Runtime/{Lifecycle,ManagedRuntime,Resource}.lean`. All 38 rows are
therefore `absent` with no witness, and none is `owned` (an `owned` row must
carry a witness). Dispositions: `derivedExpansion` for the five rows the pinned
source itself defines in terms of another pinned operation
(`ref.modify-some-no-reread`, `deferred.done-is-complete-with`,
`deferred.complete-runs-once`, `deferred.interrupt`,
`deferred.interrupt-with`); `separateCalculus` for the other 33, matching the
`PORT-MANIFEST.md` family default for Layer and keeping the cell store and the
completion store as calculi with their own identity.

Adjacent Lean that a future witness will have to reuse rather than duplicate:
`Effect4/Runtime/Scope.lean` already models scope state, LIFO close, fork
linkage and `closeState_finalizers`, which is what every `layer.*` scope clause
is stated over (`Scope.forkUnsafe`, `Scope.close`, `scopeAddFinalizerExit`);
`Effect4/Semantics/Exit.lean` and `Cause.lean` own the `Exit` and interrupt
cause that `deferred.interrupt-with` and `layer.memo-finalizer-last-observer`
carry; `Effect4/Prim`'s `Sync` op is the frame under which every `ref.*` and
several `deferred.*` behaviours execute. None of these states a `ref`,
`deferred` or `layer` fact, so no row was promoted above `absent`.

Also corrected in `docs/RUNTIME-COVERAGE.md`: the "path to full coverage" table
said "the seven `partial` rows | 7"; the emitted count was already 25 before
this packet.

Gate at this commit: `./scripts/check-effect-runtime-census.sh` →
`PASS ... 137 mechanism rows`; `PASS census ids, kinds, statement snapshots and
witness receipts join the Lean row list`; `PASS coverage: denominator 117;
owned-with-green 3; green 49, partial 25, absent 43`.

## D1 landed: the algebraic denotation of a checked flow, 2026-09-03

`Effect4/Semantics/Denotation.lean` (packet D1 of
`docs/research/2026-09-03-reification-plan.md`). A `CheckedFlow` denotes a
`Program (Flow.Sig a ⊕ₛ Flow.DecSig)`: the alphabet through
`Alphabet.toFamily` at the constant denotation `Val`, plus a decision summand
`⟨DecisionId × Bool, fun _ => Unit⟩` announcing the branch the tape already
fixed. `denoteFuel` is structural on fuel and mirrors `plan`/`loop` case for
case; `denote` is fuel-free by well-founded recursion on
`(tape.length, (raw.reachSet block).length)`, with the new measure lemma
`reachSet_length_lt_of_edge` (`CyclesWF` is the only thing admission buys it).

Theorems (all within `propext`, `Quot.sound`; receipts in
`Effect4Test/Semantics/DenotationAxiomReport.lean`):

- T1 `loop_eq_interpretRun` / `runTape_eq_interpretRun` — the runner at every
  fuel is `interpret` under
  `(tracedFlowService service nameOf).toHandler.sum decisionHandler`, closed by
  `outcomeRows`. `Family.Service.traced` logs unconditionally, so the guarded
  service carries the runner's `FlowService.pure` policy; `done` and `frontier`
  have no former in the algebra at all and are a function of the `RunResult`,
  not operations of any summand. That is the one honest gap between the letter
  of "runner = interpret ∘ denote" and what is provable.
- T2 `denoteFuel_eq_denoteGo` / `denoteFuel_eq_denote` — derived from the
  `LoopBudget` invariant of `Effect4/Semantics/Fuel.lean` (Codex's
  `run_fuelFor_finishes` lane), not from a second pigeonhole argument. The new
  helpers `segmentBudget` and `decisionBudget` factor the two budget steps.
  `runDefault_no_fuel_frontier` is this packet's name for `runDefault_finishes`.
- `interpret_log_append` / `interpret_log_of_nil` — the log is a writer, under
  the side condition `WritesLog` discharged for `traceHandler`.

Fence used: new `Effect4/Semantics/Denotation.lean`,
`Effect4Test/Semantics/DenotationContract.lean`,
`Effect4Test/Semantics/DenotationAxiomReport.lean`,
`test/contracts/flow-denotation.contract.md`; append-only lines in
`Effect4.lean` and `Effect4Test.lean`; the `semantics` row (plus the status
paragraph and the diagram tail) of `docs/TRACE-DAG.md`. `Runs.lean` and
`Fuel.lean` were read, never edited: the guarded traced service lives in the new
module, not in `Runs.lean` as the plan sketched.

Two declarations carry `-- upstream: lean4-effects`:
`Effects.FlowAlphabet.toAlphabet` and `reachableNoChoose_trans` /
`reachSet_length_lt_of_edge`. `length_le_of_nodup_subset` is reproved privately
for a third time (it is private in `Effects/Flow/Raw.lean` and private again in
`Effect4/Semantics/Fuel.lean`); making it public upstream would retire all three
copies.

Next in this lane: D2 (regions as a scope summand) needs a third summand and a
stateful upper handler through `Handler.mapHom`/`MonadHom.stateT`; D5 (the
`Script` embedding) needs `interpret_vis_of_pure`.

## D4 fence A landed: the uninterrupted fragment and fuel additivity, 2026-09-03

Claim (Claude, frame-simulation lane, worktree `agent-aa0ab582898ec636e`,
branch `codex/effect4-cutover`): `Effect4/Runtime/Runtime.lean`
(**additions only**, appended after `step_scopedFrame`);
`Effect4/Semantics/FrameSimulation.lean` (new);
`Effect4Test/Semantics/FrameSimulationContract.lean`,
`Effect4Test/Semantics/FrameSimulationAxiomReport.lean` (new);
`Effect4Test/Runtime/FramesContract.lean` and
`Effect4Test/Runtime/FramesAxiomReport.lean` (**section F10 only**, appended);
`test/contracts/frame-simulation.contract.md` (new); `docs/FRAMES-DAG.md`,
`docs/TRACE-DAG.md`, `Effect4.lean`, `Effect4Test.lean` (appended lines only).
Packet: `docs/research/2026-09-03-frame-simulation.md`, packet D4 of
`docs/research/2026-09-03-reification-plan.md`.

Fence A adds twelve public theorems to `Effect4/Runtime/Runtime.lean` and edits
nothing that was already there. `step_preserves_uninterrupted` says
`interruptedCause = none` with `deferredInterrupt = false` is a `step`
invariant; `popFrom_never_skips` and `getCont_never_defers` are its two
consequences (no handler is skipped, the deferred interrupt is never answered),
so `FRAME-FB-NONNULL` is *vacuous on the fragment reachable from
`FrameFiber.start`* and is **not** retired — see the new closing section of
`docs/FRAMES-DAG.md`. `run_add`, `run_add_finished`, `run_add_running` and
`run_mono` are the fuel composition and monotonicity laws the bounded runner
lacked; DB-04's live-frontier ruling forbids the `forall fuel` form, so every
downstream statement is `forall fuel >= bound` and needs them. All twelve are
within `propext` / `Quot.sound`.

Anyone touching `Effect4/Runtime/Runtime.lean`: the additions are at the end of
the file inside a re-opened `namespace FrameFiber`. Nothing above line 2212 of
the pre-D4 file was changed.

## D4 fence B landed: the simulation theorem, 2026-09-03

New module `Effect4/Semantics/FrameSimulation.lean` with battery
`Effect4Test/Semantics/FrameSimulationContract.lean`, axiom report
`Effect4Test/Semantics/FrameSimulationAxiomReport.lean`, and light contract
`test/contracts/frame-simulation.contract.md`. Root import lines appended to
`Effect4.lean` and `Effect4Test.lean`; `docs/FRAMES-DAG.md` and
`docs/TRACE-DAG.md` updated. Nothing frozen was edited.

`compile_simulates`: for `bound tape <= fuel` and `answersOf H p s0 = tape`, the
frame machine started on `compile 0 p` with the table `tapeInterp p tape`
finishes with `exitOf ((interpret H p).run.run s0).1`, with `H` into
`ExceptT (Cause Val Unit Unit Unit) (StateT St Id)`. The workhorse is
`run_in_context`. `compile_simulates_fail` is the `Cause.fail` corollary.

**Read the scope line before quoting it.** The answers are *supplied*: the tape
is the oracle, `PrimInterp` is pure and total, and what is proved is that the
machine's control flow and exit equal the algebra's given agreeing answers. It
is a simulation modulo an effect oracle, not "the machine computes `interpret`".

`docs/TRACE-DAG.md` `semantics` moves to `required-closed` **for the Lean pair
only**, with an explicit scope line; the host agreeing with either emitter is
still executable evidence under a mask. `bridges` stays `required-open` and
cannot close by theorem. **No census row turns green**: coverage is scored
clause by clause and a composite theorem is nobody's clause. Nothing under
`generated/` or `Effect4Test/Audit/` was touched; adding the composed-run
evidence to `rule.frames-are-primitives` is a separate packet with a separate
claim.

Two open items for the merge, both flagged in the contract:

1. **Module placement.** `Effect4/Semantics/FrameSimulation.lean` imports
   `Effect4/Runtime/Runtime.lean`, and `docs/ARCHITECTURE.md` places Runtime
   above Semantics (FRAMES-DAG separation 2). No other `Effect4/Semantics/`
   module imports it, so no existing edge is reversed and there is no Lean import
   cycle; but if strict directory layering is preferred the module moves to
   `Effect4/Runtime/FrameSimulation.lean` unchanged.
2. **`Flow.Sig`.** Declared locally as `Effect4.FrameSimulation.Flow.Sig` and
   marked `-- to be unified with Denotation.lean`. A sibling packet declares the
   same signature; the coordinator merges them.

The finalizer half is **not** started. Its statement is a comment at the end of
the module, and it is blocked on a ruling, not merely unscheduled: the machine
merges a failing finalizer into a failing body with `Cause.combine`, while
`Effect4.Flow.Region.closeFrame` keeps only the first release failure (pinned by
`E4-FLOW-CE-019`), and TRACE-DAG separation 3 makes the fail payload exactly what
a mask cannot erase. Settle that before writing the fence.

## Wave integration: seven agent branches merged one at a time, 2026-09-03

Operator ruling: no trust gate per merge; merge in order, build the library
after each, elaborate the branch's batteries, run every gate once at the end.

Merged into `main`, in this order, each with `lake build Effect4` green:
census re-pin (clean), D1 denotation, D4 frame simulation (both fences), D3
skeleton IR (fixtures byte-identical), D2 merged-failure region runner and
`closeExitsM`, DB-04 approximation laws, M0/M1 wire hardening and the `Scopes`
family. Conflicts were append-only (`COORDINATION.md`, `docs/TRACE-DAG.md`,
`Effect4Test.lean`, `harness/trace/Generate.lean`, `tracer.ts`, `tsconfig.json`,
`scripts/check-trace-host.sh`) and resolved keep-both; the flow goldens now
carry the structured rule set and the M0 budget rows together.

Fallout found by the single sweep and fixed on `main`:

- `Effect4/Semantics/Approximation.lean` kept only its runner half; the region
  half was written against the pre-D2 failure carrier and is owed (noted in
  the module and `docs/TRACE-DAG.md`).
- The v0.6.0 `Outcome.defect` arm was missing from the golden admission check
  in `Generate.lean`; the wire battery named the event constructor through an
  `abbrev` (unresolvable) — both one-line repairs.
- `tracer.ts` declared `budgetHit` twice after the merge (the M0 latch and the
  pre-M0 computation); the latch stays. Its value encoder had no arm for an
  `Error` defect, so the swapped-arms mutant surfaced as a tracer defect
  instead of a divergence; an error now renders by its `_tag`, else its
  message, under `{"defect":…}`.
- The structured and patched host runs never passed the golden's budget row
  through, so `swap.budget` finished instead of reaching the frontier; both
  forms spend the same primitives up to the frontier (19 at the default yield
  setting, 79 at the floor of 3, measured), so the same row serves all three.
- `Generate.lean types` had been dropped in P-T9a and the straight-line type
  receipts were silently unchecked since: the command is restored and
  `scripts/check-lowering-types.sh` now fails on an empty or refused
  generator run instead of looping over nothing.
- `Effect4.Target.TypeScript.Skeleton` (D3) renders strings and is admitted
  exactly in `Effect4Test/Audit/AxiomGate.lean`; `TraceWire` is imported by
  the audit root; four line-numbered citations in research notes were reworded.
- The axiom gate now judges a compiler auxiliary or equation lemma
  (`f.eq_def`, `f.eq_<n>`, `f._f`, …) by the admission of the declaration it
  was generated from (`ancestors` in `AxiomGate.lean`): the skeleton
  renderers' equation lemmas are minted in `StructureLaws`, which unfolds
  them, and the three `render*_wellScoped` transports carry `_f` auxiliaries.

Sweep outcome after the repairs, all on the merged tree: goldens regenerated
and byte-stable; host, patched, types, property, coverage, census, family
check, the three planted-mutant self-tests (goldens, coverage, lowering
4/4), citations and the trust gate all green. Agent worktrees and branches
are removed. Not pushed.

## DB-04 region half landed, 2026-09-03

`Effect4/Semantics/Approximation.lean` carried only the tape runner's half of
the DB-04 approximation laws; the region half had been drafted against the
pre-D2 region runner and was cut when D2 changed the failure carrier to a
merged failure list. It is now in the tree, restated over that carrier.

The laws travel on four properties of a region-run computation, each closed
under `bind`, so each law is one structural walk over `regionLoop`'s branches
rather than a repeat of the plain runner's computation: `Appends` (the log
only grows), `Sound` (it appends, it punctuates a fuel frontier with the
marker it emitted, a failing run's merged list is headed by the reported
error, and a run that did not fail has an empty merged list), `Below` (one
computation observes below another), `Settles` (wherever the first did not
exhaust its fuel the second is the identical run).

What landed:

- `regionStep_log_extends` — one block's worth of region fuel only appends.
- `regionLoop_fuel_stable` — once a run at fuel `i` has finished, failed,
  refused, stuck or run out of tape, every fuel `j ≥ i` gives the *same* run:
  result, unconsumed tape, merged failure list, log and service state.
- `region_obs_mono`, `region_obs_chain`, `regionObservation_stable`, and the
  `runRegions` forms `runRegions_obs_mono`, `runRegions_obs_chain`,
  `runRegions_obs_stable`, with `runRegionsChain`/`runRegionsColimit`.
- `regionLoop_frontier_live` — a fuel frontier is a `fuel` frontier, never a
  `failed` and never a `refused` result, and the merged failure list is
  untouched: it is `[]`. This is DB-04's "fuel exhaustion is a live frontier,
  never a failure, never a refusal" for the region runner.
- `regionLoop_failed_head` — the D2 carrier's own law: a failing region run's
  merged list is headed by the error the wire and `RunResult.failed` report.
  The carrier is `closeFrame_failure_merge`'s, close order, first failure
  first.

The fuel formula. The region runner had none. It does not need one of its own:
an `enter` erases to a jump, an `acquire` to a `perform`, a `leave` to a jump
at the region's `continue_`, so `regionLoop` spends exactly one unit of fuel
per block of `flow.erase` — the graph `CyclesWF` constrains. So
`regionFuelFor flow tape = fuelFor flow.erase tape`, which
`regionFuelFor_blocks` reads back as `(tape.length + 1) * flow.blocks.length
+ 1` on the region flow's own table, and `runRegions_fuelFor_finishes` proves
it suffices — `Fuel.lean`'s `LoopBudget` carried through `regionLoop`'s
branches, with `lookupBlock_erase` as the bridge. `runRegionsColimitDefault`
is therefore total, not an `Option`, exactly as `runColimitDefault` is for the
plain runner; the module docstring's old "the region runner has no
fuel-sufficiency theorem yet" paragraph is retired.

Receipts (`Effect4Test/Semantics/ApproximationContract.lean`, new file — the
runner half's counterexample receipt was referenced by the module docstring
but had no file): the antisymmetry counterexample (two fuel frontiers with the
same log and different resumption blocks are mutually below and not equal, and
equal once observed), and the four DB-04 facts on `regionNested`,
`regionTwoFail` and `regionBothSucceed` from `harness/trace/Generate.lean`
plus one program whose release fails under a failing body. Allotments 9, 7, 5
and 6; the runs settle at 5, 4, 4 and 3, so the allotment is sufficient and not
tight. The merged-failure program's carrier is `[boom, boom]` — the body's
failure and the release's, in close order — while its wire result is
`failed boom`. Axioms in `Effect4Test/Semantics/ApproximationAxiomReport.lean`:
`propext` and `Quot.sound` only, no `Classical.choice`.

Tracing. `harness/trace/Generate.lean` grew a `region-frontier` arm: for each
region program it emits the Lean-face golden at one fuel below finishing — the
region rows already written, then a `frontier` row — the region counterpart of
`swap.budget`. It prints to stdout only; no file was added under `generated/`
and no script was touched, so nothing in the gate set changed.

Not closed. The `approximation` row of `docs/TRACE-DAG.md` stays
`required-open`: nothing host-side is claimed, and no gate compares a host run
at a region fuel frontier against the new golden. `Chain.colimit_below` and
`Chain.colimit_bound_mono` are stated once, over an arbitrary chain, and serve
both runners; there is no separate region restatement of them.

`lake build Effect4` green.
## D4 finalizer half landed, 2026-09-03

New module `Effect4/Semantics/RegionSimulation.lean` with battery
`Effect4Test/Semantics/RegionSimulationContract.lean` and axiom report
`Effect4Test/Semantics/RegionSimulationAxiomReport.lean`. Root import lines
appended to `Effect4.lean` (after `Target.TypeScript.Simulation`, which it
imports) and `Effect4Test.lean`. `harness/trace/Generate.lean` gains a
`frame-trace` arm. Nothing frozen was edited; no script was touched.

**The ruling fence B was blocked on is settled, and settled the other way from
what the note feared.** Packet D2 gave the region runner a merged failure list
in close order (`closeFrame_failure_merge`, against `Exit.asVoidAll`), so the
machine's `Cause.combine bodyCause finalizerCause` and the runner's list are
related by a projection: `causeOfFailures` is the section, `failuresOfCause`
(`cause.reasons.filterMap Reason.error?`) is the direction that is a total
function, and `failuresOfCause_causeOfFailures` says it retracts.

The empty-annotation hypothesis of the research note's section 5(b) is **not**
a hypothesis of this module, and the reason is sharper than avoidance:
`Cause.combine` is `Cause.dedup` of the concatenation and `dedup` keeps the
first occurrence, so the head of a merged cause is the head of the body's cause
whatever annotations either side carries, and `Exit.toOutcome` reads exactly
that head. `toOutcome_combine` proves it with no hypothesis on
`ReasonAnnotations`. 5(b) stays live only for a statement comparing whole
causes rather than their wire projection; nothing here does.

What is proved, in full generality:

- `unwind_failure`: a failing exit propagating through a fragment stack runs
  exactly the finalizers that stack names, in pop order, every one against the
  *same* exit — which is what `closeReleases` does — and then yields that exit,
  in `(unwindNames stack).length + 1` machine steps or more.
- `close_success`: a closing value runs the `onExit` frames above the answering
  `onSuccess` frame, latest-registered first, each against the closing exit, and
  then the region frame answers with its named continuation under the stack
  below it.

Both carry `hfin`: every finalizer succeeds. That is exactly the hypothesis
`regionReleaseFails` violates, which is also why that flow has no host golden
(`E4-TARGET-CE-012`); the failing-release case is recorded as owed.

What is *not* proved: the general `regions_simulate`. Its exact wording is in
the module header as an owed note, and it is closed by evaluation at the three
region programs the harness pins — `regions_simulate_regionBothSucceed`
(one region, one release), `regions_simulate_regionNested` (nested regions,
successful releases), `regions_simulate_regionTwoFail` (two releases of one
region closing on a failing body) — each `by rfl`, each with both sides pinned
to a literal so the equation cannot be satisfied vacuously. So of the operator's
ladder, (a) and (b) are closed as instances and generally as machine-side
theorems; (c), a *failing* release, is closed for neither: the runner gives
every release of one close the same closing exit, while the machine threads the
accumulating exit, so the two differ on the second release's `finalizer` row.
That is a real divergence, not a proof gap, and it belongs to whoever re-pins
`E4-FLOW-CE-019`'s neighbour.

What blocks the general theorem is the induction, not the payload: the runner's
`leave` continues at `row.continue_` with the fuel and decision tape it holds
*at the leave*, while the frame `enter` pushes is named at the *enter*. Closing
it needs a `leaveConfig` that walks a region body to its close under the oracle
plus a proof that it agrees with the runner — a second copy of the runner, and
its own fence.

The compilation is the host's shape. `enter` becomes `Prim.onSuccess body ν`
(`Effect.scoped(Effect.onExit(…))`, whose value continues at `continue_`) and
pushes **no** finalizer, because the row it writes is `leave` and `leave` has no
frame-machine shadow — compiling it to `Prim.onExit` would manufacture a
`finalizer` row the runner never writes. `acquire` becomes the fence-B `sync`
gadget followed by `Prim.onExit rest (RegionName.fin region point) false`
(rc.112's `scopedFrame`, `Effect.acquireRelease`), so the frames stack in
registration order and pop latest-first: the order `E4-TARGET-CE-012..014` pin.

Separation 4 holds with room to spare: `ν := RegionName` is an inductive over
`Config = Nat × BlockId × Env × Tape`, first-order data with a derived
`DecidableEq`, and the battery's `DecidableEq (Prim …)` gate is what fails the
moment anyone instantiates a name alphabet at a function type. `Config.fuel` is
a step counter, so a point occurs at most once in a run and needs no separate
occurrence index. `compileRegion` recurses structurally on its fuel argument
(not on `Config.fuel`), which is what makes the compiled program
kernel-reducible and the three instances provable by `rfl` rather than by
`#guard` alone.

Also in this packet, small and separate: `Effect4.FrameSimulation.Flow.Sig` —
the local copy marked `-- to be unified with Denotation.lean` — is gone.
`FrameSimulation` now imports `Effect4/Semantics/Denotation.lean` and uses
`Effect4.Flow.Sig`; the five `variable` lines move from `Alphabet.{0,0} Ty` to
`FlowAlphabet.{0,0} Ty` and every theorem statement is unchanged, `Flow.Sig a`
resolving through the enclosing namespace. The "later fence" note at the end of
`FrameSimulation.lean` is replaced by a pointer to the new module.

Open for the merge: `Effect4/Semantics/RegionSimulation.lean` inherits fence
B's placement question — it imports Runtime, Flow and the trace bridge, so it
sits above all three, and if strict directory layering wins it moves to
`Effect4/Runtime/RegionSimulation.lean` unchanged.

## DB-06 logic layer landed, 2026-09-03

`Effect4/Semantics/Logic.lean` (was a breadth stub) now carries the
weakest-precondition logic DB-06 asked for, over the semantics D1 fixed. An
*answer specification* says which answers an operation may return; `box` is
the weakest liberal precondition (EffHOL's angle modality, read as DB-06 reads
it), `dia` its dual, `total` says every reached operation is answerable, `wp`
is the total judgment. Discharged: `wp_iff_wlp_and_total` for every `Program`;
`Flow.wp_iff` for a checked flow against a tape and input, where `total`
excludes exactly the unanswered frontier and the refusal (fuel never appears,
the denotation is fuel-free by T2). Soundness: `box_sound` and `dia_complete`
against `interpret` for deterministic handlers (`DetRun`, instances for
`StateT σ Id` and for a `StateT` layer over any deterministic monad, so the
runner's `RunM (StateT σ Id)` is covered); `Flow.wlp_runDefault` and
`Flow.wp_runDefault` carry that to the runner at the allotted fuel through
T1/T2. Against a deterministic oracle the box is evaluation
(`box_ofOracle_iff`, `Flow.wp_ofOracle_iff`), which is what the receipts in
`Effect4Test/Semantics/LogicContract.lean` decide on `incr` and `chooser`
(`decide` runs the fuelled denotation in the kernel). Finding pinned by a
receipt: a specification is per operation, never per state — under the oracle
`incr` answers `41`, not the runner's `42`, because the second `get` cannot see
the `put`. `docs/DESIGN-BASIS.md` DB-06 no longer lists the obligation as
pending. Axioms within the ceiling; nothing host-side is claimed.

## Equivalence bridge landed, 2026-09-03

`Effect4/Semantics/Equivalence.lean` (was a breadth stub): `Flow.Equiv` — two
checked flows denote the same program against every tape and input — is an
equivalence relation, and by T1/T2 it is exactly indistinguishability by the
runner: `Equiv.runTape`/`runDefault` (result, unconsumed tape and log agree
under every service, from every log, at any sufficient fuel), `Equiv.log`, and
by the logic: `Equiv.wp`/`wlp`/`total`. `equiv_iff_denoteFuel` is the
executable face (the fuelled denotations at `fuelFor` agree), and
`equiv_of_erase_eq` says the denotation reads only the erased graph. This is
the relation D3's T4 (structured ≡ dispatch) instantiates. Axiom report
`Effect4Test/Semantics/EquivalenceAxiomReport.lean`; nothing host-side.

## M2 landed, 2026-09-03

Interruption as decisions. The packet's one refusal is the mask: it is a model
fact of the flow that the lowering does not spell (no `Effect.uninterruptible`
is emitted), so the masked golden observes the tail's own deferral rather than
rc.112's. Everything else is a Lean face with a host that agrees.

Lean (`Effect4/Flow/Interrupt.lean`, imported from `Effect4.lean`):

- An `Interrupts` decision family over the region runner. Points are before
  every `perform` of a plain block and at every region `leave`; `acquire` is
  not a point (rc.112 acquires uninterruptibly). Every point writes one
  `Trace.Event.decide` row at its own site, whatever the answer.
- The site space is disjoint by construction: `Point.site` lands at or above
  `interruptBase = 1000000`, `perform` sites odd and `leave` sites even.
  `Point.site_ne_choose` refuses every `choose` site below the base,
  `Point.site_inj` separates the two shapes, and `sitesSeparated` decides per
  flow that its authored sites lie below the base. One wire carries both tapes.
- Exhaustion of the interrupt tape is *not* a frontier: it answers "not
  delivered". So the empty tape is the uninterrupted run and the tape names
  only the points that deliver. A tape entry for another point is neither
  consumed nor an answer here.
- A mask defers, it does not drop: `interruptPoint_masked_defers` keeps a
  delivered answer in `IState.pending` (rc.112's `_deferredInterrupt`),
  `interruptPoint_unmasked_delivers` delivers it at the first unmasked point.
  A mask is inherited by every open region on the frame stack, its own `leave`
  point included (`isMasked`).
- Delivery closes every open region innermost-first with `Outcome.interrupted`
  and ends the run `done interrupted`. `closeFrame_interrupted_log` is
  `closeFrame_log` at that outcome, so the A1 arm finally has a Lean producer:
  before M2 only the P-T11 projection could build one.
- `RunResult` and `regionLoop` are untouched — the new runner is
  `runInterrupts` with its own `InterruptResult` — so every region-runner
  theorem still speaks about the function it spoke about.

Host: `Skeleton.interruptPoint` and `Lowering.interruptPoint`
(`rule.interrupt-point`, the twenty-fifth rule) render `yield*
interrupts.point(<site>)`; `FlowProgram`/`RegionProgram` gained
`interrupts : Bool := false` and `masked : List RegionId := []`, so
`flow-fixture.ts` and `structured-fixture.ts` are additive — every program
that existed before M2 lowers to the same bytes (checked with `cmp` before the
new programs were added). `harness/trace/interrupt-tail.ts` is the
interruptor: it answers the tape exactly as `interruptRead` does, pushes the
same `decide` row, and calls `fiber.interruptUnsafe()` at the delivered site,
the idiom `tracer.ts` already uses on the budget path.

Goldens: `generated/traces/flow/interrupt/{interruptUnmasked, interruptMasked,
interruptFinalizer}.tsv` — unmasked delivery, masked deferral then delivery at
the first unmasked point, and two nested finalizers seeing `interrupted`. They
sit in a subdirectory so the flow host loop's `flow/*.tsv` glob does not hand
them to `flow-tail.ts`, which has no `Interrupts` service; `interrupt-tail.ts`
gets its own section in `scripts/check-trace-host.sh`. All three agree under
`outcome`, `m1` and `m2` at the default yield setting and at the rc.112 floor
of 3 (run directly, not through the gate).

Editing `scripts/generate-trace-goldens.sh` rewrites the `generator` and
`input` digests every golden carries, so every `.tsv` under `generated/traces`
is regenerated in this branch; the event rows of the pre-M2 goldens are
unchanged.

Batteries: `Effect4Test/Flow/InterruptContract.lean` (the three goldens' logs
as `#guard`s, the empty-tape and foreign-entry runs, the site algebra, axiom
report `propext`/`Quot.sound`) and
`Effect4Test/Counterexamples/Flow/Interrupt.lean` (`E4-FLOW-CE-022`,
`E4-FLOW-CE-023`). Both reachable from `Effect4Test.lean`.

Owed after M2: the mask as a lowered primitive (which rc.112 spelling carries
`RegionProgram.masked` — `Effect.uninterruptible` around the region body is the
obvious candidate, and it changes the primitive count the budget goldens
measure); the interruptor identity, which the wire drops; and an interrupt
point at `acquire`, refused here because rc.112 acquires uninterruptibly.
## D2 denotation landed, 2026-09-03

The remaining third of packet D2. `Effect4/Flow/Region.lean` already had the
merged-failure runner and the `Scope` lemmas L1/L2; what was owed was the
denotational statement, and it is now `Effect4/Semantics/RegionDenotation.lean`
(String-free, in `Effect4.lean` after `Denotation.lean`).

The scope summand `ScopeFam` has **four** names, not the plan's three. `enter`
(param `RegionId`, answer `Unit`), `acquire op release` (param `Val`, answer
`Option (Except Val Val)`), `leave` (param `Val`, answer `Option Failures`) and
`fail` (param `Val`, answer `Failures`). Three deviations from the plan text,
each forced by reading `Region.lean` rather than the plan:

1. **`fail` is an operation.** A failing operation makes `regionLoop` call
   `Flow.fail`, which closes *every* open region (`unwind`). That reads the whole
   stack, so it is scope state, not something a pure denotation can inline.
2. **`acquire` and `leave` answer an `Option`.** Both arms of `regionLoop` match
   on `stack` and fall through to the stuck frontier when it is empty. Emptiness
   is runtime state; `none` is that refusal. Region admission refuses an
   `acquire` or a `leave` outside every region, so `none` should be unreachable
   on an admitted flow — **that stack invariant is owed, not assumed**; it is
   stated in the module docstring and nothing here depends on it.
3. **`leave` answers the merged failure list**, not `Except Val Val`. That is
   the runner's own carrier after D2's first two thirds: `closeFrame` keeps every
   failing release in close order, `regionLoop` continues at the region's
   `continue_` exactly when the list is empty and otherwise fails with its head
   and carries its tail. So `scopeHandler`'s `leave` arm *is* `closeFrame`, and
   L1/L2 are literally that arm's facts; its `fail` arm is `unwind`.

The alphabet summand is **not** D1's `Fam`: a `RegionService` answers
`Except Val Val` where a `FlowService` answers `Val`, so `RegionFam` and
`regionTraceHandler` are the fallible twins. The decision summand is D1's
`DecSig`, lifted, unchanged.

**Shape: `Handler.sum`, not `Handler.mapHom`.** The plan offers
`interpret (scopeHandler.mapHom (MonadHom.stateT (interpretHom traceHandler)))`
as the alternative. The pinned lean4-effects v0.3.1 (`rev 2447edd`) has no
`Effects/Hom.lean` at all — no `MonadHom`, no `Handler.mapHom`, no
`interpretHom`, no `interpret_mapHom` — so that shape does not type and is not
used. The sum shape is taken instead: all three summands are handled into one
monad, `ScopeM M a = StateT (Stack a) (RunM M)`, with the two stackless handlers
lifted by `Handler.overStack` (a hand-rolled `StateT.lift` transport, which is
exactly what `mapHom` would give). If lean4-effects later gains the `Hom` module,
`overStack` is the one declaration to replace.

Theorems: `regionLoop_eq_interpret` (T1 for regions, generalised over stack and
log), `runRegionsCause_eq_interpret`, `runRegions_eq_interpret`,
`runRegionsDefault_eq_interpret`, and the corollary that ties D2 to D1,
`regionLoop_erase` / `runRegions_erase` (on a flow whose every block is `plain`
the region runner and `Runs.lean`'s plain runner agree — result, unconsumed tape
and log — through `FlowService.toRegionService`). Axiom union `propext`,
`Quot.sound`; no `Classical.choice`.

**Owed, and named as owed:** the fuel-free region denotation. `denoteRegionsFuel`
is fuelled, as D1's `denoteFuel` is, but there is no `denoteRegions` through
`CyclesWF` and therefore no region twin of T2 `denoteFuel_eq_denote`. The erased
graph carries the same lexicographic measure, but `enter`/`acquire`/`leave` need
their own decreasing argument and the plan did not ask for one; `denoteRegions`
here is `denoteRegionsFuel` at a supplied fuel. The exact wording of what is
owed is in the module's `## The denotation` docstring.

Receipts: `Effect4Test/Semantics/RegionDenotationContract.lean` (the frozen
surface, the summand's parameters and answers by `rfl`, and T1 as `#guard` on
the three region goldens `regionNested`, `regionTwoFail`, `regionBothSucceed`,
plus a region-free program for the erase corollary) and
`RegionDenotationAxiomReport.lean`. `harness/trace/Generate.lean` gains a
`region-oracle` arm beside `oracle`: per region program it computes the runner's
log and the `interpret` side's log and reports agreement. No script was touched.
`docs/TRACE-DAG.md`'s `semantics` row is updated in place with both scope lines.
## M3 landed, 2026-09-03

`Fibers` as a traced family and a two-fiber host. Nine goldens under
`generated/traces/fiber/`, one per assertion of
`harness/fiber-supervision/runtime-check.ts` that this alphabet can carry, all
agreeing with the pinned rc.112 install under `outcome`, `m1` and `m2`.

**The projection I chose, stated so the next packet does not have to guess.**
A `fork` enqueues its child and then reads one entry off the tape at the fork's
own site. On `true` the child is given the processor *at the fork point* — and
so is every other queued child, in fork order, because rc.112 drains its whole
run queue at a yield. On `false` nothing runs, and the child waits for the
first `join` or await that blocks the parent. So the packet's "at the fork
point *or* at the first join/await" is not a choice made once: the tape makes
it per fork, and it is observable — `raceImmediateSuccessStopsLaunch` differs
from `raceFailureAllowsNextLaunch` in exactly that decision, and
`emptyRacePendingUntilInterrupted` is pending only because its one decision is
`false`.

The other three clauses, each read off the host before it was written down:
`join` and the awaits drain **only** when their target has not published, so
awaiting a winner that already finished launches nothing (which is what
`raceReentrantEmptySetBypasses` turns on); `interrupt` never drains, and a
child interrupted while still queued never runs and is never cleaned;
`started` and `cleanups` are `Effect.sync` reads and never hand the processor
over.

The supervision half is `FiberTable.parentExit`: the parent's own exit
interrupts and waits for every *tracked* child and leaves daemons running —
`Supervision.interruptAllRequests` / `awaitAllChildren` and
`commitFork_daemon_untracked` as handler behaviour. It happens after the last
traced row, so no golden shows it; what it accounts for is why every program of
the corpus terminates at all, and why `daemonSurvivesParentExit` terminates
with its child still running where the same program with a tracked child would
wait forever.

**Two rows that stay host-only, and the honest reason.**
`Effect4/Concurrency/Scheduler.lean`'s `Machine` carries no program, so nothing
in the Lean tree steps two fibers against each other. Consequences, registered:

- `E4-SEM-CE-010` — `join` of an interrupted child. rc.112 ends the run
  `{"interrupted":true}`; the family's abort channel is `Nat` and could only
  invent `{"failure":n}`. The projection refuses (`FiberTable.stuck`) and the
  `fiber-golden` arm emits nothing for such a program. Witness:
  `Effect4Test/Counterexamples/Concurrency/FiberProjection.lean`.
- `E4-SEM-CE-011` — a `false` decision is not a fact about the run. At
  `EFFECT4_MAX_OPS=3` the run loop yields on its own and a deferred child
  starts with no `decide` row for it; measured on
  `emptyRacePendingUntilInterrupted`, `answer started []` against
  `answer started [4, []]`. The `fiber` section of `check-trace-host.sh`
  therefore runs at the default threshold only and says why — it is the one
  family without a yield-every-op run.

**Refusals of spelling, recorded where they bite.** `await` is a reserved word
in the generated-binding profile, and Stratum V admits type spellings of depth
two, so `Option (Except Nat Nat)` — the exact shape of an rc.112 `Exit` — is
not a spelling the DSL has. Rather than widen the stratum (which would change
`Effect4/Meta/Derive.lean`, whose digest is provenance for every golden in the
tree) or hand-roll a tag encoding into a `List Nat`, the trichotomy is two
operations built from the alphabet's own formers: `awaitValue` answers
`some v` exactly when the child succeeded, `awaitError` answers `some e`
exactly when it failed, and an interrupted child answers `none` to both.
Neither ever invents a code. The tenth runtime-check assertion,
`race-reentrant-nonempty-set-includes-late-insertion`, is refused outright: it
is distinguished from the empty-set case only by cleanups run from inside the
winner's own completion callback, and this family has no former for a child
that completes another child.

**Where the handler lives, and why.** `Effect4/Concurrency/FiberFamily.lean`,
under `Effect4/` and audited by `#effect4_axiom_gate` with no exemption, so
`Effect4Test/Flow/FibersContract.lean` can hold the `#guard` receipts of all
nine goldens' rows without restating the family. The error channel is `Nat`,
not `String`, to keep string folds out of the semantics; the report is
`propext` only (`Effect4Test/Flow/FibersAxiomReport.lean`).

**One shared file moved.** `harness/trace/tracer.ts` gained an optional
`RunOptions.armed`, consulted first by `TapeScheduler.shouldYield`. Existing
tails pass nothing and are byte-for-byte unaffected (the straight-line and
scope families were re-run against their goldens to confirm). Its digest is
provenance in `generated/lowering-property.tsv`, whose `input` line is updated;
the `row` line is untouched because the property loop's behaviour is not.

**Generation note for the sweep.** Every golden in `generated/traces/` carries
`harness/trace/Generate.lean`'s digest, and that file gained the four
`fiber-*` arms, so all 21 existing projections were regenerated; the diff is
exactly two provenance lines each, no row moved. The generator scripts were not
run (the packet forbids it): the arms were driven directly and the provenance
block reproduced verbatim, and `scripts/check-trace-goldens.sh` in the sweep is
the check that this was done correctly.

Not run here, left for the sweep: `check-trace-host.sh` end to end, the trust
gate, the property loop, `check-trace-patched.sh`. Run here: `lake build
Effect4` (green), every new battery under `lake env lean` (all silent), the
harness type gate `check.mjs` (tsc and tsgo ok over 13 files), and the `fiber`
tail against all nine goldens plus the straight-line and scope families as a
regression on the `tracer.ts` change (51/51 mask comparisons ok).

One pre-existing failure is untouched and not ours: the Effect4Test
module-closure gate rejects `Effect4Test/Protocol/ByteParserContract.lean`,
which is not reachable from the audit root and was not reachable before this
packet either.
## D5 landed, 2026-09-03

`Effect4/Target/TypeScript/ScriptDenotation.lean` gives the straight-line
script embedding a meaning and proves the graph agrees with it. `denoteScript`
reads the program off a `Script`'s steps — one `vis` per performed operation,
literals and atoms included, the environment as the open block's scope — and
`Script.toFlow_denote` says that `Flow.denoteGo` of `Script.toFlow`'s output, on
the empty tape, is `liftScript` of that program (`liftScript` is
`Program.inl` into `FullSig` followed by `done` with the untouched tape: a
straight-line run announces no decision and always returns). The `m2` oracle of
`docs/TRACE-DAG.md` is now a corollary per embedded program rather than an
observation.

The `Build` invariant the packet asked to be named is two predicates proved as
their own lemmas: `Appends` (every clause of `materialize` and `embedStep` only
extends the block list, the table and the scope, and keeps `next` counting the
blocks) and `Ordered` (the blocks carry the ids `0, 1, 2, …` in order, so
`lookupBlock` resolves positionally — `lookupBlock_ordered`). The induction runs
`performTo_segment` → `mint_segment` → `literal_segment` →
`materialize_segment` → `step_segment` → `stepsWalk_denote`, composed through
`Segment`, a straight stretch of the graph with its walk; `Leaves` and its
`bind_congr` are what let the next segment be rewritten under a `bind`.
`interpret_vis_of_pure` is the erasure lemma the packet named: a `vis` whose
handler answers purely is the continuation at that answer, which is exactly the
status of the literal and atom rows of an embedded table
(`tableService_handle_pure`). Everything is inside `propext`/`Quot.sound`;
`List.findIdx?_eq_some_iff_findIdx_eq` is classical upstream and is reproved
privately as `findIdx?_lt` so the module needs no gate exemption. The
semantics live in a module of their own because `ScriptFlow` and `EffectV4` are
exempt for `Classical.choice` as renderers.

The oracle arm of `harness/trace/Generate.lean` gained a third face: it now
interprets `denoteScript` under the same table service and prints three-way
agreement per program (`incr`, `twice`: traced service, Flow runner, script
denotation, 7 rows each). Receipts:
`Effect4Test/Target/TypeScript/ScriptDenotationContract.lean` (the theorem at
each of the four programs of `Generate.lean`'s `programs` list, plus `#guard`s
that each embeds, is admitted, is denoted, and mints the ids in order) and
`ScriptDenotationAxiomReport.lean`.

**What D5 did not deliver.** `example : denoteScript <rows> <name>.script =
<name> := by rfl` cannot be stated: `denoteScript` lands in
`Program (Sig (tableAlphabet id table)) Val` while `<name>` lands in
`Program X.Sig A`, and relating them needs a decoding `Val → X.Answer name`
that the DSL has no half of (`E4-TARGET-CE-016`, `Effect4/Meta/Derive.lean`
carries the owed note in its module docstring). What `effect_program` emits
instead is the strongest agreement the two faces admit and is new:
`performedNames X.Name.spelling X.answerDefault (<name> default)
= <name>.script.operationNames`, one `rfl`-checked `example` per declaration,
green on all eleven `effect_program` declarations in the tree.
`effect_signature` gained one emission for it, `X.answerDefault`, an inhabitant
per answer; every admitted Stratum V spelling has one.

Also noted, not fixed: `E4-TARGET-CE-015` is cited by
`Effect4/Target/TypeScript/Trace.lean`, `harness/trace/Generate.lean` and
`harness/trace/wire-tail.ts` but has no row in
`test/counterexamples/REGISTER.md`.
## D3 theorems landed, 2026-09-03

Packet D3's second half: the control skeleton has a denotation, and the
dispatch form's agreement with the flow denotation is a theorem.

`Effect4/Target/TypeScript/SkeletonSemantics.lean` (new, ~2 100 lines) defines
`⟦·⟧` as `Skeleton.denote`: a tape-indexed evaluation of a lowered statement
list into the *same* `Program (FullSig alphabet) (RunResult × Tape)` that
`Effect4/Semantics/Denotation.lean` denotes a checked flow into. The machine is
a total slot store plus the dispatch index variables plus the block last
entered; statement lists are structural and fuel is spent only by a loop
iteration, so one turn of a `dispatchLoop` is one block of the flow and the
skeleton's fuel is `Flow.denoteFuel`'s fuel unit for unit. That alignment is
what makes T3 an equation at every fuel instead of an inequality at a large one.

Two decisions worth recording because they are load-bearing:

- `perform`, `atom` and `literal` denote the **same** `Sig` operation. `plan`
  never reads the operation table, so a family call, a pure atom and a literal
  are one `perform` of the algebra; what separates them is a spelling
  (`Skeleton.render`) and a tracing policy (`FlowService.pure`), never a
  different program. This is why T3 can be stated as equality of `Program`s
  rather than equality after a handler.
- The three region nodes (`enterScoped`, `acquire`, `leave`) have no denotation
  here. Regions are a scope summand of `FullSig` that packet D2 owns and this
  module does not import; they stop the machine at a `stuck` frontier of the
  block last entered, which is what `enterBlock` is carried for.

Landed:

- **T3** `skeletonDispatch_denote` — for every checked flow and every tape,
  `⟦skeletonDispatch flow⟧ = Flow.denote flow`. Closed, no side conditions
  beyond admission.
- **T4 on the flat fragment** `skeletonStructured_denote_dispatch` — for a
  graph with no join and no loop the structured form and the dispatch form
  denote the same `Program`, through `skeletonStructured_denote`. `Skel.Flat`
  is the fragment; `Skel.flatBelow` is its decidable half and
  `Skel.flat_of_flatBelow` closes the gap for any `Flow.graphOf`.
- `Skel.execList_skeletonBlockWith` — one block of a checked flow runs exactly
  as `plan` says, for an **arbitrary** transfer. Both forms are instances; a
  third lowering only has to name its own transfer's law.

Owed, and stated in the module (§18) and in `docs/TRACE-DAG.md` in the same
words: the merge and loop-header shapes of `Structuring.emitNode`. Neither is a
gap in the denotation — `Skel.execList` interprets `labelled`/`breakTo` and
`loop`/`continueTo`, and the block law is transfer-parametric — the missing half
is two facts about the pinned `typescript` package's own algorithms, the same
two `Effect4/Target/TypeScript/StructureLaws.lean` leaves open under
`BreakScopedStatement`.

Receipts: `Effect4Test/Target/TypeScript/SkeletonSemanticsContract.lean`
(the machine's own laws, the four packet flows rebuilt, which graphs are flat,
and T3/T4 instantiated at them) and `SkeletonSemanticsAxiomReport.lean`
(74 declarations, union `propext` + `Quot.sound`, no `Classical.choice`). Two
library lemmas were deliberately not used because they cross the ceiling:
`List.filter_eq_nil_iff` and `Exists.choose` — `Skel.movedMachine` names the
machine a `perform`'s continuation needs rather than choosing it.

`lake build Effect4` green. No gate script run from this worktree.

## D3 merge note, 2026-09-03

D3 forked before M2 landed the `interruptPoint` skeleton node and the
`interrupts : Bool` argument of every skeleton builder. At merge the D3 lemmas
were restated at `interrupts = false` and T3/T4 (`skeletonDispatch_denote`,
`skeletonStructured_denote`, `skeletonStructured_denote_dispatch`) carry a
`noInterrupts : program.interrupts = false` hypothesis, discharged for the
contract's programs by `interrupts_of_program?`. `Skeleton.denote` has no case
for `interruptPoint`; giving it one (a `decide` at the interrupt site, matching
`Effect4/Flow/Interrupt.lean`) and dropping the hypothesis is owed.

## Wave 2 sweep, 2026-09-03

One sweep over the merged tree after all seven branches (D3, D2 denotation,
DB-04 region half, D4 finalizer half, D5, M2, M3) plus DB-06 and the
equivalence bridge: goldens regenerated (straight-line, flow, interrupt,
scope, fiber families), hermetic goldens, citations, host, patched, types,
property, coverage, census, family check, the three planted-mutant self-tests
and the trust gate all green. Fallout repaired on `main`: the frame-simulation
contract follows D4's `Flow.Sig` unification (its alphabet is now a
`FlowAlphabet`), and the fiber receipts render rows inline because the axiom
gate scans test declarations. Agent worktrees and branches removed. Not pushed.

## Full reification continuation: region denotation, 2026-09-03

Codex resumes the operator's full-reification goal from `70bd017`. The supplied
Wave 2 handoff and the current single-worktree census establish that its merged
lanes are finished; the older trace-lane reservations above are superseded only
for the following continuation fence. The full objective remains all phases
and required assurance routes in `PLAN.md`, including the open host boundaries.

| File or section | Owner |
| --- | --- |
| `test/contracts/region-total-denotation.contract.md`, `Effect4Test/Semantics/RegionTotalContract.lean`, `Effect4Test/Semantics/RegionTotalAxiomReport.lean` | Codex independent breaker; new packet, frozen before implementation |
| `Effect4/Semantics/RegionTotal.lean` | Codex builder; fuel-free region meaning and agreement with the existing fuelled denotation |
| `Effect4.lean`, `Effect4Test.lean` (RegionTotal import lines only), `test/fixtures/trust-gate/known-red.txt` (RegionTotal entries only) | Codex packet wiring |
| `docs/TRACE-DAG.md` (region fuel-free scope line only), `docs/research/2026-09-03-reification-plan.md` (D2 remainder only), `Effect4/Semantics/RegionDenotation.lean` (owed documentation only) | Codex coordinator after verification |

The existing region runner, failure/cleanup policy, scope signature, fuelled
denotation, dependency pins and frozen batteries are unchanged by this fence.
The packet must prove agreement at every sufficient fuel for every admitted
region flow and finite decision tape, without hiding unanswered frontiers or
assuming a stack invariant. No runtime-coverage or host-bridge closure follows.
Only the coordinator launches package builds; agents run narrow Lean files.

## Routing documentation reconciled, 2026-09-03

Codex documentation continuation claimed and completed only the current
dependency paragraph, Wave 2 continuation pointer and near-term effectful-field
row in `PLAN.md`, plus the dependency paragraph and external-package table
rows in `docs/ARCHITECTURE.md`. The narrow claim superseded only those sections
of the completed Schema documentation reservation, as supported by the Wave 2
integration note and generated assurance closure, and is now released.

Both dependency revisions match `lakefile.toml` and `lake-manifest.json`.
The effectful-field row matches all eight closed edges and the closed graph
status in `generated/schema-structural-assurance.tsv`; document and wire edges
remain open. The extraction parity history is retained. Source comparisons,
the continuation link, a citation check limited to the two edited documents,
and `git diff --check` passed. No build or generated-output change was needed.

## Full reification continuation: break-scoping counterexample, 2026-09-03

Codex breaker (`algebra_choices`) claims only the following fence, dispatched
by the coordinator after a kernel proof refuted the existing generic
`BreakScopedStatement`. The merged Wave 2 reservations are superseded only for
these paths and append-only sections. Production `StructureLaws.lean` and
`SkeletonSemantics.lean` remain unchanged by this packet.

| File or section | Owner | State |
| --- | --- | --- |
| `Effect4Test/Counterexamples/Target/BreakScoped.lean` | Codex breaker (`algebra_choices`) | new kernel witness and actual-lowerer edge-discipline receipts |
| `test/counterexamples/REGISTER.md` (`E4-TARGET-CE-018` only) | Codex breaker (`algebra_choices`) | append-only counterexample row |
| `test/contracts/flow-structured-lowering.contract.md` (2026-09-03 amendment only) | Codex breaker (`algebra_choices`) | original quantified statement refuted; corrected hypothesis and intended full T4 remain explicit |

The coordinator owns root test imports and the shared coordination commit.
This breaker runs only the narrow Lean file and its axiom receipts.

Break-scoping packet released: commit `2bd2077` contains only the three files
above (244 added lines). `lake env lean
Effect4Test/Counterexamples/Target/BreakScoped.lean` exited 0; its eleven
theorem receipts use at most `propext` and `Quot.sound`. The staged diff check
passed. Root test imports, shared coordination commit and any generated
counterexample-register projections remain coordinator-owned. The corrected
generic statement and full T4 are still open. No package build ran here.

## Fuel-free region proof integrated, 2026-09-03

The independent packet was frozen at `8351f88`, after 24 concrete controls,
missing-declaration red checks and a rejected first-failure-only mutant. The
coordinator implements its four public declarations in
`Effect4/Semantics/RegionTotal.lean`; helper declarations are private. The
recursive definition uses tape length and erased non-choice reachability,
never a fuelled runner. The equality quantifies over every sufficient fuel
and every handler answer, including refusals and failures.

The coordinator additionally claims the D2 row in the Wave 2 status table,
the existing semantics row in `docs/TRACE-DAG.md`, and the false
`BreakScopedStatement` sentence in its structured-agreement row. Root imports
for this packet and the committed break-scoping witness are coordinator-owned.
No other packet's proof or generated status is included in this amendment.

`lake build Effect4.Semantics.RegionTotal` and both narrow packet files
passed. A first axiom inspection found `Classical.byContradiction` introduced
by arithmetic automation on the impossible zero-fuel branch. Direct
`False.elim` removed it; all four fresh receipts now contain exactly
`propext` and `Quot.sound`. Independent review also traversed the definition
dependencies, verified the six decreases and every branch, and confirmed that
neither fuel-free definition reaches a fuelled runner or `fuelFor`.

The default `lake build` compiled the library root and new packet, then failed
on the two existing declared-red modules (`ByteParserContract` and
`RaceRepresentativeContract`) and their audit-root closure consequence. This
is not an all-green package or a full-goal completion claim. The separate
stack invariant, finalizer-machine connection and host boundaries remain open.

## Full reification continuation: region simulation boundaries, 2026-09-03

Codex independent breaker (`corpus_measurement`) claims only the following
packet, dispatched after the same-scope cleanup and live-frontier mismatches
were reproduced in scratch Lean checks. The completed Wave 2 trace-lane
reservations are superseded only for these paths and append-only sections.

| File or section | Owner | State |
| --- | --- | --- |
| `Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean` | Codex breaker (`corpus_measurement`) | new kernel witnesses and successful controls |
| `test/counterexamples/REGISTER.md` (`E4-TARGET-CE-019` through `021` only) | Codex breaker (`corpus_measurement`) | append-only target rows |
| `test/contracts/frame-simulation.contract.md` (2026-09-03 independent boundary amendment only) | Codex breaker (`corpus_measurement`) | append-only correction; general finite-prefix and residual-state obligation |
| `test/counterexamples/target/region-simulation-boundary.mjs` | Codex breaker (`corpus_measurement`) | pinned rc.112 finite host reproducer, with source-hash verification |

Production implementations, existing witnesses, root imports, generated
evidence and runtime coverage are outside this fence. The coordinator owns
the shared coordination commit and packet wiring. This breaker runs the
narrow Lean witness, host reproducer and scoped citation/diff checks only.

Region-boundary packet released at `623141b`: exactly the four claimed files,
356 added lines. All 26 narrow Lean theorem receipts use only `propext` and
`Quot.sound`; the pinned host's three finite controls and four-file citation
and diff checks passed. The shared coordination file was excluded from that
commit. The new general simulation, production component, root imports and
generated-register projections remain coordinator-owned and open.


## Full reification continuation: structured order contract, 2026-09-03

Codex independent breaker (`web_semantics`) claims only the three new files
below, dispatched by the coordinator before production `StructureOrder`
implementation. This continues the corrected edge-local body premise of
`E4-TARGET-CE-018`; the previous counterexample and frozen packet remain intact.

| File or section | Owner | State |
| --- | --- | --- |
| `test/contracts/structure-order.contract.md` | Codex independent breaker (`web_semantics`) | new minimal public declaration/conditional theorem contract |
| `Effect4Test/Target/TypeScript/StructureOrderContract.lean` | Codex independent breaker (`web_semantics`) | exact signatures, actual-body control and illicit-body rejection |
| `Effect4Test/Target/TypeScript/StructureOrderAxiomReport.lean` | Codex independent breaker (`web_semantics`) | trust receipts for the frozen public surface |

The intended production file is `Effect4/Target/TypeScript/StructureOrder.lean`
owned by the separate builder (`algebra_choices`) after this packet is frozen.
Existing `StructureLaws`, graph algorithms, emitter, CE-018 witness and the old
structured-lowering contract remain unchanged. The existing
`docs/TRACE-DAG.md` structured-agreement route remains open for computed
dominator correctness, full merge/loop agreement and interrupt denotation.
The coordinator owns root imports, known-red wiring and the shared coordination
commit. The breaker commits only the three new packet files and runs narrow
Lean files; only the coordinator launches package builds.

## Full reification continuation: checked region stack safety, 2026-09-03

Codex independent breaker (`corpus_measurement`) claims the three new packet
files below before production `Effect4/Semantics/RegionSafety.lean` exists.
This closes no frame-simulation or host boundary and continues only D2's
reachable-stack safety obligation in the existing `docs/TRACE-DAG.md` route.

| File or section | Owner | State |
| --- | --- | --- |
| `test/contracts/region-safety.contract.md` | Codex breaker (`corpus_measurement`) | exact three-theorem contract and private ownership-proof requirement |
| `Effect4Test/Semantics/RegionSafetyContract.lean` | Codex breaker (`corpus_measurement`) | universal ascriptions, checked-run controls and invalid-stack witnesses |
| `Effect4Test/Semantics/RegionSafetyAxiomReport.lean` | Codex breaker (`corpus_measurement`) | exact public theorem trust receipts |

Existing runner, validation, Scope, RegionTotal, prior packets and canonical
carriers remain unchanged. The separate coordinator builds RegionSafety after
freeze and owns root imports, known-red wiring, generated evidence and the
shared coordination commit. The breaker commits only these three new files
and runs narrow Lean checks, including isolated missing-declaration checks.

RegionSafety packet released at `fa53b97`: only the three claimed files,
268 added lines. All 31 existing-meaning controls pass; changing the invalid
empty-stack expectation is rejected at that assertion; the restored controls
pass. Scratch declaration and axiom checks reject exactly the three absent
public names. Direct imports separately fail on missing `RegionSafety.olean`.
The scoped citation and staged diff checks pass. Production, root imports,
known-red wiring and the shared coordination commit remain coordinator-owned.

## Full reification continuation: structured order implementation, 2026-09-03

Codex builder (`algebra_choices`) claims only
`Effect4/Target/TypeScript/StructureOrder.lean`, after independent breaker
commit `5b29edb4b33ebf7e7afb28f110dc7119e0ed1fef` froze its seven-name
surface and red battery. The builder preserves that packet, existing
`StructureLaws.lean`, `SkeletonSemantics.lean`, all graph algorithms and the
CE-018 witness. The graph-order theorems and conditional strict-scoping
induction come from checked scratch proofs; computed-dominator correctness
and full T4 remain open. Further CHK invariants stay in scratch until separately
frozen. The coordinator owns root imports, graph status, shared coordination
commit and package builds. This builder runs only narrow Lean checks.

## Coordinator integration fence, 2026-09-03

The coordinator claims the root imports for `RegionSimulationBoundary` and
`StructureOrder`, the `frame-simulation` and `structured-agreement` rows in
`docs/TRACE-DAG.md`, and the D3/D4 continuation rows in
`docs/research/2026-09-03-reification-plan.md`. The boundary warning at the
head of `Effect4/Semantics/RegionSimulation.lean` is documentation only;
its definitions and existing proofs remain unchanged. The independent
amendment at `623141b` owns the corrected scope/frontier obligation.

The coordinator also claims `generated/fiber-assurance.tsv` only for
regeneration by its existing generator if the new counterexample register
rows make its full-register digest stale. No generator, Fiber declaration,
contract or status rule is changed by this projection refresh.

Structured-order implementation released at `6697ebc`: only the new
`StructureOrder.lean` (578 lines). Its SHA-256 is
`6912febbfe71a7b2c0ed7623657dd8bd375209202ab8aa2076984d2ddabb9005`.
Direct narrow Lean compilation, the unchanged frozen contract and its public
axiom report passed; all seven public receipts use at most `propext` and
`Quot.sound`. The independent breaker reviewed this exact saved source and
approved the frozen conditional lexical-scope/order claim. Root imports,
proper Lake/package builds and graph status remain coordinator-owned. The
actual CHK continuation remains scratch-only pending its separate freeze;
computed-dominator correctness and full T4 are still open.

## Full reification continuation: interrupt mask boundary amendment, 2026-09-03

Codex independent breaker (`web_semantics`) claims the four packet paths below
before any production interrupt or lowering repair. The stable flow IDs are
`E4-FLOW-CE-024` (the host withholds the request) and `E4-FLOW-CE-025` (pending
delivery at restoration, including a direct return).

| File or section | Owner | State |
| --- | --- | --- |
| `Effect4Test/Counterexamples/Flow/InterruptMaskBoundary.lean` | Codex independent breaker (`web_semantics`) | new corrected-boundary red battery, reusing canonical fixtures |
| `harness/trace/interrupt-mask-boundary.mjs` | Codex independent breaker (`web_semantics`) | new historical generated-target and real rc.112 runtime reproducer |
| `test/contracts/flow-regions-runner.contract.md` | Codex independent breaker (`web_semantics`) | append-only M2 boundary amendment |
| `test/counterexamples/REGISTER.md` | Codex independent breaker (`web_semantics`) | append-only CE-024 and CE-025 rows |

The original interrupt positive battery, original counterexamples, all
production, and generated files stay unchanged in this packet. The new tests
freeze immediate pending delivery after successful masked cleanup without a
fresh outside point; actual runtime requests are made while uninterruptible.
The reproducer retains a historical baseline by exact Git revision and uses
the pinned Effect bytes at both 1000000 and 3 operation thresholds. These are
finite observations, not a general host equivalence or coverage result. The
coordinator owns the later semantic/lowering repair, root wiring, shared
coordination commit, and package builds; this breaker commits only the four
packet paths and runs narrow Lean and host checks.

Interrupt boundary packet released at `3fbf47d`: exactly the four claimed
files, 443 added lines. The new Lean file fails exactly its three corrected
boundary guards; its five isolated controls pass, a wrong uninterrupted-result
mutant fails that control, and the restored controls pass. The original
interrupt contract and counterexample file both pass unchanged. The durable
historical host reproducer passes all ten runs (five variants, thresholds
1000000 and 3); a scratch mutation deleting the real mask is rejected on the
complete trace, and restoration passes. The scoped four-file citation and
staged diff checks pass. No production, generated target, root import, or
coverage projection was changed. This packet adds no public library theorem;
its new expectations are finite executable probes, not axiom receipts or a
general host bridge. Shared coordination and the later repair remain
coordinator-owned.

## Coordinator region stack-safety implementation, 2026-09-03

The coordinator claims `Effect4/Semantics/RegionSafety.lean` against the
independent frozen packet `fa53b97`, plus its root imports and the D2
reachable-stack status in `docs/TRACE-DAG.md` and the current research plan.
The private proof invariant must match each frame identity to the current
region and its parent chain. Existing admission, runners, Scope, RegionTotal,
the three packet files and prior counterexamples remain unchanged. Closure
requires the exact three public theorems, narrow battery, axiom receipts,
independent ownership-proof review and the applicable build checks.

The same coordinator claims the now-stale stack-proof commentary in
`Effect4/Semantics/RegionDenotation.lean` for a documentation-only correction.
Its semantic definitions and existing theorem bodies stay unchanged.

## Full reification continuation: computed dominator facts, 2026-09-03

Codex independent breaker (`web_semantics`) claims only the three new packet
files below while the separate builder (`algebra_choices`) keeps its actual
CHK proof checkpoint in scratch. The packet will expose computed graph facts,
starting with `idom_index_le`, and only complete further computed obligations
whose frozen statement and trust check are ready. Forest/table/ancestry helpers
remain private. Existing `StructureOrder`, its packet, the pinned graph
algorithm and the CE-018 counterexample remain unchanged.

| File or section | Owner | State |
| --- | --- | --- |
| `test/contracts/structure-computed.contract.md` | Codex independent breaker (`web_semantics`) | new minimal computed-fact declaration record |
| `Effect4Test/Target/TypeScript/StructureComputedContract.lean` | Codex independent breaker (`web_semantics`) | exact universal signatures and nonempty actual-computation controls |
| `Effect4Test/Target/TypeScript/StructureComputedAxiomReport.lean` | Codex independent breaker (`web_semantics`) | trust receipts for the new public facts |

The intended new production module is
`Effect4/Target/TypeScript/StructureDominators.lean`, implemented separately only
after the packet commit. The existing `docs/TRACE-DAG.md` structured-agreement
route owns these derived facts; full transfer/parameter/fuel agreement and
interrupt denotation remain open. The coordinator owns root imports, known-red
wiring, graph status, shared coordination commit and package builds. This
breaker commits only the three packet files and runs narrow Lean checks.

Computed-dominator packet released at `1c65135`: exactly the three claimed
files, 322 added lines. The four frozen public names are `idom_index_le`,
`computed_dominatorFacts`, `emitWith_wellScoped_computed`, and
`skeletonBody_wellScoped_computed`. All 20 existing-meaning controls pass;
the nested-parent-to-entry mutant fails its changed guard and restoration
passes. Import-replaced red tests reach exactly the four missing names, and
the axiom red file rejects the same four constants. The full battery combined
with the builder's trimmed scratch proof passes, with all four public axiom
receipts exactly `[propext, Quot.sound]`. The scoped three-file citation and
staged diff checks pass. No production module, old packet, algorithm,
generated file or root import was changed; no package build or host check ran.
The separate builder may now implement `StructureDominators.lean` against this
packet. Shared coordination and final integration remain coordinator-owned.

## Full reification continuation: computed dominator implementation, 2026-09-03

Codex builder (`algebra_choices`) claims only the new
`Effect4/Target/TypeScript/StructureDominators.lean`, after independent breaker
commit `1c651352c481ea9e61b9c13bbd1c2c278fc24828` froze its four public
theorems and red battery. The builder preserves that packet, existing
`StructureOrder`, the pinned TypeScript graph algorithm and CE-018. All table,
forest, traversal and ancestry helpers remain private. The implementation
proves the two existing computed-parent facts and derives strict lexical
scoping; full T4 transfer/parameter/fuel denotation and interrupt meaning stay
open. Only narrow Lean compilation, the frozen battery and axiom receipts run
here. The coordinator owns root imports, graph/status changes, shared
coordination commit and package builds.

Computed-dominator implementation released at `f7cd8a1`: only the new
`StructureDominators.lean` (1112 lines), final SHA-256
`32f1e6358de56b4bd000aae423310b5f78356b60436af8b1dc986d252affff53`.
Direct narrow Lean compilation, the unchanged frozen computed contract and
its four public axiom receipts pass; every receipt uses only `propext` and
`Quot.sound`. The independent breaker inspected the actual computation,
intersection bound, parent-chain preservation and walk proof, and approved
this four-theorem scope; the only subsequent edit removed a trailing blank
line and the source was rechecked. The frozen packet, earlier order module,
algorithm and CE-018 remained unchanged. Root imports, proper Lake/package
builds, graph status and the shared coordination commit remain
coordinator-owned. The exact computed lexical-placement facts are proved;
full structured/dispatch denotation and interrupt meaning remain open.

## Independent scope-close stepping packet, 2026-09-03

Codex independent breaker (`corpus_measurement`) claims only the three new
packet files below. The coordinator requested a reusable, independently
stepping close component at `Effect4/Runtime/ScopeMachine.lean`; production is
reserved to the separate coordinator builder after this packet is reviewed
and committed. No compiler, Flow decoder, general region simulation, root
import, generated evidence or graph status is changed by this breaker.

| File or section | Owner | State |
| --- | --- | --- |
| `test/contracts/scope-machine.contract.md` | Codex breaker (`corpus_measurement`) | proposed first-order request/response close state, exact APIs and local semantic obligations; root technical review before freeze |
| `Effect4Test/Runtime/ScopeMachineContract.lean` | Codex breaker (`corpus_measurement`) | independent existing-Scope controls, pause/failure attacks and exact new-surface checks |
| `Effect4Test/Runtime/ScopeMachineAxiomReport.lean` | Codex breaker (`corpus_measurement`) | exact public theorem trust receipts |

The packet reuses `E4-RUN-CE-001`, `002`, `003`, `008`, `009` and
`E4-TARGET-CE-019`/`020` as the state-first, LIFO, idempotence, capture/merge,
fixed-exit and live-frontier requirements. Existing Scope, Exit, Cause,
Runtime and all prior contracts/counterexamples remain unchanged. The
coordinator owns the shared coordination commit, production implementation,
graph/coverage status and package/host builds. This breaker runs only narrow
Lean/scratch checks and commits the three claimed packet paths.

Scope-close stepping packet released at `e5a2bdb`: exactly the three claimed
files, 552 added lines. The coordinator approved the exact data fields, APIs,
independent body-value universe, prefix identity/state relation and complete
returned machine/service pair before the freeze. All 27 existing-Scope
controls pass; threaded-exit, abort-after-first and singleton-merge mutants
each fail exactly their intended assertion, and restored controls pass.
Declaration-red reaches exactly 21 missing names and axiom-red exactly ten.
The abstract signature shell type-checks all approved ascriptions and 72
future machine guard expressions without executing or proving the absent
implementation. The three-file citation check and staged diff check pass.
Both real packet checks remain honestly import-red until ScopeMachine exists.
No production, old packet, root import, generated projection or host file was
changed. The separate coordinator may implement `Effect4/Runtime/ScopeMachine.lean`
against this frozen packet; full D4 compilation/prefix, frame/finalizer-program,
host, interruption and parallel-scheduling connections remain open. Shared
coordination and its commit remain coordinator-owned.

## Structured packet proof-trust repair, 2026-09-03

Codex independent breaker (`web_semantics`) claims the proof bodies in
`Effect4Test/Target/TypeScript/StructureOrderContract.lean` and, only if its
helper receipt requires repair,
`Effect4Test/Target/TypeScript/StructureComputedContract.lean`, plus append-only
proof-amendment receipts in their existing `test/contracts/structure-order.contract.md`
and `test/contracts/structure-computed.contract.md`. The coordinator's trust
self-test rejected `terminal_childIndex` for reaching `Classical.choice`.
Every statement, accepted domain, control, public receipt and production file
stays unchanged. The breaker inspects every constant owned by these two
packets, including private concrete-premise proofs, and uses direct
constructive elimination for any impossible branch that introduced choice.
Only affected packet paths will be committed. Shared coordination, the trust
gate and its allowlist, package builds and the full gate rerun remain
coordinator-owned.

The repair is released at `04f28cf`: only
`Effect4Test/Target/TypeScript/StructureOrderContract.lean` and its existing
contract's append-only proof amendment, 36 insertions and 4 deletions. Only
`terminal_childIndex`'s proof body changed; a source comparison confirms the
rest of the Lean packet is identical. Its receipt is now `[propext]`. The
exhaustive ownership-based scratch audit passes all 25 current declarations
in the order, computed and RegionTotal test modules; no computed or RegionTotal
edit was needed. The saved order packet, unchanged computed packet and both
public axiom reports pass. Fresh source control/original-proof mutant/restored
control results are 0/1/0, with the mutant rejected specifically for
`Classical.choice`. The repository citation gate passes (1151 tokens, 2986
files), and the two-file staged diff check passes. Other agents' staged files
were excluded by the explicit `git commit --only` path list. No package build,
full trust self-test, production, gate or allowlist change was performed;
the coordinator owns that rerun and this shared coordination commit.

## Scope-close stepping implementation and integration, 2026-09-03

Codex coordinator claims `Effect4/Runtime/ScopeMachine.lean` after the separate
breaker committed `e5a2bdb835b414ef329c1067ef95bec467dceae6`. The exact data,
operations, ten universal statements and independent battery stay frozen.
The module interprets one request at a time, retains actual replies and
service state, and proves arbitrary-prefix and completed-fold equations.
It imports only existing Scope and stores no function or source runner.
The coordinator also claims the new module's root imports and ownership/edge
entries in `docs/SCOPE-DAG.md`, `docs/TRACE-DAG.md` and the current reification
plan. Existing Scope/Exit/Cause, the frozen packet, runtime census, host
lowering and generic frame machine remain unchanged. Root owns narrow and
package builds, independent review, trust-gate rerun and shared integration.
The full D4 compiler/residual relation, arbitrary finalizer programs, host,
interruption and parallel scheduling edges remain open.

## General structured denotation packet, 2026-09-03

Codex independent breaker (`web_semantics`) claims exactly the three new files
`test/contracts/structure-semantics.contract.md`,
`Effect4Test/Target/TypeScript/StructureSemanticsContract.lean`, and
`Effect4Test/Target/TypeScript/StructureSemanticsAxiomReport.lean`.
The coordinator approved the exact two public theorem signatures proposed
for `Effect4/Target/TypeScript/StructureSemantics.lean`, in namespace
`Effect4.Target.EffectV4`: `skeletonStructured_denote_of_fuelFor_le` and
`skeletonStructured_denote_dispatch_of_emitted`. They compare the actual
successful ordinary-Flow emitter outputs as complete Programs for every tape
and input, with `interrupts = false` and sufficient target fuel explicit.
No flatness, extra graph facts, successful-answer or complete-tape premise is
allowed. All helper declarations in production remain private. The existing
flat theorem, denotations, algorithm and prior packets stay unchanged.
The breaker tests non-flat merges, loops, parallel parameter swaps, frontiers,
mismatches and deliberately corrupted targets; verifies declaration-red and
trust receipts; and commits only the three packet files. The separate builder
waits for that commit before writing its new production module. Shared
coordination, root wiring, proof-graph status and package/full gates remain
coordinator-owned. No region or interruption denotation claim is made here.

Structured-denotation packet released at `33409c6`: exactly the three claimed
files, 385 added lines, parent `e8e3a58568654cfe94cf1da1f2d9fb86a76c921e`.
All 40 independent existing-meaning controls pass. Mutating actual merge
break, nested-loop continue and parallel-swap source targets is rejected at
5, 6 and 2 corresponding semantic guards; restoration passes. Declaration-red
reaches exactly the two missing public names and the first theorem's handler
consumer, while axiom-red rejects those two absent constants. Direct repository
imports separately fail on missing `StructureSemantics.olean`. The full packet
against immutable candidate `f16d64a1` passes; its two public receipts are
`[propext, Quot.sound]`, and the exhaustive current-module scan accepts all 202
candidate/test constants, including private helpers and generated auxiliaries.
The 13 isolated control constants also meet that ceiling. The repository
citation check (1151 tokens, 2990 files) and three-file staged diff check pass.
Existing production, old flat theorem, prior packets, counterexamples and graph
algorithm are unchanged. No package build or host gate ran. The separate
builder may create only the new production module; root imports, graph status,
package/full gates and this shared coordination commit remain coordinator-owned.

## Local proof integration receipt, 2026-09-03

The coordinator implemented and committed `RegionSafety` at
`11e915618b9a1ca3ee04a669cc1a7ddee3dffd62` and `ScopeMachine` at
`abefdb131a6b3153f3193fa6fca250cd7d9ffef1`, each as a separate production-only
commit against its previously frozen independent packet. RegionSafety's three
public equations retain matching region/parent stacks under every checked
entry run; ScopeMachine's ten equations retain complete cleanup prefixes,
actual replies and state and agree with existing Scope close/restore.
The original carriers and frozen assertions are unchanged.

Exact independently accepted source hashes are
`fb1ed8fb86d4bbff6101e344a61cc013a5759b86fb3365d441e2daa0b0e77bfa`
for RegionSafety and
`1189173bca2b6b76e114bc178d1945463e0e862e0faca3d0ed91cf04ddb95979`
for ScopeMachine. Independent receipts are
`/tmp/effect4-region-machine-design/REGION-SAFETY-REVIEW.md` and
`/private/tmp/effect4-scope-machine-review-r1rtmikv/REVIEW.md`. The latter
also rebuilt the reviewed source into a fresh scratch olean before rerunning
the complete battery, excluding stale artifact acceptance.

Root verification on the integrated working tree based at `04f28cf`:

- `lake build Effect4.Semantics.RegionSafety` and its unchanged contract and
  axiom files: exit 0; 31 guards and all three exact universal statements.
- `lake build Effect4.Runtime.ScopeMachine` and its unchanged contract and
  axiom files: exit 0; all 27 existing-owner controls, 72 machine guards and
  ten exact universal statements.
- `lake build Effect4.Target.TypeScript.StructureDominators`, unchanged
  computed battery and axiom report: exit 0; the earlier order/computed
  packets remain intact except the independent proof-only helper repair
  committed at `04f28cf`.
- All thirteen new public semantic receipts use at most `propext` and
  `Quot.sound`. The ScopeMachine request/response/budget/scope group uses only
  `propext`; its four prefix/completion/result/restore theorems use both.
- `lake build`: exit 1 with exactly `Effect4Test.Protocol.ByteParserContract`,
  `Effect4Test.Concurrency.RaceRepresentativeContract` and
  `Effect4Test.Counterexamples.Flow.InterruptMaskBoundary` failing. These are
  the exact three declared red modules; the library and new modules build.
  Log: `/private/tmp/effect4-scope-machine-default-build.log`.
- `scripts/test-trust-gate.sh`: exit 0 after the `terminal_childIndex` repair.
  The fresh temporary tree verifies the exact declared-red set, excludes only
  those three modules, accepts the unmodified and restored controls, and
  rejects the planted partial, unsafe and unadmitted-choice definitions.
  Tokenizer, exact public/private admission, fresh semantic-helper and Expr
  equality/declaration controls also pass. This verifies no trust property for
  the three excluded modules. Log:
  `/private/tmp/effect4-scope-machine-trust-gate.log`.
- `scripts/check-fiber-assurance.sh`: exit 0 for the generated input-digest
  refresh; seven representative and six local supervision edges only. No
  runtime coverage count changed. Log:
  `/private/tmp/reification-fiber-september3-check.log`.
- `scripts/check-internal-citations.sh`: exit 0, 1151 citation tokens in 2987
  files across six trees; lexical check only. `git diff --check`: exit 0.

The general D4 region compiler and residual simulation, arbitrary-program
finalizers, M2 restoration/lowering, remaining host relations, the generated
Scope assurance join, and all other open PLAN phases remain open. No new host
execution is claimed by these local Lean equations. The tracked research
bundle was separately reverified: 55/55 manifest entries, 56 bundle files and
the 151844-byte PDF, with no missing or changed component. No push occurred.

## Scope restoration composition packet, 2026-09-03

Codex independent breaker (`corpus_measurement`) claims the five new files
below after coordinator approval of the exact interp-first adapter and nine
theorem types in `/private/tmp/effect4-scope-restoration-proposal.lean`.

| File | Owner and fence |
| --- | --- |
| `test/contracts/scope-restoration.contract.md` | independent breaker; frozen local composition, source/profile and assurance boundaries |
| `Effect4Test/Runtime/ScopeRestorationContract.lean` | independent breaker; exact approved surface and executable restoration/pause/cleanup controls |
| `Effect4Test/Runtime/ScopeRestorationAxiomReport.lean` | independent breaker; nine public theorem trust receipts |
| `Effect4Test/Counterexamples/Runtime/ScopeRestorationBoundary.lean` | independent breaker; durable named witnesses using existing ScopeMachine and Runtime only |
| `harness/trace/scope-restoration.mjs` | independent breaker; explicit-path, off-pin-rejecting replay of finite real-request/failure/defect host evidence |

The intended production owner is the separate coordinator's future
`Effect4/Runtime/ScopeRestoration.lean`. It adds no carrier and maps only a
completed ScopeMachine restored exit through the real FrameFiber.step after
changing current to Prim.ofExit. Existing ScopeMachine, Scope, Runtime, Exit,
Cause, old assertions and M2 packet stay unchanged. General D4/M2, source/tape
embedding, arbitrary finalizer programs and host equivalence remain open.
Root owns imports, known-red wiring, generator/graph status and package gates.

The breaker also claims append-only `test/counterexamples/REGISTER.md` rows
`E4-RUN-CE-025` and `E4-RUN-CE-026`: the coordinator corrected the initially
proposed IDs to preserve the historical live-stack reservation for 022–024.
The new rows cover pending interruption overwriting an existing failure and
discarding outer cleanup causes after interruption has been delivered.
Only these six packet paths, never this shared coordination file, will be
committed by the breaker.

Scope restoration packet released at `945f729`: exactly the six claimed
paths, 781 insertions. The 27 independent existing-owner guards and five
named counterexample proofs pass; all 41 declarations in their source pass
the ownership-based axiom audit. All 29 future behavior checks also pass
through the existing reference composition (45 declarations audited).
Six separate policy mutants each fail only the intended candidate guard,
and restored controls pass. Declaration-red names exactly ten absent
declarations; axiom-red names exactly nine. The signature shell elaborates
the complete approved surface. Against the coordinator's immutable scratch
candidate, the full saved battery passes 56 guards and exact signatures;
all 167 current-module declarations, including anonymous ascriptions and
private helpers, use at most propext/Quot.sound. The repository's new direct
imports remain honestly red until the production module is saved/built.

The durable host probe passes all 40 cases, labels JavaScript-only fallible
releases separately from legal defects, rejects a changed version and each
of four changed source/runtime pins before imports, then reproduces the
original observations on restoration. The six-file citation and staged
diff checks pass. Scratch receipts are under
`/private/tmp/effect4-scope-restoration-breaker`. Existing production and old
packets remain unchanged. Root owns the new production implementation,
root imports, assurance graph and generated input-digest refresh, package
gates and this shared coordination commit. No full D4/M2 or host agreement
claim is closed by the packet.

## General structured denotation implementation, 2026-09-03

Codex builder (`algebra_choices`) claims only the new
`Effect4/Target/TypeScript/StructureSemantics.lean`, after the independent
breaker packet commit `33409c647cd040ff43659f01eb78083ca23f692b`. The exact
two public statements are `skeletonStructured_denote_of_fuelFor_le` and
`skeletonStructured_denote_dispatch_of_emitted`; every helper stays private.
The immutable checked scratch candidate is SHA-256
`f16d64a1da115d0618844b10919456399d3aed90d4e288a60a7e6b863eacfed9`.
The builder adds an ownership header and removes scratch receipt commands,
preserving the proof and frozen signatures. Existing algorithms, denotations,
flat theorems, contracts and counterexamples stay unchanged. Narrow Lean
checks and independent saved-source review precede this single-file commit.
The coordinator owns imports, graph status, package and trust gates, and the
shared coordination commit. The profile is ordinary checked Flow with
interrupts disabled, actual successful emission and the stated fuel allowance;
region, interruption, rendering and host-semantic bridges remain separate.

The general structured denotation builder released its file fence after
production commit `1ca39de8bd69e6cb0a18a5e817dc0756703934b7`, parent exactly
`33409c647cd040ff43659f01eb78083ca23f692b`. The commit contains only the new
`StructureSemantics.lean` (1076 lines), SHA-256
`bcc228b68ce81f92f20910ad5e41e1adae4d5c967b3395c2651bf4c8e145bae8`.
Independent breaker acceptance compared its saved bytes to the frozen-tested
candidate: only the ownership/profile header and removal of scratch receipt
commands differ. Its fresh saved-module audit ran the unchanged packet and
accepted all 202 production/test-owned constants; both public theorem
closures are exactly `[propext, Quot.sound]`.

Builder narrow checks: direct production Lean exit 0 (1.75s); direct single
module olean emission exit 0 (1.43s); frozen StructureSemanticsContract exit 0
(1.11s); frozen StructureSemanticsAxiomReport exit 0 (0.47s). The old semantic,
order and computed modules, frozen packets and CE-018 are unchanged;
`git diff --check` exits 0. These are complete Program equalities for actual
successfully emitted ordinary Flow, every tape and input, interrupts disabled
and the stated sufficient fuel. Arbitrary merges, loops and parameter moves
are included; lower fuel, regions, interruption, rendering and host execution
are not newly established. Root imports, proof-graph status, proper Lake
module/package builds and full trust gates remain coordinator-owned.

## General structured denotation integration, 2026-09-03

The coordinator claims new StructureSemantics imports in `Effect4.lean` and
`Effect4Test.lean`, and its current equation/profile entries in
`docs/TRACE-DAG.md` and `docs/research/2026-09-03-reification-plan.md`.
Production `1ca39de` and frozen packet `33409c6` remain unchanged. Root's proper
`lake build Effect4.Target.TypeScript.StructureSemantics` and both unchanged
contract/axiom checks pass. The independent saved-source audit accepts all
202 owned production/test declarations and all 40 controls; each of the two
public equations uses only `propext` and `Quot.sound`. Package and current
root trust integration are pending the concurrently frozen ScopeRestoration
module, so its temporary missing import is not mistaken for a completed gate.

## Scope restoration implementation, 2026-09-03

The coordinator claims only new `Effect4/Runtime/ScopeRestoration.lean` after
independent breaker commit `945f729` froze the ten-name surface and nine exact
universal statements. The checked candidate SHA-256 is
`e10e40f2059a43bcd2688c0e5cd4715219bb614e94d2168333792583cf957caa`.
Only the namespace-approved implementation, ownership comments and removal of
scratch print commands are promoted. Existing ScopeMachine, Runtime, Scope,
Exit, Cause, the frozen packet and host probe remain unchanged. Root also
claims the new imports and local connection receipts in `Effect4.lean`,
`Effect4Test.lean`, `docs/SCOPE-DAG.md`, `docs/TRACE-DAG.md` and the reification
plan, plus the mechanical REGISTER digest refresh in fiber assurance.
Independent saved-source review precedes production commit. Default build,
trust, host-probe and drift checks remain root-owned; general M2/D4 and the
three declared unfinished modules remain open.

## Coordinator hand-off and integration, 2026-09-03

Codex's pipeline is finished for this cycle; the operator handed the tree to
the Claude coordinator. This commit lands the integration Codex left staged in
the working tree: root imports for `Effect4/Runtime/ScopeRestoration.lean` and
`Effect4/Target/TypeScript/StructureSemantics.lean` with their three
batteries, the `SCOPE-DAG`/`TRACE-DAG`/plan rows, the regenerated
`generated/fiber-assurance.tsv` provenance, and the standards-survey digest
manifest under `docs/research/2026-09-02-standards-sources/`. Verified before
committing: `lake build Effect4` green (136 jobs) and all five batteries
elaborate within `propext`/`Quot.sound`. One sweep over the whole tree follows.
## Independent live-stack breaker claim, 2026-09-03

Codex's separate live-stack breaker claims the following packet only in this
isolated worktree, based at `bfda8d8bd25929662f89a036efc231769adcc88d` on
`codex/live-stack-integration`:

- `test/contracts/live-stack.contract.md` and `docs/LIVE-STACK-DAG.md`;
- `Effect4Test/Runtime/LiveStackContract.lean` and
  `Effect4Test/Runtime/LiveStackAxiomReport.lean`;
- `Effect4Test/Counterexamples/Runtime/LiveStack.lean`;
- a declaration-free `Effect4/Runtime/LiveStack.lean` stub;
- new LiveStack import lines in `Effect4.lean` and `Effect4Test.lean`;
- new LiveStack entries in `test/fixtures/trust-gate/known-red.txt`; and
- the new `E4-RUN-CE-022` through `E4-RUN-CE-024` rows in
  `test/counterexamples/REGISTER.md`.

The builder owns the later implementation and host harness. The frozen
contract distinguishes whole-`FramePop` agreement with the existing pop loop
from the source's deferred-first entry. It retains a masked deferred answer
and records the event when an unmasked answer is discarded; compatibility
with the old entry is guarded, while false-skip compatibility is unrestricted.
The while-law fixes the inner-call/outer-loop relationship and event order.
No new primitive or fiber carrier, asynchronous execution, scheduler
simulation or default-runtime switch is admitted. `Runtime.lean`, every
pre-existing frame packet, dependency pins and generated assurance remain
unchanged. The main checkout is not edited by this breaker.

The new stub and nine counterexample theorems build; all counterexample
receipts are within `propext`. The contract has only the recorded missing-name
errors and the two resulting unavailable-evaluation diagnostics; its independent
13-case pop positive control passes. The axiom report has eight missing-name
errors. Exact diagnostics, test counts and source hashes are frozen in
`test/contracts/live-stack.contract.md`. The two new red modules are declared.

## Live-stack builders, 2026-09-03

The independent packet is committed at `8323eaf`. Root owns only
`Effect4/Runtime/LiveStack.lean`, `scripts/check-live-stack.mjs`,
`docs/LIVE-STACK-IMPLEMENTATION.md`, and removal of the two new
known-red entries once green. The host builder owns
`harness/live-stack/public.ts`, `harness/live-stack/host.mjs` and
`harness/live-stack/HOST.md`; the compiled inspection builder owns
`harness/live-stack/Inspect.lean` and `harness/live-stack/inspect.mjs`.
The mutation builder owns `scripts/test-live-stack-mutations.mjs` only.
Root also claims the new `generated/live-stack-assurance.json` projection,
written only by `scripts/check-live-stack.mjs --write`. Existing generated
files remain outside this claim. The projection records checked declarations,
proof dependencies and finite host observations; it cannot close the open
source simulation or authorize a default-runtime switch.
The frozen contract, DAG and test files remain unchanged. All work is in
this isolated branch; no builder switches or edits the shared main checkout.

## Live-stack implementation verification, 2026-09-03

The eight frozen public declarations are implemented without changing the
contract, DAG, battery or existing carriers. Both complete local checks
(`check-live-stack.mjs --write` and a separate fresh drift run) passed;
`generated/live-stack-assurance.json` has digest
`88b983b638016ba9c9a62a59ed3569a340eddef149790ecabe013412de491d85`.
The independent review's three checker findings were repaired and verified.
The trust self-test passed on its declared-red-excised temporary copy. The
default package build still has the two old declared-red failures and their
consequential root diagnostic; the separate Fiber projection and four
pre-existing citation errors remain open. `docs/LIVE-STACK-IMPLEMENTATION.md`
records exact evidence and the still-open source/compiler/scheduler edges.
No shared main-checkout source or default runtime was changed.

## Live-stack branch merged and re-pinned, 2026-09-03

`codex/live-stack-integration` (two commits, never merged) is merged: the
`LiveStack` runtime module, its three batteries, `docs/LIVE-STACK-*.md`, the
host harness under `harness/live-stack/`, its gate and mutation self-test, and
register rows `E4-RUN-CE-022..024`. The library builds and the batteries
elaborate within the ceiling. The gate's frozen-input table had drifted on four
files that packet D4 fence A extended additively after the fork
(`Effect4/Runtime/Runtime.lean`, `docs/FRAMES-DAG.md`, the frames contract and
axiom report); their digests, the contract's own digest, and the declared-red
assertion (now "no live-stack module is red, both historical orphans are") are
re-pinned, and `generated/live-stack-assurance.json` regenerated with
`--write`. `node scripts/check-live-stack.mjs` reports `local-pass` against the
pinned install (`EFFECT4_EFFECT_NODE_MODULES`, as `harness/live-stack/HOST.md`
documents; the repo has no `node_modules`).

## M2 repair landed: restoration in the runner, the mask in the lowering, 2026-09-03

Against the independent amendment (`3fbf47d`, `E4-FLOW-CE-024`/`025`):

- `Effect4/Flow/Interrupt.lean`: a `leave` whose remaining stack is unmasked
  delivers a pending interrupt at once — no continuation, no fresh point, no
  tape read — and a `ret` with a pending interrupt is delivered likewise. The
  three guards of `InterruptMaskBoundary.lean` are green and the module leaves
  `known-red.txt`; the historical `decide 1000009` expectations in
  `InterruptContract.lean` and `Counterexamples/Flow/Interrupt.lean` are
  amended as the appendix requires, and the appendix records acceptance.
- lean4-typescript v0.4.2 (`31665ff`, tagged locally; the push to GitHub is
  pending operator approval — the manifest already pins the commit):
  `Stmt.scopedGenMasked` renders `Effect.uninterruptible(Effect.scoped(...))`.
- `Skeleton.enterScopedMasked` / `Lowering.regionEnterMasked`, rule
  `region-masked` (twenty-six rules), emitted by both forms for a region in
  `RegionProgram.masked`; `StructureLaws` covers the new node.
- `harness/trace/interrupt-tail.ts` no longer emulates the mask: it requests
  the interrupt wherever the tape answers, and rc.112 defers and restores.
  Goldens, fixtures and receipts regenerated; the host gate passes every golden
  under every mask at both yield settings; the ledger is current.

## Job runner landed, 2026-09-03

The packet's "first real program": a resource-managed job runner, written in
Lean as a region flow, lowered by the existing pipeline, and run against a real
host service. Full account and every gap:
`docs/research/2026-09-03-job-runner.md`; `job-runner` row in
`docs/TRACE-DAG.md`.

- `harness/trace/Generate.lean`: family `Jobs` (`connect` answering an opaque
  `Handle "JobQueue"`, `next`, `run` aborting, `attempt` in the data reading of
  the same error, `ack`, `requeue`, `disconnect`), a `Queue` handler over
  pending/acked/requeued jobs and a per-job failure schedule, the region flows
  `jobRunnerFlow` (seventeen blocks, one region, three decision sites) and
  `jobPoisonFlow`, three lowered programs (`jobRunner`, `jobRunnerMasked` with
  region 1 uninterruptible, `jobPoison`), and six golden entries. New arms:
  `job-fixture`, `job-programs`, `job-golden <program> <golden>`, `job-types`,
  `job-queues`; usage string extended.
- Host: `harness/trace/job-queue.ts` (the queue is a JSON file in a temporary
  directory, written and read with `node:fs` on every operation; `disconnect`
  deletes the directory) and `harness/trace/job-tail.ts` (`attempt` and `run`
  wait on `Effect.sleep`; the tail reports `released`). `dec` added to
  `harness/trace/atoms.ts`. `harness/trace/job-fixture.ts` generated.
- Six goldens under `generated/traces/job/`: a clean drain of three jobs, a job
  that fails once and succeeds on retry, a job requeued after exhausting its
  retries, an interrupt delivered mid-queue with the release still running, the
  same delivery inside the masked critical section (deferred, delivered at the
  leave, per the M2 repair), and the aborting `run` closing the region with its
  failure. All six agree with rc.112 under `outcome`, `m1` and `m2` at the
  default yield setting and at `EFFECT4_MAX_OPS=3 EFFECT4_EXPECT_YIELDS=1`;
  receipts under `harness/trace/receipts/job/`. `released` is `true` on every
  golden.
- First goldens carrying two tapes on one wire: the choice sites are below
  `Effect4.Flow.interruptBase` and every interrupt site at or above it, so
  `job-tail.ts` splits `EFFECT4_TAPE` by site into the `Decisions` reader and
  the `Interrupts` reader.
- Lean receipts: `Effect4Test/Flow/JobRunnerContract.lean` (the exact rows of
  all six goldens inline, admission of both graphs, `sitesSeparated`, the final
  queue of each run, the refusals, axiom report `propext`/`Quot.sound`).
- Gaps filed: `E4-TARGET-CE-022` (a two-parameter operation has no flow
  request: `familyTable` writes `"unsupported"` and `Lowering.callOf` emits one
  argument, so the packet's `run : Handle × Nat → …` had to become
  `run : Nat → …`), `E4-FLOW-CE-026` (an aborting operation ends the run, so
  retry-after-failure needs the data reading of the error), `E4-FLOW-CE-027` (a
  flow never branches on a value: the queue-empty test and the retry bound are
  tape questions and the carried attempt budget cannot be compared). Witnesses:
  `Effect4Test/Counterexamples/Target/JobRequest.lean`,
  `Effect4Test/Counterexamples/Flow/JobRunner.lean`. Recorded without a row: a
  region hands back exactly one value (`RegionClause.continueTyped`), so a
  masked critical section *inside* the drain has no spelling and the whole
  region is masked instead.
- Refuted: "the interrupt tape is per program not per job" is only half true.
  `interruptRead` consumes the head entry only on a site match, so a
  non-delivering entry at a site moves delivery to the next occurrence of that
  site — which is how the mid-queue golden interrupts the second job. A tape
  still names a control point and never the job the run holds at it.
- `scripts/generate-trace-goldens.sh` and `scripts/check-trace-host.sh` gained
  their `job` sections; neither was run by this packet. **`Generate.lean`
  changed, so every existing golden's `input harness/trace/Generate.lean`
  provenance digest is stale**: the coordinator should run
  `./scripts/generate-trace-goldens.sh` once. The job goldens already carry the
  digests that run will write.
## Deferreds family landed, 2026-09-03

`effect_signature Deferreds` (`harness/trace/Generate.lean`) is the third
handle-carrying family, after M1's `Scopes` and M3's `Fibers`, and the first
whose operations may have no answer at all. Seven operations — `make`,
`succeed`, `fail`, `isDone`, `poll`, `awaitValue`, `awaitError` — over real
rc.112 `Deferred` objects, with six programs and six goldens under
`generated/traces/deferred/`. Every program agrees on the host under every mask
at both yield settings, including the rc.112 floor of 3; receipts under
`harness/trace/receipts/deferred/`.

Three things worth citing.

*The handle needed nothing new.* M1's `Handle "T"` carried this family
unchanged: `Handle "Deferred.Deferred<number, number>"`, an index in Lean, the
index on the wire, rc.112's own type on the target, and `registerHandle` in
`deferred-tail.ts` branding cells by `"~effect/Deferred"` so the tracer numbers
them in the `make` order the Lean face uses. The one DSL repair this packet
owed was a paren case in `tsOfTypeFuel`: a nested spelling is written
`Option (Except Nat Nat)`, and the parentheses were being read as a type former
the profile had no name for.

*`poll` is one operation answering `Option (Except Nat Nat)`.* That is exactly
the type of a cell of the projection's table — pending, completed with a value,
completed with a failure — so the answer of `poll` and the state of the
projection are the same first-order datum and the wire form falls out of the
shared `ToVal` instances with no encoding to document. A `(Bool, Nat)` pair
cannot separate a pending cell from one completed with the failure `0`; a
`pollDone`/`pollValue` split would make `pollValue` on a pending cell a
frontier rc.112 does not have. It is the first spelling to nest one namespace
inside another (`Option.Option<Result.Result<number, number>>`), which is a
question for the *value* import trigger: `usesResult` tests a prefix, and this
spelling does not start with `Result.`, so the trigger stays false and `Option`
and `Result` reach the generated module through the same type-only import
`Scopes` and `Fibers` use for `Scope` and `Fiber`. `EffectV4.lean` is untouched
and all five earlier fixtures regenerate byte-identically. A family that ever
needs one of those namespaces as a *value* will have to widen the trigger from
a prefix test to an occurrence test; nothing does yet.

*A pending await is a frontier, not a failure.* rc.112's `Deferred.await`
parks the fiber until another one completes the cell (`Deferred.ts` `_await`
pushes a resume onto `self.resumes`). The sequential projection has no other
fiber, so both faces stop there and write `frontier`: the projection because
`deferredsTraced` writes no `failed` row for a stall — which is why it does not
use `Family.Service.tracedExcept`, whose every abort is a `failed` row — and
the host because the new `RunOptions.stallMs` in `harness/trace/tracer.ts`
interrupts a run that has parked. The op budget cannot reach a parked run: it
fires from inside `Tracer.context`, and a parked fiber evaluates no primitive.
`stallMs` sits beside M3's `armed` and is passed by one program only; every
other tail leaves it out and must still settle on its own.

Rows `E4-SEM-CE-012` (the failure reading collapses a stalled run into a
genuine failure under *every* mask, so no host comparison could catch it) and
`E4-SEM-CE-013` (no function of the projection's table separates the parked run
from the one a second fiber resumes), witnessed in
`Effect4Test/Counterexamples/Flow/Deferreds.lean`.

Owed, and handed on: the two-fiber program in which a forked child completes
the cell the parent awaits. It is still not spellable now that `Fibers` exists.
`effect_program` binds one family per program (`… over <family>`), and `Fibers`
has no former for a child that performs operations of its own — its bodies are
numbers drawn from `bodyOutcome` — so a `Fibers`-only variant cannot express it
either. Writing it needs either a two-family program or a `Fibers` child whose
body is a program over another family; whichever lands first should claim
`E4-SEM-CE-013`. `deferredPendingAwait` records the half the projection can
see. The note sits on `DeferredEntry` in `harness/trace/Generate.lean`.

One gate line still open: `scripts/check-lowering-types.sh` does not read the
`deferred-types` arm this packet added to `Generate.lean`, the way it does not
yet read `scope-types` or `fiber-types` either. Two of the six declaration
lines are frozen inline as `#guard`s in the contract meanwhile.
## Refs family landed, 2026-09-03

`Refs` is the second lane over an opaque host handle after M1's `Scopes`, and
the one where the handle is the whole of what the family owns.
`Handle "Ref.Ref<number>"` prints rc.112's own type, so `harness/trace/ref-tail.ts`
keeps **no store**: `make` is `Ref.make`, `get` is `Ref.get`, and so on down the
row; the ref objects go straight through and `tracer.ts`'s `registerHandle`
indexes them. That is the whole benefit of building on M1 — my pre-rebase draft
carried a hand-rolled index table on both faces, and none of it is needed.

Corpus in `Effect4/Stateful/RefFamily.lean`, following M3's precedent
(`Effect4/Concurrency/FiberFamily.lean`) rather than M1's harness-local one:
`Effect4Test/Flow/RefsContract.lean` then guards the *imported* corpus, so a
second copy of the handler cannot drift from the goldens while every receipt
still passes. `Effect4/Stateful/Ref.lean` is untouched — still a breadth stub,
still someone else's to freeze.

Seven programs: make-get, set-get, update twice, `modify` answering the old
value, `getAndSet`, two handles interleaved, and `takeUnderflow` over a second
family `ERefs` whose `tryTake` refuses rather than underflowing — the refusal is
an answer, not an abort, and the read after it is unaffected.

**Host agreement, run directly (no gate script):**
`EFFECT4_PROGRAM=<p> node ~/Dev/effect4-tools/packages/harness/trace.mjs harness/trace --golden generated/traces/ref/<p>.tsv --masks generated/traces/masks.tsv --tail ref-tail.ts`.
All seven agree under `outcome`, `m1` and `m2`, at the default yield threshold
and at `EFFECT4_MAX_OPS=3 EFFECT4_EXPECT_YIELDS=1`. `tsc.original` and
`effect-tsgo --strict` both accept the extended file set (0 diagnostics over 15
files), and every `ref-types` line is emitted byte-identically by the pinned
compiler. Following M1's `scope-types` precedent that arm is **not** wired into
`scripts/check-lowering-types.sh`, which still covers only `types` and
`flow-types`.

Two register rows, `E4-SEM-CE-014` and `E4-SEM-CE-015`, witnessed by
`Effect4Test/Counterexamples/Runtime/Refs.lean`.

**012 is a constraint on M1's machinery that anyone adding a third handle lane
needs.** `tracer.ts`'s `nextHandleIndex` is *one* module-global counter over
every branded object, while a Lean face numbers each family's handles from 0 in
its own store. With both `~effect/Ref` and `~effect/Scope` branded,
`harness/trace/ref-probe.mjs` prints `first scope -> 1`, `next ref -> 2` where a
per-family store would say 0. First-seen order equals creation order only within
one branded type. `ref-tail.ts` brands one; `scope-tail.ts` brands one; a tail
that brands two must reconcile the counters before its goldens mean anything.

**013 matters for anyone writing a golden.** When an operation's answer and its
new state share a type, the *type* separates nothing: `Ref.modify` with its
tuple swapped is accepted by the pinned compiler with zero diagnostics, and only
a golden with a non-zero amount catches it. `ERefs.tryTake` is the contrasting
half — differently-typed components, so the compiler does pin the order.

**A probe, not a gate.** `harness/trace/ref-probe.mjs` records what rc.112
actually answers under each declaration; nothing imports it and no script runs
it. It earned its keep by killing a claim I had written into a docstring — that
`Ref.update` leaks the new number under `Effect<void>`. It does not: it is a
block-bodied arrow and answers `undefined`, which is exactly what the census row
`ref.update` has said since `b11ef32`. I had not seen that row, because the
worktree I was given predated the census re-pin; the rebase would have caught
the error a second time. Worth stating plainly: **the ten `ref.*` census rows
are the reading of record for this lane** — `ref.set-void-returns-cell`,
`ref.cell-set-returns-self`, `ref.update` and `ref.modify` between them already
pin everything the probe re-observed. Check them before writing a claim about
rc.112's ref semantics.

What survives as this packet's own finding is the pair, not either half: two
`void`-declared operations of one rc.112 module disagree about their runtime
answer (`Ref.set` hands back the `MutableRef`, `Ref.update` hands back
`undefined`). That is a sharper argument for TRACE-DAG separation 7 than the
single observation it was minted from — no runtime-value heuristic could cover
both, so the typed rule is not a convenience.

**Goldens.** Only `generated/traces/ref/*.tsv` (7, new) were written, against
main's generator. The pre-existing goldens' provenance rows are deliberately
**not** refreshed here even though `Generate.lean`, `Effect4.lean` and
`generate-trace-goldens.sh` all changed — that is the coordinator's sweep.

**Files.** New: `Effect4/Stateful/RefFamily.lean`, `Effect4Test/Flow/RefsContract.lean`,
`Effect4Test/Flow/RefsAxiomReport.lean`, `Effect4Test/Counterexamples/Runtime/Refs.lean`,
`harness/trace/ref-fixture.ts`, `harness/trace/ref-tail.ts`,
`harness/trace/ref-probe.mjs`, `generated/traces/ref/*.tsv`. Modified:
`Effect4.lean`, `Effect4Test.lean`, `harness/trace/Generate.lean` (four `ref-*`
arms before the one usage arm, and that arm's string), `harness/trace/tsconfig.json`,
`scripts/check-trace-host.sh` (a `ref` section before the one closing `echo PASS`),
`scripts/generate-trace-goldens.sh`, `docs/TRACE-DAG.md` (new `refs` edge row),
`test/counterexamples/REGISTER.md`. `atoms.ts` needed no change: the ref scripts
call the `succ` that is already there.

**Census.** Not touched. `docs/RUNTIME-COVERAGE.md` gives the census no
`observed` column — the denominator is anchored spans of the vendored pin and
the only sanctioned witness is a Lean theorem in
`Effect4Test/Audit/RuntimeCoverage.lean`. Host agreement under a mask is not a
witness in that vocabulary and should not be smuggled in as one. Main already
carries ten `ref.*` rows from `b11ef32`/`9585fce`, so there was nothing to add
to the denominator either. Six of them are the behaviours these goldens now
exercise end to end — `ref.make`, `ref.get`, `ref.set-void-returns-cell`,
`ref.update`, `ref.modify`, `ref.get-and-set` — and that is worth knowing for
whoever attaches numerator witnesses: the executable evidence exists, it is
simply host evidence and so belongs in the receipts under
`harness/trace/receipts/ref/`, not in `Effect4Test/Audit/RuntimeCoverage.lean`.
The four rows about `setAndGet`, `modifySome`, `updateSomeAndGet` and
`MutableRef.set` are untouched by this lane: none of those calls is an operation
of the family.
## Answer profile widened, 2026-09-03

The declared answer-type profile is reified and goes to depth three, and a pure
atom is now one declaration with every face derived from it.

**The profile.** `Effect4/Target/TypeScript/EffectV4.lean` gains `Spelling`, the
type spellings both faces know, with `render` (the TypeScript spelling), `depth`
(constructor nesting), `profileDepth = 3`, `admitted`, `wireDefault` (the wire
inhabitant) and `namespacesOf` (which `effect` namespaces a spelling needs, at
any depth — a prefix test missed `Result` inside `Option.Option<…>`).
`effect_signature` no longer holds a private string function: it parses Lean
type syntax into a `Spelling` and reads the rest from the profile. Parentheses
are now transparent to that parser and `×` is admitted, which is what capped the
DSL at depth two. Newly admitted, with their spellings:
`Option (Except E A)` → `Option.Option<Result.Result<A, E>>`,
`Except E (Option A)` → `Result.Result<Option.Option<A>, E>`,
`List (A × B)` → `ReadonlyArray<readonly [A, B]>`,
`Option (A × B)` → `Option.Option<readonly [A, B]>`,
`A × Except E B` → `readonly [A, Result.Result<B, E>]`. `Handle "T"` stays
depth one. Depth four is refused with its depth in the message; a type outside
the grammar is refused as before. Both refusals are pinned by `#guard_msgs`.

This retires the first half of the M3 refusal note above: `Option (Except Nat
Nat)`, the shape of an rc.112 `Exit`, is now a spelling the DSL has. Retiring
the `awaitValue`/`awaitError` pair that stands in for it would move the
`Fibers` goldens and is left to whoever owns that family. The second half
stands: `await` is still a reserved word in the binding profile.

**The host side.** `harness/trace/tracer.ts` `wireAnswer` now parses the row's
declared spelling and encodes at it (`parseSpelling`, `wireTyped`) instead of
reading the shape of the host value. Above depth two the value is not enough
information — a pair and a list are both JavaScript arrays — which is row
`E4-TARGET-CE-024`. A spelling outside the profile (a `Handle`'s target type)
falls back to the untyped encoder, whose handle branch indexes the object, and
`void` still answers unit whatever the host hands back (separation 7). The
`Scopes` and `Fibers` goldens are unaffected and were re-run to confirm it.

**Atoms.** `effect_atoms X where | succ (n : Nat) : Nat ⟪ "n + 1" ⟫ := n + 1`
emits the Lean function, `X.rows : List AtomRow`, `X.table` (the flow
embedding's `AtomTable`), `X.eval : String → Val → Val` (the wire dispatcher,
built from the new `OfVal` class, the converse of `ToVal`) and `X.source`, the
generated `atoms.ts`. `harness/trace/atoms.ts` is now generated and
byte-compared by `scripts/check-trace-host.sh` beside the five module fixtures.
Declaring an atom in one face only is `E4-TARGET-CE-025`. `OfVal` is the
decoding direction row `E4-TARGET-CE-016` says the DSL lacked; it is partial,
so that row stays open — nothing about `denoteScript` is closed by it.

The binding profile also gained `reservedExtra`: `TypeScript.reservedIdentifiers`
(lean4-typescript v0.4.2) carries the ECMAScript reserved words but not the
predefined names, so `bindingName` refuses `arguments`, `eval`, `undefined`,
`NaN` and `Infinity` on top of it.

**Corpus.** A fifth straight-line program: family `Tri` with
`lookup : Nat → Option (Except String Nat)`, program `probe`, golden
`generated/traces/probe.empty.tsv`, atom `firstOr`. The host agrees with it
under every mask:

```text
EFFECT4_PROGRAM=probe node ../effect4-tools/packages/harness/trace.mjs harness/trace \
  --golden generated/traces/probe.empty.tsv --masks generated/traces/masks.tsv --tail tail.ts
trace probe.empty mask outcome ok (1 rows)
trace probe.empty mask m1 ok (5 rows)
trace probe.empty mask m2 ok (5 rows)
```

**For the sweep.** `Effect4/Meta/Derive.lean` changed, and its digest is a
provenance input of every golden under `generated/traces/`, so **every**
golden's provenance block is stale and must be regenerated
(`./scripts/generate-trace-goldens.sh`). No golden *body* moved: a full
regeneration into a scratch directory was compared row-for-row against the
thirty-three committed files and only the digest lines differ. Only
`probe.empty.tsv` was written by this packet; the other thirty-three were
deliberately left untouched so the regeneration is one commit in the sweep
rather than a conflict in every branch. The five generated modules
(`fixture.ts`, `flow-fixture.ts`, `structured-fixture.ts`, `scope-fixture.ts`,
`fiber-fixture.ts`) regenerate byte-identically apart from `fixture.ts`, which
gains the `Tri` class and `probe`; `harness/trace/atoms.ts` is current.
`generated/lowering-coverage.tsv` was left untouched for the same reason as the
goldens: it digests `Effect4/Target/TypeScript/EffectV4.lean` and the goldens it
claims, so it has to be regenerated after them, not before. No lowering rule was
added or removed — `probe` exercises `service-acquire`, `perform-call`,
`perform-bind`, `perform-discard`, `ret` and `atom-call`.

Packet: `test/contracts/answer-profile.contract.md`; batteries
`Effect4Test/Target/TypeScript/AnswerProfileContract.lean` and
`Effect4Test/Counterexamples/Target/AnswerProfile.lean`; rows
`E4-TARGET-CE-024` and `E4-TARGET-CE-025`.
## Layers family landed, 2026-09-03

Packet M4. `Layers` is the fourth traced family, built on the `Scopes` (M1) and
`Fibers` (M3) shape: the family, its handler and its programs are a library
module, `harness/trace/Generate.lean` only renders them, and the host tail is
compared against the goldens under every mask.

Landed:

- `Effect4/Layer/LayerFamily.lean` (new, routed from `Effect4.lean`):
  `effect_signature Layers` with `build`, `provideCount`, `scopeOf`, `close`
  over a memo-table handler, eight `effect_program`s, `layerGoldenLog`,
  `layerPrograms`, and eight `rfl` clauses. It declares no semantic object on
  behalf of `Effect4/Layer/Memo.lean`, which stays the empty owner of build
  identity as a semantic object; a family is a signature, a first-order handler
  and the rows that render it.
- `harness/trace/layer-fixture.ts` (generated, byte-compared),
  `harness/trace/layer-tail.ts`, `generated/traces/layer/*.tsv` (eight),
  a `layer` section in `scripts/check-trace-host.sh` and generation lines in
  `scripts/generate-trace-goldens.sh`, and `layer-fixture` / `layer-programs` /
  `layer-golden` / `layer-types` arms in `Generate.lean`.
- `Effect4Test/Flow/LayersContract.lean`,
  `Effect4Test/Flow/LayersAxiomReport.lean` (all eight clauses axiom-free),
  `Effect4Test/Counterexamples/Semantics/Layers.lean`, rows
  `E4-SEM-CE-016`..`015`, the `layers` row of `docs/TRACE-DAG.md`.

### Two decisions worth not rediscovering

- **Release is an answer, not a `finalizer` row.** The packet allowed either.
  `Family.Service.traced` is an around-wrapper over a handler in `M`: it writes
  one `op` and one `answer` per operation and cannot reach `M`'s state, so a
  family that keeps the derived tracer cannot emit region or finalizer events
  at all. `Layers.close` therefore answers *the services it released, in
  release order*, which is exactly what `Scopes.close` does with the keys it
  ran. Emitting `finalizer` rows would have meant a bespoke traced handler and
  giving up `interpret_traced_fst` on this family.
- **The build handle is the service object, not the `Context`.**
  `buildWithMemoMap` maps `Context.add(CurrentMemoMap, memoMap)` over the
  built context (`layer.build-with-memo-map-service`), so the `Context` wrapper
  is a *fresh object on every build* while the service inside it is replayed
  unchanged by the memo entry. Probed on the pinned install before the family
  was written; a handle on the `Context` would have made every memo hit look
  like a construction.

### One additive DSL change

`Effect4/Meta/Derive.lean`'s `tsOfTypeFuel` now matches its heads by the *last
component of the name as written* rather than by quotation patterns, and strips
parentheses. An ident's preresolution depends on the enclosing namespace, so
`` `(Handle $s:str) `` matched only where the DSL was used at the top level —
`Generate.lean` — and failed inside `namespace Effect4.LayerFamily` with
"unsupported type syntax" pointing at the string literal. The same change is
what admits `List (Handle "T")` as an answer. `Except`, `Option` and `List` are
matched the same way now; no spelling changed, and `fixture.ts`,
`flow-fixture.ts` and `scope-fixture.ts` regenerate byte-identically.

### Follow-up, not done here

`harness/trace/patched/patch-manifest.json` already carries a `layer.memo-build`
hunk that fires once per `memoMapBuild`. Pairing it with the layer goldens would
give a frame-level cross-check of the construction count — the number of
`layer.memo-build` frames under a patched run should equal the total of
`provideCount` at the end of each program. It is **not** done here and the
manifest is untouched: the frame stream is not an emitter of this alphabet
(`bridges` is `required-open`), so the pairing would be a new kind of receipt,
not an extension of an existing one. Whoever takes it should also decide
whether `scripts/check-trace-patched.sh` grows a `layer` assertion beside its
three scope facts.

### Claims

Released with this commit: `Effect4/Layer/LayerFamily.lean`,
`harness/trace/layer-*.ts`, `generated/traces/layer/**`,
`Effect4Test/Flow/Layers*.lean`,
`Effect4Test/Counterexamples/Semantics/Layers.lean`, the `layer` sections of
both trace scripts, the `E4-SEM-CE-016`..`015` rows, the `layers` row of
`docs/TRACE-DAG.md`, and the `Effect4.lean` / `Effect4Test.lean` import lines
for the above. `Effect4/Meta/Derive.lean` was edited additively under the
existing trace-lane claim. `Effect4/Layer/Memo.lean` and `Effect4/Layer/Laws.lean`
were not touched and remain unclaimed stubs.

## Multi-argument operations landed, 2026-09-03

`E4-TARGET-CE-022` is repaired. A family operation of two or more parameters is
now performed by a flow, and the job runner runs the packet's own signatures:
`run : Handle × Nat → Nat !! String`, `ack : Handle × Nat → Unit`,
`requeue : Handle × Nat → Unit`.

### What changed, and what deliberately did not

The flow alphabet and `plan` are untouched. An operation of `n` parameters is
performed with **one** request `Var` whose value is the right-nested pair
`Effects.Trace.ToVal` builds from the parameter product — the same nesting on
both faces, and the same spelling `Spelling.prod` renders.

* `Effect4/Target/TypeScript/ScriptFlow.lean`: `OpSpec` carries the row's
  parameters, `OpSpec.arity` is the call's argument count, and `familyTable`
  spells every request through the new `requestSpelling`. The string
  `"unsupported"` is gone.
* `Effect4/Target/TypeScript/Skeleton.lean`: `Lowering.tupleArgs` is the
  projection (`lowering: rule.perform-tuple`) and `Lowering.callOf` selects it
  by arity, so `jobs.ack(b10p3[0], b10p3[1])` is emitted over
  `let b10p3!: readonly [JobQueue, number]` while a one-parameter operation
  lowers to the bytes it lowered to before.
* `Effect4/Target/TypeScript/Lower.lean`: `Rule.performTuple`, **appended last**
  in `Rule.all` (26 → 27) so the three positional windows the contract batteries
  pin do not move. `FlowLower.ruleSet` emits it; `LoweringCoverage.lean` carries
  its row, `pinned` on the job goldens.
* `Effect4/Target/TypeScript/EffectV4.lean`: `Spelling.arity`, and
  `OpRow.answerArity`, which `rowsDecl` writes **only when it is above one** —
  so every pre-existing fixture regenerates byte-identically (`cmp`-verified
  against `fixture`, `flow-fixture`, `structured-fixture`, `scope-fixture`,
  `fiber-fixture`, `deferred-fixture`, `ref-fixture` and `layer-fixture`).
* `harness/trace/tracer.ts` encodes a tuple answer positionally from
  `answerArity`. It has to: `readonly [JobQueue, number]` does not parse,
  because a `Handle` target is outside the wire grammar on purpose, and `wire`
  would otherwise read the host array as a list.
* `Effect4/Meta/Derive.lean`: `effect_atoms` takes an optional
  `importing handles [T] from "./m.ts"` clause, because an atom over a host
  handle names a type `atoms.ts` cannot work out for itself. `atomsModule` takes
  the imports. There is also an `OfVal` instance for `Handle`.

### The residual limit, and why the job runner looks like this

A flow still cannot **build** a pair: `perform` names one request `Var`, a
literal answers a constant, an atom is a unary wire function. A two-parameter
request can only occupy a slot some *answer* already filled. So `Jobs.next`
answers a **job ticket** — the connection and the job id — `run`, `ack` and
`requeue` take that ticket whole, and a new unary atom `snd` takes it apart for
the one-parameter `attempt`. That is `E4-FLOW-CE-028`, witness `unpairedRaw` in
`Effect4Test/Counterexamples/Target/JobRequest.lean`, whose forced repair is a
pairing former in `RawTerm`/`RegionTerm` with arms in both runners, all three
lowerings and the admission clause that types it.

### Receipts

The six `generated/traces/job/*.tsv` bodies and `harness/trace/job-fixture.ts`
are regenerated (provenance headers untouched, as for every other golden), and
`harness/trace/atoms.ts` carries `snd`. All six goldens agree with rc.112 under
`outcome`, `m1` and `m2` through `harness/trace/job-tail.ts`, at the default
yield setting and at `EFFECT4_MAX_OPS=3 EFFECT4_EXPECT_YIELDS=1`.
`Effect4Test/Flow/JobRunnerContract.lean` carries the six exact logs;
`Effect4Test/Target/TypeScript/MultiArgContract.lean` is new and pins the
destructured call bytes, the tuple binding, the rows declaration and the census
row.

Neither battery declares a string-traversing `def`: a rendered module reaches
`Classical.choice`, so each module is rendered inside the `#guard` that reads it
(this also removes the three `Classical.choice` declarations `JobRequest.lean`
used to carry). Nothing new outside the modules `Effect4Test/Audit/AxiomGate.lean`
already exempts reaches `Classical.choice`.

### Claims

Released with this commit: `Effect4/Target/TypeScript/{ScriptFlow,Skeleton,Lower,FlowLower,EffectV4,ScriptDenotation}.lean`,
`Effect4/Meta/Derive.lean` (additively, under the existing trace-lane claim),
`harness/trace/{Generate.lean,tracer.ts,job-tail.ts,job-fixture.ts,atoms.ts}`,
`generated/traces/job/**`, `Effect4Test/Counterexamples/Target/JobRequest.lean`,
`Effect4Test/Flow/JobRunnerContract.lean`,
`Effect4Test/Target/TypeScript/{MultiArgContract,LoweringCoverage,FlowLowerContract,RegionLowerContract,StructuredLowerContract,AnswerProfileContract}.lean`,
the `Effect4Test.lean` import line for the new battery, the `E4-TARGET-CE-022`
and `E4-FLOW-CE-028` rows, the `job-runner` and `coverage` rows of
`docs/TRACE-DAG.md`, `docs/LOWERING-COVERAGE.md`, and
`docs/research/2026-09-03-job-runner.md` §1 and §3.1.

## Flow v3 landed, 2026-09-03

Carrier: lean4-effects v0.7.0 (`a117157`, tagged and pushed): `performCatch`
and `branch`, successor-indexed clauses, 18 admission clauses,
`EF-FLOW-CE-007/008`. Effect4 pins it. Runners: `plan`/`step`, the region and
interrupt runners, `RegionTotal`/`RegionSafety`/`Approximation`/
`RegionDenotation`/`RegionSimulation` take both terminators; the failure edge
is travelled only where a service can fail (the region and interrupt runners).
Semantics: `denoteGo`/`denoteFuel` arms, T1/T2 re-proved; the plan inversions
generalised (`plan_choose_inv`, `plan_exhausted_inv` and `plan_mismatch_inv`
are disjunctions over `choose` and `branch`; `plan_performCatch_inv` is new);
both skeleton block laws and the bind-form law of `StructureSemantics` gain a
`performCatch` conjunct and the `branch` alternatives, with the branch's
value/tape agreement discharged through `Holds` and admission's operand bound
(`testBound`) — T3 and the general T4 hold over the v3 carrier with no new
hypothesis. Lowering: `perform-catch` (rc.112 `Result` reading of the call and
a `switch` on `_tag`) and `branch-if` (`decisions.report(site, test)` then
`if`), appended last in `Rule.all` (29) so no positional window moved; the
`Decisions` service gains `report` on both faces (`tracer.ts`: tape-checked,
same `decide` row, a value mismatch dies where the runner refuses). Tracing:
the job runner is rewritten on the new terminators (`nonEmpty`/`positive`
atoms declared in `effect_atoms`), its six goldens re-derived (the requeue
scenario now schedules three failures against a budget of two so the drain
requeues, retakes and finishes the job) and host-green at both yield settings;
`E4-FLOW-CE-026`/`027` are repaired with positive controls `caughtFlow` and
`valueFlow`. Owed: nothing in Lean; the `ret` rule of the interrupt runner
under a pending interrupt is unchanged by this packet.

## Wave 0 of the refactor plan landed, 2026-09-03

Plan and evidence: `docs/research/2026-09-03-refactor-plan.md`, the two surveys beside
it. Main 5125131. Trust gate is root-only and stamped (`scripts/lib/stamp.sh`; 84 s on a
miss, 1 s on a hit, nine planted defects, no rebuild ever); the default `lake build` is
the green closure `Effect4TestGreen` with per-area targets; goldens generate in one Lean
process (4 s); the host harness stages only what a run reads; four hermetic gates run in
CI on Ubuntu; every `lean --run` in `scripts/` fails loudly. Sweep 10: fourteen gates
green in 232 s. Wave 1 dispatched from 5125131: 1a semantics, 1b lowering API, 1c effects
v0.8.0 (upstream only; the pin bump and Effect4-side deletions follow as a short packet),
1d stamped sweep. Agents do not edit this file; landings are recorded here on merge.

## Wave 1 of the refactor plan landed, 2026-09-03

Main 63e6e45. 1a: a `branch` is decided by tape-and-value agreement only
(`E4-FLOW-CE-029`), `RunResult.refusedSite`/`refusedValue` with `Tape.read_mismatch_ne`,
`BlockLaw` record (block laws 1405 → 1084 lines, no `maxHeartbeats` left), plan inversions
in `Effect4.Flow` (`Effect4/Semantics/PlanInversion.lean`), scoped simp sets. 1b: rule
identity by id, `OpSpec.unary`/`infallible`, slot-typed `tupleArgs`, `Expr.member`
(lean4-typescript v0.4.3), `Skeleton.lean` split from `SkeletonRender.lean` (the IR reaches
no `Classical.choice`), `E4-TARGET-CE-026`. 1c: lean4-effects v0.8.0 (a4ee7a1), pinned here;
`errorTy` is an `Option` (`some`, behaviour kept; the `"never"` → `none` reading is owed to
the lowering packet), `RegionSafety` ported mechanically through `regionWF_iff_check` (field
rewrite owed), seven duplicated lemmas and the `namespace Effects` block deleted. 1d: every
sweep gate stamped; `scripts/sweep.sh` is the entry point (177 s forced, 14 s unchanged).
Owed and recorded: H16 remainder (`OpSpec` defaults, five sites), `String.mk` in
`Trace.lean` with a golden regeneration, `flow-runner.contract.md` lines 13/35 (two refusal
constructors, four endings), `Interrupt.lean` docstring "four of five", the `_With`-from-
`_bind` derivation (scope predicate abstraction). Sweep: twelve gates green, trust gate
nine planted defects rejected. Waves 2–5 are on hold until the user says so.

## The Surface library dispatched, 2026-09-04

Plan: `docs/research/2026-09-04-surface-library-plan.md` (read it first; §10 is the
wave table). The lean4-typescript pin `6a70b884` (v0.5.0) existed in no clone and no
remote, so v0.5.0 was re-created from the printer's 58 byte pins at `71bad12` in
`~/Dev/lean4-typescript` (tag `v0.5.0`, not yet pushed) and this tree is repinned to
it; `lake build Effect4` 145 jobs green; the default battery is green in 273 of 274 jobs,
the one red being the pre-existing module-closure gate at `Effect4Test.lean:138`, which
rejects the untracked `Effect4/Char/*.lean` that no root import reaches (the Char lane's
connect step owns that). Publish the tag before a fresh clone resolves the pin.

### Claims

| File or tree | Claimed by | State |
| --- | --- | --- |
| `Effect4/Surface/**`, `Effect4.lean` (Surface import lines only) | Surface builders (waves 1a, 2a–2c of the plan) | in progress |
| `Effect4/Meta/Surface.lean`, `Effect4Test/Audit/AxiomGate.lean` (Surface exemption entries only) | Surface builder 3a | pending 2a–2c |
| `test/contracts/surface-*.contract.md`, `Effect4Test/Surface/**`, `Effect4Test/Counterexamples/Surface/**`, `test/counterexamples/REGISTER.md` (`E4-SURFACE-CE-*` rows only, append) | Surface breaker (wave 1b) | in progress, red until the builders land |
| `harness/surface/**`, `scripts/check-surface-generation.sh`, `scripts/test-surface-generation-gate.sh`, `scripts/sweep.sh` (one row), `vendor/wrangler-3.114.16/**` | Surface builder 3b | pending 2a–2c |
| `skills/lean-surface*/**`, `skills/README.md` (four rows), `docs/SURFACE.md`, `docs/ARCHITECTURE.md` (one row), `PLAN.md` (one paragraph) | Surface author 3c | pending |
| `lakefile.toml` (`Effect4TestSurface` lib), `Effect4Test.lean` (Surface import lines), `COORDINATION.md` (this section) | Surface coordinator | integration |
