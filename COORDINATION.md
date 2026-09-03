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
