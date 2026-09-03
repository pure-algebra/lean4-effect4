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
