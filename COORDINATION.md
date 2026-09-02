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
| `Effect4/Concurrency/Supervision.lean`, `test/contracts/fiber-supervision.contract.md`, `Effect4Test/Concurrency/FiberSupervisionContract.lean`, `Effect4Test/Counterexamples/Concurrency/FiberSupervision.lean`, `Effect4Test/Concurrency/FiberSupervisionAxiomReport.lean` | Codex fiber subagent | direct-child supervision packet, breaker then builder |
| `test/counterexamples/REGISTER.md`, `test/counterexamples/concurrency/ATTACKS.md` (`E4-CONC-CE-012` only) | Codex fiber subagent | append-only supervision attack |
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
| `Effect4Test.lean` (RuntimeCoverage import line only), `Effect4Test/Audit/AxiomGate.lean` (RuntimeCoverage exemption entry only), `.github/workflows/lean_action_ci.yml` (runtime census step only) | Claude | Effect runtime coverage slice wiring |
| `docs/SCOPE-DAG.md`, `test/contracts/scope.contract.md`, `Effect4Test/Runtime/ScopeContract.lean`, `Effect4Test/Runtime/ScopeAxiomReport.lean`, `Effect4Test/Counterexamples/Runtime/Scope.lean`, `test/counterexamples/runtime/ATTACKS.md` | Claude | Scope runtime packet frozen, RED; breaker-owned, do not edit while implementing |
| `test/counterexamples/REGISTER.md` (`E4-RUN-CE-001`..`009` only), `Effect4Test.lean` (Scope import lines only), `test/fixtures/trust-gate/known-red.txt` (Scope entries only) | Claude | Scope runtime packet wiring, append-only |
| `generated/fiber-assurance.tsv` | Claude | regenerated in the Scope breaker commit because `test/counterexamples/REGISTER.md` is a pinned input; no other change |
| `Effect4/Runtime/Scope.lean` | Claude (builder) | **built, green**: the frozen surface is implemented and the battery, axiom report, and counterexample module all build. All 98 public theorems stay within `propext`/`Quot.sound`, and both Scope entries were removed from `test/fixtures/trust-gate/known-red.txt`. The packet and battery were not edited. The `SCOPE-L7` coverage join in `Effect4Test/Audit/RuntimeCoverage.lean` remains a separate, unclaimed packet |

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
