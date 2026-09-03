# Host conformance harnesses

This directory holds exact-pin TypeScript, Effect v4 runtime/replay, and
`@effect/tsgo` language-service checks. Harness output is evidence about a
named host profile and file set; it never defines the Lean semantics. Each
section below states one harness's purpose, its entry script, its pins, and
what a pass does and does not establish.

The entry point for all of them together is `./scripts/sweep.sh`, which runs
the trace, lowering, citation and runtime-census gates in dependency order --
hermetic before host, self-tests last -- one process at a time, and writes
`.lake/sweep-summary.tsv`. `--hermetic` is the host-free subset that CI runs,
`--keep-going` runs every gate rather than stopping at the first failure,
`--force` ignores every stamp, and `--list` prints which gates are in which
lane. Each gate keys a stamp under `.lake/stamps/` on the content of what it
reads -- its fixtures, the goldens it compares with, the Lake traces of the
Lean modules its driver imports, the effect4-tools runner it invokes, and the
identity of the pinned Effect installation -- and prints its stamped summary
instead of re-running when none of that has changed. The header of each gate
names its own inputs. A sweep with nothing changed takes about seven seconds;
a forced one takes about four minutes.

Four harnesses below are not in the sweep and are still run by hand:
`schema-generation/`, `schema-annotations/`, `schema-effectful-field/` and
`fiber-supervision/`. Routing them is survey finding H34, not this packet.

`schema-generation/` contains the first complete bridge fixture. Run
`./scripts/check-schema-typescript-generation.sh`; it regenerates the fixture
from Lean, byte-compares it, runs the unpatched TypeScript compiler, executes
Effect's document reviver, and requests strict diagnostics from the Effect
language service. `EFFECT4_EFFECT_NODE_MODULES` may point at another exact
installation of the pinned packages.

The same command also generates a second document containing one
field-admissible representative for each of the 22 representation tags and
both check constructors. Its bytes are compared against Lean generation, and the runtime receipt
checks that Effect revives the exact canonical tag order.

`schema-annotations/` exercises annotations as a typed data plane over an
existing Schema. Run `./scripts/check-schema-annotations.sh`; it checks
higher-order annotation combinators, decoded-side, encoded-side, and key-side
metadata, last-check resolution, persisted raw representation data, the
unpatched TypeScript compiler, and strict Effect language-service diagnostics.
The custom dimensions use `effect/Schema` module augmentation, so TypeScript
checks their payloads without changing Schema's runtime carrier.

`schema-effectful-field/` lowers a `PropertySignature` whose annotation bag
carries an `EffectfulFieldSpec` into a TypeScript optic whose read and write
cross an Effect service. Run `./scripts/check-schema-effectful-field.sh`,
which is being added by a sibling agent in this sweep; it drives
`harness/schema-effectful-field/check.sh`, and that runs `check.mjs`. The pin
is asserted in `check.mjs`: `effect` 4.0.0-rc.112, `typescript` 7.0.2, and
`@effect/tsgo` 0.38.0, read from `EFFECT4_EFFECT_NODE_MODULES` or the
neighboring Foldlab installation, plus the unpatched `tsc.original` found in
that tree. `tsconfig.json` is strict with `exactOptionalPropertyTypes`,
`noUncheckedIndexedAccess`, and `verbatimModuleSyntax`, and raises
`floatingEffect`, `missingEffectError`, `missingEffectContext`, and
`schemaSyncInEffect` to errors.

A pass means four separate projects behave exactly as named: `positive.tail.ts`
draws no diagnostic, and `floating.tail.ts`, `missing-error.tail.ts`, and
`missing-context.tail.ts` each draw exactly the one diagnostic they are named
for, with one file checked and Effect v4 detected in every case; then `api.ts`
is regenerated from `harness/schema-effectful-field/Generate.lean` and executed
against a live `UserFieldPolicy`, and the observed read/write event order is
compared with the Lean receipt. It does not close the target edge: the frozen
contract is `test/contracts/schema-effectful-field-typescript.contract.md`, and
`PORT-MANIFEST.md` keeps `E4-TYPE-SCHEMA-EFFECTFUL-FIELD-SPEC` `required-open`
pending that join. Nothing here holds for another service, another diagnostic,
or another Effect version.

`trace/` compares Lean's expected service-level traces with the pinned host, in
both the straight-line and the Flow-dispatch lowered form. Run
`harness/trace/check.sh`; it runs `./scripts/check-trace-goldens.sh`,
`./scripts/check-trace-host.sh`, `./scripts/check-lowering-types.sh`, and
`./scripts/check-lowering-coverage.sh` in that order. `./scripts/sweep.sh` runs
those four and, additionally, `check-trace-patched.sh`,
`check-lowering-property.sh` and the three mutation self-tests. The pin is
[`host-pin.json`](trace/host-pin.json): Effect 4.0.0-rc.112 at upstream commit
`2600f62f4532026928454dcea8d1c48557b3f942`, 2,341 files, package-tree SHA-256
`aea8ac8a25b17aa82796fad7acc1371bc9a92bbd7d25ce24f2598016f9920aad`, TypeScript
7.0.2, diagnostics 0.38.0. `tsconfig.json` checks `fixture.ts`, `atoms.ts`,
`tracer.ts`, `tail.ts`, `flow-fixture.ts`, and `flow-tail.ts` under the same
strict profile and diagnostic severities. The runner is the external
`$EFFECT4_TOOLS/packages/harness/check.mjs`, default `../effect4-tools`, which
re-asserts the three package versions before compiling.

A pass means `fixture.ts` and `flow-fixture.ts` regenerate byte-identically
from `harness/trace/Generate.lean`; `generated/traces/` is current with no
stale or orphan projection; the Flow runner and the traced service agree under
mask `m2` in the internal oracle; and the host traces agree with every golden
under every mask in `generated/traces/masks.tsv`, both at the default op budget
and at `EFFECT4_MAX_OPS=3`, which forces a yield after every op. Receipts are
written under `trace/receipts/`. What that agreement does not establish is the
refusal list of `docs/TRACE-DAG.md`: semantic preservation beyond the corpus,
anything about primitives or frames, interruption, concurrency or scheduler
order, types, layer build and memoization, host error identity or defect
payloads, termination, and any statement about the host derived from a Lean
theorem.

`effect-v4-family/` is the end-to-end lowering fixture for a derived family:
one `effect_signature Cell`, one `effect_program incr`, the Lean handler
receipt `cellLive`, and the generated Effect v4 module. Run
`harness/effect-v4-family/check.sh`; there is no `scripts/` wrapper. This
harness carries no `host-pin.json`, so its profile is only what the shared
runner `$EFFECT4_TOOLS/packages/harness/check.mjs` asserts — `effect`
4.0.0-rc.112, `typescript` 7.0.2, `@effect/tsgo` 0.38.0 by default, overridable
through `EFFECT4_HOST_PIN` — against the installation named by
`EFFECT4_EFFECT_NODE_MODULES`. `tsconfig.json` checks `fixture.ts`, `atoms.ts`,
and `tail.ts` under the same strict profile as the trace harness.

A pass means `lake env lean --run harness/effect-v4-family/Generate.lean`
reproduces `fixture.ts` byte for byte, the unpatched compiler accepts the three
files, the language service reports no strict diagnostic, and `tail.ts` runs
under node, providing `Cell` from a `Ref`-backed layer and observing
`incr(0) = 42` from cell 41 — the value the Lean receipt in `Generate.lean`
fixes as `(42, 42)`. It establishes nothing about any other family, program, or
handler, and nothing about concurrency, interruption, or scheduling. The Lean
receipt and the host run are placed side by side; no simulation between them is
proved here.

`fiber-supervision/` records finite host observations of fork, race, daemon and
tracked children, and parent cleanup ordering. Run
`./scripts/check-fiber-supervision-host.sh`; it installs nothing.
[`fiber-supervision/README.md`](fiber-supervision/README.md) owns the case
list. The pin is [`host-pin.json`](fiber-supervision/host-pin.json), the same
rc.112 profile as the trace harness: upstream `2600f62f…`, 2,341 files,
package-tree SHA-256 `aea8ac8a…`, TypeScript 7.0.2, diagnostics 0.38.0. The
script also compares the installed `src/internal/effect.ts` byte for byte with
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`, refuses any package
symlink, and prints the node version and platform with each run.

A pass means the ten cases in `runtime-check.ts` produce their recorded
results, the direct compiler analyzes the actual harness file, an
intentionally wrong assignment is rejected and its restoration accepted, the
Effect diagnostic provider reports one file examined, and only the restored
unchanged bytes are executed. These are finite observations of one pinned host.
They do not establish all schedules, eventual completion, an interpretation of
arbitrary callbacks, or a Lean-to-host simulation; the Lean statements and
their trust receipts belong to `test/contracts/fiber-supervision.contract.md`
and its proof graph.
