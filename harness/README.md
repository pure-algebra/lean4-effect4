# Host conformance harnesses

This directory holds exact-pin TypeScript, Effect v4 runtime/replay, and
`@effect/tsgo` language-service checks. Harness output is evidence about a
named host profile and file set; it never defines the Lean semantics. Each
section below states one harness's purpose, its entry script, its pins, and
what a pass does and does not establish.

The entry point for all of them together is `./scripts/sweep.sh`, which runs
the citation and runtime-census gates in dependency order -- hermetic before
host, self-tests last -- one process at a time, and writes
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
`E4-TYPE-SCHEMA-EFFECTFUL-FIELD-SPEC` stays open pending that join (the
`PORT-MANIFEST.md` that tracked it was archived on 2026-09-04 with the Foldlab
vendor). Nothing here holds for another service, another diagnostic,
or another Effect version.

`trace/` and `effect-v4-family/` were archived to branch `archive/flow-route`
on 2026-09-04 with the Flow route they served, together with their gates
(`check-trace-*.sh`, `check-lowering-*.sh`), their goldens under
`generated/traces/`, and `docs/TRACE-DAG.md`.

`fiber-supervision/` records finite host observations of fork, race, daemon and
tracked children, and parent cleanup ordering. Its runner
`scripts/check-fiber-supervision-host.sh` was retired on 2026-09-04 with the
supervision calculus; the cases are `fiber-supervision/runtime-check.ts`, run
against the host the pin names, installing nothing.
[`fiber-supervision/README.md`](fiber-supervision/README.md) owns the case
list. The pin is [`host-pin.json`](fiber-supervision/host-pin.json), the
rc.112 profile: upstream `2600f62f…`, 2,341 files,
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
arbitrary callbacks, or a Lean-to-host simulation; the Lean side is the
reference machine's clauses and witnesses (`Effect4/Deep/Clauses.lean`,
`Effect4/Deep/Witnesses.lean`), joined in
`Effect4Test/Audit/RuntimeCoverage.lean`.
