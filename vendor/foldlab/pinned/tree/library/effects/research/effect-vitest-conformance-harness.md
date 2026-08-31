# A generic @effect/vitest harness for Lean conformance testing

Status: design review (G0), 2026-08-27. This report designs the generic
harness and fixture machinery that would let the TypeScript suite consume
any committed Lean conformance family mechanically — one binding per
family kind, everything else shared — against the pinned
`@effect/vitest@4.0.0-rc.111` API. Nothing here is ratified and nothing
is implemented: the R2 implementation slice is in flight in the same test
tree, so this note proposes shapes and a decision docket only. Citations
are `file:line` at the pin.

## 1. What exists, and what repeats

The committed consumption pattern (`test/ReplayFixtures.ts`) has five
parts, and every future family repeats four of them:

1. **Wire schemas** hand-mirroring the Lean JSON encoders
   (`ReplayFixtures.ts:13-126`) — the only genuinely per-family work.
2. **A pinned envelope**: `family` and `model` as `Schema.Literal`, rows
   typed by the row schema (`ReplayFixtures.ts:139-145`). The remote
   families add an `oracle` field the replay envelope lacks.
3. **A loader** (`node:fs` + JSON + `Schema.decodeUnknownEffect`).
4. **A pure fold** of the system under test over the row's inputs,
   projecting the comparable observation (`runFixture`,
   `ReplayFixtures.ts:154-180`).
5. **A comparator** iterating rows with the case id embedded in the
   structural assertion (`assertFamily`, `ReplayFixtures.ts:185-202`) —
   deliberately reusable with a substituted system under test, which is
   what the direction-2 mutation-red suite exploits.

Parts 2–3 and 5 are family-independent today in all but their types.
Part 4 varies by *family kind*, not family: reducer families fold
`reduce`, remote families interleave `ops`/`schedule`/`sequence` into
machine inputs and fold `step`. That factoring — per-kind runner,
per-family schema, shared everything else — is the design's spine.

## 2. The pinned @effect/vitest facts the design stands on

- `it.effect` is a `Tester<Scope>` and runs every test under the test
  environment: `TestClock` and `TestConsole` are provided by default
  (`internal.ts:42-44`), `it.live` omits them, and `layer(...)` accepts
  `excludeTestServices` (`index.ts:150`). Conformance suites therefore
  run with no ambient wall clock by construction — and `TestClock`
  becomes the deterministic-time hook when R4's retry schedules put
  time into fault schedules.
- `layer(L)(name, (it) => ...)` shares one memoized layer across a
  describe block, **nests** (`it.layer`), and accepts a shared
  `Layer.MemoMap` (`index.ts:106-114,147-157`) — one harness server or
  one adapter build can back many family blocks without rebuilds.
- `it.effect.each(cases)` drives parameterized tests (`index.ts:60-62`),
  but vitest collects tests synchronously, so per-row test entries
  require the manifest to be loaded at module collection time.
- `it.prop` accepts **Schema values directly as arbitraries**
  (`Arbitraries`, `index.ts:48-50`) with FastCheck parameters (seed,
  numRuns) in the options — the property lane can generate inputs from
  the same schemas that validate manifest rows.
- `makeMethods` and `describeWrapped` (`index.ts:253-259`) build custom
  `it` surfaces — the sanctioned seam for a `conformance.*` method
  family if sugar is ever wanted.
- `flakyTest` exists (`index.ts:231`) and is *prohibited* here: retrying
  conformance evidence until it passes is not evidence.

## 3. The design

### 3.1 The family binding — the only per-family artifact

```ts
// test/conformance/Family.ts (test tree at first; packaging is D-V6)
export interface FamilyBinding<Row, SUT> {
  readonly family: string            // "RMT-001" — Schema.Literal pin
  readonly model: string             // "effects-model@0.1.0" — pinned
  readonly row: Schema.Codec<Row>    // the hand-mirrored wire schema
  readonly hasOracle: boolean        // remote envelopes carry `oracle`
  /** Interpret one row against the system under test and return the
   * observation in the row's own `expect` shape. Pure of I/O; the SUT
   * arrives from context. */
  readonly run: (row: Row) => Effect.Effect<unknown, never, SUT>
}
```

Two *kind-level* runners cover every current family: the reducer fold
(replay/session/composition families over `ReplayReducerSUT`) and the
machine fold (remote families over `RemoteStepSUT`, deriving inputs from
the split `ops`/`schedule`/`sequence`). A binding is then one schema plus
one line naming its runner. New families cost exactly their wire schema.

### 3.2 The system under test is a Layer — one suite, four evidence lanes

Each kind declares a `Context.Service` tag whose shape is the pure step
function (`ReplayReducerSUT: (state, input) => StepOut`, `RemoteStepSUT:
(state, input) => StepOut`). The derived suites require the tag; layers
decide what is being tested:

| Evidence lane | Layer provided | Derived machinery |
| --- | --- | --- |
| Direction-1 vectors (tsEvidence) | the model mirror | `familySuite(binding)` — every row green |
| Direction-2 mutation-red | one mutant per declared meaning | `assertMutantRed(binding, mutant)` — comparator must go red, kill witnesses named |
| Property lane (R5, declared evidence) | the mirror (+ generators) | `it.prop` over Schema-derived inputs asserting law shadows |
| Differential / live lane (R2+, R6) | the real adapter + a `ConformancePeer` | same scenarios through the adapter, compared at the machine boundary |

This is the ratified four-lane evidence architecture mechanized: one
binding, four lanes, selected by layer substitution — the same move the
library itself uses for replayable services. `layer()` nesting keeps it
readable:

```ts
layer(MirrorLayer)("direction-1", (it) => {
  it.effect("RMT-001 consumes every ratified admission row structurally",
    () => familyAssert(rmt001Binding))
  ...
})
layer(AdapterLayer.pipe(Layer.provideMerge(ReferencePeer.layer)),
  { memoMap })("differential", (it) => { ... })
```

### 3.3 Manifest access is a service too

`ConformanceSource` (a `Context.Service`) resolves a family name to
decoded rows. The default layer reads the committed
`conformance/manifest/*.json` files — the manifests remain the ONLY
inter-lane coupling. An in-memory layer exists solely to test the
harness itself. Deliberately refused: a layer that shells out to
`lake exe conformance_manifest` for "live" vectors — regeneration
belongs to the conformance lane's gate, and a live source would blur
manifest-as-interface into build-coupling.

The envelope decode is **closed** (strict schemas, unknown keys fail):
closed decoding is the drift tripwire between the Lean encoders and the
hand-mirrored TypeScript schemas. Family digests stay deferred as ruled
at M4 Pass A; this is the interim guard, and it already catches added,
removed, and renamed fields.

### 3.4 Suite granularity

Two registration shapes, both supportable:

- **One test per family** (current pattern): loading stays inside
  `Effect`, the case id rides in the structural diff. Default.
- **One test per row** via `it.effect.each(rows)`: better reporter
  granularity and `.only` filtering, but requires top-level `await` at
  collection time, moving manifest I/O outside the Effect pipeline.
  Offered as an opt-in debugging mode (`familySuiteEach`), never the
  gate path — the gate counts families, not rows, and the per-row mode
  must not diverge in what it asserts.

### 3.5 The peer matrix and the LeanServer seam

The differential lane parameterizes over `ConformancePeer` bindings with
capability filtering (`it.skipIf` on missing capability — visibly
skipped, never silently). A peer entry may carry **expected divergences**:
named cases where the peer is known non-conforming. For LeanServer,
those are exactly its audited gaps (gRPC trailers in headers, early
HTTP/2 request construction, WebSocket masking and fragmentation): the
suite asserts the divergence IS detected — a detection-target test
fails the run if the peer suddenly agrees or the difference goes
unnoticed, which is the operational meaning of "audited gaps are named
detection targets." A peer with an empty divergence list is asserted to
agree everywhere. LeanServer lands at its own slice as one more entry in
the matrix; nothing else changes.

### 3.6 The property lane hook (R5, not before)

`it.prop` with the binding's input schemas as arbitraries, pinned seed
and run count in the options, asserting *law shadows* — executable
consequences of the ratified sentences (the entitlement guard excludes
cache decisions on random un-entitled inputs; rejection memory is
monotone over random input lists). These enter as declared evidence at
R5 ratification per the workflow; the harness carries the mechanism now
so R5 is a wiring slice, not a build. Shrunken counterexamples become
candidate vector rows only through the conformance lane (a Lean-side
row landing additively), never by committing TS-discovered cases
directly — the generated-vectors law stays intact.

### 3.7 Time under test

`it.effect`'s default `TestClock` means conformance code can never
consult wall clock even accidentally, and it composes with the library's
replay tripwires (semantic Clock use in replay mode still surfaces as
`Violated` — the tripwire is the library's, the TestClock is the
harness's; the suites already run green under both). When R4 puts
`retryAfter` delays and attempt deadlines into fault schedules, the
schedule vector's time entries map onto `TestClock.adjust` between
machine inputs — deterministic time-dependent conformance with no new
machinery. This is also the standing answer to the parked D7
deterministic-tracing-clock revisit for test contexts.

## 4. What the harness refuses

- It never writes, regenerates, or repairs a manifest; a decode failure
  is a red suite, not a fix-up.
- No snapshot testing as evidence — expectations come from Lean-executed
  vectors only (generated-vectors law).
- No `flakyTest`, no retries, no `it.live` in conformance suites;
  nondeterminism is a defect, not noise.
- No silent skips: capability filtering must render as skipped tests
  with the capability named.
- A green suite is sampled evidence at G4 attached to the pinned
  commit's manifests — the harness never upgrades a claim, and its
  README section must say so.
- Harness self-tests (the in-memory source, the red-path of the
  comparator) are ordinary tests, never conformance evidence.

## 5. Decision docket

| # | Decision | Recommendation |
| --- | --- | --- |
| V1 | Factoring | Generic harness = loader service + envelope pinning + comparator + lanes; per-family cost = one wire schema + a kind-level runner reference (two runners cover all current families). |
| V2 | SUT injection | `Context.Service` tags per family kind; evidence lanes select by layer substitution; `layer()` blocks with one shared `MemoMap` for adapter and peer reuse. |
| V3 | Manifest access | `ConformanceSource` service; default = committed files, closed strict decode as the drift tripwire; live-regeneration source refused; family digests stay deferred. |
| V4 | Granularity | One test per family remains the gate path; `it.effect.each` per-row mode as opt-in debugging only. |
| V5 | Peer matrix | Peers carry typed expected-divergence lists; LeanServer's audited gaps become detection-target assertions that fail when NOT detected; capability skips always visible. |
| V6 | Packaging | Build in the test tree at the next conformance-lane slice (after R2 acceptance, so codex's in-flight structures are absorbed, not fought); promote to a shipped `@foldlab/effect-replay/conformance` subpath at M6's packaging review so third-party adapters run the identical suites by providing layers. |
| V7 | Property lane | `it.prop` with Schema-derived arbitraries and pinned seeds, wired at R5 as declared evidence; TS-discovered counterexamples route back through Lean-side vector rows, never committed directly. |
| V8 | Time | Rely on `it.effect`'s TestClock as the deterministic substrate; map R4 schedule-time entries onto `TestClock.adjust`; `it.live` prohibited for evidence. |

Sequencing note: nothing here lands while the R2 packet is in flight —
the harness's first implementation slice generalizes what R2 delivers
(the remote runner, the peer interface, the adapter layers) rather than
prescribing shapes into codex's working tree mid-delivery. The docket,
if ratified, binds that future slice.

**Post-ratification status (2026-08-27):** V1–V8 ratified with two
operator riders — upstream vitest/Effect testing semantics lead the
integration (no custom runners; the section-14 record is binding), and
the sequencing above is amended: the harness dogfoods on the current
R2 slice as a packet rider, absorbing the in-flight structures. See
`CONFORMANCE-WORKFLOW.md` §14, "Conformance-harness ratification".
