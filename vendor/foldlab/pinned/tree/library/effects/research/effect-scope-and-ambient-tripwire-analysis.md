# Scope APIs and the ambient-service boundary: an analysis

Status: conception-mode research, 2026-08-27. G0/G1 hypotheses and
recommendations only; nothing here is promoted, and no ratified rule or
model statement is changed by this document. Sources are the pinned
Effect study clone at `.reference/clones/effect` (commit
`0dd7825e4da4d3a00fa9bd410a1d55f3d4874d07`, the rc.111 correspondence
commit) read first-hand, plus the in-tree runtime extraction report and
service-derivation survey. No new external material was consulted.

## Questions

1. Are Effect `Scope` APIs warranted as a more Effect-idiomatic way of
   handling any CAS or replay behavior in this library?
2. Can Effect's continuations be analyzed or modeled to avoid — or to
   handle better — the Clock and ambient-service challenges, of which
   the M5 tracing trap (`Effect.fn` spans tripping the replay-mode
   Clock tripwire) is the observed instance?

## Source-verified facts

All line references are into the pinned clone's
`packages/effect/src/internal/effect.ts` unless noted.

- **Span timing consults the Clock service, guarded by a dedicated
  reference.** `makeSpanUnsafe` reads
  `timingEnabled = fiber.getRef(TracerTimingEnabled)` (5753) and takes
  `startTime: timingEnabled ? clock.currentTimeNanosUnsafe() : BigInt(0)`
  (5769); span end is guarded the same way (5889). This is exactly the
  method the replay tripwire clock throws from, which is why traced
  methods inside replayed orchestration trip the wire.
- **Two per-scope levers already exist as `Context.Reference`s.**
  `TracerEnabled` (`effect/References/TracerEnabled`, default true;
  `internal/references.ts`) disables span propagation wholesale —
  `makeSpanUnsafe` folds it into `disablePropagation` (5730) — and
  `TracerTimingEnabled` disables only the clock reads, with public
  `withTracerEnabled` / `withTracerTimingEnabled` combinators built by
  `provideService` (5677, 5686). Both are ordinary per-scope references,
  the same mechanism the tripwires already use.
- **Span completion is a scope finalizer receiving the `Exit`** —
  tracing observes success and failure paths through the scope
  machinery (extraction report, pinned at `internal/effect.ts`
  5790–5815). This is runtime prior art for any future
  "always leave evidence on exit" behavior.
- **The extraction report's own model boundary places instrumentation
  outside pure semantics** (its T7 row: tracing/metrics are observation
  projections; "do not encode scheduler, host timing, or tracing into
  the pure semantics").
- **The plan's Effect-surface decision (§4) excludes `Scope` for this
  slice** ("`Scope`, `Fiber`, `Scheduler` | Excluded | Absent |
  Resources, cancellation, nondeterminism"), and the delivered library
  honors it: the in-memory store holds no resources, and per-scope
  service provision (tripwires, session-scoped `Replay`) is reference
  provision, not scope management.
- **The service-derivation survey already assigns scope its future
  home**: remote clients, connection pools, refresh workers, and
  subscriptions "belong to the layer scope," with `EventLogRemote`
  pinned as nearby idiom; the pin also ships `ScopedCache`/`ScopedRef`,
  the natural carriers for the survey's layer-owned success cache.

## Recommendations

### R1 — replay construction provides `TracerTimingEnabled = false`

The minimal, source-verified fix for the M5 trap: alongside the tripwire
Clock and Random, the replay environment provides
`TracerTimingEnabled = false`. Spans still exist and propagate (span
structure is preserved for any observer), but the runtime never consults
the Clock for them — traced orchestration replays cleanly with no
`Effect.fnUntraced` discipline burden, while genuinely semantic Clock
use (`sleep`, `currentTimeMillis` in user code, timeouts) still trips
the wire exactly as ratified. This reclassifies span *timing* from
ambient use to disabled instrumentation, which the extraction report's
own semantics boundary supports. The stronger lever
(`TracerEnabled = false`, spans fully disabled in replay) exists and is
named here as the alternative; timing-only is recommended because it
subtracts precisely the ambient consultation and nothing else.

Cost: one provided reference in replay construction, a fixture flip
(traced orchestration replays clean; a semantic Clock use still
surfaces `Violated`), and a documentation line replacing the
`fnUntraced` warning. This revises the reject-first boundary's edge for
one named infrastructure channel, so it is an operator ruling, not a
convenience change.

### R2 — the principled answer to deterministic time: describe it

The library already contains the better way, with zero new machinery: a
program that needs time or randomness under replay describes a `Time`
(or `Random`) service like any other — one operation description, one
`replayable` kit — and its reads become recorded occurrences that
substitute on replay. Ambient challenges dissolve exactly where the
ambient read is promoted to a described operation; the tripwire remains
the guard for the *undescribed* path, which is its ratified job. This
is a documentation recipe, not a feature: it belongs in the README's
usage guidance and needs no model change, no new obligation, and no
tripwire revision.

### R3 — Scope: the exclusion stands here; two named adoption points

For the in-memory slice the §4 exclusion remains correct — there is no
resource to acquire, release, or finalize, and forcing `Scope` in would
be idiom theater. Scope is warranted at two named points:

1. **The remote `CasStore` slice** (already designed this way in the
   survey): `Layer.scoped` acquisition for clients/auth/pools,
   `ScopedCache` for the layer-owned success cache, forked consumers in
   the layer scope. Adopting it there amends the plan §4 row as part of
   that slice's Pass A — a declared change, not a drift.
2. **A future session-exit witness guarantee** (named Pass A item, not
   scheduled): today an interrupted session fiber leaves no witness —
   `session` persists evidence only on completion, rejection, or
   violation paths. An `Effect.onExit`/scope-finalizer flush is the
   idiomatic shape (the runtime's own span-end finalizer is the
   pattern), but the witness outcome taxonomy (`Completed`/`Rejected`/
   `Violated`) deliberately has no interruption case — the interruption
   channel is a deferred contract decision. So this is taxonomy growth
   plus lifecycle engineering together, and it must enter through its
   own Pass A when interruption semantics are taken up, never as a
   finalizer bolted on under the current taxonomy.

### R4 — continuation modeling is not the tool for this

The defunctionalized continuation machine remains the extraction
report's G3 trajectory, and nothing here changes it. Analyzing runtime
continuation frames to classify ambient *callers* (infrastructure vs
program) is rejected below; and the reified Lean program carrier needs
no ambient leaf class, because R2 handles ambient reads at the
description level where they become ordinary occurrences.

## Rejected designs

- **Faking replay time** — a deterministic Clock returning invented
  values in replay would manufacture observations the recording never
  contained; rejected on the generated-vectors/honesty principle.
- **Continuation-frame introspection to classify ambient use** —
  distinguishing "tracing called the Clock" from "the program called
  the Clock" by inspecting fiber continuation state is runtime-internal,
  version-fragile, and unnecessary: the runtime already separates the
  channels by reference (`TracerTimingEnabled` vs the Clock service
  itself).
- **A witness-on-interrupt finalizer under the current taxonomy** — it
  would force an interrupted session into `Rejected` or `Violated`,
  both false.

## Obligations if adopted

R1: an operator ruling recorded in the workflow record; one
implementation-lane rider (the provided reference + fixtures + docs).
R2: README recipe only. R3.1: plan §4 row amendment at the remote
slice's Pass A. R3.2: a named entry on the deferred-interruption
docket. R4: none.

## Source standing

The Effect clone is existing registered study material at its recorded
commit; the extraction report and service-derivation survey are in-tree
landed research. No new sources; no new provenance entries required.
