# Contract: the patched rc.112 copy and the frame projections (P-T11)

Light ceremony by operator ruling D2; ruling R3 phase 2. The unpatched host
stays the evidence for every service-level claim; the patched copy adds
frame-level rows that are recorded, never compared.

## The copy (`harness/trace/patched/`)

- `patch-manifest.json`: seven observation-only hunks, each inserting one
  `globalThis.__effect4Frame?.(row, data)` call and changing no control flow:
  `frame.pop` and `frame.deferred-interrupt` (`getCont`), `frame.exit-fail-cause.skip`
  (the handler-skipping loop of `exitFailCause`), `scope.close-inline`,
  `scope.close-single` and `scope.close-lifo` (the three arms of `scopeCloseUnsafe`
  and the finalizer loop), `layer.memo-build`.
- `apply.mjs` copies the pinned `effect` package beside symlinks to the rest of
  the pinned installation, applies every hunk (an anchor must occur exactly
  once), and writes `trace-host-pin.json`: the base pin plus the manifest
  digest and every patched file's digest before and after. The copy lives in
  `_copy/` (ignored) and is selected only through `EFFECT4_EFFECT_NODE_MODULES`.
- Every harness tail defines the sink and reports `patchedFrames`; `effect4-trace`
  records them in the receipt with `host.patched` naming the manifest and its
  digest (`harness/trace/receipts/patched/`).

## Facts pinned on the host (`scripts/check-trace-patched.sh`)

- The patched copy agrees with every flow golden under every mask: the hunks
  observe and change nothing.
- `regionTwoFail`: two releases run latest-first through the finalizer loop,
  each with the closing `Failure` (`scope.close-lifo`, indices 1 then 0).
- `regionBothSucceed`: a single release never enters the loop; it closes
  through the inline arm with the closing `Success` (`scope.close-inline`),
  which is the reified `ScopeState.openInline` and the second arm of
  `Scope.closeResult`.
- `regionNested`: both single-release scopes close inline with the failure,
  inner first.
- Every run records its continuation pops (`frame.pop`).

## The Lean half (`Effect4/Target/TypeScript/Simulation.lean`)

`Exit.toOutcome`, `FrameEvent.toTrace`, `FrameEvent.traceOf`, `Event.toTrace`:
finalizers and outcomes project into the service-level alphabet; frames,
scheduling, joins, interrupts and masks project to `none`. Receipts in
`Effect4Test/Target/TypeScript/SimulationContract.lean`. No simulation is
claimed: `docs/TRACE-DAG.md` edge `bridges` stays `required-open` with a
statement now available to it.

## Acceptance

```text
lake env lean Effect4Test/Target/TypeScript/SimulationContract.lean
./scripts/check-trace-patched.sh
./scripts/check-trace-host.sh        # the unpatched copy is unchanged
```
