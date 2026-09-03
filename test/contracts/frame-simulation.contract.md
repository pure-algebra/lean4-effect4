# Frame-machine simulation of `interpret` — light contract

Status: GREEN, authored and implemented together 2026-09-03 (packet D4 fence B;
light ceremony, one new module and no change to any frozen surface)

Implementation fence:
`Effect4/Semantics/FrameSimulation.lean` (new), plus twelve appended theorems in
`Effect4/Runtime/Runtime.lean` (packet D4 fence A, frozen in
`Effect4Test/Runtime/FramesContract.lean` section F10)

Lean battery:
`Effect4Test/Semantics/FrameSimulationContract.lean`

Axiom report:
`Effect4Test/Semantics/FrameSimulationAxiomReport.lean`

Proof graphs: `FRAME-PG-STACK` in `docs/FRAMES-DAG.md` (the fence A section and
the fence B section at the end); the `semantics` edge of
`docs/TRACE-DAG.md`

Packet source: `docs/research/2026-09-03-frame-simulation.md`, packet D4 of
`docs/research/2026-09-03-reification-plan.md`

## What is claimed

`Effect4.FrameSimulation.compile_simulates`. For

- a first-order alphabet `a` and its monomorphic signature `Flow.Sig a`, where
  every request and every answer is `Effects.Trace.Val`;
- a handler `H` into `ExceptT (Cause Val Unit Unit Unit) (StateT St Id)`;
- a program `p : Program (Flow.Sig a) Val` and an initial state `s0`;
- the answer tape `tape` with `answersOf H p s0 = tape`;
- any `fuel` with `bound tape ≤ fuel`,

the frame machine started on `compile 0 p` with the continuation table
`tapeInterp p tape` **finishes**, and the exit it yields is
`exitOf ((interpret H p).run.run s0).1`.

`compile_simulates_fail` is the same statement for a handler whose error carrier
is the raw user error, through `run_liftFail`.

## What is not claimed

- **That the machine computes `interpret`.** It does not. `PrimInterp` is a
  record of pure total functions, so the machine has nowhere to put a handler's
  monad; the answers are *supplied* by the tape. `hOracle` is what makes the pure
  table legitimate, and quoting the theorem without it is misquoting it. The
  content is that the machine's **control flow** — which continuation runs, in
  which order, with which exit — equals the algebra's, given agreeing answers.
  This is a simulation modulo an effect oracle.
- **Anything about the host.** No Lean theorem reaches JavaScript;
  `FRAME-L9-HOST-EVIDENCE` and the `bridges` edge of `docs/TRACE-DAG.md` stay
  open by construction.
- **Anything about interruption or concurrency.** Fence A proves the interrupt
  half of the machine is *inert* on this fragment, which is not the same as
  modelling it. Interruption remains evidence-only until A1 and a two-fiber
  model.
- **Anything about finalizers, brackets or regions.** `Program` has `pure` and
  `vis` and no bracket former, and `Handler.handle` takes an operation and never
  a subcomputation, so `FrameEvent.finalizersRun` has no algebra-side
  counterpart. The finalizer half is a later fence, stated in a comment at the
  end of `Effect4/Semantics/FrameSimulation.lean` and blocked on a ruling; see
  "Open" below.
- **Any coverage number.** `docs/RUNTIME-COVERAGE.md` scores clause by clause,
  and a composite theorem is nobody's clause. **No census row turns green.**
  What changes is the *kind* of evidence for `rule.frames-are-primitives`,
  `op.Success`, `op.Sync` and `op.OnSuccess`: from single-transition equations to
  a composed run. Recording that on `rule.frames-are-primitives` is a separate
  packet with a separate claim, under the `runtime-coverage` procedure.

## CATEGORIES

- `interpreter` — `compile` and `tapeInterp` are a compilation plus its table;
- `algebraic-laws` — `exitOf`/`exceptOf` round-trip, `residual_append`,
  `interpret_pure`/`interpret_vis`;
- `total-functions` — every definition is total and first-order over finite data;
- `protocol-state` — the compiled fragment is closed (`inFragment`), so no mask
  combinator, `exitFrame`, `whileLoop` or `iterator` is ever entered.

## Rulings this packet makes, and why

1. **The tape carries outcomes, not bare answers.** The research packet writes
   `tape : List Val`. That statement is false: a handler may fail at an
   operation, a bare `List Val` cannot record where, so the machine has no way to
   fail and the two sides disagree on every failing run. `Answer` is the
   two-constructor outcome alphabet (`ok`, `failed`), and `Tape := List Answer`.
   The failing occurrence is the last entry, and no entry follows it.
2. **`bound` is a function of the tape.** The packet writes `bound p` with "the
   sup over the taken branch, discharged along the tape". The taken branch *is*
   the tape, so `bound tape = 2 * tape.length + 1`: two machine steps per
   performed operation (push the `OnSuccess` frame; run the `Sync` and pop it)
   and one to yield the exit. Under `hOracle` this is `bound (answersOf H p s0)`,
   a function of `p`, `H` and `s0`. The battery's last `#guard` is the tightness
   receipt: one unit below `bound` the run has *not* finished, and that is a live
   DB-04 frontier and not a result.
3. **Empty annotations are not a hypothesis here.** The research packet asks for
   one (its section 5(b)). The risk it names is `Cause.combine` deduping
   `Reason`s that differ only in their `ReasonAnnotations`, and `Cause.combine`
   is reachable only through `Exit.restoreAfterFinalizer` on an `onExit` arm,
   which this fragment never emits (`compile_inFragment`,
   `tapeContA_inFragment`). Adding it would be a vacuous hypothesis that weakens
   nothing. It becomes live in the finalizer fence, and is recorded there.
4. **The name alphabet is gated.** `ν := Nat` and `σ := Nat`, and two `example`s
   in the module and two in the battery assert `DecidableEq Code` and
   `DecidableEq Machine`. The trap `docs/FRAMES-DAG.md` separation 4 exists to
   forbid — `ν := Σ op, (S.Answer op → Program S Val)` — elaborates fine and
   silently drops decidable equality from the emitted `Prim`, turning every
   `frame-arm` census row from a statement about frames into a statement about
   Lean functions. These four ascriptions fail to elaborate if anyone does it.
5. **Module placement is an open ownership question.**
   `Effect4/Semantics/FrameSimulation.lean` imports `Effect4/Runtime/Runtime.lean`,
   and `docs/ARCHITECTURE.md` places Runtime **above** Semantics
   (`docs/FRAMES-DAG.md` separation 2). No other module under
   `Effect4/Semantics/` imports this one, so the established Runtime → Semantics
   edge is not reversed for any existing module; but if the merge prefers strict
   directory layering the module moves to `Effect4/Runtime/FrameSimulation.lean`
   unchanged. Flagged here rather than resolved unilaterally.
6. **`Flow.Sig` is declared locally.** `Effect4.FrameSimulation.Flow.Sig` is
   marked `-- to be unified with Denotation.lean`: a sibling packet declares the
   same signature, and the two are merged by the coordinator, not here.

## Open

The finalizer half, against `Effect4.Flow.runRegions` through
`FrameEvent.traceOf`. Its statement is in a comment at the end of
`Effect4/Semantics/FrameSimulation.lean`. It is **blocked**, not merely unstarted:
`armA` / `armE` on `onExit` compose through `Exit.restoreAfterFinalizer`, so a
failed body with a failed finalizer yields
`failure (Cause.combine bodyCause finalizerCause)`, while
`Effect4.Flow.Region.closeFrame` keeps only the *first* release failure and
reports the body's error unchanged (pinned by `E4-FLOW-CE-019`). The two models
disagree on the failure payload on every run where a release fails under a
failing body, and TRACE-DAG separation 3 fixes the `m1` outcome as
`(tag, reason tags in order, fail payload)` — so the payload is exactly what a
mask cannot erase. Either restrict the statement to runs with at most one failure
and say so in the statement, or add the missing `Cause.combine` to the region
runner and re-pin `E4-FLOW-CE-019`. That ruling belongs to the finalizer packet.

## Verification

```text
lake build Effect4
lake env lean Effect4/Semantics/FrameSimulation.lean
lake env lean Effect4Test/Semantics/FrameSimulationContract.lean
lake env lean Effect4Test/Semantics/FrameSimulationAxiomReport.lean
lake build Effect4Test
./scripts/test-trust-gate.sh
```

Every public theorem of this packet is within `propext` / `Quot.sound`; the
`#print axioms` receipts are in the axiom report.
