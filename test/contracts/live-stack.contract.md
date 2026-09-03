# Live-stack traversal contract

Status: FROZEN / RED, independently verified 2026-09-03.

This packet adds a live-stack traversal to the existing frame machine. It
preserves the full result of the old pop loop for every current primitive,
arm and interruption-skipping flag. Its public entry checks deferred
interruption before deciding whether to skip the answer and records that
event even when the answer is discarded. This corrects a difference between
the source's nested loops and the old entry point; it does not replace the
old entry point.

Implementation: `Effect4/Runtime/LiveStack.lean` only. The independent battery
is `Effect4Test/Runtime/LiveStackContract.lean`; receipts are in
`Effect4Test/Runtime/LiveStackAxiomReport.lean`; registered witnesses are in
`Effect4Test/Counterexamples/Runtime/LiveStack.lean`. The ownership and
assurance route is `LIVE-STACK-PG` in `docs/LIVE-STACK-DAG.md`.

## Frozen boundary

The canonical owners remain `Effect4.Prim`, `Effect4.FrameFiber`,
`Effect4.FramePop`, `Effect4.ContAnswer`, `Effect4.FrameEvent` and
`Effect4.Arm` in `Effect4/Runtime/Runtime.lean`. Causes, reasons and annotation
maps remain owned by `Effect4/Semantics/Cause.lean`. This packet adds no type,
constructor, closure-bearing content, interpretation parameter or dependency.

The existing fourteen-primitive profile is unchanged. `AsyncFinalizer`,
`Async`, `Yield`, callback parking, finalizer execution, the scheduler and
fiber trees remain outside it. In particular, the source's AsyncFinalizer
counterexample is not encoded by giving an existing constructor a new
meaning. It is separate host evidence for the later profile extension.

All public functions and theorems quantify over `ν σ ε δ ι α : Type u`,
`β : Type v`, arbitrary finite stacks, arbitrary current programs, arbitrary
full causes and annotation maps, every `Arm`, and both values of `skip` where
that argument occurs. They require no equality, inhabitedness, ordering or
default-value instance. The source-facing pairs are `contA` with no skip and
`contE` with the source failure loop; `contAll` and `contA` with skip remain
total model inputs, not admitted source calls.

`FramePop` equality includes the complete answer, popped-frame sequence,
chronological events and all five returned fiber fields. It preserves nested
primitive bodies, continuation and thunk identities, repeated ordered reasons,
ordered annotation entries, current program, remaining stack, mask, pending
cause and deferred flag. No quotient, erased observation or projection may
replace that equality.

## Public declarations

The battery's exact ascriptions are authoritative. The module exports exactly
these eight authored declarations in `Effect4.FrameFiber`; all supporting
definitions and lemmas are private.

```lean
popLive (self : FrameFiber ν σ β ε δ ι α)
  (demand : Arm) (skip : Bool) : FramePop ν σ β ε δ ι α

getContLive (self : FrameFiber ν σ β ε δ ι α)
  (demand : Arm) (skipInterrupted : Bool) : FramePop ν σ β ε δ ι α

popLive_eq_popFrom (self : FrameFiber ν σ β ε δ ι α)
  (demand : Arm) (skip : Bool) :
  self.popLive demand skip =
    popFrom demand skip self.stack { self with stack := [] }

getContLive_eq_getCont (self : FrameFiber ν σ β ε δ ι α)
  (demand : Arm) (skip : Bool) (hdeferred : self.deferredInterrupt = false) :
  self.getContLive demand skip = self.getCont demand skip

getContLive_false_eq_getCont (self : FrameFiber ν σ β ε δ ι α)
  (demand : Arm) :
  self.getContLive demand false = self.getCont demand false

getContLive_deferred_kept (self : FrameFiber ν σ β ε δ ι α)
  (demand : Arm) (skip : Bool) (hdeferred : self.deferredInterrupt = true)
  (hkeep : (skip && self.interrupted) = false) :
  self.getContLive demand skip =
    ⟨.deferred self.pendingCause, [], [.deferred self.pendingCause],
      { self with deferredInterrupt := false }⟩

getContLive_deferred_discarded (self : FrameFiber ν σ β ε δ ι α)
  (demand : Arm) (hdeferred : self.deferredInterrupt = true)
  (hinterrupted : self.interrupted = true) :
  self.getContLive demand true =
    let next := ({ self with deferredInterrupt := false }).popLive demand true
    { next with events := .deferred self.pendingCause :: next.events }

getContLive_while (self : FrameFiber ν σ β ε δ ι α) (demand : Arm) :
  self.getContLive demand true =
    let first := self.getContLive demand false
    match first.answer with
    | .empty => first
    | _ =>
      if first.fiber.interrupted then
        let next := first.fiber.getContLive demand true
        { next with popped := first.popped ++ next.popped,
                    events := first.events ++ next.events }
      else first
```

## Operational requirements

`popLive` consumes the top frame, calls the existing `Prim.ensure` on the
fiber with that frame removed, and applies the existing `Prim.answerOf` and
`Prim.passEvents`. If traversal continues, it continues on the actual stack
returned by the hook. It re-reads `after.interrupted` after the hook before
discarding an answer. A hook that masks an ordinary finalizer stops that
discard, leaving its restoring frame above the untouched suffix.

The implementation must actually follow that live stack. Aliasing or calling
`FrameFiber.popFrom` or `FrameFiber.getCont` from either executable entry,
including through another executable helper or a fallback, is not accepted.
The old functions are comparison targets in proofs only. Exact equality on
the current profile cannot itself distinguish two extension strategies;
source review and a compiled dependency check must enforce this requirement.

Both public entries are total. A private well-founded recursion or a private
fuelled helper with a proved sufficient bound is allowed. Whenever the loop
continues, the actual post-hook stack is shorter for this fourteen-constructor
profile: a frame that pushes is an `OnExit` that also masks, answers every arm,
and therefore cannot have its answer skipped. This is the required reason for
termination, not a future guarantee for AsyncFinalizer. No exhausted budget
may be returned as an empty answer or discarded through an arbitrary default.
There is no public low-fuel result that loses the stopped state.

`popLive` does not inspect or clear the deferred flag. `getContLive` first
observes and clears it. A deferred answer is kept unless
`skipInterrupted && self.interrupted` is true. If it is discarded, its event
is prepended to the following live pop's events; its popped sequence is empty.
The while-law independently fixes the relationship between an inner call and
the conditional outer loop, including the concatenation of observations.

## Source and legacy distinction

Pinned source: Effect `4.0.0-rc.112`, commit
`2600f62f4532026928454dcea8d1c48557b3f942`. Read `FiberImpl.getCont` in
`vendor/effect-4.0.0-rc.112/src/internal/effect.ts` and `exitFailCause` in
`vendor/effect-4.0.0-rc.112/src/internal/core.ts`.

The source first answers a deferred interruption. Its outer failure loop
discards that answer only when the resulting fiber is interruptible and has
a pending cause. Old `FrameFiber.getCont` clears the deferred flag whenever
`skip=true`, even on a masked state, and omits the deferred event. Therefore
unconditional whole-result equality to that old entry would contradict this
packet. `getContLive_eq_getCont` explicitly requires no deferred interruption;
the all-state false-skip law remains exact. The counterexample establishes
this distinction on representable model states. Source reachability of every
such state is not assumed or proved here.

The while-law relates model operations following those source loop boundaries;
it is not a theorem connecting Lean execution to JavaScript execution. The
source state relation, callback admission, compiler behavior and scheduler
connection remain open. The old `FRAME-FB-NONNULL` boundary also remains:
`pendingCause` is total and gives `Cause.empty` when no cause exists.

## Independent attacks and controls

| Register row | Required discrimination |
| --- | --- |
| `E4-RUN-CE-022` | Reject a candidate that keeps only the answering shape or exit while changing current program, primitive identity, full cause/annotations, stack suffix, repeated popped frames or event order. Generic battery targets quantify over actual payloads. |
| `E4-RUN-CE-023` | Reject a pre-hook or entry-only interruption decision. An ordinary masking finalizer must stop skipping; restoring interruptibility may start it. Keep masked deferred answers and record discarded deferred events. No-pending and false-skip controls must still pass. |
| `E4-RUN-CE-024` | The source extension can select the same next continuation and eventually finish with the same exit while leaving interruption disabled at an intervening callback. The current `Prim` profile has no AsyncFinalizer and is not itself a witness of this source defect. |

The builder's independent package-local host harness must compile its public
Effect program with the pinned TypeScript compiler and then exercise a first
callback with cancellation, a second callback, an interruption request and a
late second reply. The delayed-push candidate must differ at the interruption
prefix, even if the eventual exits coincide. The unmodified runtime,
ordinary-finalizer, already-protected and no-cancellation controls must pass.
Mutate only an isolated fiber or package copy; do not patch the global runtime
or import the research workspace's observer as the expected result.

The stable host acceptance checklist is:

1. Use `harness/fiber-supervision/host-pin.json` as the existing authority for
   package bytes, Effect version and upstream revision, TypeScript version and
   diagnostic version. Reject a missing package, an empty source set or a pin
   mismatch before executing a witness. Record the actual Node version and
   platform separately.
2. Compile the public callback program directly with the pinned TypeScript
   compiler, execute that emitted program, and retain its scheduler choices,
   callback replies, interruption request and every compared prefix. Preserve
   the strict distinction between this typed source program and the separate
   test controller that observes it.
3. Show that the delayed-push candidate reaches the intended interruption
   checkpoint and is rejected there. The same eventual exit is not acceptance.
   Retain ordinary-finalizer, already-protected and no-cancellation controls,
   plus the unmodified runtime before and after the mutation.
4. Exercise the actual source `Failure.evaluate` on deferred states with
   interruption allowed and with it masked. Report these as constructed
   internal-state observations, not as proved public-program reachability.
   Distinguish keeping the deferred answer from discarding it, and retain the
   observed call/event order.
5. Hash the exercised source bytes before and after every mutation campaign.
   Global source/prototype changes, leaked pending test fibers, early build
   failures and missing observations cannot count as a semantic rejection.

For every planted implementation violation, compile the candidate first and
then run the unchanged independent detector. A parse or unrelated build failure
does not count as semantic rejection. Record accepted control, compiled
negative, intended rejection and restored control separately. At minimum,
exercise lost restoring frame, erased returned state/cause or trace, stale
post-hook interruption, and the legacy deferred shortcut.

## Trust and acceptance

The checker is Lean `4.33.1`. `sorry`, `admit`, project axioms,
`Classical.choice`, `native_decide`, `unsafe` and `partial` are prohibited in
the packet and implementation. Public theorem dependencies must remain inside
`propext` and `Quot.sound`. The axiom report also inspects both executable
entries; a proof-based fallback to a default answer is not accepted.

The breaker requires the counterexample module and the declaration-free stub
to build. The contract and axiom report must be red solely because the eight
promised names are absent. The complete diagnostic set is recorded after
verification with `-DmaxErrors=10000`; parse errors, import failures and errors
in independent positive controls block the freeze. Both red modules must be
declared in `test/fixtures/trust-gate/known-red.txt` and removed when green.

The builder runs the new narrow battery, axiom report, counterexamples, the
unchanged old frame packet, the package build, declaration/dependency checks,
pinned host prefix gate and compiled mutations. The existing declared
byte-parser and binary-race failures cannot be counted as new packet success
or removed to manufacture a full-build pass. No runtime coverage row changes
in this packet. Generated joins affected by the appended register rows are a
separate owned obligation, not an excuse to edit existing projections.

The breaker handoff freezes source hashes and exact red diagnostics below.

## Freeze evidence

Verified at `2026-09-03 05:55:12 UTC`, from base
`bfda8d8bd25929662f89a036efc231769adcc88d` on the isolated
`codex/live-stack-integration` branch. No builder implementation is present.
The resumed direct contract, axiom and counterexample checks reproduced these
results at `2026-09-03 06:01:59 UTC`. All sixteen recorded source hashes still
matched, and each existing source matched its base-commit bytes.

| Command | Recorded result |
| --- | --- |
| `lake build Effect4.Runtime.LiveStack Effect4Test.Counterexamples.Runtime.LiveStack` | Exit 0, six jobs. The declaration-free stub and the independent counterexamples built. |
| `lake env lean -DmaxErrors=10000 Effect4Test/Counterexamples/Runtime/LiveStack.lean` | Exit 0 after the final witness edit. Nine theorem receipts: eight depend only on `propext`; `cause_tags_do_not_identify_annotations` has no axioms. |
| `lake env lean -DmaxErrors=10000 Effect4Test/Runtime/LiveStackContract.lean` | Exit 1 with 19 unknown-constant errors naming only the eight promised declarations, plus two consequent unavailable-evaluation diagnostics at the final candidate guards. The literal-table positive control and the 13/9 nonempty case counts passed. No parse, import, field-resolution or independent-helper error remained. |
| `lake env lean -DmaxErrors=10000 Effect4Test/Runtime/LiveStackAxiomReport.lean` | Exit 1 with exactly eight unknown-constant errors, one per promised declaration. |
| `lake build Effect4Test.Runtime.FramesContract Effect4Test.Runtime.FramesAxiomReport Effect4Test.Counterexamples.Runtime.Frames` | Exit 0, seven jobs; Lake reused the unchanged existing frame build. This is not presented as a fresh rebuild of that old packet. |
| `lake build` | Exit 1. The final failure list is exactly `Effect4Test.Runtime.LiveStackAxiomReport`, `Effect4Test.Runtime.LiveStackContract`, `Effect4Test.Protocol.ByteParserContract` and `Effect4Test.Concurrency.RaceRepresentativeContract`. The first two are this declared red packet; the last two were already declared red at the base. |
| `./scripts/check-internal-citations.sh` | Exit 1 with four pre-existing violations in two unchanged research documents. No violation is in the live-stack packet. |
| `git diff --check` | Exit 0. |

The citation failures are in
`docs/research/2026-09-02-effect4-of-ocaml-review/integration-review.md`
at line 89, and `docs/research/2026-09-02-schema-consumer-survey.md`
at lines 508, 521 and 522. Both files were checked byte-for-byte against the
base commit and remain outside the breaker fence. They are not repaired by
this packet, and the failed repository check is not reported as a pass.

The complete expected contract diagnostic inventory is four missing
`Effect4.FrameFiber.popLive` references, nine missing
`Effect4.FrameFiber.getContLive` references, and one missing reference for
each of the six public theorem names. Its last two guards additionally report
`cannot evaluate code` because those missing functions left elaboration errors.
Those blocked guards are not semantic-negative receipts. Every other error
category, unknown name, failed positive control or changed case count blocks
the breaker freeze. The axiom report's expected set is exactly the eight
public names listed above, each once. Both modules are declared red in
`test/fixtures/trust-gate/known-red.txt`.

The following SHA-256 values identify the old sources held unchanged and the
independent test packet. This table is a freeze record, not a generated
closure override.

| File | SHA-256 |
| --- | --- |
| `Effect4/Runtime/Runtime.lean` | `fa73134f37da77489bfc4bb14776d32a482171d0f43c9fcc3e26bd811075ccd4` |
| `test/contracts/frames.contract.md` | `03b162e30538eecee5e91c10efa8ccb4289cf80c1922f6ae8569598b0c569b48` |
| `docs/FRAMES-DAG.md` | `78738c025b1f13db14bb9b04fb6448de921252d69e635a7981eeb1165d98dd9a` |
| `Effect4Test/Runtime/FramesContract.lean` | `f52f93567af2cda199c6f82431b5201b6f0319839914f25a5f9b0e0b3a26296d` |
| `Effect4Test/Runtime/FramesAxiomReport.lean` | `02391a0afd9bcae89d216765db51d92ab5b574c6d7bcd5c852ac8f1576ba8cae` |
| `Effect4Test/Counterexamples/Runtime/Frames.lean` | `8038b59ab9826fb0099a38b31df60c965b9ba5f315fedc6fbcbedef528ce44a3` |
| `Effect4/Semantics/Cause.lean` | `fc7d008f2955a5ea812717a77e2f3e3d187980c924fc0cb25d5014644c7f7196` |
| `Effect4/Semantics/Exit.lean` | `a4a4c024ad54a8ab6e52acc1493183349bb532e668af0ed7c2512fa134161383` |
| `vendor/effect-4.0.0-rc.112/src/internal/effect.ts` | `0e32b42fbc8901ae75419fbd2999bf5c96b40e4bb54cc42c4fc2ec778cc641f0` |
| `vendor/effect-4.0.0-rc.112/src/internal/core.ts` | `233b7a1fb3a53b9f49f63c01f810052cb174cc13742f52ea2e8bd482f302fd11` |
| `lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lakefile.toml` | `bb0c3b670f01d7f7599400a1329a49301d126c2eeeed36d6e64fd80112e3522d` |
| `harness/fiber-supervision/host-pin.json` | `aeb20902b93b6ca00278f55ff857340542b43c35240bcf23890e54f97be5af85` |
| `Effect4Test/Runtime/LiveStackContract.lean` | `3b48462973b45a09b9fa95e4cf567372dffd6166b7a787548e8af51827a9254a` |
| `Effect4Test/Runtime/LiveStackAxiomReport.lean` | `e7a84c14d4262bfd7b6936eeedee531330aacc7c991141d2b1d196cd701a6a76` |
| `Effect4Test/Counterexamples/Runtime/LiveStack.lean` | `af2e8579e456fbf556c2261de7f64433d6be3fe62cb019399a3c58f9cf72075c` |
