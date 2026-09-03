/-
Counterexample witnesses for the sequential projection of two fibers (packet
M3). Both rows are *host-only protocols*: they name a fact about rc.112's run
loop that the Lean face cannot carry, and the repair each forces is a refusal,
not a definition. Register: `test/counterexamples/REGISTER.md`,
`E4-SEM-CE-010` and `E4-SEM-CE-011`.

Doc comments cannot precede `#guard`, so the receipts carry line comments.
-/

import Effect4.Concurrency.FiberFamily

namespace Effect4Test.Counterexamples.Concurrency.FiberProjection

open Effect4.FiberFamily

/-! ## E4-SEM-CE-010 — `join` of an interrupted child has no Lean answer

The attacked statement: *the `Fibers` handler can answer every operation of the
family, so every program over it has a golden.*

rc.112 `Fiber.join` of an interrupted child fails the joining fiber with an
`Interrupt` cause, and the run ends `{"interrupted":true}` (probed against the
pinned install; `harness/fiber-supervision/runtime-check.ts` pins the same
disposition through `E4-CONC-CE-025`). The family's abort channel is `Nat`, so
the only outcome the Lean face can produce here is `{"failure":n}` for some
invented `n`, and every registered mask keeps the outcome — the two faces
cannot agree under `outcome`, `m1` or `m2`.

The forced repair is a refusal: the handler sets `FiberTable.stuck`, and
`harness/trace/Generate.lean`'s `fiber-golden` arm refuses to emit a golden for
a program that sets it. No program of the corpus reaches this arm, so it is
only reachable by planting one, which is what this witness does. -/

/-- Fork a child that can never complete, interrupt it, and join it. -/
def joinInterrupted : Effects.Program Fibers.Sig Nat :=
  Fibers.fork 4 >>= fun child =>
    Fibers.interrupt child >>= fun _ =>
      Fibers.join child

-- The projection refuses: the run is marked stuck.
#guard fiberStuck joinInterrupted [(0, true)] == true

-- What it would have emitted if it did not refuse: a *failure* outcome, where
-- the host's is `{"interrupted":true}`. The two are different rows under every
-- mask, which is why the emitter refuses instead of writing this golden.
#guard (fiberGoldenLog joinInterrupted [(0, true)]).getLast? ==
  some (.done (.failure (.nat 0)))

-- The same refusal for a child that was never given the processor: interrupted
-- before it ran, it published an interruption just the same.
#guard fiberStuck (Fibers.fork 4 >>= fun child =>
    Fibers.interrupt child >>= fun _ => Fibers.join child) [(0, false)] == true

-- The positive control: joining a child that *failed* is answered, not
-- refused, and the outcome is that child's typed error resumed here.
def joinFailed : Effects.Program Fibers.Sig Nat :=
  Fibers.fork 2 >>= fun child => Fibers.join child

#guard fiberStuck joinFailed [(0, true)] == false
#guard (fiberGoldenLog joinFailed [(0, true)]).getLast? == some (.done (.failure (.nat 1)))

-- And joining a child that succeeded.
#guard fiberStuck (Fibers.fork 0 >>= fun child => Fibers.join child) [(0, true)] == false
#guard (fiberGoldenLog (Fibers.fork 0 >>= fun child => Fibers.join child) [(0, true)]).getLast? ==
  some (.done (.success (.nat 11)))

-- A child that can never publish and is never interrupted is refused too: the
-- host deadlocks there and the projection has no answer to invent.
#guard fiberStuck (Fibers.fork 4 >>= fun child => Fibers.awaitValue child) [(0, true)] == true

/-! ## E4-SEM-CE-011 — a `false` decision is not a fact about the run

The attacked statement: *the sequential projection's interleaving is a property
of the program and its tape, so a golden holds at any host yield setting.*

It does not. The tape drives `TapeScheduler.shouldYield`
(`harness/trace/tracer.ts`), but rc.112's run loop also yields on its own once
`MaxOpsBeforeYield` is reached, and at the floor of 3 — the setting every other
family's goldens are re-run at in `scripts/check-trace-host.sh` — a child the
tape left queued starts anyway, with no `decide` row to account for it. Probed
against the pinned install for `emptyRacePendingUntilInterrupted`:

```
trace fiber.emptyRacePendingUntilInterrupted mask m1 DIVERGES at row 3
  expected: answer	started	[]
  actual:   answer	started	[4, []]
```

The forced repair is again a refusal: the `fiber` section of
`scripts/check-trace-host.sh` runs at the default threshold only, and says so.
Scheduler-order insensitivity is not claimed and is not claimable until a
two-fiber model exists.

The Lean half of the witness is that the decision is *load-bearing*: the same
program under the two tapes has different rows, so an unaccounted host yield
cannot leave the trace alone. -/

def pending : Effects.Program Fibers.Sig (List Nat) :=
  fiberEmptyRacePendingUntilInterrupted 0

-- Under `false` nothing runs; under `true` the child runs and is cleaned.
#guard (fiberGoldenLog pending [(0, false)]) != (fiberGoldenLog pending [(0, true)])

-- Exactly which rows move: the `started` answer, the `cleanups` answer, and
-- the outcome, which is the run's whole observable content here.
#guard (fiberRun pending [(0, false)]).2.startOrder == []
#guard (fiberRun pending [(0, true)]).2.startOrder == [4]
#guard (fiberRun pending [(0, false)]).2.cleanupOrder == []
#guard (fiberRun pending [(0, true)]).2.cleanupOrder == [4]
#guard (fiberGoldenLog pending [(0, false)]).getLast? == some (.done (.success .unit))
#guard (fiberGoldenLog pending [(0, true)]).getLast? ==
  some (.done (.success (.pair (.nat 4) .unit)))

end Effect4Test.Counterexamples.Concurrency.FiberProjection
