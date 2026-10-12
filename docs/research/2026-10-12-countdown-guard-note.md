# 2026-10-12 The countdown guard

Status: research note (history, not authority). Base: `6bab4ac42` on `land/tc-seat-B`.

**Withdrawn (2026-10-12).** The change below was not merged. The base had already removed
`Pending.waitingOn` (`256b60ac5`), which the guard reads. The owner then asked whether the guard
changes a run in 4.0.1: it does not, since rc.112 and 4.0.1 fire each countdown observer once. So
`Evaluating.countdown_parks_positional` stays a planned goal, and branch `land/tc-seat-B` stays
unmerged. Findings 1 to 4 remain the analysis of that goal.

## Question

The layer merge reads the exits of `awaitAll` by position (row 349): one column pair per target,
in target order. Can `ConfigTyped` keep such a countdown record over the machine as it stands?

## What was read or run (each with its evidence word)

- Reading: `fireObserver`, `countdownWalk` and `exitFiber` (`src/Effect4/Machine/Fibers.lean`).
- Reading: `fiberAwaitAll`, `addObserver` and the exit of a fiber in rc.112
  (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:779-811`, `:560-571`, `:619-624`).
- Reading: the same three in 4.0.1 (`vendor/effect-4.0.1/src/internal/effect.ts:804-836`,
  `:536-553`, `:605-617`).
- Reading: the observer and queue clauses of J, `StoredObserverOk` and `ObserverCommandOk`
  (`src/Effect4/Laws/Program/Typed/Scheduler.lean`), `QueueOk`
  (`src/Effect4/Laws/Program/Typed/Assembly.lean`).

## Findings (each with its evidence)

1. **A fired observer stays stored** (reading). `exitStore` publishes the exit, queues one
   `observe` command per stored observer, then `exitDone`. Neither `observe` nor `fireObserver`
   removes the fired observer. `exitDone` clears it after the last `observe`.
2. **The stale observer breaks a column condition** (reading). Take `awaitAll [s, t]` at the
   certificate `.tuple [exitOf A₁ E₁, exitOf A₂ E₂]`, with `s` declared at `A₁`, `E₁`. Let `A₁`
   not be below `A₂`. When `s` exits, its observer fires and the record waits on `t`. The exited
   `s` still holds its observer. A condition on the waited column then asks `A₁` below `A₂`.
3. **J types a duplicate command** (reading). No clause of J makes a countdown key unique.
   `ReservedKeysR` bounds the keys, and `QueueOk.observer` bounds the source. Two queued
   `observe s x (.countdown W tok)` commands are typed. The second appends one exit past the
   last position. The tuple then fails, since `ItemsFit` demands equal lengths
   (`src/Effect4/Laws/Program/Typed/Membership.lean`).
4. **The reference fires each countdown observer once, at its target** (reading). In rc.112 the
   walk registers one closure on its first live target (`:801-804`). The closure pushes the
   exit and resumes the walk. An exiting fiber calls each stored closure once (`:621-623`), then
   empties the list (`:624`). In 4.0.1 the walk is the same (`:826-829`). The exiting fiber
   detaches its list before it calls the closures (`:611-617`).

## The change

The coordinator ruled the change on 2026-10-12, with the owner's approval of a machine change
that simplifies.

- `fireObserver` acts at a countdown only when the found record waits on the firing fiber,
  `p.waitingOn = some id`.
- Otherwise it returns the machine with its `observerFired` event and no command.
- Under the guard, the arm does what it did before. No other arm changes.

## Why the guard drops no firing of the reference

- In the reference, a countdown observer is the one closure that the walk registered on its
  current target. It runs once, at that exit, before the walk moves on.
- The machine stores a countdown observer only on the current target of the record. The park
  and each advance store it. A cancelled park drops its token's observers (`dropToken`).
- So the machine queues a countdown `observe` only from the current target, when it exits. The
  guard holds at that firing.
- The guard drops a stale observer of an exited fiber, or a duplicate command. The reference has
  neither.

## What J drops

- `CountdownAt` loses its column condition. It holds the payload of the record only.
- `StoredObserverOk` at a countdown is `CountdownAt`.
- `ObserverCommandOk` at a countdown is `CountdownAt` and the exit typed at the declaration of
  the source.
- The payload reads no machine. Each remaining target is declared, so `MachineWide.fibers` gives
  its fiber at the observation.
- J needs no uniqueness of countdown keys. Under the guard, a stale or duplicate firing changes
  nothing but the trace.

## What this does not establish

- No theorem states that a run from a load never takes the dropped branch. The argument above is
  reading.
- The behaviour gates against the Effect runtime and the OCaml route are owed at the merge. The
  `lcnf` group reads `Effect4.Machine.Fibers`, so `make gen-lcnf` regenerates its four outputs.
- J is an invariant. It is not progress.
