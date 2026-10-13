# The fiber machine

This guide explains the Effect4 fiber machine on one page. It defines how fibers execute, how stacks manage frames, how tapes supply decisions, how scopes finalize resources, and how runs advance.

## What the machine is {#machine-overview}

The fiber machine is an abstract state machine that executes compiled program code. Its state is represented by `RunMachine` (`src/Effect4/Machine/Fibers.lean`).

The machine holds:
- Active and suspended fibers.
- Shared mutable stores for references, deferreds, and scopes.
- Fresh identifier counters.
- Queues for pending commands and external host answers.
- A trace of diagnostic execution events.

Every choice the machine cannot make alone is a decision on a tape. So a run is a function of its program and a tape that answers every decision. The scheduling rules are on the page [Reactive Scheduling](../../semantics/reactive-scheduling/).

## Fibers and the root {#fibers}

A fiber is a thread of execution in the machine, identified by a `FiberId`. Each fiber holds its own continuation stack, its interruptibility and its context.

A run begins with exactly one root fiber. The root fiber runs the loaded program (`Api.load`).

A running fiber can spawn child fibers using explicit fork operations. When a fiber terminates, it produces an exit value indicating success or failure with a cause.

## Frames and continuation stacks {#frames}

A continuation frame represents a defunctionalized step waiting for a sub-computation to finish. The machine stores frames in a first-order list on the fiber.

When a fiber starts the first part of a sequence or of a handler, it pushes a frame that holds the rest. When that part finishes, the machine pops the top frame and gives it the result.

Frames are first-order data, not host closures, so a machine state can be inspected and replayed.

## Decisions and tapes {#decisions}

A decision is one choice the host makes for the machine (`RunDecision`, `src/Effect4/Machine/Fibers.lean`). It evaluates a fiber, flushes the queued tasks, answers a host call, interrupts a fiber or advances the clock.

A decision tape is the list of decisions, read in order. Because the decisions are data, a concurrent run can be replayed exactly.

A program's full meaning is a relation over decision tapes. A tape that answers every decision fixes one run.

## Live frontiers {#frontiers}

A frontier is a machine state where the run waits. It waits for a budget, a host answer, a timer or a decision (`FrontierReason`).

A frontier is live:
- A frontier is never a typed error.
- A frontier is never a defect or failure cause.
- A frontier is never a located refusal.

When a run reaches a frontier, the machine pauses cleanly with its state kept intact. Execution resumes whenever a caller provides additional budget or answers the pending choice.

## Scopes and finalization {#scopes}

A scope holds the finalizers that release its resources (`ScopeState`, `src/Effect4/Machine/Scope.lean`). The page [Scope Lifetime and Finalization](../../semantics/scope-lifetime-finalization/) gives its claims.

When a scope closes:
- it closes once, and a second close keeps the first exit;
- a sequential scope runs its finalizers in the reverse order of their registration, each with the closing exit;
- a finalizer registered after the close runs at once, with the closing exit.

A finalizer runs whether the work succeeded, failed or was interrupted, and it receives that exit.

## Uninterruptible regions {#masks}

An uninterruptible region saves the fiber's interruptibility, turns it off for the region, and restores the saved value at the region's end.

An interrupt that arrives inside the region is recorded and deferred, never dropped. The fiber receives it when its interruptibility returns (`FrameFiber.deferredInterrupt`).

A `restore` inside the region gives its part the interruptibility saved at the region's entry. Inside an outer uninterruptible region, that part stays uninterruptible.

An explicit close of a scope runs its finalizers uninterruptibly, as Effect 4.0.1 does (decisions row 359).

## How a run proceeds {#execution-flow}

A run begins when `Api.load` places a program in the root fiber, with empty stores. The page [Store Typing](../../semantics/store-typing/) says what the stores may hold.

At each step the tape's next decision says what the machine does, and the frame machine runs the chosen fiber's code.

A run ends in one of three outcomes (`Outcome`, `src/Effect4/Api.lean`):
- finished: the root fiber has exited, with a value or with a failure's cause;
- a frontier: the run waits, live, for a budget, a host answer, a timer or a decision;
- stuck: a halt on malformed code, which a typed program never reaches (`machineTyped_not_halted`).
