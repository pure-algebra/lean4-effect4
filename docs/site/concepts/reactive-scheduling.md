# Reactive scheduling and machine invariants

This page explains reactive scheduling and machine invariants in Effect4. It covers how concurrent fibers step cooperatively, how configuration invariants exclude stuck states, and why invariant safety is distinct from progress.

## The runtime concept {#runtime-concept}

Effect programs schedule concurrent fibers using cooperative yields, callback dispatchers, and queue processing. In Effect rc.112, the runtime manages fiber queues and interleaves execution.

Effect4 reifies this behavior as an operational small-step transition system in `RunMachine` (`src/Effect4/Machine/Fibers.lean`). Commands and scheduling choices execute from explicit decision queues.

Scheduling coordinates multiple fibers, dispatches armed listeners, and handles asynchronous completions cleanly.

## Literature foundations {#literature}

Machine type safety builds on the syntactic approach of Wright and Felleisen (1994). Small-step concurrent transition systems adapt the models in Harper (PFPL chs. 39–41).

Invariants and execution trace properties adapt Owicki and Gries (1976) and Manna and Pnueli (1991). Safety methods establish trace inclusions following Lynch and Vaandrager (1995).

## What Effect4 keeps and what it cuts {#adaptations-and-cuts}

Effect4 keeps small-step execution driven by explicit data decisions (`RunDecision`). Configuration typing is governed by the invariant `ConfigTyped` (`src/Effect4/Laws/Program/Typed/Assembly.lean`).

Under decisions row 139, Effect4 strictly separates invariant consequences from progress:
- The theorem `machineTyped_not_halted` states that a typed machine is not halted.
- That fact is an invariant consequence, not operational progress.
- Operational progress additionally requires classifying states as finished, stepping, or waiting at a live frontier.

Effect4 cuts unbounded tokens by enforcing `keysBelow` in `QueueOk` (decisions row 106). Queued observer and enrollment identifiers are bounded below `nextId` (decisions rows 134 (e) and 189).

Administrative markers such as raw scope exit callbacks are excluded from general program typing (decisions row 188). Finite queue fairness (`flush_fair`) states that, with enough command fuel, each owner armed at the start is entered. It takes at most as many rounds as there are owners.

## How to read the claims {#reading-claims}

The claims under this concept state that machine transitions maintain configuration validity and that scheduling queues behave fairly.

Key properties to inspect:
- [`machine-typed-not-halted`](#claim:machine-typed-not-halted): A typed machine state never halts at an invalid stuck configuration.
- [`flush-fair`](#claim:flush-fair): Armed callback owners fire within a bounded number of execution rounds.
- [`frontier-names-work`](#claim:frontier-names-work): An unfinished machine whose tape runs out waits at a frontier, which is empty exactly at deadlock.

The table of claims on this page gives each claim's status and its statement.
