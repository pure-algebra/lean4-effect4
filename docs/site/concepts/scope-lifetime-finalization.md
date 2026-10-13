# Scope lifetime and finalization

This page explains scope lifetime and finalization in Effect4. It covers how resources are registered, how scopes close idempotently in reverse order, and how uninterruptible masks protect cleanup execution.

## The runtime concept {#runtime-concept}

Effect programs allocate managed resources such as database connections, worker threads, and file descriptors within scopes. In Effect rc.112, a scope guarantees cleanup upon normal exit or failure.

Effect4 models scopes as explicit containers in `Scope` (`src/Effect4/Machine/Scope.lean`). Each scope maintains an insertion-ordered table of registered finalizers.

Closing a scope executes registered cleanup routines to ensure that allocated resources do not leak.

## Literature foundations {#literature}

The metatheory adapts region-based resource management from ATTAPL ch. 3 (Henglein, Makholm, Niss). In that framework, resource lifecycles align with structured computational regions.

Stack unwinding and abnormal exit handling adapt Harper (PFPL ch. 28). Control stacks manage cleanup frames during evaluation and failure unwinding.

## What Effect4 keeps and what it cuts {#adaptations-and-cuts}

Effect4 keeps dynamic scope allocation and insertion-ordered finalization tables. It models scope presence in the world using `ScopeLive` (`src/Effect4/Laws/Program/Typed/World.lean`).

Under decisions row 156 (`E4-RUN-CE-001`), Effect4 enforces state-first unwinding:
- The scope transitions to closed before running any finalizer.
- Re-entrant registrations on a closing scope execute immediately.
- Finalizers run in strict reverse registration order (`closeOrder_eq`, `E4-RUN-CE-002`).
- Closing an already closed scope is idempotent and returns without re-executing cleanup (`close_twice`, `E4-RUN-CE-003`).

Effect4 cuts operations on absent scopes (`E4-SCHED-CE-020`). Operating on a missing scope handle halts the machine because dangling handles are invalid. Defect transmission is restricted by `ShapeFree` (decisions row 152).

Uninterruptible masks protect cleanup execution by saving the fiber's interruptibility flag and restoring it on region exit (decisions rows 227 and 244).

## How to read the claims {#reading-claims}

The claims under this concept state that resource cleanup executes in predictable order without double execution or leaks.

Key properties to inspect:
- [`close-order-eq`](#claim:close-order-eq): Finalizers execute in strict reverse registration order.
- [`close-twice`](#claim:close-twice): Applying close repeatedly is idempotent.
- [`saved-mask-restoration`](#claim:saved-mask-restoration): An uninterruptible mask restores the previous interruptibility flag on exit.

These claims show that scopes release resources deterministically across all exit paths.
