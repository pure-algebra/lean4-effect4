# Typed-state protocol repair (2026-09-24)

The repair the [typed-state admission audit](2026-09-23-typed-state-admission-audit.md) §6
proposed, landed on the owner's instruction after the census and the dynamic lane (decision row
89). The machine, stored syntax, decision tapes and the axiom ceiling are unchanged; this is a
proof-side repair of `Typed/Admission.lean` and `Typed/Residual.lean`.

## What landed

Every fiber or store row whose answer generated code consumes now certifies that answer's type,
and its precondition pins the certificate to what the machine installs or what answers it.
Most of these rows do not hand their answer back directly: the evaluator saves the continuation
as a stack frame and installs code (a body, a race, a generator, a park), and the answer arrives
through the stack walk (`evaluateFiberR`, `EvaluateR.lean:162-280`). So the post is "an exit at
the certified type", as the mask row already had.

| row | certificate | precondition | post |
| --- | --- | --- | --- |
| `scoped`, `forkScoped`, `forkIn` | the body's `EffTy` | the body's point checks at it (`PointTyped`) | an exit at it; a fiber declared at it |
| `gen`, `loop` | `EffTy` | the node's own point checks at it | an exit at it |
| `raceAll` | `EffTy` | every entrant's point checks at a subtype | an exit at it |
| `async` | `EffTy` | a timer's `unit`, a deferred's promise-table columns, a host row's table columns, below it | an exit at it |
| `raceRegister`, `async` on a host slot | `EffTy` | none: the race state or host protocol pins it | an exit at it |
| `awaitAll`, `awaitAllFailFast` | `Ty` | the list of the targets' exit types, through the fiber table | a strong value at it |
| `snapshotChildren` | `Ty` | the checker's `list (fiberOf unknown unknown)` | a strong value at it |
| `getContext` | `Ty` | the checker's `Context` handle | a strong value at it (shape only, below) |
| `awaitNewChildren` | none | none | `unit` |
| `construction` | none | none | each completed exit at its fiber's declared type |
| `frontier` | none | none | `False`: fuel exhaustion is never answered |
| `refModify`, `refModifySome` | none | the cell is declared | a `nat` (the row's column) |
| `deferredPoll` | none | the deferred is declared | a `bool` |
| `memoBuild` | none | none | a scope handle |
| `memoGet` | none | none | `unit` or a memo hit (shape only, below) |

Two more findings of the audit's kind were repaired with them:

- `forkIn`'s post named its fiber's type existentially (`∃ c`), which types nothing; it now
  names the certified type, as `fork` does.
- `HandlesFit` required a fiber's declared type to equal the handle's, while the checker's
  `Ty.sub` is covariant in fibers, so a widened handle (`fiberOf unknown unknown`) never fit. It
  is covariant now; refs and deferreds stay invariant, as in the checker.

Source admission reads the program's host-row table: `ProgramSource` carries the program and
its table (a bare program coerces with the empty table), and `PointTyped` checks under it
(`E4-SCHED-CE-014`). The three world-weakening laws are declared under `Typed.M3bWorld` at
ceiling 3 (`strongValue_mono`, `strongExit_mono`, `typedProg_mono`).

## Checks

- `Test/Counterexamples/Machine/Semantics/TrivialPosts.lean`: the five CE-013 shapes, now
  typed (the sleep code, the join-all, a performed modify, the frontier, a callback reading a
  completed exit), and CE-014's repair (`hostBody_admitted`).
- `Test/Program/LoadedAdmission.lean`: the code the reference machine loads for five
  checker-typed programs (`sleep`, `fork`, `scoped`, a race, a generator) is typed at the
  checker's type, at every world. The source checks inside are kernel-evaluated.
- `Test/Program/AdmissionCensus.lean`: no consumed row keeps a `True` post
  (`fiberPostTrivial_sound`); 1,203 of the 1,349 context programs reach no shape-only row.
- The dynamic lane is unchanged and clean (34,336 runs; the repair is proof-side).
- `make check` exit 0: 492 modules, 67,753 declarations at `[propext, Quot.sound]`. Unique ledger
  345 total, 333 proved, 12 open (the nine historical names and the three `M3bWorld` laws).
  Evidence: `2026-09-24-protocol-repair-evidence/`.

## What is not done

1. **Contexts (decision row 90).** The context read's post types the context as a handle but
   not its services, and a memo hit's cell has no type, so every program that reads a service or
   builds a memoized layer (146 of the 1,349 context programs, 11 of the 77 entries) is still
   untypable. Typing them needs a typing of the fiber's context, a representation decision.
2. **Admission of every corpus entry.** Five loaded programs are proved; the other entries,
   most of which pass through `bind`'s guard and construction, follow the same pattern with value
   inversions. Briefed to Codex:
   [loaded admission](2026-09-24-codex-brief-loaded-admission.md).
3. **Adequacy.** Each strengthened post must be true of the machine. That is stated over the
   typed state (slice 5 §3.6), with the race-state and host-slot correlations owned by the state
   predicate. Empirically, every row whose answer can become a root exit was exercised by the lane
   with no violation.
4. **World weakening.** Declared, not proved.
