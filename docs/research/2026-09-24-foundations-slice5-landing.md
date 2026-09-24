# Foundations slice 5: landing record (2026-09-24)

Slice 5 of the [packet](2026-09-21-codex-packet-divergence-and-slice-5.md), done in the
coordinator session on the owner's instruction, on top of the contract ruling (2026-09-23), the
protocol repair and decision row 90 (2026-09-24). Base `cd2acd46`. Nothing pushed.

## What is proved

| obligation | statement | gate |
| --- | --- | --- |
| `popR_typed` | delivering a typed exit to a typed stack either installs typed code over a typed remainder, or completes with an exit at the stack's final type; premises `HookLaws` and `InterruptProvenance` only | `Typed.M4Stack` |
| `saveAnswerR_typed` | installing an operation's code below its answer adapter keeps the saved state typed | `Typed.M4Stack` |
| `deliver_active` | a resume at the parked token installs the code, typed at the token's declared type, over the park's stack | `Typed.M4Stack` |
| `deliver_stale` | a resume at another token changes nothing | `Typed.M4Stack` |
| `hookLaws_interpR` | the reference interpreter meets the hook laws, so `popR_typed_interpR` needs no hook premise | `Typed.M5Hooks` |
| `capture_lookup` | a capture's release point is admitted at the checker's type, over the node's environment extended by the acquired value and the exit | `Typed.M3bAssembly` |

All at `[propext, Quot.sound]`. The walk's seven arms: masks restore a recorded interrupt
(clean); a guard runs its arm, misses through the arrow's skip, or is preempted and passes the
sanitized cause (`U-01`, clean); answer glue types its result through the pure and unguard
inversions; the async finalizer, iterator and loop arms use the hook laws. The brief's §3.3 hook
contracts closed outright rather than waiting for M5, because the repaired protocols state them.

The `Keeps` ladder (`Laws/Machine/Keeps.lean`, imports the fiber machine only): replacing a fiber
keeps every other field and the id list, a lookup at another id is unchanged, a lookup at the
replaced id finds the replacement; appending to the trace keeps every other field.

## What is defined and declared

`Typed/Assembly.lean`: `preds` (the generated bundle with the strong judgments: saved frames at
their fiber's declared type, strong exits, typed resumes, typed contexts, heap and promise cells
at their declared types, due completions at their token's declared type, admitted captures),
`TypedState` (validity, the whole-state predicate, and the active-delivery correlation),
`RReachable`, `AnswerOk`, `QueueOk`, `StepPreserves`. Declared, open:

- `typedState_load` (M5 initialization), ceiling 1;
- the transition ledger (M6): one `StepPreserves` obligation per command constructor (18),
  `decision_preserves` for a tape decision under an admitted answer, and the capstone
  `typedState_reachable`; ceiling 20.

The brief asked for M6 declarations per protocol row. After the repair every consumed row's post
types its answer, and a row's adequacy is exactly what the step that performs it must preserve,
so the ledger is declared per command, the boundary the machine's driver actually has. Two limits
of the generated bundle are recorded in the module: `PendingOk` sees the enclosing position, not
the fiber, and `RaceOk` pins only the host's parked token; the race's result type reaches the host
through `ResumeOk` on the resume it enqueues.

## Controls

`Test/Program/TypedStack.lean`: an error-removing catch accepted and its walk typed; the same catch
preempted, completing with the sanitized cause at `never`; a pass-through frame from `nat`/`nat` to
`nat`/`never` refused; a stale resume inert on a real parked machine (by reduction); the assembled
typed state elaborating over a reachable machine.

## Checks

`make check` exit 0: 496 modules, 67,932 declarations at `[propext, Quot.sound]`. Unique ledger
372 total, 339 proved, 33 open: the nine historical names, the three `M3bWorld` laws,
`typedState_load`, and the 20 ledger obligations. Evidence: `2026-09-24-slice5-evidence/`.

## What slice 5 did not do

The loaded admission of every corpus entry (the repair's acceptance test) is briefed separately
([loaded admission](2026-09-24-codex-brief-loaded-admission.md)); seven entries are proved. The
world-weakening laws stay declared.
