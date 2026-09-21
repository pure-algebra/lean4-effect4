# Foundations slice 2 receipt

Merge note: this lands the interfaces, not M3a/M3b preservation. `TypedProg`, the named-frame
protocols, and the capture environment relation remain parameters. `park_extension` is an
explicit open obligation. No world-validity, arbitrary-world transport, scheduler-reachability
or host-execution theorem is claimed.

Base: `3aa1a9f1` (slice 1); original goal base: `3a1b456d`. Head: the commit carrying this
receipt on `codex/foundations-slices`, worktree `/private/tmp/effect4-foundations-slices`.
Nothing pushed; the original checkout and the owner decision register are unchanged.
Authority: the attached goal and `2026-09-20-foundations-plan-and-next-two-slices.md` §3.

## Changes

- `Typed/Vocabulary.lean` adds `Source.owner`. `Sources.lean` replaces the three saved-state
  fields plus six ScopeFrame rows with one `SavedOk` owner; the two capture rows with one
  `CaptureOk` owner; and the two resume answer rows with their constructor owners. The table
  goes from 95 to 86 rows. `RunMachine.races`, `RunFiber.context`, and `Env.Service.value` stay.
- `TypedStateDecl.lean` builds a structure clause over the entire owner, or a constructor
  clause over every argument. Predicate arguments are checked together for compatible types.
  Metadata fields are included even when they are not value positions. Accounting still
  refuses an owner row if no clause was emitted.
- Necessary wiring omitted from the brief's file list is in `TypedSources.lean` (decode the
  new source; share owner coverage) and `PositionGate.lean` (use that coverage in the join).
  A nested type reached outside an owner still needs its own rows. A second row under an
  owner is a duplicate, including plain metadata and transitive children. Constructor fields
  are read from declarations, using the census's naming rule; names alone never imply a
  containment relationship.
- `State.lean` deletes both `saved_from_clauses` declarations. `Frames.lean` re-pins from fresh
  output: RunFiber stays 16 theorems / 87 reused clauses / 9 premises; the other records stay
  46 theorems, with 68 reused clauses and 33 premises (formerly 90 / 27). Whole saved/capture
  clauses require a fresh premise for every field update.
- `World.lean` adds the per-fiber token table Θ, includes its pointwise extension in `World.le`,
  and adds `addToken`. Existing order and allocation proofs retain the token table. The
  `park_extension` marker asks for fresh-token growth and the inserted lookup, and stays open.
- New `Contracts.lean` contains the seven-arm frame judgment, composing stack judgment,
  shared-intermediate saved judgment, token-indexed resume judgment, structural interrupt
  provenance and capture-environment interface. `Laws.lean` imports it beside World.
- The focused audit files exercise the new interfaces, metadata distinctions, missing rows,
  duplicate coverage, shared child occurrences, single- and multiple-constructor owners,
  and frame premises. The named-bank red fixture now assembles one whole saved-state clause.
  `STATE.md` and `GENERATED.md` reflect the landed interfaces.

## Model record

| Carrier | Role / retained data | Boundary |
| --- | --- | --- |
| `Eff` | Existing canonical stored program; unchanged | No second stored syntax |
| `RProgram`, `ScopeFrame`, `RSaved` | Existing reference proof carrier; callbacks, seven frame forms, code, stack and interrupt fields retained | Higher-order proof carrier, not serialized program content |
| `FrameAccepts`, `StackAccepts` | Prop judgments over those carriers; each frame is an input/output arrow, cons shares its middle type | `TypedProg` and three named-hook protocols supplied by M3a; no `popR` agreement theorem here |
| `SavedOk` | One witness types current code and the stack input; separate interrupt provenance | The old independent field clauses are deleted |
| `World.Θ` / `ResumeOk` | Per-fiber token declaration and target/token/code correlation | Active parking must supply the lookup; stale/absent-token conditional is not a monotonicity theorem |
| `CaptureOk` | Environment relation at the capture's root/path with the entire capture passed through, including env, ctx, fuel and tape | Checker environment supplied by M3a |

Behavior remains the existing `popR` / `saveAnswerR` / scheduler. This slice changes no runner,
operation/answer alphabet, decision tape, fuel, live frontier, typed failure or refusal.
The observation in `ExitFits` is `CompletionOk` at the effect type's answer/error columns.
Masks retain the same input/output type; resume carries running and skipped-exit premises;
its failure-skipping premise is conservative over the frame's absent scheduler context.
Iterator, loop and asynchronous-finalizer arms retain explicit named-protocol premises
(`FrameProtocols`), since their names alone do not establish behavior. Those premises are
interfaces, not asserted facts. No safety, termination, divergence or fairness result follows
from merely constructing these relations.

`InterruptProvenance` is the structural scheduler condition: all recorded reasons are
interrupts and a deferred interrupt has a cause. It does not assert that an arbitrary record
has a reachable history. Reachability and the connection to `interruptRecord` are M3b/M4 work.
The relation does not classify interruption as a typed error. No new modality, extraction
pipeline, executable certificate or target realization is introduced.

The positive example `Contracts.Example.changing_middle` constructs Nat → Bool → Unit with
two answer frames; `middle_differs` proves the middle differs from each end. This checks the
interface with a named finite program relation, not the actual runtime's typing. Negative
controls distinguish resume targets and tokens, capture paths and roots, and a saved interrupt
flag. The token controls keep the same numeric token for two fibers at different types and
refute replacing an existing token declaration under `World.le`.

## Validation

The standalone Contracts build passed before the generator was edited (`contracts-first.log`).
Vocabulary and source rows were written before generator changes. Fresh generator output was
used to update the pins, not guessed expected output. `FinalAudit.lean` prints the actual kernel
declarations of Preds, TaskOk, CmdOk, RSavedOk, CaptureOk, the affected frame rules and contracts.

One extra adversarial check found that the initial coverage implementation accepted a duplicate
metadata row: `MetadataDuplicateRed.lean` failed its expected-refusal check in
`metadata-duplicate-red.log`. The coverage walk now includes all constructor fields for this
purpose. The same probe passes after repair, and the permanent battery retains this control.
The red log is failure evidence only, not a passing check.

Commands and final retained results:

- `lake build Effect4.Laws.Program.Typed.Contracts` before generator changes: exit 0.
- `make check-typed-state`: exit 0; existing omission and indexed-column controls retained.
- `lake build Effect4.Laws.Program.Typed.World Effect4.Laws.Program.Typed.State Effect4.Laws.Program.Typed.Contracts Effect4.Laws.Program.Typed.Frames Test.Program.TypedStateRulesRed Test.Audit.PositionCensus Test.Audit.TypedStateDecl`: exit 0 (`targeted-build.log`).
- `make build`, then `make check`: final build, trust/closure audit, fresh roots and generated
  drift; results in `make-build.log` and `make-check.log`.
- `lake env lean -DwarningAsError=true .../MetadataDuplicateRed.lean`: after repair, exit 0
  (`metadata-duplicate-green.log`).
- `lake env lean -DwarningAsError=true .../FinalAudit.lean`: declaration prints, exact checked
  references, open ledger names, and axiom output (`final-audit.log`).
- `git diff --check`.

The source gate reports 85 positions from four roots: 11 owner, eight custom, five exit,
three column, one refused position, six journal and 51 hook positions. There are still two
named refusals because the external-store refusal is an edge: external rows (DI-57) and
stored scope exits (DI-94). The skeleton emits 17 predicates / 10 carrier predicates / two
refusals. No runtime coverage count is inferred from these source counts.

Full-check and final ledger details follow below. Build log trailing whitespace is normalized
only when retained in Git; local raw copies retain the output verbatim. `make check-full`,
external host oracles and slice 3 were not requested in this goal.

```text
Effect4: 236 paired, 73 without a namesake, 0 mismatches
OPEN Effect4.Api.M1Origin.source_fork_site
OPEN Effect4.Api.TraceFacts.M1Trace.step_agrees
OPEN Effect4.Program.Guard.M4Handshake.parkHandshake_reachable
OPEN Effect4.Api.TraceFacts.M1Trace.reachable_agrees
OPEN Effect4.Api.M1Origin.source_two_race_sites
OPEN Effect4.Api.M1Origin.source_forkScoped_site
OPEN Effect4.Api.M1Origin.source_race_site
OPEN Effect4.Program.Typed.WorldWanted.park_extension
OPEN Effect4.Api.M1Origin.source_forkIn_site
OPEN Effect4.Run.M1Trace.observe_replace_trace
UNIQUE LEDGER: 309 total; 299 proved; 10 open
```

Both final `make build` and `make check` exited 0. The final trust audit checked 471 modules
and 66,791 declarations, with 138 API/utility modules and 199 Laws-only modules reachable.
Semantic/test axioms remain `[propext, Quot.sound]`; the unchanged implementation boundary
permits `Classical.choice` in 14 exact modules and 29 exact declarations. The changed world
proofs and the two-frame example use `[propext, Quot.sound]`; the middle-type distinction uses
no axioms; whole-owner frame rules use `[propext]`. No audit boundary was broadened.

The kernel print confirms:

```text
SavedOk  : W → Expect → RSaved → Prop
ResumeOk : W → Expect → FiberId → Nat → RProgram → Prop
CaptureOk : W → Expect → Capture → Prop
```

`generator-first.log` and `frames-first.log` retain the initial count-pin failures: their
fresh output is the evidence used to update the expected counts. They are not passing builds;
the later focused build and both full checks verify the re-pinned state. The metadata red
and green logs likewise record distinct runs, with the red kept as failure evidence.
