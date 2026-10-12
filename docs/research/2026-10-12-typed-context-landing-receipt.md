# Typed-context landing: receipt (2026-10-12)

**Know this first.** M6 and M7 hold modulo five planned goals, and all five are placed. Four wait on
the restore slot. The fifth is the positional countdown park:

| Planned goal | Path | Waits on |
| --- | --- | --- |
| `clause_closeScope` | `src/Effect4/Laws/Program/Typed/Commands/Evaluate.lean` | the restore slot |
| `Evaluating.settle_callback` | `src/Effect4/Laws/Program/Typed/Commands/Evaluate.lean` | the restore slot |
| `clause_scoped` | `src/Effect4/Laws/Program/Typed/Commands/Evaluate.lean` | the restore slot |
| `foreignFinalizer_ambient` | `src/Effect4/Laws/Program/Typed/Commands/Clauses/Close.lean` | the restore slot |
| `Evaluating.countdown_parks_positional` | `src/Effect4/Laws/Program/Typed/Commands/Clauses/Park.lean` | `J` ruling out a stale or duplicate countdown firing |

The restore slot is what Effect 4.0.1 does (`updateContext` pushes its restore frame with
`onExitUnsafe` in the same step as the switch). Its plan is
`docs/research/2026-10-12-restore-slot-plan.md`. The positional countdown goal is no runtime
question: rc.112 and 4.0.1 fire each target's observer once (`fiberAwaitAll`).

## Base and head

- Base: `refactor/phase1-phase3` at `68856e778`, merged into `land/typed-context` at `8da469a1c`.
- Head: `land/typed-context`, the commit that adds this receipt. The Test triage is seat C's
  branch `land/tc-test` (base `048da962f`), merged.

## What changed

- One ambient judgment, `AmbientProg`. Every program's failure row is within its entry row,
  interruptible or not. The machine typing, `MCodeOk` and `MHostStack`, is at it.
- Every clause file under `src/Effect4/Laws/Program/Typed/Commands/Clauses/` is migrated: Answer,
  Store, StoreScope, StoreDeferred and StoreRef (seat B); Iter, Gen and Loop (seat A); Park, Spawn,
  Command, Close and Async; then `Typed/Edits.lean`.
- A point that a fiber operation enters carries its parameters' stack typing at the entry row
  (`AmbientPointTyped` in `ambientFiberPre`'s scoped, forkIn, forkScoped, gen and race arms;
  `AmbientStackTyped` in the loop arm). M5's producers record it.
- A race entrant is typed at an entry row within the registering reply's row (`EntrantsWithin`).
  `ChildCode` and `RacePayload.programs` are cut: only transports read them.
- A finalizer is typed by `AmbientFinalizerTyped`. Every finalizer but a captured release is
  administrative code, lifted by `ambientProg_of_admin`.
- The registry claim `close-seq-protocol` points at `Effect4.Program.Typed.closeSeqProtocol`.
  The batteries `Test/Program/ProtocolPosts.lean` and
  `Test/Counterexamples/Machine/Semantics/AwaitLoad.lean` are retired (history at
  `git:68856e778:Test/Program/ProtocolPosts.lean` and
  `git:68856e778:Test/Counterexamples/Machine/Semantics/AwaitLoad.lean`).
- Seven corpus rows move: the checker now refuses a raw context read at a closed row. They are
  named in the compatibility policy's `verdict_moves`.

## Commands and results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4 Effect4.Laws` (merged tree) | 1079 jobs, success |
| `#axiom_audit` over the 142 modules the landing touches | 37027 declarations within `[propext, Quot.sound]`; 25 modulo planned goals; 5 planned goals |
| `make -k gen` | every group regenerated, `semantics` included |
| `make -k check-full` | every gate passes except `check-schema-ts` and `check-corpus` |
| `EFFECT4_EFFECT_NODE_MODULES=<main checkout>/harness/schema-host/node_modules make check-schema-ts` | pass (the worktree has no install of its own) |
| `make gen-corpus-results`, then `make check-conservativity BASE=HEAD` | 7 rows promoted; self-test 29 of 29; PASS, 4 of 4 clauses |

The truth, host-protocol, schema-codec, native, compiler, OCaml, target, ts-reader, tsdiag and
ingest gates pass in the `check-full` run.

## Open obligations

- The five planned goals above.
- Two Lean docstrings cite the retired battery: `src/Effect4/Laws/Program/Typed/Residual.lean`
  and `src/Effect4/Laws/Program/Typed/Membership.lean`. Edit them with the next upstream change,
  to avoid a full rebuild for a comment.
- `Test.Audit.ProofStyle` fails, as it does on `refactor/phase1-phase3` before this landing: 176
  findings, of which 170 are stale baseline entries. Its repair is a separate task.
- `popR_hostTyped` and `deliverR_hostTyped` (`src/Effect4/Laws/Program/Typed/HostWalk.lean`) have no
  consumer since `Test/Program/HostWalk.lean` retired. They are cleanup candidates.
- Unverified: once `Test.All` builds, the goal gate's `restingPin` list
  (`Test/Audit/AxiomGate.lean`) may need the declarations that now rest on the planned goals.

## The batteries (seat C)

The owner ruled on 2026-10-12. A battery that refutes a copy of a superseded definition retires,
and so does one that restates a theorem. A reader of a live law, a control and a finite evaluation
stay.

- Repaired: AnswerGate (42 fiber constructors), ProofGraphPlan,
  TyTables, TyViewContract, FragmentCensusContract, HandlesContract, ReadOnlyStoreClauses,
  SemaphoreTraces, PoolTraces, MemoTable, WriterPhase and the Atomic writer chain,
  TypedDenotation, ScopeExitCallback, AdmissionCensus.
- Retired, history at `git:68856e778:<path>`: ProtocolPosts, AwaitLoad, ValueMembership,
  StaleCode, M6Capstone, FramesNotKripke, LoopProtocols, TimerColumn, WaiterColumn, FitsOrder,
  RawOrderLoad, H1Shapes, TrivialPosts, LoadedAdmission, RegistrationColumn, EnrollmentBound,
  LaunchEntrant, RegistrationYield, HostWalk (the battery).
- 27 register rows moved to `Test/Counterexamples/Archive/REGISTER.md`, each with its retirement
  status and its history citation.
- SemaphoreTraces' and PoolTraces' budget windows moved by +5 operations. The masked provider
  entry (`c2a1cdda4`, on the base) runs more counted steps. The windows were recomputed by a probe,
  and every red control still separates its window.

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=2 lake build Test` (seat C, merged tree) | 1951 jobs; fails only on `Test.Audit.ProofStyle` |
| `#axiom_audit` over the Test modules touched, two rounds | 734 and 666 declarations within `[propext, Quot.sound]` |
| `python3 -I scripts/check-docs.py` | pass |

## Proposed decisions row 349 update

Row 349 (option A, a typed context reader and a `provideContext` region): landed 2026-10-12. The
machine's typed state is at the ambient judgment. M6 and M7 hold modulo the five goals above.

## Evidence kind

Everything above is Lean proof or a named gate's run. Nothing is bounded or host-only, except the
truth and host-protocol gates, which compare with the Effect runtime on their corpora.
