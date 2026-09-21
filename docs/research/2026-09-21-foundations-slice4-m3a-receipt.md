# Foundations slice 4 receipt: M3a residual, admission, and settling cases

Merge note: The unheld M3a foundations are proved and checked. This includes strong values
and exits, D13 lexical source admission, control admission and marker payload inversion,
Store Protocol Ψ_S (31 SyncOp rows with ghost certificates), Fiber Protocol Ψ_F (40 FiberOp
rows with dependent carriers under `#answer_gate`), concrete `TypedProg`, interpreter hook
contracts, and the two settling program cases (polymorphic ref allocation on a heterogeneous
heap and addressed fork/mask with body admission). The dependent stack (`popR_typed`,
`saveAnswerR_typed`) and interruption preemption (`DeliveryStateOk`, `FrameAccepts.resume`
replacement) remain held under counterexamples `E4-SCHED-CE-006` and `E4-SCHED-CE-007`.

Base: `5a9611c42f026a79ee0ca2c6114eb972dc0ff7bf` (the independent foundations commit).
Head: the commit carrying this receipt (`git log -1 --format=%H -- <this path>`).
Branch: `codex/foundations-slices-3-4`; checkout: `/private/tmp/effect4-foundations-slices`.
Nothing pushed. The original checkout and its local document edits are retained.

The scope and plan were established in `2026-09-21-foundations-slice4-m3a-plan.md`.

## Statements and proof boundaries

| Ledger | Statements | Final gate |
| --- | --- | --- |
| `Effect4.Program.Typed.M3aAdmissionObligations` | `unguard_payload_inv`, `finishFinalizer_payload_inv` | 0 open, 2 proved, ceiling 0 |
| `Effect4.Program.Typed.M3aResidualObligations` | `settling_ref_allocation`, `settling_ref_preserves_nat`, `settling_fork`, `settling_mask` | 0 open, 4 proved, ceiling 0 |

Both ledgers have exact `#obligation_proved` references and close at ceiling 0 using `aesop (rule_sets := [Effect4.TypedState])`.

### 1. Strong Values & Exits
- `HandlesLive`: handles carried within a value are within allocated bounds in the world (`state.refs`, `deferreds.cells`, `Γ`).
- `HandlesFit`: nested handle types structurally align with typing tables (`Ρ`, `Π`, `Γ`).
- `StrongValue`: conjunction of `ValueOk`, `HandlesFit`, and `HandlesLive`.
- `StrongCause`: failure payloads have admitted value images satisfying `StrongValue`; defects and interruptions remain unconstrained.
- `StrongExit`: successful values satisfy `StrongValue` at `answer` type; failures satisfy `StrongCause` at `error` type.

### 2. D13 Lexical Source Admission
- `EnvTyped`: pointwise `StrongValue` of evaluation environment.
- `PointTyped`: source admission at program points.
- `BodyTyped`: body admission for evaluated expressions, pure terms, sync calls, closures, acquisitions, releases, and layer builds.

### 3. Control Admission & Marker Payload Inversion
- `ControlAdmitted`: dedicated control-admission predicate guaranteeing that top-level control nodes carry payloads satisfying `StrongExit`. For pure leaves and other operations, holds by recursion on continuations.
- `unguard_payload_inv`: inversion extracting `StrongExit` from `.unguard` nodes.
- `finishFinalizer_payload_inv`: inversion extracting `StrongExit` from `.finishFinalizer` nodes.

### 4. Protocols Ψ_S and Ψ_F
- `StoreCert`: ghost certificates for all 31 `SyncOp` rows (`refMake` takes target `Ty`, `deferredMake` and `memoBuild` take `Ty × Ty`, others unit).
- `storePre` and `storePost`: precise contracts relating world transitions to operation arguments and results.
- `Ψ_S`: `Protocol World StoreSig`.
- `FiberCert`: dependent certificates for all 40 `FiberOp` rows (`fork` and `mask` take `EffTy`, others unit).
- `fiberPre` and `fiberPost`: fiber contracts admitting child bodies and registering created fiber certificates in `Γ`.
- `Ψ_F`: `Protocol World FiberSig`.
- `#answer_gate`: macro reflection verifying the exact 31 `SyncOp` + 40 `FiberOp` = 71 constructor manifest against the runtime mechanism census.

### 5. Concrete TypedProg & Interpreter Hook Contracts
- `TypedProg`: conjunction of `Typed hostOrder (Ψ_S.sum Ψ_F) w (fun w' ex => StrongExit w' ty ex) prog` and `ControlAdmitted root w ty prog`.
- `frameProtocols`: trivialized non-stack interpreter hook contracts for async finalizers, iterators, and loops.

### 6. Settling Cases
- `settling_ref_allocation`: allocates a boolean ref on an initial world with an existing nat ref at index 0, reads back from the allocated handle, and proves the returned exit carries `StrongExit` at `.bool`.
- `settling_ref_preserves_nat`: monotonic preservation of existing ref typing across the allocation.
- `settling_fork`: addressed `fork` admitting a child body produces a typed fiber handle carrying `.fiberOf cert.answer cert.error`.
- `settling_mask`: addressed `mask` admitting body preserves its certificate type.

## Controls and trust

`Test/Program/TypedResidual.lean` validates both positive behaviors and negative boundaries:
- Positive tests for settling cases, primitive boolean strong values, and pure boolean strong exits.
- Negative controls:
  - `forged_cell_not_live`: unallocated cell handle rejected by `HandlesLive` on an empty heap.
  - `forged_cell_not_fit`: unallocated cell key rejected by `HandlesFit` at type `.refOf .bool`.
  - `forged_fiber_not_fit`: unallocated fiber ID rejected by `HandlesFit` at type `.fiberOf .bool .unit`.
  - `unguard_inversion_rejects_unadmitted`: unadmitted payload rejected by `unguard_payload_inv`.
  - `finishFinalizer_inversion_rejects_unadmitted`: unadmitted payload rejected by `finishFinalizer_payload_inv`.

`Test/Audit/AnswerGate.lean` invokes `#answer_gate`, checking the exact 31 `SyncOp` and 40 `FiberOp` rows.

`Test/Audit/AxiomGate.lean` admits `Effect4.Laws.Auto.AnswerGate` to `auditImplementationModules` (metaprogramming command elaborator inspecting the environment; declares no theorems). The full gate checks 483 modules and 67,149 declarations: all semantic and test declarations are strictly bounded by `[propext, Quot.sound]`.

## Verification

All commands run from the `/private/tmp/effect4-foundations-slices` worktree:
- `lake build Effect4.Laws.Program.Typed.Admission`: exit 0, ceiling 0.
- `lake build Effect4.Laws.Program.Typed.Residual`: exit 0, ceiling 0.
- `lake build Test.Audit.AnswerGate Test.Program.TypedResidual`: exit 0.
- `lake build Test.All`: exit 0 (700 jobs).
- `make build`: exit 0 (704 jobs).
- `make check`: exit 0 (fresh root elaboration and generated-file drift pass).
- `FinalAudit.lean`: exit 0. Unique production ledger: **342 total; 333 proved; 9 open**. Exactly 6 new obligations added and proved; the 9 historical open obligations remain unchanged:
  - `Effect4.Api.M1Origin.source_fork_site`
  - `Effect4.Api.TraceFacts.M1Trace.step_agrees`
  - `Effect4.Program.Guard.M4Handshake.parkHandshake_reachable`
  - `Effect4.Api.TraceFacts.M1Trace.reachable_agrees`
  - `Effect4.Api.M1Origin.source_two_race_sites`
  - `Effect4.Api.M1Origin.source_forkScoped_site`
  - `Effect4.Api.M1Origin.source_race_site`
  - `Effect4.Api.M1Origin.source_forkIn_site`
  - `Effect4.Run.M1Trace.observe_replace_trace`

## Held work

Stack and interruption preemption contracts remain held under `E4-SCHED-CE-006` and `E4-SCHED-CE-007`:
- `popR_typed` and `saveAnswerR_typed` are not asserted or placed in the ledger.
- `FrameAccepts.resume` replacement and `DeliveryStateOk` remain held pending the delivery contract redesign.
