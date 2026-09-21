# Foundations slice 4 continuation: M3a protocols, admission and TypedProg plan

The independent foundations (D12 protocol certificates and C2–C4 representation foundations)
landed in `5a9611c4`. The dependent stack and interruption preemption contracts remain held
under the counterexamples `E4-SCHED-CE-006` and `E4-SCHED-CE-007`.

This landing implements the unheld remainder of Slice 4 (M3a): strong values and exits,
lexical source admission (D13), control admission and marker payload inversion, the complete
31-row Store and 40-row Fiber protocol manifests under `#answer_gate`, concrete `TypedProg`,
and the two settling program cases.

Base: `5a9611c4`. Branch: `codex/foundations-slices-3-4`; checkout: `/private/tmp/effect4-foundations-slices`.

## 1. Modules and declarations

### `Effect4.Laws.Program.Typed.Admission`
- `HandlesLive (w : World) (v : Val) : Prop`: for all `h ∈ v.keys`, cell index `< w.state.refs.length`,
  promise index `< w.state.deferreds.cells.length`, and fiber target `(w.Γ id).isSome = true`.
- `HandlesFit (w : World) (v : Val) (ty : Ty) : Prop`: recursive alignment of nested handles with
  the typing tables (`w.Ρ` for `.refOf`, `w.Π` for `.deferredOf`, `w.Γ` for `.fiberOf`,
  `HandlesLive` at `.unknown`, branch disjunction at `.union`).
- `StrongValue (w : World) (ty : Ty) (v : Val) : Prop := ValueOk w ty v ∧ HandlesFit w v ty ∧ HandlesLive w v`.
- `StrongCause (w : World) (errTy : Ty) (c : CauseV) : Prop`: every `.fail e` reason carries an
  admitted `valOfErr e = some v` satisfying `StrongValue w errTy v`. Die/interrupt reasons remain
  admitted without error-column restriction.
- `StrongExit (w : World) (ty : EffTy) (ex : ExitV) : Prop := Contracts.ExitFits w ty ex ∧
  (∀ v, ex = .success v → StrongValue w ty.answer v) ∧ (∀ c, ex = .failure c → StrongCause w ty.error c)`.
- `EnvTyped (w : World) (env : List Ty) (vals : List Val) : Prop`: length equality and pointwise `StrongValue`.
- `PointTyped (root : Eff) (w : World) (point : Point) (ty : EffTy) : Prop`: checker agreement at
  `Node.at_ (.eff root) point.path` under `EnvTyped w env point.env`.
- `BodyTyped (root : Eff) (w : World) : Body → EffTy → Prop`: inductive predicate on the six `Body`
  constructors (`at_`, `fin`, `raceCleanup`, `acquireIn`, `release`, `layerBuild`).
- `ControlAdmitted (root : Eff) : World → EffTy → RProgram → Prop`: inductive predicate ensuring
  top-level control nodes (`.unguard`, `.finishFinalizer`, `.scoped`, `.scopeExit`) carry admitted payloads.
- `unguard_payload_inv`: inverts `.unguard ex` to `StrongExit w ty ex`.

### `Effect4.Laws.Program.Typed.Residual`
- `Ψ_S : Protocol World StoreSig`: 31 `SyncOp` rows with certificate types (`Ty` for `refMake`,
  `Ty × Ty` for `deferredMake` and `memoBuild`, `PUnit` otherwise).
- `Ψ_F (root : Eff) : Protocol World FiberSig`: 40 `FiberOp` rows partitioned into Direct Answers,
  Delayed Delivery, Control & Preparation, and Live Frontier.
- `TypedProg (root : Eff) (w : World) (ty : EffTy) (p : RProgram) : Prop :=
  Typed hostOrder (Ψ_S.sum (Ψ_F root)) w (fun w' ex => StrongExit w' ty ex) p ∧ ControlAdmitted root w ty p`.
- `frameProtocols : Contracts.FrameProtocols`: operational hook arrows.
- The two settling cases proved:
  1. `settling_ref_allocation`: polymorphic ref allocation and read on heterogeneous heap.
  2. `settling_fork_mask`: addressed fork and mask with body admission.

### `Effect4.Laws.Auto.AnswerGate`
- `#answer_gate`: checks that every constructor of `SyncOp` (31) and `FiberOp` (40) has an exact row
  in the manifest and prints the table.

### Tests
- `Test/Audit/AnswerGate.lean`: checks `#answer_gate`.
- `Test/Program/TypedResidual.lean`: checks positive/negative controls (forged handles rejected,
  `badShapeExit` defect behavior, `unguard_payload_inv`, settling cases).

## 2. Done means
- All new modules build with `-DwarningAsError=true` and pass the trust gate at `[propext, Quot.sound]`.
- M3a ledger ceiling finishes at 0 open.
- The 9 open historical obligations remain unchanged.
- `make build` and `make check` pass cleanly.
