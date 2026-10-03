# The denotation's proof graph

Cut from `docs/research/2026-09-05-slice-1-compile-ground.md` §6 at the landing of slice 1
and its slice-2 theorem, 2026-09-05. Packet: `Test/contracts/program-denotation.contract.md`.
The graph past the straight-line fragment (the behaviour over tapes, the reference
scheduler, the simulation, the congruence) is planned in
`docs/research/2026-09-05-runtime-proof-graph.md`, with its mathematics in
`docs/research/2026-09-05-runtime-semantics-core-math.md`.
Every node is at `propext`/`Quot.sound` (`Test/Audit/AxiomGate.lean` enforces it; the four
axiom reports named below are the receipts).

The theorem at the root of the graph, as landed (`src/Effect4/Program/Agreement/Machine.lean`):

```lean
theorem run_eq_meaning (e : NativeEff) (fuel : Nat) (hs : Straight e = true)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      (Api.run e fuel).exit = some (meaning e [] Stores.empty).1 ∧
      (Api.run e fuel).stores = (meaning e [] Stores.empty).2
```

It is a Lean theorem about the Lean machine and the Lean algebra; it says nothing about
rc.112, and it is not an equivalence, a bisimulation, or a trace agreement
(`E4-DEN-CE-003`).

## Nodes

| node | module | depends on | discharged by |
| --- | --- | --- | --- |
| `TYPED/value` `Val.hasTy`, `Fits` | `Program/Typed.lean` | `Ty`, `Val` | definitions (`hasTy` is well-founded on the value and the type) |
| `TYPED/term` `evalTerm_hasTy`, `evalTerm_isSome` | `Program/Typed.lean` | `nativeAtom_typed`, `Lit.toVal_*` | mutual induction over terms |
| `TYPED/row` `syncOpOf_isSome`, `syncOpOf_async_none` | `Program/Typed.lean` | `hasTy` | cases on the row |
| `STORES/order` `Stores.le`, `syncOpStep_le` | `Machine/StoresLaws.lean` | `refStep_length` | cases on the operation |
| `STORES/valid` `validIn`, `WF`, `syncOpStep_isSome_of_valid`, `syncOpStep_wf`, `syncOpStep_answer_valid`, `syncOpStep_read_unchanged` | `Machine/StoresLaws.lean` | `STORES/order`, `refPoke_valid`, `refStep_valid` | cases on the operation |
| `DEN/carrier` `StoreSig`, `denote`, `storeHandler`, `meaning` | `Program/Denote.lean` | `Effects.Program`, the compile's helpers | definitions |
| `DEN/equations` `meaning_*` | `Program/Denote.lean` | `Effects.interpret_bind`, `interpret_perform`, `interpret_pure` | the algebra's laws |
| `DEN/oracle` the `agrees` guards | `Test/Program/DenoteContract.lean` | `Api.run` | `decide`, one program at a time |
| `AGR/local` `localStep`, `localRun`, `Reaches`, the frame-step lemmas, `popFrom_pass` | `Program/Agreement.lean` | `Machine/Frames.lean` (`step`, `popFrom`, `ensure`, `answerOf`) | `rfl` on the frame machine's arms; the pass lemma through `popFrom_continue_*` |
| `AGR/compile` `compileEff_*` at positive fuel, `suspendBodyAt_*`, `contAOf_*`, `contEOf_*` | `Program/Agreement.lean` | `Compile.lean` | `simp` on the compile's match |
| `AGR/reach` `localRun_compile`, `localRun_root` | `Program/Agreement.lean` | every `AGR/*` node above, `DEN/equations` | structural induction on the program, the outer stack generalised, the step count existential and bounded by `steps` |
| `MACH/plain` `PlainCode`, `PlainFrame`, `plainCode_compileEff`, `plain_at`, `plainCode_suspendBodyAt`, `localStep_plain` | `Program/Agreement/Machine.lean` | `AGR/local`, `AGR/compile` | every subterm of a plain root is plain; the hooks answer plain code; the local step keeps the fiber plain |
| `MACH/quiet` `Quiet`, `syncOpStep_quiet`, `dueResumes_quiet` | `Program/Agreement/Machine.lean` | `Machine/Stores.lean` (`DeferredStore.complete`, `cancel`, `make`) | cases on the operation; a completion with no waiter owes nothing |
| `MACH/frames` `popFrom_plain`, `getCont_plain`, `finalizerOr_plain`, `evaluatePrim_plain` | `Program/Agreement/Machine.lean` | `Machine/Frames.lean` (`popFrom_answer_answer`), `AGR/local` (`popFrom_pass`), `Machine/Fibers.lean` (`evaluatePrim`) | no plain stack answers an `onExit` frame, so `finalizerOr` is `stepFrame` |
| `MACH/commands` `iteration_M`, `drive_loop_*`, `drive_deliver_*`, `drive_drainDue`, `drive_finish_M`, `drive_evaluate_load` | `Program/Agreement/Machine.lean` | `Machine/Clauses.lean` (`drive_loop_continues`, `drive_loop_answered`, `drive_deliver`, `drive_finish`, `drive_evaluate_enters`, `iteration_evaluates`, `injectYield_no_verdict`, `exitFiber_no_middleware`, `flushAll_idle`) | one local step per command; a store `sync` owes a drain, which is the identity on a quiet store |
| `MACH/sim` `Owes`, `drive_localRun` | `Program/Agreement/Machine.lean` | `MACH/*`, `AGR/local`, `DEN/budget` | induction on the local run's length, the mode (loop or delivery), the op count and the resume token carried, at most two commands per local step; what the loop owes is the exit path, or a yield with at least `defaultBudget - 1` fewer steps left |
| `DEN/agreement` `replay_Mexit`, `run_eq_meaning` | `Program/Agreement/Machine.lean` | `AGR/reach`, `MACH/sim`, `DEN/budget`, `Machine/Fibers.lean` (`replayEval`, `stepDecision`) | the chain `evaluate`, the simulation, then either `finish`, two drains and `flush` on nothing armed, or the park, one drain and the rounds of `flush` |
| `PROGRESS/answer` `Stores.HeapNat`, `answer_typed`, `step_heapNat`, `syncOpOf_validIn`, `progress` | `Program/Progress.lean` | `TYPED/*`, `STORES/valid` | cases over the twenty rows; `Stores.WF` alone does not type the answers (`E4-PROGRESS-CE-001`), the heap must be typed and the typed route keeps it so |
| `DEN/onExit` the agreement under the finalizer mask | `Program/Agreement.lean`, `Program/Agreement/Machine.lean` | `AGR/*`, `MACH/*`, `Frames.lean` (`ensure`), `Fibers.lean` (`finalizerOr`) | `exitFrom` mirrors `finalizerOr`: the exit's pop answers an `onExit` frame, the finalizer program runs under the mask (the fiber's interruptible flag, `maskStack`), the restoring frame is passed on the way out; `E4-DEN-CE-004` repaired |
| `DEN/budget` `Myield`, `drive_loop_yield`, `fire_Myield`, `flushAll_Myield` | `Program/Agreement/Machine.lean` | `MACH/*`, `Clauses.lean` (`iteration_injected`, `drive_loop_parked`, `fire_eq`, `flushAll_round`, `drive_resume_guard`, `drive_evaluate_enters`) | at the loop with the count at the budget the injected iteration parks the root behind a fresh token, its primitive queued at priority 0 on its own dispatcher, the dispatcher armed; `fire` drains that one task, the resume unparks the root on its guard and `evaluate` re-enters the loop at count zero; induction on the rounds of `flush`, each yielding round having spent at least `defaultBudget - 1` steps; `E4-DEN-CE-005` repaired |
| `DEN/trace` agreement on the trace under a mask | later | `Effects.Trace` | not this slice (`E4-DEN-CE-003`) |

## Receipts

`Test/Program/TypedAxiomReport.lean`, `Test/Machine/Runtime/StoresLawsAxiomReport.lean`,
`Test/Program/DenoteAxiomReport.lean`, `Test/Program/AgreementAxiomReport.lean`,
`Test/Program/ProgressAxiomReport.lean`.

## Rows

`E4-TYPED-CE-001`, `E4-TYPED-CE-002`, `E4-STORES-CE-001` through `E4-STORES-CE-003`,
`E4-DEN-CE-001` through `E4-DEN-CE-005`, `E4-PROGRESS-CE-001`, `E4-PROGRESS-CE-002` in
`Test/Counterexamples/REGISTER.md`.
