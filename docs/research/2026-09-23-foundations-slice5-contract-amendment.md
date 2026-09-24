# Proposed slice 5 contract amendment

Slice 5 cannot admit the cleanup stack of a checker-typed `sleep(1)` under its frozen
contracts. Three kernel-checked counterexamples are retained at `2a00ce296a17dbef84197d8b8d84e8dbec0884ee`
in `Test/Counterexamples/Machine/Semantics/AsyncHookContract.lean`. This proposal needs an
owner ruling before the production proof contracts change. The runtime repair for U-01
is integrated and is not reopened by these findings.

## Checked obstruction

The source `.perform .sleep (.lit (.nat 1))` checks at `EffTy.pure .unit`. After one evaluate
decision, the reference machine is parked at token 0 with exactly:

```lean
[.asyncFinalizer (.withWaiter (.store .cancelSleep) Api.root 0),
 .answer Effects.Program.pure]
```

The same source finishes with `.success .unit` when its timer fires. Those are finite
controls. The following refusal theorems quantify over every world; their transitive axioms
are within `[propext, Quot.sound]`.

| ID | What fails | Checked result |
| --- | --- | --- |
| `E4-SCHED-CE-010` | The brief §3.3 async-finalizer clause accepts every cause containing an interrupt, regardless of its typed failures | `sleep_stack_rejected`: no choice of the two intermediate types admits the exact stack above under that clause and its identity answer arrow. The challenge is `Fail 42` together with an interrupt |
| `E4-SCHED-CE-011` | `fiberPost` for `guard_` is `True` | `guard_admits_wrong_arm` and `clean_cancellation_still_rejected`: an `onSuccess` guard must type a failure answer that the real handler cannot receive. Even a clean, well-typed interruption cannot make cancellation `TypedProg` at Unit/never |
| `E4-SCHED-CE-012` | `ControlAdmitted.vis_inl` quantifies over every answer without the operation's postcondition | `control_cancellation_cannot_type`: it requires the cleanup's Unit-returning store row to accept a Nat reply, then requires the resulting unguard payload to fit Unit. `store_rejects_wrong_answer` checks that the existing store post already excludes that reply |

These failures are independent. Restricting the incoming cause alone leaves CE-011;
strengthening only the fiber protocol leaves CE-012, whose predicate does not consult that
protocol. A generic theorem under uninhabited hook premises would not admit this source case.
No counterexample to the no-run-premise `popR_typed` conclusion under adequate hook laws is
claimed here.

## Requested ruling and exact boundary

Authorize a proof-contract repair before resuming the original slice 5 sequence:

1. Amend both the concrete async hook and its `HookLaws` field from

   ```lean
   tin = tout ∧ ∀ cause, cause.hasInterrupts = true →
     TypedProg root w tout (interp.cancelThenFail name cause)
   ```

   to

   ```lean
   tin = tout ∧ ∀ cause, StrongExit w tin (.failure cause) →
     cause.hasInterrupts = true →
     TypedProg root w tout (interp.cancelThenFail name cause)
   ```

   `popR` already has the incoming `StrongExit`; the amendment uses existing evidence.

2. Reopen the `guard_` row of `FiberCert`/`fiberPre`/`fiberPost`. Record the incoming guard
   type in a ghost certificate and require a `some ex` answer to satisfy both
   `kind.hasExitArm ex = true` and `StrongExit` at that type; retain the `none` body-entry
   case. State the actual-delivery obligation for this strengthened post. This replaces
   the instruction that every `Ψ_F` row must remain unchanged; no other row is opened by
   this proposal.

3. Reopen `Typed/Admission.lean`'s control judgment and its connection to `TypedProg` in
   `Typed/Residual.lean`. Continuation admission must use the operation's postcondition,
   and nested guard markers must use the guard's intermediate type. Keep the source/body
   admission definitions before the operation protocols and avoid a circular definition.
   Freeze and check the revised control declaration before proving its laws. Retain the
   top-level `unguard` and `finishFinalizer` payload inversions needed by the real walk;
   removing those inversions or accepting arbitrary marker payloads is not this repair.

The additional write fence is `Typed/Admission.lean` and the named guard protocol row in
`Typed/Residual.lean`; the rest uses the existing slice 5 files, counterexample register,
root imports, answer gate and focused tests. Runtime code, stored syntax, decision tapes,
world order, the axiom ceiling, U-01 and its signed host exception remain fixed. The hard
proofs retain `InterruptProvenance` and `HookLaws` with **no run premise**.

Before promoting the revised declarations, check the sleep stack above and its cancellation
with an interrupt-only cause, the ordinary Nat-removing catch, a guard that changes its
intermediate value type, and generated cleanup. Keep negative controls for the wrong guard
arm, wrong typed failure, wrong middle type and invalid top-level marker payload. Then finish
slice 5's stack/delivery proofs, assembly and M6 declarations and run the original packet
checks. Recompute the M6 count from the actual strengthened manifest; do not omit a row or
carry an obsolete ceiling forward.

The three old-contract witnesses stay as local reviewed propositions or historical tests;
their repaired counterparts must be positive admission controls. This document proposes the
repair boundary and obligations. It does not claim the replacement control judgment has
already been implemented or proved.

## Why work stopped

The controlling [slice 5 brief](2026-09-21-codex-brief-foundations-slice-5.md) §1 requires:
“Stop the slice and record the smallest amendment on a checked counterexample to a frozen
statement” and also names “a reachable case a source row refuses”. Section 2 currently opens
`Contracts.lean` only for R3 and `Residual.lean` only for `frameProtocols`; it does not authorize
the two additional changes above. The owner's earlier “yes proceed” approved the CE-009
runtime carrier and its three consumers, not these newly checked proof-contract changes.
