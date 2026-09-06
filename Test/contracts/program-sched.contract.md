# Program sched contract packet

Status: FROZEN / GREEN, authored and landed 2026-09-06 (slice two, R1 of
`docs/research/2026-09-05-slices-2-3-worksheets.md`; plan
`docs/research/2026-09-05-runtime-proof-graph.md` §3, Layer R). The module landed with its
battery and its report; every theorem below is proved. R2 amends the answer family
and adds residual frontier addresses under the owner's 2026-09-06 correction.
The corrected signature, battery and dependency receipts pass their narrow build.

Implementation: `src/Effect4/Program/Sched.lean`; its R2 consumer and corrected
denotation contract are `Program/DenoteR.lean` and `program-denote-r.contract.md`.

Lean battery: `Test/Program/SchedContract.lean`. Axiom report:
`Test/Program/SchedAxiomReport.lean`. Counterexamples: `E4-SCHED-CE-001`–`003` in
`Test/Counterexamples/REGISTER.md`.

Depends on: `src/Effect4/Program/Denote.lean` (`StoreSig`, `storeHandler`, `denote`,
`meaning`), the algebra package's `Effects.Algebra.Sum` (`Signature.sum`, `Handler.sum`,
`interpret_inl`), the machine's fiber vocabulary (`Supervision`, `FiberId`, `Ctx`, `EffName`,
`Point`).

## Claim boundary

This packet freezes the *signature* the term scheduler's fibers speak and one fact about
its store half. It does not give the fiber operations a semantics: that is the term
scheduler itself (worksheet R3–R4, owed), a state machine over the fiber machine's
decisions, bookkeeping and stores, not a handler into `StateT Stores Id`.

1. `FiberOp` is first-order and decidable. It covers the fiber-level arms of the
   machine's `evaluatePrim`, alongside addressed scope/body operations and frontiers.
   Every operation that encloses a program carries a
   `Point`, never a program (positivity; and the compile holds compiled code at the same
   address).
2. `RSig = Signature.sum StoreSig FiberSig` at universe `.{0, 0}`, `RSig.Op = SyncOp ⊕
   FiberOp`. Store answers are `Val`; fiber answers are `FiberOp.answer`: `ExitV` for
   masks, scopes, scope close, acquisition/release, races, effect joins, async,
   scoped forks and frontiers, `Val` for the other
   operations. These shape equations are by `rfl`. This replaces R1's all-`Val` claim
   so operations that deliver exits do not need an extra decoding convention.
   The scout's claimed encoding collision was false: `E4-SCHED-CE-002` retains the
   disjointness and round-trip proofs against the actual encoding. R2 also retains
   the allocated scope id in `scoped`, the link key in `forkIn`, and an explicit
   first-order `ResumePoint` at every frontier.
3. A store node of an `RSig` program is `vis (.inl op) k`; `perform` is the derived
   one-node program (`perform_inl_bind`).
4. `interpret_inl_store`: the straight-line denotation injected on the left means, under
   the summed handler, what it means under the store handler; `meaning_via_rsig`
   recovers `meaning`. This is the target `denoteR_straight` (R2) lands on.

Refused by name (in the module header): `SCHED-FB-FIBER-HANDLER`, the placeholder
`fiberRefusal` is not a semantics of the fiber operations; `SCHED-FB-REFUSE`,
`FiberOp.refuse` carries the machine's refusal defect so `denoteR` can name it.

## ENSURES

1. `RSig_op`, `RSig_answer_inl`, `RSig_answer_inr` — the shape, by `rfl`.
2. `perform_inl_bind` — `bind (perform (.inl op)) k = vis (.inl op) k`, by `rfl`.
3. `rHandler_inl`, `rHandler_inr` — the summed handler's two halves, by `rfl`.
4. `interpret_inl_store` — through `Effects.interpret_inl`.
5. `meaning_via_rsig` — `(interpret rHandler (inl (denote e env))).run s = meaning e env s`.

## Counterexample rows

| id | status | claim attacked | witness | disposition |
| --- | --- | --- | --- | --- |
| `E4-SCHED-CE-001` | SEEDED | The summed handler is a semantics of the fiber operations | `rHandler.handle (.inr FiberOp.getId)` on the empty store answers `unit` and leaves the store: a `getId` that names no fiber | the right half is a placeholder (`SCHED-FB-FIBER-HANDLER`); the fiber operations are interpreted by the term scheduler, owed |
| `E4-SCHED-CE-002` | SEEDED | The R2 scout's proposed exit-encoding collision | The battery proves the proposed images differ, and `exitOfVal (reifyExitVal ex) = some ex` for every exit | correct the rationale: dependent exit answers give a direct interface; encoding was already reversible |

## Falsifiers

An omitted fiber arm or an undocumented additional semantic operation falsifies
claim 1 (the arm map and corrected R2 packet are the check). A
program performing a fiber operation whose `meaning_via_rsig`-style equation is stated
here falsifies the claim boundary.
