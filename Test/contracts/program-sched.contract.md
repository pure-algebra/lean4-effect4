# Program sched contract packet

Status: FROZEN / GREEN, amended for R3/R4, authored 2026-09-06 (slice two, R1 of
`docs/research/2026-09-05-slices-2-3-worksheets.md`; plan
`docs/research/2026-09-05-runtime-proof-graph.md` §3, Layer R). The module landed with its
battery and its report; every theorem below is proved. The owner authorized R2's
dependent answers and residual frontier addresses, then the R3/R4 correction
retaining handler/cleanup boundaries and naming synthesized bodies. The signature,
battery and dependency receipts pass their focused build and the coordinator's
whole-tree gate. Final receipt: `docs/research/2026-09-06-r3-r4-implementation.md`.

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
scheduler itself (`Program/RuntimeR.lean`, worksheet R3–R4), a state machine over the fiber machine's
decisions, bookkeeping and stores, not a handler into `StateT Stores Id`.

1. `FiberOp` is first-order and decidable. It covers the fiber-level arms of the
   machine's `evaluatePrim`, alongside addressed body operations, the checkpoints and
   frontiers. Fork and mask carry `Body`, whose three first-order constructors name a
   source `Point`, a store finalizer with its exit, or the race whose settled cleanup
   a synthesized mask body runs (`Body.raceCleanup`, source-repairs §16 D6a; it
   replaced the winner-time fiber list of `Body.interruptFibers`). Other enclosing
   operations retain source points. None carries a
   program. `GuardKind` names success, failure, both-arm and exit-finalizer boundaries;
   `guard_`, `unguard` and `finishFinalizer` retain their explicit entry and exit
   markers for the evaluator. Since P2 (2026-09-06, `docs/research/2026-09-06-p0-fable-record.md`
   §4) four operations are the checkpoints the pinned host counts where the term has
   no store or fiber work of its own: `suspend` (the counted step that returns code,
   `Suspend`), `sync` (a pure thunk's value through the `answered` phase), and the
   initial entries `gen` and `loop` of a generator and of a cursor loop, whose later
   iterations run inside the body's delivery. Under source-repairs §12, `scoped`
   is one counted entry at its eager body point; `scopeExit` is stateful callback
   glue carrying the prior context, scope and body exit. Both answer ExitV. Under
   source-repairs §16 (D6a), `raceRegister race` is the counted Async registration
   of a race: the race entry allocates its bookkeeping and returns this operation
   as the host's next program, and evaluating it runs the entrants and either
   continues with the accepted exit or parks under the cleanup guard. It answers
   ExitV. Under §19 (D6b), `interruptAs target who` is `fiberInterruptAs`: the
   program the public `interrupt` entry returns, evaluated by the shared record-and-
   delegate helper; it answers `Val`, and the `asVoid(fiberAwait)` return it installs
   flows through the saved answer slot. A frontier carries its reason and point;
   Under §20, `ambientScope` is the counted `Scope` service read (`Context.ts:423`)
   that `forkScoped`'s `flatMap(scope, forkIn)` wrapper runs first, answering the
   handle as a `Val`; `closeWalk strategy order exit` is the counted `fnUntraced`
   suspend of `scopeCloseFinalizers` (two or more finalizers), answering unit, and
   `closeIter strategy order exit` its counted `Iterator` entry, answering the walk's
   exit: sequentially the generator runs through the term's iterator hook at
   `.store (Name.closeSeq …)` with each finalizer under the term's own `Exit` guard
   (`exitR`); in parallel the step forks every finalizer as an immediate daemon
   (`FiberAction.closePar`) and the shared `closeParAwait` command yields the await under
   the generator's frame (`ScopeFrame.iter (.store .closeParDone)`). A frontier carries
   its reason and point; the unfolding-budget reason and the residual generator/loop
   addresses are gone with the budget. The R2 packet defines the erasure that removes the
   markers and checkpoints when proving agreement with the existing straight denotation.
2. `RSig = Signature.sum StoreSig FiberSig` at universe `.{0, 0}`, `RSig.Op = SyncOp ⊕
   FiberOp`. Store answers are `Val`; fiber answers are `FiberOp.answer`: `ExitV` for
   masks, scope close, acquisition/release, races, effect joins, async, scoped forks,
   frontiers, the two closing control markers and the generator and loop entries;
   `Option ExitV` for boundary entry (`none` enters, `some exit` resumes outside); `Val`
   for the other operations, the two checkpoints included. These shape equations are by
   `rfl`. This replaces R1's all-`Val` claim so operations that deliver exits do not need
   an extra decoding convention. The scout's claimed encoding collision was false:
   `E4-SCHED-CE-002` retains the disjointness and round-trip proofs against the actual
   encoding. R2 also retains the link key in `forkIn`, and every frontier carries its
   first-order point.
3. A store node of an `RSig` program is `vis (.inl op) k`; `perform` is the derived
   one-node program (`perform_inl_bind`).
4. `interpret_inl_store`: the straight-line denotation injected on the left means, under
   the summed handler, what it means under the store handler; `meaning_via_rsig`
   recovers `meaning`. This is the target `denoteR_straight` (R2) reaches after
   explicit control erasure.

Refused by name (in the module header): `SCHED-FB-FIBER-HANDLER`, the placeholder
`fiberRefusal` is not a semantics of the fiber operations; `SCHED-FB-REFUSE`,
`FiberOp.refuse` carries the machine's refusal defect so `denoteR` can name it.

## ENSURES

D5 construction amendment (2026-09-06): `FiberOp.construction` is an
administrative query whose answer is `List (FiberId × ExitV)` and whose default
answer is `[]`. It introduces neither an Eff constructor nor a host operation.
`prepareR` answers it before the next counted evaluator step, as specified in
the denotation/runtime packets. Its answer and default equations are pinned in
`SchedContract`. The other dependent answer types remain unchanged.

1. `RSig_op`, `RSig_answer_inl`, `RSig_answer_inr` — the shape, by `rfl`.
2. `perform_inl_bind` — `bind (perform (.inl op)) k = vis (.inl op) k`, by `rfl`.
3. `rHandler_inl`, `rHandler_inr` — the summed handler's two halves, by `rfl`.
4. `interpret_inl_store` — through `Effects.interpret_inl`.
5. `meaning_via_rsig` — `(interpret rHandler (inl (denote e env))).run s = meaning e env s`.

## Counterexample rows

| id | status | claim attacked | witness | disposition |
| --- | --- | --- | --- | --- |
| `E4-SCHED-CE-001` | SEEDED | The summed handler is a semantics of the fiber operations | `rHandler.handle (.inr FiberOp.getId)` on the empty store answers `unit` and leaves the store: a `getId` that names no fiber | the right half is a placeholder (`SCHED-FB-FIBER-HANDLER`); the fiber operations are interpreted by `Program/RuntimeR.lean` |
| `E4-SCHED-CE-002` | SEEDED | The R2 scout's proposed exit-encoding collision | The battery proves the proposed images differ, and `exitOfVal (reifyExitVal ex) = some ex` for every exit | correct the rationale: dependent exit answers give a direct interface; encoding was already reversible |

The R3/R4 cleanup counterexample is pinned in `DenoteRContract`:
`cleanup_boundary_distinct` proves different raw boundaries for cleanup and an
ordinary success continuation, while their erased terms coincide. Its reference
machine execution is recorded in the coordinator's R3/R4 contract correction.
This is why control markers must remain in the scheduler's term.

## Falsifiers

An omitted fiber arm or an undocumented additional semantic operation falsifies
claim 1 (the arm map and corrected R2 packet are the check). A
program performing a fiber operation whose `meaning_via_rsig`-style equation is stated
here falsifies the claim boundary.
