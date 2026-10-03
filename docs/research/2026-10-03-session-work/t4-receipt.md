# Session accepted-success membership receipt

The coordinator must know: this is a successful-reply contributor to T4, not a proof that every admitted reply is typed. The actual session accepts a failure containing `badName`, while `ExitOk` forbids it. That discriminator passed and is retained in `t4-audit.lean`; no runtime admission behavior changed.

Base: `4dfa15dacfb235d51bc2dece726a3e11959bb691`.
Implementation head: `8379326a8159677488fa71f80761d3a07ace240f`.
Branch: `codex/session-work`.

## Delivered and placement

Only `src/Effect4/Laws/Api/HostSession.lean`, `Test/Api/HostSessionContract.lean`, and this research directory changed. Existing law files remain reachable through the existing roots. No runtime, wire, registry, decision or root-import edit was made.

`PreparedSuccess` retains the actual selected association, call ID, returned answer decision, parked external row/request and successful preparation code. Its membership conclusion is conditional on that selected row's answer column being shape-decided, and then holds in every typed world. The prepared result and allocation table are those used by the existing `external_prepared_answer_typed` theorem.

`preflight_success_prepared_fits` connects successful actual session preflight to that witness, requiring a successful completion and a non-stuck machine. It composes the existing envelope, executable admission, preparation and membership theorems. `submit_success_prepared_fits` is the concrete API consumer: it starts from a successful receipt phase and returns the accepted decision together with the witness.

The preceding `t4-plan.md` places these declarations under concept 9's `typed-replay-session` requirement, meeting concept 1 membership, as proposed property `session-success-prepared-membership` and a T4 contributor. The local `PreparedWanted.preflight_success_prepared_fits` goal reports 0 open, 1 proved, 1 total. This serves R12 and the executable-admission boundary feeding M6; M5–M7's ghost admission premises are unchanged.

There is no `AnswerOk`, `ExitOk`, token declaration in a typed world, residual-machine typing, whole-session guarantee or T4 closure. Membership remains conditional for a selected row outside `shapeDecides`, including handles, fibers, cells, deferreds, `unknown` and nested exits. Failure admission and its defect exclusion are outside the theorem. Rows 97–99, 117, 138–139 and 152 keep their existing bounds.

## Verification

Commands ran only in `/Users/pooks/.codex/worktrees/session-work/lean4-effect4`, with `leanprover/lean4:v4.33.1` and the private build cache.

- `lake build Test.Api.HostSessionContract` — exit 0, 377 jobs. The new `received_prepares_nat` fixture consumes the actual successful receipt theorem and proves membership of the actual prepared result at `nat`, in every world. Its concrete returned code is `success (nat 2)`. Existing wrong-shape, wrong-session, stale-key and duplicate-reply controls still pass. The new fragment controls reject `unknown` and nested exit types.
- `lake build Effect4.Laws.Run Test.Run.RunContract Effect4.Laws.Program.Typed.Admission` — exit 0, 400 jobs. Direct Run law and battery consumers pass after the changed session-law import graph.
- `lake env lean docs/research/2026-10-03-session-work/t4-audit.lean` — exit 0. The retained `t4-axioms.log` records all four new public contract/theorem/fixture declarations at `[propext, Quot.sound]` and prints the exported theorem types.
- `git diff --check` — exit 0.

The same successful audit checked all three reserved-defect discriminator guards: session preflight returns the exact answer decision; executable `admit` returns no refusal; `externalAdmits` returns true. It also checked the proof that `ExitOk w admitted.ty (failure (Cause.die badName))` is false for every world. This is a retained finite boundary discriminator, not a runtime-profile amendment. `t4-audit.lean` contains its exact expressions and proof; exit 0 confirms they all passed. The existing AnswerSchema lemmas were not duplicated.

The initial build caught unused premise names in the obligation marker; the initial concrete fixture needed an explicit equality for `externalRow`'s normalized row. Both were repaired and the commands above passed. No `sorryAx`, `Classical.choice`, trust-ceiling widening, full battery sweep or main-worktree build was used for the finished slice.

## Merge and follow-up

Cherry-pick implementation `8379326a8159677488fa71f80761d3a07ace240f` and the receipt commit. Earlier work-inspection commits were already handed off separately. The coordinator owns central registry reconciliation and the final combined affected-graph check. No further slice is proposed here.
