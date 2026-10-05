Codex Overwatch at 944897ed: rows 253–254 match the owner's direction.

Before DOGFOOD dispatch, apply these source-grounded corrections.

1. After `Rows.receive`, use `Run.play [.apply key]` or `Run.step`.
   `Rows.answer` binds, submits and applies in `src/Effect4/Run.lean`.
   It introduces another receipt attempt after the first receipt.
2. Reuse `harness/truth/session/Keyed.lean`, `run-keyed.ts`, `keyed-recorder.ts` and `check-keyed.ts` for separately scheduled receipt and application.
   Ordinary `Truth.fixtureRun` uses `Api.run` and completion lists.
   Existing keyed controls separate arrival order from application order.
   The recorder refuses completion after cancellation; that scenario needs a bounded extension.
3. The OCaml wrappers fix an empty row table in `interp_of`, `step` and `run_api`.
   Generated `api_replay` already accepts the table and separate command and compile budgets.
   Prefer a test-local adapter before changing `E4_engine.INSTANCE`.
   Bind table bytes to the admitted fixture; preserve frontiers and application remainders.
4. Raw replay has no HostSession pending, retired or consumed metadata.
   Compare its named machine projection; retain the full OCaml session clause as waiting for its connector.
   Copying Lean metadata into the OCaml result does not exercise row 254's full observation.

The dogfood review names sources, placements, premises, exclusions and immediate prerequisites.
Its path is `dogfood/review.md` beside this note.
The review uses source evidence only; no builds ran.

FOLD's latest proof source reuses termMaps_of_typed, refStep_modify, foldlM_answers, fold_fits, handle membership, raw containment and shared binder syntax.
No new semantic defect appears in this bounded review.
Final dependency and axiom acceptance remain pending.
One optional cleanup can wait: getElem?_weaken repeats private lookup_weaken in Program/Typing/Rules.lean.
Expose and reuse the existing generic lookup fact once the proof batch is stable.

Q0 remains in scratch while both seats run.
The coordinator's Test/All import anchor and delayed registry join are recorded.

Delivery status: NOT SENT.
Two input attempts were stopped by the computer-use guard because the user changed Claude.
The refreshed composer remains empty; preserve the user's ongoing UI activity.
