# Codex: PROC-6, slices P and A reviewed; land slices B to F in one run

## The one thing to know first

Slices P and A conform to the locked plan. Commit slice A, merge main, then land slices B, C, D, E
and F in one run. Continue to slice G only on the condition in § "The run".

Your brief stays the authority for every slice:
`docs/research/2026-10-14-proc6-prep/landing-prompt.md`. This message adds the review, the
fixes, the base gap and the run's stop rules.

## The review of slices P and A

Slice P (`9d404a1ec`):

- `blockAlgB` copies `denoteRowsB`'s arms field by field: `bind`, `select`, `exit`, the catches,
  `onExit` and `iterate`. Its leaves read `denoteRows.alg`.
- `denoteBlockB_loopedDataRows` is true as stated. `call` and `param` have kind `.program`
  (`NativeOp.kind`, `src/Effect4/Program/Native.lean`), so `LoopedDataRows` refuses them.
- `denoteBlockB_approx` closes by an outer induction on the budget with the structural one inside.
  `invoke`'s captured arguments are subterms, so the inner hypothesis covers them.
- `argSitesAt_body`'s address `p.path ++ [0]` is the compile's own (`suspendBodyAt`).
- The stage 3 goals copy their loop analogues (`localRunC_to_rowsB`, `hostRunB_exits`,
  `hostRunB_stable`). The registry entry and the 24 goals stand.

Slice A (uncommitted, built once at 13:41):

- Stage 0a covers every site of the plan's §5. The OCaml regeneration changes only the call arm's
  new frame, `[] :: params`; the rest is renumbering.
- The premise swap covers the 23 statements: 12 in `Machine.lean`, 2 in `Segment.lean`, 6 in
  `Hosted.lean` and 3 in `Api/SessionMeaning.lean`.
- The removed `try`, `first | …` and bare `simp` in touched proofs are right. Keep them so.

## Two fixes, folded into builds you already owe

1. `src/Effect4/Laws/Program/Agreement/Segment.lean` still says "Reach: `LoopedRows`" in its module
   docstring and in `drive_seg`'s. The premise is `PlainHooks` now. Fix both when slice F edits
   `Segment.lean`, and check the other 22 statements' docstrings then.
2. `Agreement/Blocks.lean`, `Agreement/HostedBlocks.lean`, `Api/SessionMeaningBlocks.lean` and
   `ValidatedBlocks.lean` lack the `/-! … -/` module header the other leaves carry. Add it, with
   concept, claim and reach, in the slice that proves each module's goals.

## Finish slice A, then merge main

- Finish `make gen-lcnf`, the `dune build` and the gates of slice A. Commit as the brief says.
- Your base `d6e162caf` predates two commits that your gates read:
  - `f78fda8ef`: `harness/truth/P2b.lean` passes `[]` as the key names to `requirementType`.
    Without it, `check-truth` fails at your base. That failure is the baseline's, not yours.
  - `6c3bbf320`: the to-do fixture. Your regenerated `ocaml/engine/test/scenarios/todo.txt` is
    byte-identical to it.
- After slice A's commits, run `git merge refactor/phase1-phase3`. Main changes no file under `src/`,
  so `Effect4` and `Effect4.Laws` do not rebuild. The merge touches none of your files.
- The merge re-pins the kit at `3e5e793`, which GitHub does not hold. Before the next `lake`
  command, seed it:
  `git -C .lake/packages/whatwg fetch /Users/pooks/Dev/lean4-whatwg-svg html/svg`.
- Rerun `make check-truth` once after the merge, and record the result.

## The run

Land slices B, C, D, E and F in order, as the brief gives them. Commit each slice, or each coherent
part of one, as it closes. Write each slice's receipt section as you go.

The build order:

- Slice B edits `Block.lean`, `Ref/Cache.lean`, the dogfood tests and `src/Effect4/Laws.lean`. Make
  every move and deletion first, then build the dependents once.
- Slices C, D and E prove goals in the leaf modules. Each rebuilds its leaf and the root. Iterate
  with `lake build <leaf>`.
- A proof replaces its `proof_goal` in place, with no second statement.
- Slice F edits the hosted spine bottom-up, as the brief's build plan says. Check the plan's risk 6
  first, before any rework: whether `meaning_settled` and `tape_holds_host` read `Leads` only
  through a final outcome.

Continue to slice G only when all three hold at the end of slice F:

- no goal of stages 0 to 4 is open (`#plan_status rows-block-host`);
- the hosted spine's `#axiom_audit` is clean;
- no stop rule below fired.

Otherwise stop after slice F and report.

## Stop and report at once when

- a goal of the plan is false as stated: give the counterexample, then stop;
- risk 6 fails: give the reading of `Leads` that needs more than a final outcome;
- a proof needs an edit to `src/Effect4/Program/Compile.lean` or `Agreement.lean` that the plan
  does not name;
- a gate fails beyond its baseline in the prep receipt.

## Unchanged rules

- Build only through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, one `lake` at a time.
- Never push, download nothing, never write `2>/dev/null`, and never `git add -A`.
- Propose decisions rows in your receipt, never in the register.
- Your receipt opens with the one thing the coordinator must know before merging.
