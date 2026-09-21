# Brief for Codex: the interruption divergence slice (before slice 5)

Repo `lean4-effect4` (Lean 4.33.1). Base: the head of `refactor/phase1-phase3` that carries
this brief's final text (`git log -1 --format=%H -- docs/research/2026-09-21-codex-brief-foundations-divergence-slice.md`).
Branch `codex/foundations-divergence` in the worktree
`/private/tmp/effect4-foundations-divergence`, prepared by the coordinator at that base;
nothing is pushed. Ruling of record: §4 of
[`slices 3–4 review and the FR-08 ruling`](2026-09-21-foundations-slices-3-4-review-and-fr08-ruling.md),
with the checked probe `2026-09-21-foundations-fr08-evidence/DivergenceProbe.lean`. Read
that probe first: its `stripFail`, `sanitize`, `sanitize_clean` and the changed branch of
`popR'` are the exact content of this slice. Slice 5 follows this slice and is retargeted
on its head.

Goal in one sentence: **make the reference machine strip what a skipped catch was typed to
remove, in both walks, as a signed divergence from rc.112, so that no typed failure ever
escapes an error-removing catch and the typed-state theorem needs no run premise.**

## 0. What is being changed and why

rc.112 (`internal/core.ts:540-545`) discards every failure continuation while the fiber is
interruptible with a recorded interrupt and passes the original cause on. An interrupt
recorded during a masked region, followed by a failure leaving that region, therefore lets a
typed failure escape a catch: `Effect<number, never>` completes with `Fail 42`
(`E4-SCHED-CE-008`, `U-01`). Effect 3 skipped the handler too but replaced the cause by
`stripFailures(cause)` and appended the recorded interrupt. The owner ruled that the machine
does not adopt the regression. This is the only slice authorized to change runtime source in
the foundations series, and only as stated here.

## 1. Standing constraints

As in the slices 3–6 brief §2 (one compiler per checkout; explicit paths; nothing pushed;
`-DwarningAsError=true`; receipts and evidence force-added; no `first`, `simp_all` or `try` by
hand; narrow builds, `make check` at the end), plus:

- The runtime change is exactly §2. Any other change to an evaluator, the frame machine, a
  generated predicate or a store is out of scope; stop and record it.
- OCaml comes only from LCNF: regenerate in the fixed order, never edit generated files.
- Every pinned expectation that flips is listed in the receipt with its old and new value and
  the reason (the divergence), never silently re-pinned.

## 2. The runtime change (two sites, one helper)

1. `Machine/Cause.lean`: `def stripFail (c : Cause …) : Cause … := ⟨c.reasons.filter fun r =>
   r.tag != .fail⟩` beside `combine`, with `mem_stripFail` (membership iff member and not a
   `Fail`), `stripFail_nodup` from `dedup_nodup`'s shape if the cause carries a nodup law, and
   `sanitize c ic := combine (stripFail c) ic` with `sanitize_clean` (no `Fail` reason, by
   `mem_combine`). The probe has the proof.
2. `Laws/Program/EvaluateR.lean`, `popR`, the `.resume` arm's `else` branch: when the skip is a
   preemption (the arm would have run: `kind.hasExitArm ex = true`; `ex = .failure cause`;
   `frame.interruptedCause = some ic`), continue with `.failure (sanitize cause ic)`; a guard
   miss continues with `ex` unchanged. Exactly the probe's `popR'`.
3. `Machine/Frames.lean`, the compiled walk: `popFrom` and `passPushed` discard a frame that
   answers while `skip && (frame.ensure fiber).fst.interrupted`. At that discard, when the
   demand is the failure arm and the fiber's `interruptedCause` is `some ic`, the exit the walk
   carries becomes its sanitized form. State the change so that the four `hskip`-conditioned
   lemmas near `Frames.lean:1615-1646` and the two near `:1878-1892` keep their statements
   and gain the one new arm; if the walk carries the exit outside these functions, name the
   carrier you changed. Cite the census row (`checkpoint.exit-failcause-skip`) in the
   docstring as the divergence, not as a transcription.

Nothing else moves: the success-path injections at `restoreMask`/`finalizerMask` and
`asyncFinalizer`, the guard-miss skip, `onExit false`, answer glue, hooks and `deliverR`'s
deferred interception are unchanged in both machines.

## 3. Proofs and pins that follow

- `Laws/Program/Simulation/Walk.lean` (the term/frame walk agreement, four `popR` sites) and
  `RuntimeR.run_eq_ref` / `run_eq_ref_exit`: the resume arm's new branch on both sides.
- `Test/Program/RuntimeRContract.lean` and `RuntimeRReference.lean`: `agrees` on every
  masked/interrupt program stays green (both machines change alike); no pinned exit there
  exercises the escape, so none should flip. If one does, list it.
- `Test/Counterexamples/Machine/Semantics/InterruptEscape.lean` becomes the divergence's
  positive witness: the poisoned root exits `.failure (Cause.interrupt (some root))` with the
  interrupt annotations the machine records (pin the exact value from the run), and the
  contagion program's poisoned runs no longer die; keep the quiet rows and the two theorems,
  add `escaped_no_longer` as the exact new guards, and rewrite the header. Register row
  `E4-SCHED-CE-008`: status stays, "Forced repair" becomes the sanitize rule with this
  slice's commit.
- `Test/Counterexamples/Machine/Semantics/InterruptDelivery.lean`: `restore_then_skip` and
  `delivery_does_not_intercept_failure` are equations on the old walk; update their expected
  values to the new walk and their docstrings to say they now witness the sanitized skip (the
  input audit's proposal is still refuted by `proposed_entry_mask_exception_false`, which is
  about the type of the *original* failure and stays as it is).
- Runtime coverage: `generated/effect-runtime-census.tsv` row `checkpoint.exit-failcause-skip`
  (`internal/core.ts:539-545`) must carry a **signed divergence**. The census has no such
  convention; add the smallest one in the sanctioned format of `docs/RUNTIME-COVERAGE.md`
  (a `divergence` disposition naming `U-01` and the Lean witness) to
  `scripts/generate-effect-runtime-census.sh` and `scripts/check-effect-runtime-census.sh`,
  so the gate reports the row as diverged rather than covered or missing. Do not touch any
  other row.
- Truth harness: add the escape program to `harness/truth/Truth.lean`'s fixtures with the
  poisoned tape, record its host run (rc.112 delivers `Fail 42`) and mark the Lean/host
  difference as a signed exception in the harness's result columns (the `note` column names
  `U-01`). `make check-truth` must stay green with the exception stated, not by omitting the
  fixture.
- `docs/UPSTREAM-BACKLOG.md` `U-01`: the disposition becomes "diverged at this slice's
  commit; the machine strips as Effect 3 did"; the upstream column is the owner's.

## 4. Regeneration

`make gen` in the fixed order (variances, derived, lcnf, eff, wire, cas, ts, readme, truth,
host-protocol, schema-ts, census) with `LEAN_NUM_THREADS=1` as the earlier landings did; the
OCaml build and the differential run (`make check-ocaml`, `check-truth`, `check-census`);
refuse any drift outside the files the change reaches. Record the touched generated files in
the receipt.

## 5. Build, finish, receipt

Narrow builds of the touched modules and batteries, then `make build`, `make check`, and the
three host checks above. Finish: both walks sanitize; `run_eq_ref` at `[propext, Quot.sound]`;
`InterruptEscape.lean` green as the divergence witness; the census row diverged and gated;
the harness fixture recorded with its exception; receipt
`2026-09-21-foundations-divergence-receipt.md` with base and head, the exact runtime diff,
every flipped pin with old/new values, every regenerated file, commands with exit codes, and
the unique ledger line (no obligation is added or closed by this slice). If the frame
machine's walk cannot carry the sanitized exit without a second change to the evaluator,
stop, retain the case as `E4-SCHED-CE-009`, and report.
