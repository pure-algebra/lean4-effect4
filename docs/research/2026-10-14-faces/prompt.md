# Codex: the to-do on every face, each run checked by Lean

## The one thing to know first

The owner wants to build (decisions row 387). The procedures close-out is paused, and none of it
ran. This chunk finishes the vertical slice of `docs/research/2026-10-13-lowering-vertical-slice/README.md`.
At its end, one Effect program, the to-do, has these:
- Lean claims about it;
- runs on the Lean machine, on rc.112 through the printed TypeScript, and in OCaml;
- each run checked by Lean against those claims' premises.

Most of it exists:
- V1, V2 and V4 landed;
- `h9_blocks` carries the claims to the Lean machine;
- `apps/todo/Check.lean` checks each recorded run.

What is left is small and concrete: the checked bank entry, the host rule on handles, V3, V5 and
one report. Then stop.

## Read first

- `AGENTS.md`, all of it.
- `docs/research/2026-10-13-lowering-vertical-slice/README.md`, §3 and §6: the slice, its steps
  and the per-run check.
- `docs/STATE.md`, item 0000.
- Decisions rows 378, 381 and 387.
- `apps/todo/` (`Check.lean`, `run.ts`, `repo.ts`, `server.ts`) and `Tools.RunChecks`.
- `docs/research/2026-10-14-proc-close/codex-review.md` §2 Q10 and §3: your own findings on
  `Bank.Entry` and on hosts.

## Where you work

Your worktree, `/Users/pooks/Dev/lean4-effect4-codex`, on the branch the launch message names, at
the coordinator's head. The rules of PROC-6's brief hold
(`docs/research/2026-10-14-proc6-prep/landing-prompt.md`, "The rules that bind every slice").

## The slices, in order

### F0: the agent's small fixes

STATE's item 0000 lists them: answers with no hex unless asked, the session's JSON named, a
refused fill at a missing address, the catalogue's gaps, refusals that name their definition and
parameter, and the session tool's `"run"`. Some landed in Gemini's consolidation rounds. Check
each against the tree, finish the rest, and list each one's commit.

### F1: the checked bank entry

`Bank.Entry` (`src/Effect4/Program/Authoring/Claims.lean`) accepts an invented digest, model
name or theorem name (your `uncheckedEntry` control). Add the checked way to make one:
- it recomputes the digest from the block (`Canonical.digest`);
- it resolves the claim's theorem in the environment, and checks that its statement is about
  that block;
- it fills `assumes` from the theorem's premises, with their grades;
- it gives a located refusal otherwise.

Move every existing entry (the Ref cache, the to-do) to it. `uncheckedEntry` becomes a red
control that the checked form refuses.

### F2: the host rule on handles

Your `allocation_changes_host_answer` shows a host can read a handle's index from a request.
List every row in the tree whose request type holds a handle. If none needs one, refuse such a
row at admission, with a located refusal. Otherwise record each row and why it needs the handle.
The coordinator writes the rule into `docs/core/host-boundary.md` from your report.

### F3: V3, the runtime surface from Lean data

The slice note's V3 row: the rows' bindings interface, moved from `bindingsType`; the inputs'
and answers' Schemas; the prelude package without sqlite (`ts/prelude/`). tsgo 7 checks a host
adapter against the printed interface. The Schemas' exactness is proved in Lean. The Schemas run
against rc.112 (`check-schema-codec`). The to-do's TypeScript consumer then imports the generated
surface, not hand-written types.

### F4: V5, the to-do in OCaml

**Moved** (decisions row 391 (5)): this slice runs as LC-6 of the lowering cleanup
(`docs/research/2026-10-14-lowering-cleanup/prompt.md`), with the repository made from LCNF. Skip
it here.

The slice note's V5 row, with a native repository:
- `ocaml/engine/e4_host.ml` and its `.mli`: evaluate; at a parked call, ask a reactor, apply the
  answer, flush; write the record;
- `ocaml/app/todo/`: read the built programs' bytes and the row table, and give a repository.

`apps/todo/Check.lean` checks each OCaml record, unchanged. Add the OCaml face to the gate that
runs the rc.112 face (`make check-host-protocol`), with one red control: a repository that
forgets a write fails `agrees`. Build OCaml only through `opam exec --switch=effect4`.

### F5: one report

One command prints the to-do's verification in one table:
- each claim, with its `#plan_status`;
- each face (Lean, rc.112, OCaml), with each recorded run's verdicts;
- each premise that is assumed, not decided (rc.112, bun, SQLite and OCaml on unrecorded runs).

Take every number from the tools that measure it.

## The gates each slice owes

- F1: the narrow build and `#axiom_audit` of its modules.
- F3: `check-target`, `check-ts-reader`, `check-schema-codec`, `check-schema-ts`.
- F4: `check-ocaml`, `check-native`, `check-host-protocol`.
- F5: the report runs clean on a fresh database, and the red control fails where it should.

## Stop and report at once when

- a check fails beyond its baseline;
- a slice needs an edit to the machine, `Eff`, `Ty` or `Store.Val`;
- a claim is false as stated: give the counterexample.

## What you report

The receipt is `docs/research/2026-10-14-faces/receipt.md`. It opens with the one thing the
coordinator must know before merging. Then, per slice:
- the base and head commits;
- the files;
- the commands and their results;
- the axiom output;
- what is proved, what is decided per run, what is tested and what is assumed.

Propose decisions rows in the receipt, never in the register.

The next chunk, after this one: the queue-workers crew's open goals (`jobs_step`, `rest_step`,
`logs_history`) by the direct route, then the lowering (V5's repository through LCNF, then V6).
