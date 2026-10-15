# Codex: organize the paused seats' work into the existing work streams

## The one thing to know first

The owner paused the codegen seat and the lowering-cleanup seat on 2026-10-15: "they've landed
enough", and two parallel seats were "too distracting ... and causing conflicts". The codegen
seat's work is merged. The cleanup seat's S3 is committed on its own branch, unmerged, because its
OCaml route gates never ran. Place every open item they leave into the existing work streams, in
one ordered list. Write a proposal only. Add no work stream unless an item fits none, and say why
if so.

## Base

`refactor/phase1-phase3` at the commit that adds this brief. Rows 387, 391 to 397 of
`docs/core/decisions.md` govern it.

## What to read

1. `docs/STATE.md`, "Next, in order" and "What the owner must decide". Its list is dated
   2026-10-13. It predates the codegen refactor, the interop plan and the cleanup seat.
2. The codegen seat's receipt, `docs/research/2026-10-15-codegen-review/receipt.md`, with its
   "Wind-down handoff" section, and the review it serves, `docs/research/2026-10-15-codegen-review/`.
3. The cleanup seat's brief, `docs/research/2026-10-15-seat-cleanup-brief.md`. Its receipt and
   tools are on branch `claude/cleanup` at `435f599d4`, not on the base: read them with
   `git show claude/cleanup:docs/research/2026-10-15-seat-cleanup-receipt.md`, its
   "Wind-down handoff" and "S4" sections. S3 is that commit's code.
4. The lowering state, `docs/research/2026-10-15-lowering-state/README.md` §6.
5. The interop plan, `docs/research/2026-10-15-interop-plan/README.md` (P0 to P6), and the
   exploration's slices A1 to A7, `docs/research/2026-10-15-ocaml-interop-explore/README.md` §7.7
   and §9, with Codex's own review there. Slice A1 is unbuilt on branch `wip/a1-document-json`;
   its note is `docs/research/2026-10-15-a1-wip/README.md` there.
6. The coordinator's gate plan, `docs/research/2026-10-15-gate-consolidation/README.md`: seven
   targets, gates keyed on content and shared, and fixture writers that import no battery. It
   replaces the cleanup seat's S4.
7. Decisions rows 387, 391 to 397.

## The questions

1. **The streams.** Name the work streams that exist: the vertical slice and its faces, the
   lowering and OCaml estate, the codegen refactor, the interop slices, the proof goals, and any
   other the documents keep. Give each its owner document.
2. **Each open item.** For every open item of the two handoffs, every unstarted step (CR-n, S-n),
   and every open proposal: name its stream, its consumer, what it waits on, and its rough size.
   Flag an item that duplicates another, or that a later ruling made moot.
3. **The order.** One ordered list across the streams, by what unlocks what. Put an owner's
   decision where it blocks.
4. **The unmerged branches.** For `claude/cleanup` (S3) and `wip/a1-document-json` (A1), say
   what each needs before it merges, and in which order.
5. **The gates.** Check the gate plan against S4's census in the cleanup receipt. Name any cut or
   repair S4 found that the plan misses.

## The deliverable

Write `docs/research/2026-10-15-workstreams/README.md`. Open with the one change to `STATE.md`'s
order the coordinator must make first. Then give the streams table, the item table and the
ordered list, and a proposed replacement for `STATE.md`'s "Next, in order", within one page.
Propose decisions rows in the note; do not edit the register or `STATE.md`.

## Rules

- Read only. Install nothing, download nothing, build nothing.
- Never redirect stderr to `/dev/null`.
- Write in the controlled English of `docs/core/controlled-english.md`.
