# Seat brief: repair the drift seat BACKLOG found (seat DRIFT, documents only)

Status: brief (history, not authority). 2026-10-13. The coordinator dispatches it.

**The one thing to know first.** Seat BACKLOG's deep dive
(`docs/research/2026-10-13-backlog-deep-dive/README.md`, its drift sections) found authority
documents that say what the code no longer does. The owner then ruled the order and the open
questions in decisions row 373. Make the documents true at HEAD, and put row 373's order into
`docs/STATE.md`. Change no code.

## What to repair

1. **`docs/STATE.md`.**
   - The `Live` face is not landed: no `Live` declaration exists, and DM5 is the only DM slice in
     the tree (`5c01db4a3`). Say what landed and what is planned.
   - The sketch does not read every whole program: it refuses a layer reference
     (`layerReference`). Say so, and cite row 373 (7), which rules the repair.
   - Item 0 names Codex's `LayerMap` scout, which has no note. Codex reached its quota on
     2026-10-12. Drop it or mark it parked.
   - The heading "Partial programs" uses a phrase the dictionary refuses. Use the dictionary's word.
   - Put row 373 (1)'s order into "Next, in order": the `Live` face (DM1 to DM4), a definition
     block in the meaning (PROC-5), one checked replay route, then HO-4 and HO-5; CX3 and CX4
     wait for a consumer. Point to the deep dive's ranked list for the rest.
   - Keep the page one page: rewrite sections, never append a log, write no counts
     (`docs/STATE.md`'s own rule).
2. **`docs/core/host-boundary.md`.** §3 still lists the holes of rows 95 to 97 ("Fiber handles are
   exploitable now"); §6 still lists X3 as parked, though `run_eq_ref_table` and `session_eq_ref`
   are proved. Bring both to HEAD, and add row 373's points 2, 3 and 12.
3. **`docs/core/lcnf-route.md`.** §8 says none of the three faces refuses outside its bounded
   range; rows 321, 322 and 357 and the repair of `E4-RUN-CE-047` changed that. Restate what row
   108 leaves open, and add row 373 (4): the share's split claim is a stage, and the target is the
   LCNF route with a proved stage law, the lowered code's semantics in Lean behind clean APIs.
4. **`docs/core/api-surface.md`.** §1 says "all four" entry modules where there are five, and
   omits the sketch and edit-session exports. Count them from the tree and fix it. Note row 332's
   claim that `Effect4.Author` re-exports `derive_step` and the module form: neither exists in
   `src/`; propose the row's repair in your reply (the register is the coordinator's).
5. **`ocaml/README.md`.** It calls the engine's tests a declared-red sweep row, but
   `make check-ocaml` runs them. Read the `Makefile` and fix the sentence.

## Boundaries

- Edit only those five files. Never edit `docs/core/decisions.md` or any code. Never commit: the
  coordinator reviews and commits.
- Verify every fact you write against the tree (`git grep`, file reads); cite declarations by name
  and path, decisions by row, commits by hash. No `lake` and no `make` builds.
- Run `python3 scripts/check-language.py --show <file>` on each file you edit, and add no new
  finding. Then run `make check-docs`, which only resolves paths and links.
- Stop at about two hours. Reply with each change in one line, the check results, and the
  proposed repair of row 332.
