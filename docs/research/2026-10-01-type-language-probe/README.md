# The type-language probe (2026-10-01): finish `Ty` once

Written 2026-10-01 by the coordinator on the owner's instruction: when records land, land every
other type form the target profile needs, so the type language is finished and stable, with its
generated machinery, faces, Schema arms and mirrors extended one time. Five probe seats, each in
its own worktree (`/Users/pooks/Dev/lean4-effect4-probe-<X>`, branch `probe/<X>`, base main
`c007d0ef`, `.lake` cloned and current), each answering a question list with checked evidence and
writing `docs/research/2026-10-01-type-language-probe/<X>/note.md` plus probes and logs, force-added
and committed on its branch. No seat edits a tracked file: a production-shaped change is made on a
copy under the seat's folder (a standalone file with its own imports, or a copied module), measured,
and reported with the lines it would touch. The coordinator synthesizes the five notes into the
data-wave briefs after pass I2 merges.

Authorities: decisions rows 119 (ruled), 122, 127, 128 (ruled), 120, 121, 123–126, 130, 131
(open, recommended); `docs/research/2026-10-01-data-probe/synthesis.md` §3 (the shapes R3.1–R3.9,
the stages, the measured cost, the commit series in §7, the open questions in §8) and its four
seat folders (`tree/`, `effect/`, `pedigree/`, `programs/`, with their model probes);
`docs/research/2026-10-01-formal-pass/types/note.md` TY-09, TY-10; Codex's reviews of the owner's
draft reference (`/private/tmp/codex-record-review-2026-10-01/review.md`, `practical-review.md`,
with its probes `ConstructiveOrdering.lean`, `NestedDeriving.lean`, `field-names.cjs`) and of
Gemini's Schema scouting, whose current state is revision 5 (copied to `S-inputs/revision-5/`:
`review.md`, `annotation-review.md`, the probes and the host harness; the first revision's
`review.md` and `probe-review.md` at the folder root are history); the owner's draft
`docs/research/2026-10-01-data-stage-1-record-theory-reference.md` (untracked; read it as a draft
with the corrections Codex lists, never as authority). The vocabulary is `AGENTS.md` and system map
§§4–5, §9: a new representation is admitted by naming its sort's signature and its arrows' kinds;
every traversal is a fold or generated from the signature; evidence words on every claim.

Seats: P (records and the type algebra, core), Q (generators, lowering, conservativity), R (terms,
faces, the acceptance harness), S (the Schema side: arms per form and the readable profile), T (the
completeness census: every form the target profile needs, and what else blocks full reification).

Rules for every seat: plan §4 of `2026-10-01-landing/plan.md` applies (the trust ceiling
`[propext, Quot.sound]`, `#print axioms` on every theorem, no `sorry`/`native_decide`/`partial`/
`unsafe`, no `simp_all`/`first | …`/`try` in a probe that proposes production text, hand `simp` as
`simp only`); `LEAN_NUM_THREADS=1`, one compiler at a time in the seat's worktree, probes by
`lake env lean -DwarningAsError=true <file>` (the tree is built; never `lake build` the roots);
generators only with their output redirected into the seat's folder; host tools (`bun`, `tsgo`,
`node`, `opam exec --switch=effect4 -- dune`) only on files in the seat's folder; never `git merge`/
`checkout`/`reset`/`push`; a refused permission is recorded, not worked around; plain words; every
number from a command named beside it. Receipt at the foot of `note.md`: base and head, changed
paths, commands and results, what is bounded or host-only, the proposed decisions rows and brief
text, and first the one thing the coordinator must know.
