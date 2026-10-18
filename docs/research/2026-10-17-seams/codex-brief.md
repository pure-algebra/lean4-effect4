# Codex: a review of the authoring system's seams, before the full Lean type signatures

## The one thing to know first

`docs/research/2026-10-17-seams/README.md` proposes the interfaces of three seams (the protocol, checking
and the store) and an exchange layer. It merges nine parallel designs, all kept in `designs/`. The
owner settles the seams after your pass, and then the full Lean type signatures are written and
landed. Check the design against the code and walk its calculations. Say where it is wrong, weak or
missing a better reuse. Settle technical questions with evidence; do not hand them back.

## Base and where you work

- The main checkout `/Users/pooks/Dev/lean4-effect4`, branch `refactor/phase1-phase3`. The head is the
  commit named in the paste prompt. The authoring branch is merged into it at `774ddc3d7`.
- Write the review to `docs/research/2026-10-17-seams/codex-review.md`. Put probes and their logs in
  `docs/research/2026-10-17-seams/review-probes/`. Edit nothing else, and commit nothing.
- Run every `lake` or `lean` command through `scratch/lean-slot.sh`, with `LEAN_NUM_THREADS=3`, one at
  a time. Never run `lake build Test`, `make build` or `make check-full`. OCaml:
  `cd ocaml && opam exec --switch=effect4 -- dune …`.

## Read first

1. `docs/research/2026-10-17-seams/README.md`, the proposal, and `cuts.md` beside it, the cut list.
2. `designs/A1` to `C3`, the nine designs, and `brief-common.md`, their brief.
3. `docs/research/2026-10-17-session-composition/plan.md` (version 2), `codex-review.md` and `ledger.md`
   beside it: your earlier review and its dispositions.
4. `docs/research/2026-10-17-authoring-and-store/README.md`: the interface to date, its duplicates,
   and the store to date.
5. `docs/research/2026-10-17-ocaml-estate-review/cas/README.md` and `plan.md` §2 there.
6. The code the proposal cites, by declaration name.

## The questions

1. **The certified-value pattern** (§2). Does one shape, data with a private constructor and an
   erased replay witness, fit `Live`, `Doc`, `FillSet`, `Tool.State`, `Cas` and `Check.Memo`? Is a
   reachability witness the right replacement for the plan's `StateInvariant` field? Probe the Lean
   form and the erasure under the OCaml lowering.
2. **The protocol** (§3). Check `act`/`ask`, `dry`, `now` and `Place.hole` against the three outcome
   kinds and your earlier controls R1 to R13. Walk the §3.3 trace against the code. Is `ask` as a
   function argument of `serve` sound, and does `serve_ask` hold as stated?
3. **The exchange** (§3.2). Is a `Tree` node the right state image? Is `Tool.load` as a replay of a
   derived transcript enough to rebuild every witness? Are the two stalenesses kept apart?
4. **Checking** (§4). Do two key constructors serve every caller? Is `combine_deps` true at depth
   one, layers included? Walk the §4.2 trace. Confirm or refute the `certifiedB` mismatch with a
   control at a filling beside a layer reference.
5. **The store** (§5). Check the transaction's refusal order and the derived action cache. Weigh
   compare-and-set on the digest, with fast-forward, against `putRoot`'s versions. Check the
   refinement clauses.
   Walk the §5.3 trace. Say what the Rocq laws in `rocq/StoreLaws.v` still cover after the changes.
6. **The data** (§5.4). Check each carrier's kind, its root and how it is rebuilt. Is `after` in
   `Entry.action` worth its bytes? Does the gate cache key omit its command today?
7. **The pedigree** (§6). Is each Jane Street precedent described accurately, and is anything
   better left untaken?
8. **The decisions** (§7) and the open points (§8). Give a verdict and a reason for each.
9. **The slices** (§9). Is the order right, is any slice too large, and is anything missing before
   Incremental?
10. **The cuts** (`cuts.md`). Confirm or refute each "cut now" row.

## What to report

Open with the finding that most changes what lands first. Then:

- a verdict per section of the proposal: holds, amend (with the amendment), or refuted (with the
  control);
- one row per finding, with these columns: ID `SM-C-<n>`, place, finding, evidence, severity, and
  the smallest change. Evidence is a reading, a probe or a test, with its command. Severity is
  before landing, soon, or nice to have;
- each probe with its command and result;
- what you did not check.

Follow `docs/core/controlled-english.md` §2, and run `python3 scripts/check-language.py --strict` on
your file.
