# 2026-10-06 transition account: implementation passes to Codex, the coordinator reviews

Status: a working note (history, not authority). It answers the owner's steer that Codex
relayed on 2026-10-06. The steer is a preparation. It is not in effect, and no register row
records it yet: the handover itself waits for the owner's own word.

## The steer, as relayed

- Implementation ownership will invert: Codex implements, and Claude reviews.
- No active seat is interrupted. Seats LIFT and SEMW finish at accepted boundaries, with
  their receipts and their remaining obligations.
- The handover point is set before the staffing plan grows.
- Codex formalizes its graph, type, session and clock research into next-slice plans, and it
  goes on scouting. Its packet follows after its own verification.
- Codex vendored nine papers at the owner's request: `vendor/papers/program-graphs/`
  (originals, a manifest with hashes, a figure guide). The folder is untracked. The
  coordinator leaves it as it is.

## What is true at the head

Measured by `make status` at `c986b839` (branch `refactor/phase1-phase3`, nothing pushed):

- the battery is built and up to date; the only untracked path is `vendor/papers/`;
- claims: 118 proved, 3 absent, 1 refuted, 1 assumed; no planned goal is open in the law
  graph; 13 requirements are open; the 24 planned goals of the batteries are the scenarios'
  and the fixtures' (11 declarations rest on them);
- the gates of the last merge (`ea036307`) passed on the merged tree: default build 1015
  jobs; 765 modules and 89517 declarations at `[propext, Quot.sound]`; `dune test --force
  engine` 1773 passing lines, none failing; the truth lane's 52 programs agree, with 1 signed
  divergence; `check-semantics`, `check-cases`, `check-docs` and `check-conservativity` pass;
- no sweep ran today: `make check`, `check-full`, `check-gen`, `check-slow`, `check-corpus`
  and `check-target` are stale by the status tool's list.

## The seats

| Seat | Branch, worktree | Done | Left | Boundary |
| --- | --- | --- | --- | --- |
| CHECK | `seat/check`, merged (`0c4f9774`, receipt `c22f908d`) | all | nothing | closed |
| LIFT | `seat/lift`, `lean4-effect4-mask` | part A merged (`3475c065`); part B, the instance at a compiled program and both batteries on its branch | the final default build and the receipt | its hand-back, then one merge with the registry claim, the required property, a decisions row and the state record |
| SEMW | `seat/semw`, `lean4-effect4-qtypes` | five steps merged (`aa70b078`, `4b57609c`, `ea036307`): the two wrapper forms, the six operations, scope, typing, nine attempt laws, the traces | the faces and the truth programs; the engine's case P9; the documents and the receipt | its hand-back, then one merge with the truth ledger, the corpus and target lanes, the claims and the records |
| WORKQ | `seat/workq`, `lean4-effect4-qsteps` | **not dispatched.** The brief is committed (`briefs/seat-workq-brief.md`, `c986b839`). The worktree is on the branch at that head, with the package links, and it holds no commit | the whole slice | a next-slice candidate, ready for the next implementer |

Each receipt is asked to serve a reader with no part in this session: the open obligations,
the next slice's starting statements and the commands that reproduce each lane.

## The proposed handover point

The handover is clean when all four hold. None is rushed, and none needs a new seat.

1. Seat LIFT is merged, with its records.
2. Seat SEMW is merged, with its records. Its truth programs move generated files, so its
   last merges run the release ledger and the corpus and target lanes.
3. The records that the coordinator still owes are landed: three dictionary entries that seat
   CUTS proposed, the README's row for the record `cuts`, and two sentence repairs of
   `docs/STATE.md`.
4. One sweep runs at that head, if the owner asks for it. A measured base then stands under
   the first slice of the next implementer.

After the fourth point the tree has no unmerged seat of today, the registers are current,
and this account is brought up to date as the handover's record.

## What the next implementer inherits

- **A ready slice:** seat WORKQ's brief, which is Codex's own first dogfood recommendation.
- **The candidates** of `docs/STATE.md` ("Candidates with no seat"), each with its place.
- **The open parts** of each requirement, in `generated/semantics.md`.
- **Idle worktrees:** `lean4-effect4-lower` and `lean4-effect4-t3b`, beside the three above.
- **One older unmerged branch:** `seat/language` (2026-10-03), not of this day's work.

## The integration procedure, as practiced today

`AGENTS.md` owns the rules. These points are practice that it does not spell out.

1. `git merge --no-commit --no-ff <head>`; then the coordinator's edits (the registry,
   `docs/core/semantics.md`, the `Makefile`, the compatibility policy).
2. The gates run on the merged tree before the commit, each through
   `scratch/lean-slot.sh`, one log for each: `lake build`; `make gen-fixtures`; `make corpus`;
   `dune build` and `dune test --force engine` through `opam exec --switch=effect4`;
   `make gen-truth` and `make check-truth`; `make gen-semantics` and `make check-semantics`;
   `make check-cases`; `make check-docs`; `lake env lean Test/All.lean` for the gate lines;
   `make check-conservativity BASE=<the previous head>`.
3. Every `make` call carries `-o ts/eff/node_modules -o harness/truth/node_modules`, written
   out. A seat's call carries `-o build` too.
4. A merge that moves a retained corpus row names it in
   `Test/fixtures/baseline/66ee4657-supplement-v1.policy.json`, with a comment, in the same
   merge.
5. A new battery that `harness/truth/Truth.lean` imports joins `TRUTH_SOURCES` in the
   `Makefile`. New truth programs promote the release ledger (`make gen-truth-ledger`, then
   `make check-truth-release`).
6. A new law module gets its default concept in `tools/Tools/SemanticsRegistry.lean`. A
   receipt's proposed claims join the claims list, each with its required property in
   `docs/core/semantics.md`.
7. Commit by explicit paths, with `git commit -F <file>`. A file under `docs/research` needs
   `git add -f` in its own command. Never push.
8. `make check-gen` is a full-tree build. It runs at a sweep, never between merges.

## Open questions for the owner

1. **Who integrates after the inversion?** One party should merge, run the wide gates and
   keep the registers (`docs/core/decisions.md`, `docs/STATE.md`, the registry,
   `lakefile.toml`). Today that party is the coordinator.
2. **Does the reviewer build?** Codex reviews today without a build or an edit. A reviewer
   that runs the gates of a hand-back finds more than one that reads only.
3. **The build slots.** The machine has two slots of two threads (8 cores, 16 GB). The next
   implementer's builds share them with any seat that still runs.
4. **The sweep** of point 4 above is the owner's to ask for.
