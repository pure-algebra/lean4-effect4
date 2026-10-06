# 2026-10-06 transition account: implementation passes to Codex, the coordinator reviews

Status: a working note (history, not authority). It answers the owner's steer that Codex
relayed on 2026-10-06. **The owner approved the handover the same day**, in session, by
voice (decisions row 277). **The handover point is reached** at `f6fa54e7`: both running
seats are merged with their records, and no seat of the coordinator runs.

## The steer, as relayed

- Implementation ownership inverts: Codex implements, and Claude reviews.
- No active seat was interrupted. Seats LIFT and SEMW finished their slices, with their
  receipts and their remaining obligations.
- The handover point was set before the staffing plan grew: no seat was added.
- Codex formalized its graph, type, session and clock research into next-slice plans. Its
  packet is filed
  (`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/capability-design-2026-10-06/`).
- Codex vendored nine papers at the owner's request: `vendor/papers/program-graphs/`. Git
  tracks the folder's index and provenance files. The originals stay on disk.

## What is true at the handover head

Measured by `make status` at `f6fa54e7` (branch `refactor/phase1-phase3`, nothing pushed):

- the tree is clean, and the battery is built and up to date;
- claims: 122 proved, 3 absent, 1 refuted, 1 assumed; no planned goal is open in the law
  graph; 13 requirements are open; the 24 planned goals of the batteries are the scenarios'
  and the fixtures' (11 declarations rest on them);
- the gates of the last merges passed on the merged tree: default build 1018 jobs; 768
  modules and 90105 declarations at `[propext, Quot.sound]`; `dune test --force engine` 1785
  passing lines, none failing; the truth lane's 61 programs: 60 agree, with 1 signed
  divergence; the corpus lane's 400 programs match, with 25 registered disagreements; the
  release ledger holds 61 programs; `check-semantics`, `check-cases`, `check-docs` and
  `check-conservativity` pass;
- **no sweep ran today.** `make check`, `check-full`, `check-gen` and `check-slow` are
  stale by the status tool's list. A sweep is the owner's to ask for.

## The seats of 2026-10-06, all merged

| Seat | Merge | Receipt | What it leaves open |
| --- | --- | --- | --- |
| REFS | `c957bfab` | `docs/research/2026-10-06-seat-REFS-receipt.md` | row 273 |
| PUB | `c46e3ca1`, `bc0ee4c1` | `docs/research/2026-10-06-seat-PUB-receipt.md` | rows 274 and 275 |
| MASKPOP | `2266ec30` | `docs/research/2026-10-06-seat-MASKPOP-receipt.md` | the lift, now landed |
| CUTS | `f3568844` | `docs/research/2026-10-06-seat-CUTS-receipt.md` | the move of the driver's laws into the law graph |
| QINV | `13a77be6` | `docs/research/2026-10-06-seat-QINV-receipt.md` | the wrapper's run |
| POOL | `0cd730ca`, `4667df9a` | `docs/research/2026-10-06-seat-POOL-receipt.md` | row 276 |
| CHECK | `0c4f9774`, `c22f908d` | `docs/research/2026-10-06-seat-CHECK-receipt.md` | nothing |
| LIFT | `d734aa6a`, `d81c4dcf` | `docs/research/2026-10-06-seat-LIFT-receipt.md` | row 278: the bracket of a region |
| SEMW | `831a76f3`, `f6fa54e7` | `docs/research/2026-10-06-seat-SEMW-receipt.md` | row 279: the runner's rule, Pool's `use` |

Each of the last two receipts serves a reader with no part in this session: the open
obligations, the next slice's starting statements and the commands of each lane.

## What the next implementer inherits

In the order that the coordinator would take them. The owner and the next implementer decide.

1. **Seat WORKQ's slice, prepared and not dispatched**: the workers over the public Queue
   (`briefs/seat-workq-brief.md` beside this note). Its worktree `lean4-effect4-qsteps`
   stands on `seat/workq` at the handover head, with the package links and no commit.
2. **The bracket of a region**, the next proof slice of R11 (row 278, point 3). Seat LIFT's
   receipt, item 8, gives the starting statements, two compositions that compile in scratch
   and the two open facts.
3. **Pool's public slice** (rows 276 and 279, point 3). Seat SEMW's receipt, section 9, lists
   eight things that `use` still needs. One of them waits for the owner: what `use` answers
   at a closed pool.
4. **The runner's rule of the truth lane** (row 279, point 1): a small slice, with its
   evidence and its steps filed (`docs/research/2026-10-06-seat-semw-evidence/README.md`).
5. **Codex's capability packet**: the checked focus, one rewrite for straight programs and
   loops, and the rest of its priorities. Every statement there is uncompiled.
6. **The other candidates** of `docs/STATE.md` ("Candidates with no seat"), and the open
   parts of each requirement in `generated/semantics.md`.

Worktrees: `lean4-effect4-qsteps` (prepared), and four idle ones: `lean4-effect4-mask`,
`lean4-effect4-qtypes`, `lean4-effect4-lower` and `lean4-effect4-t3b`. One older branch is
unmerged and not of this day's work: `seat/language` (2026-10-03).

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
   `make check-truth-release`), and the merge runs `make gen-corpus-results`,
   `make check-corpus`, `make check-ts-reader` and `make check-target` too.
6. A new law module gets its default concept in `tools/Tools/SemanticsRegistry.lean`. A
   receipt's proposed claims join the claims list, each with its required property in
   `docs/core/semantics.md`. The seat reads the entered text and corrects it in its receipt:
   seat LIFT's receipt corrected four sentences that the coordinator wrote.
7. Commit by explicit paths, with `git commit -F <file>`. A file under `docs/research` needs
   `git add -f` in its own command. Never push.
8. `make check-gen` is a full-tree build. It runs at a sweep, never between merges.
9. A document-only merge runs `make check-docs`. A registry edit runs `make gen-semantics`
   and `make check-semantics`.

## Open points for the owner

1. **Who integrates after the handover?** One party should merge, run the wide gates and
   keep the registers (`docs/core/decisions.md`, `docs/STATE.md`, the registry,
   `lakefile.toml`). Until the owner names a party, the coordinator keeps these duties.
2. **Does the reviewer build?** A reviewer that runs the gates of a hand-back finds more
   than one that reads only.
3. **The build slots.** The machine has two slots of two threads (8 cores, 16 GB).
4. **A sweep at the handover head** is the owner's to ask for.
5. **What Pool's `use` answers at a closed pool** (row 279, point 2). The pin interrupts
   there, by a reading. A probe of both builds comes before a ruling.
6. **`Cmd.loop` at an exited fiber** (row 278, point 4). The coordinator proposes no change
   while no consumer reads an exited fiber.
