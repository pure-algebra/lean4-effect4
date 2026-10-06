# 2026-10-06 brief for seat MOVE: the shared pieces of the composed modules get a home

Status: a brief (history, not authority). Base: the head of `refactor/phase1-phase3` that the
dispatch message names. The coordinator dispatches it under decisions row 237. It is step 9 of
the module procedure (`docs/research/2026-10-05-claude-lead/module-factory-plan.md`): a helper
moves to a shared home when a second module uses it.

## Why this slice comes now

Two composed modules are in the tree. Semaphore reads 93 declarations of the Queue's folders
and changed none (`docs/research/2026-10-06-seat-SEM-receipt.md`, item 8, a census of the
environment). Fourteen general statements wait in Semaphore's folder. The Queue's public path
is the next slice, and it must start on the shared homes, not on the Queue's private folder.

**The goal.** Each shared piece has one home that names no module. Both modules read it there.
No statement changes, and no step term changes.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt.

- **Worktree, branch and scratch folder:** the dispatch message names them.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **Make:** give `make` the flags `-o build -o ts/eff/node_modules`, and run it through the
  slot script too.
- **OCaml:** only through `opam exec --switch=effect4 -- dune …`.
- **No install and no download.** No TypeScript run is in this slice.
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Disk:** stop and report below 4 GiB free.

## Read first, in this order

1. `AGENTS.md`, in full.
2. Seat SEM's receipt, items 7 to 10: `docs/research/2026-10-06-seat-SEM-receipt.md`. Item 8
   lists what Semaphore reads of the Queue's folders, and the 14 statements that wait.
3. Seat QTYPES's receipt, its section of proposals:
   `docs/research/2026-10-05-seat-QTYPES-receipt.md`.
4. The files that you move from: `src/Effect4/Modules/Queue/Steps.lean` and `Cell.lean`; the
   eight files of `src/Effect4/Laws/Modules/Queue/`; the six of
   `src/Effect4/Laws/Modules/Semaphore/`.
5. Codex's review of the list facts:
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/list-lemma-review/recommendations.md`.
6. `src/Effect4/Data/Constructive.lean`, the namespace `Effect4.Constructive.List`.

## The one rule

**Move, and do not restate.** A moved declaration keeps its name, its statement and its
proof. Only its file and its namespace change, and the names of other moved declarations
inside it. Write a script that lists each moved declaration's type, before and after. Make
the moved names equal, and show that the two lists are equal. Keep the script and its output
in the scratch folder, and give the command in the receipt.

If a statement must change for the move to build, stop that declaration and report it.

## The assignment

### 1. The shared homes

Every shared declaration is in the namespace `Effect4.Modules`.

| New file | What moves there | From |
| --- | --- | --- |
| `src/Effect4/Modules/Words.lean` | The words that a step term is written with: `andT`, `orT`, `notT`, `ifT`, `isEmpty`, `len`, `noneOf`, `noneT`, `nilT`, `snoc`, `same`. The removal pass, under the name `removeById`. The type `idTy` of an identity and of a hint that carries nothing. | the Queue's `Steps.lean` and `Cell.lean` |
| `src/Effect4/Laws/Modules/Table.lean` | `Table`, with `handle`, `hint`, `Injective` and `renew`; `Table.Injective.decides` | the Queue's `Relation.lean` and `Reading.lean` |
| `src/Effect4/Laws/Modules/Reading.lean` | `Reads`, `Captured` and `Pointwise`, with their lemmas. Every `reads_…` rule of a builder or a word. The lemmas of a minted name. The values of the atoms. `reads_removeById`. | the Queue's `Relation.lean` and `Reading.lean`; Semaphore's `Reading.lean` |
| `src/Effect4/Laws/Modules/Checking.lean` | `Types`, `TypesEach` and `CapturedTy`, with their lemmas. Every `types_…` rule of a builder or a word. `types_removeById`. | the Queue's `Checking.lean` and `Typing.lean`; Semaphore's `Typing.lean` |
| `src/Effect4/Laws/Modules/Store.lean` | The three connectors to the store: `step_updates`, `step_keeps_cell` and `cell_read` | the Queue's `Steps.lean` |

Three more destinations exist already.

- `nativeAtomTy_add` goes into `src/Effect4/Laws/Program/Typing/TermIntro.lean`, beside
  `nativeAtomTy_isZero`.
- A fact that names lists and numbers only goes into `Effect4.Constructive.List`
  (`src/Effect4/Data/Constructive.lean`). Semaphore's receipt names six candidates. A fact
  that names a term or an atom stays in the shared reading file.
- A declaration that names the Queue's cell, its model or a step of it stays in the Queue's
  folder. The same holds for Semaphore.

Keep `reads_removeTaker` and `reads_removeOffer` in the Queue's folder, each as one
application of `reads_removeById`.

Where a piece's right home is not clear from this table, choose, and state the choice in the
receipt. Add no new folder beyond these files.

### 2. Both modules read the shared homes

The Queue's and Semaphore's files import the shared files and `open Effect4.Modules`.
Semaphore no longer opens `Effect4.Queue.Model`. Each battery follows.

### 3. The list facts of Codex's review

- Move the five facts of `src/Effect4/Laws/Program/Template.lean` into
  `Effect4.Constructive.List`: `flatMap_congr`, `mem_zip_map_self`, `mem_zip_middle`,
  `eq_of_mem_zip_map` and `lookup_of_mem_nodup`. Update their callers.
- Expose `lookup_weaken` of `src/Effect4/Program/Typing/Rules.lean`. Make `evalTerm_weaken`
  use it, and remove `getElem?_weaken` of `src/Effect4/Laws/Program/Typed/ListFold.lean`.
- `Typed.mem_zip_self` may follow from the shared `mem_zip_map_self`. Keep its statement.

### 4. The token `under`

Three commands reserve the token: `#exhaustive_gate`
(`src/Effect4/Laws/Auto/Exhaustive.lean`), and `#traversal_census` and `#traversal_class`
(`src/Effect4/Laws/Auto/Traversals.lean`). Write `&" under "` in each, so that the word is a
keyword in that place only. Add one control: a hypothesis named `under` in a battery that the
audit environment reads.

### 5. The report's short names

`tools/Tools/Semantics.lean` prints a node by the last component of its name. Two modules now
have a `takeStep_types` and a `takeStep_agrees`. Print the last two components where two
nodes of one requirement share the last one. Do not regenerate `generated/semantics.md`.

### 6. The documents

- `docs/ARCHITECTURE.md` and `tools/Tools/ArchitectureRoles.lean`: a row and a role for each
  new file. Two proposals wait there too. Seat QTYPES proposes a row for the typing rules.
  Seat MASK proposes rows for its three law modules and its builder
  (`docs/research/2026-10-05-seat-MASK-receipt.md`, section 10, item 8).
- Propose the default concept of each new file in the receipt, for the semantics registry.
  Do not edit `tools/Tools/SemanticsRegistry.lean`.

## The files

You may add the five new files of part 1. You may edit the Queue's and Semaphore's files under
`src/Effect4/Modules/` and `src/Effect4/Laws/Modules/`, their batteries under `Test/Program/`,
and the files that parts 3 to 6 name.

Edit a root only at its anchor:

- `src/Effect4.lean`: before `import Effect4.Modules.Queue.Cell`;
- `src/Effect4/Laws.lean`: before `import Effect4.Laws.Modules.Queue.Capacity`;
- `Test/All.lean`: beside the batteries that you touch.

Do not edit `docs/core/decisions.md`, `lakefile.toml`, `docs/STATE.md`,
`generated/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.

## The obligations and their placement

No new theorem is asked for. A moved theorem keeps its `@[semantics …]` placement. If you
state a new lemma, place it first, as `AGENTS.md` requires, and name its consumer.

- A theorem that is proved today stays proved, with its statement.
- No planned goal is added.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. Every
  warning is an error. Do not write `simp_all`, `first` or `try`.
- The proof-style baseline counts uses by file. Moved proofs move their counts. Run
  `make record-proof-style`, and show in the receipt that each kind's total did not change.

## Order

Cut the work into steps that are each green and committed.

1. The words and `idTy` into `Words.lean`, with both modules reading them.
2. The table, the reading rules and the typing rules into their three files.
3. The store connectors, and Semaphore's 14 statements to their homes.
4. Codex's list facts, and `lookup_weaken`.
5. The token `under`, the report's short names and the documents.
6. The receipt.

## Acceptance

1. **The comparison of statements** shows no difference for a moved declaration.
2. **No term moved.** `make gen-fixtures` leaves `git status` empty: the engine's fixtures of
   the Queue and of Semaphore hold the step terms' bytes. The pinned printed steps of
   `Test/Program/QueueFaces.lean` stay as they are.
3. **Run these, and give each result in the receipt:**
   - the default `lake build`, with the gate lines of `Test/All.lean`;
   - `make corpus`, then `dune build` and `dune test --force engine`;
   - `make check-cases`: give the refusal's lines, and do not pin the policy again;
   - `make check-docs`.
4. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`,
   `make check-target`, `make check-truth`, the conservativity script, `make gen-semantics`.
   The coordinator runs them at the merge. List each as "not run".

## What is not in this slice

- A new statement about the Queue or about Semaphore.
- A change of a step term, of a model or of a contract packet.
- The Queue's public path, the waiting wrapper and the mask's run-level bracket.
- A rename of a theorem, but for `removeTaker` as the pass's name.

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- `List.erase_append` of core reaches `Classical.choice`. Seat SEM proved its facts of `erase`
  by induction. Keep those proofs.
- `src/Effect4/Data/Constructive.lean` has many dependents. A change there builds most of the
  tree again, so make it once, in one step.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-06-seat-MOVE-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. each moved declaration: its old file, its new file and its new full name, as one table;
4. each command with its result, and the comparison's command and output;
5. the axiom output of the moved theorems that carry a placement;
6. each choice of a home that this brief left open;
7. the proof-style baseline's diff, by kind;
8. the default concepts that you propose for the semantics registry.

The receipt also accounts for the requirements R1 to R13, in three lists taken from
`generated/semantics.md` and from `#plan_status`. A move advances no requirement: say so, and
name the open parts that it leaves untouched.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
