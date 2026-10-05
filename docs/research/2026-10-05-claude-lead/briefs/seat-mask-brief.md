# 2026-10-05 brief for seat MASK: the mask that restores

Status: a brief (history, not authority), written ahead of its dispatch. Base: the head of
`refactor/phase1-phase3` that the dispatch message names, after seat T5's merge. The
coordinator dispatches it under decisions rows 237 and 251.

## Why this slice comes now

The Queue's wrapper masks its registration and restores the caller's interruptibility around
its wait. A probe ran the wrapper with `uninterruptible` and `interruptible` in their place
(`docs/research/2026-10-05-claude-lead/queue-readiness/queue-readiness.md`, F5). That is right
under an interruptible caller only. Under a masked caller the restore must be the identity.
This slice lands the mask, and the Queue's first path follows it (row 251).

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt.

- **Worktree, branch and scratch folder:** the dispatch message names them.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **Make:** give `make` the flags `-o build -o ts/eff/node_modules`.
- **OCaml:** only through `opam exec --switch=effect4 -- dune …`.
- **TypeScript:** only tsgo 7, the pinned `@typescript/native-preview`. Never `tsc`.
- **No install and no download.**
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Disk:** stop and report below 4 GiB free.

## Read first, in this order

1. `AGENTS.md`, in full.
2. `docs/research/2026-10-05-claude-lead/mask-second-note.md`, in full. Its findings F3 to F10
   are your specification. The owner ruled its proposals as decisions rows 244 to 246.
3. `docs/core/decisions.md`, rows 227, 239 and 244 to 246.
4. `docs/research/2026-10-05-claude-lead/waiting-design.md`, F4 and F5: what the mask is for.
5. Codex's two reviews, under
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/`: the folder
   `mask-second-review`, and the file `proof-scouting/mask-tooling.md`.
6. `uninterruptibleMask` and `interruptible` in
   `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`: the lines that the action transcribes.
7. The receipts of the two seats before you: `docs/research/2026-10-05-seat-FOLD-receipt.md`
   and seat T5's, which the dispatch message names. They show how an appended constructor
   travels through the wire, the estates and the laws.

## The assignment

Build the note's proposal: a type, an action and a node.

1. **The type.** An opaque host type with a reserved target, as F3 states it. Its members are
   the two images of the saved bit. **The image's exact encoding is your first decision,**
   before any proof (row 244). State it in the receipt with its red control: a Boolean value
   does not fit the type, and the image does not fit `bool`.
2. **The three refusals of the reserved target** (F3): an external allocation, a host answer
   column, and a service carrier in the first profile.
3. **The action `getInterruptible`,** one constructor of `ActionTerm`, appended. It transcribes
   the pin's mask at a constant body: it masks, answers the entry flag and pops.
4. **The node `restore saved body`,** one constructor of `Eff`, appended. Its body is child 0.
   It compiles with no step of its own, as F3's clause shows.
5. **The typing rules:** the three lines of F3. Typing is the check at program admission, and
   no expansion is recognized (F4).
6. **The printed TypeScript form:** the two rows of F5, with their two reserved heads. `read_print` and
   `read_exact` keep their statements, and `table_apart` and `table_shape` are decided again
   for the extended table.
7. **The derived form and its builder** on the authoring surface:
   `uninterruptibleMask body := bind (withFiber getInterruptible) (uninterruptible body)`.
8. **The wire and the estates.** One tag of `Eff` and one of the action are appended. The
   generated groups follow, in the OCaml and the TypeScript estates.
9. **The laws,** in the order of F10. The saved image's membership comes first. Then come the
   getter's answer and the body at child 0, and then the five statements of F7.

Where the note leaves a choice open, make it and state it in the receipt. Where the tree
proves the note wrong, stop that part and report with the evidence. Do not redesign.

## The obligations and their placement

The registry holds these five parts since 2026-10-05, each as a proposed claim. State each as
a planned goal first, with its placement, and then prove toward it.

| Claim | Concept, requirement | Reach | It does not establish |
| --- | --- | --- | --- |
| `saved-mask-image-membership` | `store-typing`, R4 | The reserved target, the two images, typed stores and environments, a later world | No reply admission |
| `scoped-body-substitution-boundary` | `residual-program-typing`, R4 | A checked body at child 0, a typed stack and captures | No agreement with a target |
| `saved-mask-restoration` | `scope-lifetime-finalization`, R11 | The five statements of F7: both bits, nested regions, each completed exit, pending causes | No progress, and nothing about the Queue |
| `mask-rows-table-premises` | `translation-simulation`, R8 | Program syntax: `read_print` and `read_exact` at the extended table | No typing, and no behaviour of the target |
| `mask-printed-form-profile` | `translation-simulation`, R10 and R11 | A named build, compatible decisions, the two checkpoints of F6 | No equality with the native spelling |

- A theorem that is proved today stays proved. Each gains its case.
- A planned goal is allowed only for a statement that one of the five claims owns. Give it its
  `@[semantics …]` placement, name its consumer, and list it first in the receipt.
- Before a proved top node of a requirement would rest on a goal, stop and report.
- Do not edit `docs/core/decisions.md`, `lakefile.toml` or `docs/STATE.md`.
- Proof search is `aesop` with the named rule sets. Do not write `simp_all`, `first` or `try`.
  A hand `simp` is `simp only [...]`. Every warning is an error.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`.

## Order

Cut the work into steps that are each green and committed.

1. **The route, first.** Add the two constructors and their machine clauses. Regenerate the
   LCNF group. `LcnfGen` must report no hole and pass its name check, and the engine must run
   a masked wait on both carriers. If the route refuses a clause, stop and report.
2. The type, its image and its three refusals.
3. Typing, the compile clauses and the kernel's case.
4. The faces: the two rows, the reserved heads, the readers, the prelude's alias.
5. The derived form, its builder and its scope law.
6. The laws and the registry's five claims.
7. The acceptance fixture, the truth programs and the receipt.

## Acceptance

1. **The fixture,** a new battery `Test/Program/MaskContract.lean`, imported in `Test/All.lean`
   on the line after `import Test.Program.FoldContract`. It holds:
   - the scenarios S1 to S10 of the note's F7, on the machine;
   - the control of F3 for the body's address. Each saved choice stands around a `bind` that
     reads an outer variable and then performs an operation. One more body holds a fork and a
     layer reference;
   - the two refusals: a Boolean used as a saved value, and a host answer at the reserved
     target;
   - a restore under a caller that is already masked: it is the identity.
2. **The Queue probe under the mask.** Copy `take` of
   `docs/research/2026-10-05-claude-lead/queue-readiness/QueueSteps.lean` with the mask and its
   restore in place of the stand-ins. Scenarios R2, R5 and R7 keep their answers. Add one:
   a taker under a masked caller is not interrupted while it waits.
3. **The engine.** A masked wait runs on both carriers of the generated engine.
4. **The faces.** A program with a mask around one wait prints as F5 shows, type-checks under
   tsgo 7 and reads back. Two truth programs run on the pin with the machine's answer. One
   is a mask around a wait that is interrupted. The other is a restore under a masked caller.
5. **Run these, and give each result in the receipt:**
   - the default `lake build`, with the gate lines of `Test/All.lean`;
   - `python3 scripts/generate.py` for each group you changed, then `git status`;
   - `make corpus`, then `dune build`, `dune test --force eff gen clock` and
     `dune test --force engine`;
   - `make check-truth` and `make check-ts-reader`;
   - `python3 scripts/check-conform.py compiler`;
   - `make check-cases`: give the refusal's lines in the receipt, and do not re-pin the policy.
6. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`, `make check-target`,
   the conservativity script, `make gen-truth-ledger` and `make check-truth-release`. The
   coordinator runs them at the merge. List each as "not run".

Commit each finished step, so that the branch shows where you are.

## What is not in this slice

- The Queue, the Semaphore and the waiting wrapper as a library.
- The dual mask, `interruptibleMask`. The note leaves it for later.
- The native callback spelling of the mask. It is not printed (F5).
- A service that carries the saved value. The first profile refuses it.
- The retained baselines under `Test/fixtures/baseline/<commit>/`: no hand edit. The
  compatibility policy beside them names each appended constructor.

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- A stale `.lake/corpus` makes one engine check fail after a wire change. `make corpus` prints
  the corpus again.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-05-seat-MASK-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. the changed files, by group;
4. each command with its result, and the evidence word for each claim;
5. the axiom output for the changed theorems, and each claim's `#plan_status` line;
6. each landed theorem's placement, and each planned goal with its consumer;
7. the image's encoding, and each other choice you made;
8. the open obligations, and what the Queue's slice needs from this one;
9. proposed decisions rows. Do not edit the register.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
