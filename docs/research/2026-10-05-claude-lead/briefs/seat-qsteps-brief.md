# 2026-10-05 brief for seat QSTEPS: the Queue's cell and its steps

Status: a brief (history, not authority), written ahead of its dispatch. Base: the head of
`refactor/phase1-phase3` that the dispatch message names. The coordinator dispatches it under
decisions rows 237 and 255. Row 255 is the owner's word on the design's five proposals: all
five as recommended.

## Why this slice comes now

The Queue's first path lands in three parts (`docs/STATE.md`, "Open at this landing").

1. The abstract contract, its capacity statement and its first profile are in the tree, proved.
2. **This slice:** the cell's encoding, and each step as one term that agrees with the model.
3. The public path follows seat T5 and the mask (row 251).

This slice needs neither T5 nor the mask. A probe already runs its steps and compares each with
the model on 200 states. You turn that probe into a library module with its laws.

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
2. `docs/research/2026-10-05-claude-lead/queue-readiness/queue-steps-design.md`, in full. Its
   findings F1 to F6 are your specification. Decisions row 255 rules its proposals 1 to 5 as
   recommended.
3. The probe beside it: `QueueSteps.lean` and `QueueSteps.out`. Read the section "The steps
   against the model" with care: its comparison is the executable form of your goals.
4. `Test/contracts/queue.contract.md`, and the four files it names under `Test/Program/`:
   `QueueModel.lean`, `QueueContract.lean`, `QueueCapacity.lean` and `QueueProfile.lean`.
5. `docs/core/decisions.md`, rows 219 to 222, 228 to 230, 233, 235, 238 and 240 to 243.
6. Seat FOLD's receipt, `docs/research/2026-10-05-seat-FOLD-receipt.md`, and
   `src/Effect4/Laws/Program/Typed/ListFold.lean`: `ListFoldRules` and `HandleIdentityLaws`.
7. Codex's two reviews of the design, under
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/`:
   `heartbeat-queue-steps-2311/review.md` and `heartbeat-queue-steps-2341/review.md`.

## The assignment

1. **The cell.** One record type at a message type `A`, with every field of the design's F1,
   and the initial value at a capacity. A request's identity and its hint are `Deferred`
   handles. Identities are compared by `sameHandle`.
2. **The six steps,** each one term for a `Ref.modify`: `takeStep`, `offerStep`, `pollStep`,
   `sizeStep`, `withdrawTake` and `withdrawOffer`. Start from the probe's terms.
   - A step names its notifications in the model's order: the accepted offers, then the taker
     to wake.
   - No fold states its accumulator's type.
   - A step frames every field that it does not change.
3. **The typing.** Each step term is typed at the cell's type, for any message type that the
   checker types in a cell.
4. **The model's place.** If the owner's word moves the model into the law graph, move four
   files: the model, the capacity statement, the profile and their controls. Keep each
   theorem's statement, placement and proof. The batteries keep the controls.
5. **The relation.** An encoding table gives each model identity its handle and its current
   hint. The cell's value is a function of the table and a profile state. Write both in Lean.
6. **The step goals,** one for each step, in the shape of the design's F3.
   - The domain is `FirstProfile`, with the request's premise `Requested`.
   - The table's injectivity and the replaced hint are written premises.
   - The conclusion gives the reply, the stored value and the ordered notifications: every
     signal of the model, and no other.
   - `acceptLoop_single` and `wake_profile` give the model's side in closed form.
7. **The battery.** Promote the probe's comparison into the tree.
   - The named controls C1 to C6, and the refusals P1 to P3.
   - The red controls M1 to M4.
   - Every state of the probe's universe, twelve moves on each.
   - The eight scenarios on the machine, R1 to R8.
8. **The engine.** Two scenarios run on the generated engine, through the wire.
9. **The documents.** A row for the module in `docs/ARCHITECTURE.md`, and its role in the
   architecture map's register.

Where the design leaves a choice open, make it and state it in the receipt. Where the tree
proves the design wrong, stop that part and report with the evidence. Do not redesign.

## The obligations and their placement

State each goal as a planned goal first, with its placement, and then prove toward it.

| Obligation | Concept, requirement | Reach | It does not establish |
| --- | --- | --- | --- |
| Each step's typing | `store-typing`, R4 | The cell's type at a message type, the six step terms | No agreement with the model |
| Each step's agreement with the model | `translation-simulation`, R10, a part of `queue-expansion-agrees` | `FirstProfile`, `Requested`, an injective table; the reply, the stored value, the ordered notifications | No delivery, no cancellation law, no liveness, no wrapper |
| The moved model's statements | as they stand | as they stand | as they stand |

- The consumer of each step goal is the wrapper's law, in the public path's slice.
- A theorem that is proved today stays proved.
- A planned goal is allowed only for a statement that the table names. Give it its
  `@[semantics …]` placement, name its consumer, and list it first in the receipt.
- Before a proved top node of a requirement would rest on a goal, stop and report.
- Do not edit `docs/core/decisions.md`, `lakefile.toml` or `docs/STATE.md`.
- Proof search is `aesop` with the named rule sets. Do not write `simp_all`, `first` or `try`.
  A hand `simp` is `simp only [...]`. Every warning is an error.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`.
- Keep `Nat` equality off `Classical.choice`: use `decide_eq_true` and `of_decide_eq_true`,
  never `beq_self_eq_true`.

## Order

Cut the work into steps that are each green and committed.

1. The cell's type, its initial value and their typing.
2. The six step terms and their typing. The probe's eight scenarios run on them.
3. The battery: the comparison, the controls and the universe. This is your net for the
   proofs that follow.
4. The relation in Lean, and the six goals as planned goals.
5. The proofs, shortest first: `sizeStep`, the two withdrawals, `offerStep`, `pollStep`,
   `takeStep`. Stop a proof that does not close in its step, and leave its goal planned.
6. The model's move, if the owner's word asks for it.
7. The engine's two scenarios, the documents and the receipt.

## Acceptance

1. **The battery** of the assignment's item 7 passes, with each red control red.
2. **The comparison refuses** a state outside the profile and a signal with no encoding.
3. **The scenarios** R1 to R8 keep the probe's answers.
4. **The engine** runs two of them on both carriers.
5. **The faces.** If seat T5 is merged in your base, the program R4 prints, type-checks under
   tsgo 7 and reads back. If it is not, pin the printer's refusal by name.
6. **Run these, and give each result in the receipt:**
   - the default `lake build`, with the gate lines of `Test/All.lean`;
   - `python3 scripts/generate.py` for each group you changed, then `git status`;
   - `make corpus`, then `dune build` and `dune test --force engine`, if you changed the
     engine's tests;
   - `make check-cases`: give the refusal's lines in the receipt, and do not re-pin the policy.
7. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`,
   `make check-target`, the conservativity script, `make gen-truth-ledger` and
   `make check-truth-release`. The coordinator runs them at the merge. List each as "not run".

Commit each finished step, so that the branch shows where you are.

## What is not in this slice

- The operations that wait: `Queue.make`, `Queue.offer` and `Queue.take`. They come with the
  wrapper, after the mask.
- The posted helper, its law, and the module's printed form.
- Batches, the terminal operations, `peek`, `await`, and the strategies other than `suspend`.
- A binding form in the term language. Repeat the passes, and measure each step's size.
- A hidden handle. The handle is the cell's `Ref` in this slice (row 230).

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- A stale `.lake/corpus` makes one engine check fail after a wire change. `make corpus` prints
  the corpus again.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-05-seat-QSTEPS-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. the changed files, by group;
4. each command with its result, and the evidence word for each claim;
5. the axiom output for the changed theorems, and each goal's `#plan_status` line;
6. each landed theorem's placement, and each planned goal with its consumer;
7. each choice you made, and each step's size in nodes and folds;
8. the open obligations, and what the public path's slice needs from this one;
9. proposed decisions rows. Do not edit the register.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
