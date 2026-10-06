# 2026-10-06 brief for seat PUB: the Queue's first public operations

Status: a brief (history, not authority). Base: the head of `refactor/phase1-phase3` that the
dispatch message names. The coordinator dispatches it under decisions rows 233, 237, 251, 255
and 257. It is step 3 of row 233's order, and steps 3 to 8 of the module procedure
(`docs/research/2026-10-05-claude-lead/module-factory-plan.md`).

## Why this slice comes now

Everything under the Queue's operations is in the tree:

- the abstract model, its first profile and the profile's closure
  (`src/Effect4/Laws/Modules/Queue/`);
- the cell and six step terms, each typed at every message type and proved to agree with the
  model's step (`queue_steps_agree`);
- the mask that restores, with its builder `uninterruptibleMaskWith` (rows 244 to 246);
- the shared homes of the words, the reading rules, the typing rules and the store connectors
  (seat MOVE);
- the builders that mint the name they bind (`0a10ca6d`, `8e9b9736`).

The operations themselves are test fixtures. `Test/Program/QueueScenarios.lean` and
`Test/Program/QueueMask.lean` write `take`, `offer` and `size` with written names, and a
caller's variable of the same name would be captured. No Queue program has run on a host.

**The goal.** The first profile's operations are library programs that capture no name of a
caller. Each one's atomic attempt is proved to be the model's step, at the operation's own
scope. Each runs on the Lean machine, on the generated engine and on the pinned Effect.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt.

- **Worktree, branch and scratch folder:** the dispatch message names them.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **Make:** give `make` the flags `-o build -o ts/eff/node_modules -o harness/truth/node_modules`,
  and run it through the slot script too.
- **TypeScript:** only tsgo 7, the pinned `@typescript/native-preview`. Never `tsc`.
- **The host:** bun, with the pinned `effect` 4.0.0-rc.112, loaded by its directory.
- **OCaml:** only through `opam exec --switch=effect4 -- dune …`.
- **No install and no download.**
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Disk:** stop and report below 4 GiB free.
- **A hand-back comes early.** Check your own change with narrow builds. The coordinator runs
  the wide gates at the merge.

## Read first, in this order

1. `AGENTS.md`, in full.
2. The contract packet: `Test/contracts/queue.contract.md`. Its last section lists seven
   connectors. This slice takes connectors 1, 2 and 7, and it prepares 3 to 6.
3. The wrapper's design: `docs/research/2026-10-05-claude-lead/waiting-design.md`, F3, F5 and
   F7, with F9's corrections.
4. The rulings: decisions rows 219 to 222, 226, 230, 238, 240 to 246, 255 and 257
   (`docs/core/decisions.md`).
5. The fixtures that you replace: `Test/Program/QueueScenarios.lean` and
   `Test/Program/QueueMask.lean`. Then `Test/Program/QueueWorkload.lean`,
   `Test/Program/QueueFaces.lean` and `Test/Program/QueueEngine.lean`.
6. The steps and their laws: `src/Effect4/Modules/Queue/`, `src/Effect4/Laws/Modules/Queue/`,
   and the shared homes that seat MOVE's receipt lists
   (`docs/research/2026-10-06-seat-MOVE-receipt.md`).
7. What the mask gives a client: `docs/research/2026-10-05-seat-MASK-receipt.md`, section 9,
   from "The Queue's slice and the Semaphore's protected permit take the same things".
8. What the typing rules leave: `docs/research/2026-10-05-seat-QTYPES-receipt.md`, its last
   part. Two things are not proved there: the wrapper's law at its own scope, and a string
   literal as a caller's term.
9. The minted builders: `Authoring.performTermWith` (`src/Effect4/Program/Authoring.lean`),
   `Ref.modifyWith` (`src/Effect4/Program/Authoring/Rows.lean`), `selectOptionWith` and
   `onExitWith` (`src/Effect4/Program/Authoring/Sugar.lean`), `bindWith`, `iterateWith` and
   `foldWith`.
10. How a program reaches the pinned Effect: the truth lane (`harness/truth/Truth.lean`, and
    the group `truth` of `docs/GENERATED.md`). Section 8 of seat MASK's receipt explains the
    row `resumed k`.

## The assignment

### 0. The design note, first

Write `docs/research/2026-10-06-seat-PUB-design.md`, at most two pages, before the first Lean
commit. It states:

- **the shared wrapper's parameters:** what the wrapper owns, and what a module supplies.
  Row 221 gives the module its enrolment and its cancellation;
- **each binder of each operation,** and the builder that mints it;
- **each attempt law's statement,** in Lean, with its premises. They are the profile, the
  request's premise, the table and the capture of each minted name. Say where the typing
  equation comes from (row 257, points 1 and 2);
- **how a control records row 222's four observations apart:** the commitment, the
  operation's exit, the entry of the caller's continuation, and the fiber's exit;
- **which programs go to the truth lane,** and what each one compares;
- **the name of each operation.** Take the pin's spelling
  (`vendor/effect-4.0.0-rc.112/src/Queue.ts`), and say where the first profile is narrower.

Send the note's path to the coordinator in one message, and go on without waiting. Wait only
if a statement needs a ruling: a change of meaning, of the supported domain or of a
representation.

### 1. The shared pieces of a module that waits

Add `src/Effect4/Modules/Waiting.lean`, in the namespace `Effect4.Modules`. It names no
module. Semaphore is its second user, in a later slice.

- **The posted helper** (row 238): the fork options, and one builder. The builder posts one
  helper for each request of a list, in order, with one answer (row 240).
- **The cleanup on interruption:** `onExit` with a test of the exit. It keeps the interruptor
  in the fiber's exit (the readiness note's F2,
  `docs/research/2026-10-05-claude-lead/queue-readiness/queue-readiness.md`).
- **The wrapper** (row 221, `waiting-design.md` F5). It holds the mask, the loop of attempts
  and the wait at the mask's restore site. It withdraws when the wait is interrupted. A
  module supplies its attempt, its withdrawal and what each one posts.

Every binder is minted. No written name surrounds a term that a caller supplies.

### 2. The Queue's operations

Add `src/Effect4/Modules/Queue/Ops.lean`: the first profile's operations, each over the
library's step terms. The first profile is a positive capacity, the `suspend` strategy, and
one message for each request (`FirstProfile`). The operations are the queue's construction,
`offer`, `take`, `poll` and `size`.

- The handle is the cell's `Ref` (row 255, point 2). Add no handle type.
- A capacity of zero is outside the profile. Say in the design note where it is refused.
- Keep each operation's tree. For each of the eight scenarios and for the masked caller, the
  program over the library's operations has the bytes of today's fixture program
  (`Api.bytesOf`). Where a tree must differ, the receipt gives the difference and its reason.

### 3. Scope and typing, at every scope

- Each shared piece and each operation keeps the scope judgment, by `authoring_scoped` or by
  one application of the lifts' lemmas.
- Each operation is typed at every message type with `MessageTy`, for every caller's term of
  the right type, at every scope.
- Use the steps' typing theorems (`takeStep_types` and its siblings) and the shared typing
  rules. Use `MaskFormProfile.typed` and the capture of a minted name.

### 4. The attempt laws

Each operation has one statement, at its own step term under its own binders. The cell holds
the encoding of a state of the first profile. The store step then answers the model's reply.
It writes the encoding of the model's next state, and it names the model's signals in order.
A withdrawal has the same statement. `size` has the read law.

Each law is one composition of what exists:

- `step_updates`, `step_keeps_cell` or `cell_read`;
- the step's agreement (`takeStep_agrees` and its siblings) and the step's typing;
- the capture of the minted name of the current value.

State no new fact of the model.

### 5. The controls on the Lean machine

Move the batteries to the library's operations, and keep every answer.

- **The eight scenarios** R1 to R8, and the masked caller with its red control.
- **Hygiene.** A fixture wrote some names around a caller's term. For each such name, one
  control: a caller's variable of that name keeps its reading in the library's operation.
  The fixture's form is the red control.
- **The acceptance traces** of row 221 and of `waiting-design.md` F5 and proposal 5, each
  with its positive control:
  1. a notification before the await;
  2. a cancellation after the selection and before the delivery, under an interruptible
     caller, with the masked caller beside it;
  3. a late delivery to an old hint after the request waits again;
  4. a blocked offerer that is cancelled before any step accepts its message;
  5. a blocked offerer that is cancelled after a step accepted its message, and before its
     posted answer runs;
  6. the signalling fiber exits before the dispatch;
  7. the receiver's continuation that grows: report the budget that each length needs. Claim
     no bound.
- A cancellation control records row 222's four observations apart.
- Each fault fails the promised property, and not typing alone.

### 6. The faces and the host

- The TypeScript printer prints each operation, and the reader reads it back.
  `Test/Program/QueueFaces.lean` pins the printed text of one use of each.
- Add to the truth lane the programs that your design note names. At least four:
  - a taker that waits and is woken;
  - a second offer that waits at capacity one;
  - a waiting taker that is interrupted;
  - the masked caller.
- Each printed module type-checks under tsgo 7. Each run on rc.112 agrees with the Lean
  machine on the exit and on the schedule's rows.
- Name each new truth program in `Test/fixtures/target/selection.json`.
- A disagreement with the host is a finding. Stop that program, keep its evidence, and report
  it. Do not change an operation to make a row agree.

### 7. The engine

The Queue's lane (`ocaml/engine/test/queue/`) runs R1 and R4 today. Add the taker that waits,
the interrupted taker and the masked caller, on both carriers. Write the fixtures by
`make gen-fixtures`.

### 8. The documents

- `Test/contracts/queue.contract.md`: the state of each connector that this slice moves.
- `README.md`: a short section on the Queue's operations, with one checked example.
- `docs/ARCHITECTURE.md` and `tools/Tools/ArchitectureRoles.lean`: a row and a role for each
  new file.
- Propose in the receipt the default concept of each new law module, for the semantics
  registry. Do not edit `tools/Tools/SemanticsRegistry.lean`.

## The files

You may add `src/Effect4/Modules/Waiting.lean`, `src/Effect4/Modules/Queue/Ops.lean`, and
their law modules: `src/Effect4/Laws/Modules/Waiting.lean` and
`src/Effect4/Laws/Modules/Queue/Ops.lean`. You may edit the Queue's batteries under
`Test/Program/` and the Queue's engine lane. You may edit `harness/truth/Truth.lean`, with the
files that `make gen-truth` writes, and `Test/fixtures/target/selection.json`. You may edit the
documents of part 8.

Edit a root only at its anchor:

- `src/Effect4.lean`: after `import Effect4.Modules.Queue.Steps`;
- `src/Effect4/Laws.lean`: after the last import of `Effect4.Laws.Modules.Queue`;
- `Test/All.lean`: beside the Queue's batteries.

Do not edit `docs/core/decisions.md`, `lakefile.toml`, `docs/STATE.md`,
`generated/semantics.md` or `tools/Tools/SemanticsRegistry.lean`. Do not edit a file of
Semaphore, and do not edit a step term, the model or the profile.

## The obligations and their placement

| Statement | Concept; requirement | Reach | What it does not establish | Consumer |
| --- | --- | --- | --- | --- |
| Each shared piece and each operation keeps scope | `initial-algebras-folds`; R4, a step of `operation-data-scoped` and of the lifts' scope laws | every scope, every alphabet with `ScopedOp` where the piece is generic | typing | `Api.Author.build` of each client |
| Each operation is typed | `store-typing`; R4 | the checker's judgment at every scope, for every `MessageTy` and every caller's term of the stated type | any run | a client's admission; the attempt laws' typing premise (row 257) |
| Each attempt is the model's step | `translation-simulation`; R10, a part of the proposed claim `queue-expansion-agrees` | one store step, from a cell that encodes a state of `FirstProfile`, with the request's premise `Requested` and an injective table | no delivery, no order across steps, no cancellation law, no budget, no liveness, nothing of a host | the run-level law of the next slice, which relates the wrapper's run to the model |

- **No run-level law is stated in this slice.** `queue-expansion-agrees`,
  `waiting-request-obligation-preserved`, `wait-registration-no-gap`,
  `posted-wake-profile-agrees` and `embedded-budget-sufficient` stay open parts of the
  registry. Each control of part 5 names the one that it is a finite control of.
- If your design note finds a run-level statement that is ready, propose it in the note, with
  the five placement items of `AGENTS.md`. The coordinator answers before it lands as a goal.
- A theorem that is proved today stays proved, with its statement.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. Every
  warning is an error. Do not write `simp_all`, `first` or `try`. A hand-written `simp` names
  its lemmas.
- A battery `def` over rendered text reaches `Classical.choice`: keep rendered bytes inside
  `#guard`s.

## Order

Cut the work into steps that are each green and committed. Tell the coordinator each step's
commit in one message.

1. The design note.
2. The shared pieces and the operations, with scope and typing. The batteries move to them.
   **Hand this step back for an early merge:** a second seat starts from it.
3. The attempt laws.
4. The acceptance traces and the hygiene controls.
5. The faces, the truth programs and the engine's lane.
6. The documents and the receipt.

## Acceptance

1. **No name of a caller is captured.** The hygiene controls hold, and each has its red
   control.
2. **The trees are kept.** The byte comparison of part 2 holds, or each difference is listed.
3. **Every answer is kept.** The scenarios' guards pass with their pinned answers.
4. **Run these, and give each result in the receipt:**
   - the default `lake build`, with the gate lines of `Test/All.lean`;
   - `make gen-fixtures`, then `dune build` and `dune test --force engine`;
   - `make gen-truth` and `make check-truth`, with the host's versions;
   - `make check-cases`: give the refusal's lines, and do not pin the policy again;
   - `make check-docs`.
5. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`,
   `make check-target`, `make check-truth-release`, the conservativity script,
   `make gen-semantics`. The coordinator runs them at the merge. List each as "not run".

## What is not in this slice

- A run-level law, the abstract protocol of the wrapper, and the mask's invariant of runs.
  Under a masked caller the form's exit flag is tested, and a finite probe of a candidate
  invariant is filed (`docs/research/2026-10-05-claude-lead/mask-probes/MaskStack.lean`).
- Batches, the other strategies, the terminal operations, `peek`, `clear` and a capacity of
  zero.
- A handle type, and hiding the cell.
- Semaphore's operations that wait, and its protected form.
- A bound on the budget of a delivery.
- A native queue on the target.

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- The printed `ifElse` under a union error column does not type-check on the target (row 266,
  point 3). If an operation meets it, report the program and keep it out of the lane.
- A fresh worktree needs `Tools.GeneratedStamp` built once for a lane's check.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-06-seat-PUB-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. the changed files;
4. each command with its result, the host's versions, and the evidence word for each claim;
5. the axiom output and the plan status of each placed theorem;
6. each landed theorem's placement: concept, claim, reach, what it does not establish, and
   its consumer;
7. each choice you made, each finding, and each proposal for the semantics registry.

The receipt also accounts for the requirements R1 to R13, in three lists. Take them from
`generated/semantics.md` and from `#plan_status`:

- what the slice advances;
- what its theorems still rest on;
- the older open parts that it leaves untouched.

A step theorem of one module closes no requirement.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
