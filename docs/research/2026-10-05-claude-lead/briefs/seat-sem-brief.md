# 2026-10-06 brief for seat SEM: Semaphore's contract, model, cell and steps

Status: a brief (history, not authority). Base: the head of `refactor/phase1-phase3` that the
dispatch message names. The coordinator dispatches it under decisions row 265, the owner's
word of 2026-10-06. Rows 259 to 261 rule the profile that you build.

## Why this slice comes now

Semaphore is the second composed module. The Queue is the first, and it is the worked example
of one procedure (`docs/research/2026-10-05-claude-lead/module-factory-plan.md`). This slice is
the procedure's steps 2 to 8 for Semaphore's cell and steps.

It needs neither the mask nor the Queue's public path. Three parts come later, in another
slice: the operations that wait, the wake's helper as a library program, and the protected
form `withPermits`.

**The goal.** Semaphore's contract packet, its model, its cell and its step terms are in the
tree. Each step term is typed and agrees with the model's step.

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
- **TypeScript:** only tsgo 7, the pinned `@typescript/native-preview`. Never `tsc`.
- **No install and no download.**
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Disk:** stop and report below 4 GiB free.

## Read first, in this order

1. `AGENTS.md`, in full.
2. The card, in full: `docs/research/2026-10-05-claude-lead/module-cards/semaphore.md`. It is
   your specification. Rows 259 to 261 rule its section 10.
3. `docs/core/decisions.md`: rows 259 to 261 and 265; then rows 219 to 222, 226, 230, 233, 238,
   255 and 257.
4. The module procedure: `docs/research/2026-10-05-claude-lead/module-factory-plan.md`.
5. The Queue, as the worked example:
   - its packet, `Test/contracts/queue.contract.md`, and `Test/contracts/README.md`;
   - its cell and steps, `src/Effect4/Modules/Queue/`;
   - its laws, the eight files of `src/Effect4/Laws/Modules/Queue/`;
   - its batteries, `Test/Program/Queue*.lean`;
   - the receipts of its two seats, `docs/research/2026-10-05-seat-QSTEPS-receipt.md` and
     `docs/research/2026-10-05-seat-QTYPES-receipt.md`: what each proof cost, and which
     helpers name no type of the Queue.
6. The typing rules that you reuse: `src/Effect4/Laws/Program/Typing/TermIntro.lean`, and the
   judgment `Types` with its builder rules in `src/Effect4/Laws/Modules/Queue/Checking.lean`.
7. The host probe: `docs/research/2026-10-05-claude-lead/module-cards/semaphore-probes/`. Its
   three outputs hold the pin's answers on the cases P1 to P9.
8. The machine's wake: `DeferredStore.complete` (`src/Effect4/Machine/Stores.lean`);
   `WakeMode` (`src/Effect4/Machine/Wake.lean`); `drainOwed`, the resume clause of `driveStep`,
   `yieldVerdict` and `injectYield` (`src/Effect4/Machine/Fibers.lean`).
9. `src/Effect4/Program/Authoring/Folds.lean` and `Test/Program/FoldHygiene.lean`: the fold
   builder that mints its names, and the capture that it prevents.
10. Codex's reviews, under
    `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/`:
    `heartbeat-0553-semaphore-qtypes/cards/review.md`, the Semaphore part of
    `heartbeat-0451-fixtures-semaphore/`, and `module-factory-review/breadth/report.md`.

## The ruled profile, in short

- **The surface** (row 260). A fixed total of at least 1. A request is a natural number at
  most the total. The operations are `make`, `take`, `release`, `withPermits`,
  `takeIfAvailable` and `withPermitsIfAvailable`.
- **A release** (row 261). The step releases at most what is taken, by the atom `sub`. The
  premise that a release asks for at most `taken` belongs to the public law, not to a step.
- **The wake** (row 259). The live scan. A release posts one helper. The helper visits one
  waiter at a time, in the order of enrolment. A visit resolves the hint of the next waiter
  whose count fits. That waiter resumes inside the helper's task and runs its own take step.
  A wake reserves nothing.

## The assignment

### 0. The design note, first

Write `docs/research/2026-10-06-seat-SEM-design.md`, one page, before the first Lean commit.

- The cell's type and a waiter's type, with each field. Start from the card's section 3: four
  fields each. The walk's cursor is the least stamp that it has not visited, and a first visit
  starts at zero. You may choose another cursor, if it gives the same visits.
- The five steps, each with its arguments and its reply: take or enrol, take if available,
  release, one visit of the walk, withdraw. A release's reply names the free count and whether
  a waiter is enrolled.
- The model: its state, its five transitions and its profile predicate.
- The relation: the table from a model identity to its handle and its current hint. Say
  whether `Table` and `Table.renew` of the Queue serve as they are.
- Each statement's shape: the typing of a step, and its agreement with the model's step.
- Each helper of the Queue's folder that you reuse as it is. For each one that names a type of
  the Queue, write the general statement that you need. Do not copy a helper.

Send the note's path to the coordinator in one message, and go on with part 1 without waiting.

### 1. The wake on our machine: the first check

The ruling of row 259 rests on a reading of the machine: a waiter runs inside the task that
resolves its hint. No Semaphore program ran on the machine. Run one now, before the model is
written.

- Write the battery `Test/Program/SemaphoreScenarios.lean`. Its operations are test fixtures,
  as in `Test/Program/QueueScenarios.lean`. There are three:
  - `take`, with a wait and a withdrawal;
  - `release`, with one posted helper whose body is the walk;
  - a protected body, by `onExit`.

  `uninterruptible` stands for the mask and `interruptible` for its restore.
- A fixture may hold a first form of the steps. Part 4 replaces it with the library's terms.
- Run the card's cases P1, P2, P3 and P4 on the machine. Each must give the pin's answer: who
  holds the permits, who still waits, and the cell's counts.
- Run P9 if the run's API can tell one fiber to yield at its resume. If it cannot, say so, and
  name the smallest extension.
- State the run's settings: the budget of operations before a yield, the fuel and the flushes.
- Add three red controls, each a changed walk. A walk that commits for every fitting waiter
  before any of them runs must fail P3. A walk that wakes the head alone must fail P2. A retry
  with no second check must fail the accounting on P9, if P9 runs.

**If P1 or P3 does not give the pin's answer, stop and report with the trace.** Do not change
the profile, and do not change the machine. That result would open row 259 again.

### 2. The contract packet

`Test/contracts/semaphore.contract.md`, in the form of the Queue's packet. It states the
profile, the model's transitions and the invariant. It gives the cases P1 to P4 and P9 as
traces of the model, and the faults of the card's section 9. Its falsifiers are executable: a
battery `Test/Program/SemaphoreContract.lean`.

### 3. The model and its profile

In the law graph, `src/Effect4/Laws/Modules/Semaphore/`, in the namespace
`Effect4.Semaphore.Model`.

- `Model.lean`: the state and the five transitions, each total.
- `Profile.lean`: the profile's states and their closure under every transition. The predicate
  holds what the step proofs need, in three parts:
  - `taken` is at most `permits`;
  - the stamps rise along the list and stay below the next stamp;
  - the identities are distinct.
- State two facts of the model that the public law will use, each as a theorem with its
  placement. A visit resumes the earliest fitting waiter at or after its cursor. A visit stops
  only when no permit is free or no such waiter fits.

### 4. The cell and the steps

`src/Effect4/Modules/Semaphore/Cell.lean` and `Steps.lean`, in the form of the Queue's two
files. Each opens with `module`, `public import` and `@[expose] public section`.

- Each step is one term for one `Ref.modify`. A step takes the source of the cell's current
  value, as the Queue's steps do. The module exports no row.
- Each fold is built with `Authoring.foldWith`. Never give `Authoring.fold` a fixed name
  around a caller's term. Keep one control with a caller's variable under each helper.
- A step frames every field that it does not change.
- No fold states its accumulator's type.
- Measure each step's size in nodes and folds, as seat QSTEPS did.

### 5. The typing

Each step term has its stated type at the cell's type, at every scope of names. Use `Types`
and the builder rules, and the capture of a minted name (`captured_minted`,
`src/Effect4/Laws/Modules/Queue/Reading.lean`). State each as a theorem with its placement.

### 6. The relation and the step goals

- `Relation.lean`: the table, and the cell's value of a model state.
- One goal for each step: the step term reads the model's reply, its next state through the
  table, and the identity that a visit selects. State each as a planned goal first, with its
  placement, and then prove it in place.
- The release's goal has no premise on its count: the model's release is total too.
- Join a goal to the store by the Queue's connectors: `step_updates`, `step_keeps_cell` and
  `cell_read` (`src/Effect4/Laws/Modules/Queue/Steps.lean`). They name no type of the Queue.

### 7. The batteries

- Each step term against the model's step on every state of a finite universe.
- The cases of part 1 again, now on the library's step terms.
- Each fault of the card's section 9 that a step can show, red at its own property. Typing
  alone must not catch it.

### 8. The engine, last

Two cases of part 1 replay on the generated engine: one folder under `ocaml/engine/test/`
with a `write.lean` (`docs/GENERATED.md`, the row `fixtures`). Seat MASK changes the wire. If
its merge reaches main before this part, merge main first.

### 9. The documents

A row for the module and one for its laws in `docs/ARCHITECTURE.md`, and their roles in
`tools/Tools/ArchitectureRoles.lean`.

Where the card leaves a choice open, make it and state it in the receipt. Where the tree
proves the card wrong, stop that part and report with the evidence. Do not redesign.

**Reuse first** (the owner, 2026-10-05). Before you add a helper, name its consumer in this
slice. Add no second interpreter, no new stored binding form and no proof framework of your
own. Import a helper from the Queue's folder where it stands. The coordinator moves the shared
helpers lower after your merge, when two modules use them.

## The files

You may add files under `src/Effect4/Modules/Semaphore/`,
`src/Effect4/Laws/Modules/Semaphore/`, `ocaml/engine/test/semaphore/` and `Test/Program/`
(names that begin with `Semaphore`), and the packet `Test/contracts/semaphore.contract.md`.

Edit a root only at its anchor:

- `src/Effect4.lean`: after `import Effect4.Modules.Queue.Steps`;
- `src/Effect4/Laws.lean`: after `import Effect4.Laws.Modules.Queue.Checking`;
- `Test/All.lean`: after `import Test.Program.QueueTyping`.

Do not edit `docs/core/decisions.md`, `lakefile.toml`, `docs/STATE.md`,
`generated/semantics.md` or `tools/Tools/SemanticsRegistry.lean`. Do not edit a file of the
Queue's folders. If a helper there must change, send the coordinator the change in one
message, and wait for that one thing.

## The obligations and their placement

State each goal as a planned goal first, with its placement, and then prove toward it.

| Obligation | Concept, requirement | Reach | It does not establish |
| --- | --- | --- | --- |
| Each step's typing | `store-typing`, R4 | The cell's type; the five step terms; every scope of names | No agreement with the model |
| The profile's closure | `store-typing`, R4; the model's half of the proposed `semaphore-accounting-preserved` | Every transition of the model, on the profile's states | Nothing about a program, and no progress of a waiter |
| Each step's agreement with the model | `translation-simulation`, R10; a part of the proposed `semaphore-expansion-agrees` | The profile's states and an injective table; the reply, the stored value and the selected identity | No wake's order across visits, no cancellation law, no fairness, no wrapper |
| The model's two facts of a visit | `reactive-scheduling`, R12; their consumer is the waiting clauses of the proposed `semaphore-expansion-agrees` | One visit of the model | No statement about a whole walk, and no liveness |

- The consumer of each goal is the public law, in the slice of the operations that wait.
- A theorem that is proved today stays proved.
- A planned goal is allowed only for a statement that this table names. Give it its
  `@[semantics …]` placement, name its consumer, and list it first in the receipt.
- Propose each registry claim in the receipt. The coordinator adds it at the merge.
- Before a proved top node of a requirement would rest on a goal, stop and report.
- Proof search is `aesop` with the named rule sets. Do not write `simp_all`, `first` or `try`.
  A hand `simp` is `simp only [...]`. Every warning is an error.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`.

## Order

Cut the work into steps that are each green and committed.

1. The design note.
2. The wake on the machine: part 1, with its red controls.
3. The packet, the model and the profile, with the closure proved or planned.
4. The cell and the five step terms, and their typing.
5. The batteries of part 7. They are your net for the proofs that follow.
6. The relation, and the goals as planned goals.
7. The proofs, shortest first. Stop a proof that does not close in its step, and leave its
   goal planned.
8. The engine's two cases, the documents and the receipt.

## Messages to the coordinator

Send one short message at each of these points, and go on unless the message says you wait:

- the design note's path;
- the result of part 1, with each case's answer;
- one line for each committed step of the order;
- a helper of the Queue's folder that must change (you wait for that one thing);
- anything red for a reason outside your slice.

## Acceptance

1. **Part 1** gives the pin's answers on P1 to P4, with each red control red.
2. **The batteries** of part 7 pass, with each fault red at its own property.
3. **The engine** replays two cases on both carriers.
4. **Run these, and give each result in the receipt:**
   - the default `lake build`, with the gate lines of `Test/All.lean`;
   - `python3 scripts/generate.py` for each group you changed, then `git status`;
   - `make corpus`, then `dune build` and `dune test --force engine`, if you added the
     engine's folder;
   - `make check-cases`: give the refusal's lines in the receipt, and do not pin the policy
     again;
   - `make check-docs`.
5. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`,
   `make check-target`, `make check-truth`, the conservativity script and
   `make gen-truth-ledger`. The coordinator runs them at the merge. List each as "not run".

## What is not in this slice

- The operations that wait, and the public `make`. They come with the shared wrapper.
- The wake's helper as a library program, and its law across visits.
- The protected form and its three clauses (the card's section 8). It needs the mask.
- The module printed as TypeScript, and any host run of it.
- `resize`, `releaseAll`, and a count that is no natural number (row 260).
- A hidden handle. The handle is the cell's `Ref` in this slice (row 230).

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- A stale `.lake/corpus` makes one engine check fail after a wire change. `make corpus` prints
  the corpus again.
- Three commands reserve the token `under`. Do not name a hypothesis `under`.
- `simp` at `(x == x) = true` for a `Nat` reaches `Classical.choice`. Use `decide_eq_true` and
  `of_decide_eq_true`.
- In a battery, a docstring before a `#guard` is an error, and `scoped` is a keyword.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-06-seat-SEM-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. the changed files, by group;
4. each command with its result, and the evidence word for each claim;
5. the axiom output for the changed theorems, and each goal's `#plan_status` line;
6. each landed theorem's placement, and each planned goal with its consumer;
7. each choice you made, and each step's size in nodes and folds;
8. each helper of the Queue's folder that you used, for the coordinator's move;
9. the open obligations, and what the public slice needs from this one;
10. proposed decisions rows and registry claims. Do not edit either file.

The receipt also accounts for the requirements R1 to R13, in three lists taken from
`generated/semantics.md` and from `#plan_status`:

- the existing claims and requirement rows that the slice advances, with each node's status;
- the goals and the premises that its theorems still rest on;
- the older open parts of the same requirements that it leaves untouched.

Keep no second list of statuses. Your last message gives the head commit, the receipt's path
and the first item of the receipt.
