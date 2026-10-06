# 2026-10-06 brief for seat POOL: Pool's contract, model, cell and steps

Status: a brief (history, not authority). Base: the head of `refactor/phase1-phase3` that the
dispatch message names. The coordinator dispatches it under decisions row 237. Rows 267 to
269 rule the profile that you build: the owner's word of 2026-10-06.

## Why this slice comes now

Pool is the third composed module. The Queue and Semaphore are the two worked examples of one
procedure (`docs/research/2026-10-05-claude-lead/module-factory-plan.md`). This slice is the
procedure's steps 2 to 8 for Pool's cell and steps.

It needs neither the public operations of the Queue nor Semaphore's protected form. Three
parts come later, in another slice: the public `make` and `use`, the wake's helper as a
library program, and the close that waits.

**The goal.** Pool's contract packet, its model, its cell and its step terms are in the tree.
Each step term is typed at every scope and agrees with the model's step.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt.

- **Worktree, branch and scratch folder:** the dispatch message names them.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **Make:** write the flags out on each call, `-o build -o ts/eff/node_modules`, and run it
  through the slot script too. Never keep the flags in a shell variable: zsh does not split it.
- **OCaml:** only through `opam exec --switch=effect4 -- dune …`.
- **No install and no download.** No TypeScript run and no host run is in this slice.
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`. Read `git status` before each commit.
- **Disk:** stop and report below 4 GiB free.
- **A hand-back comes early.** Check your own change with narrow builds. The coordinator runs
  the wide gates at the merge.

## Read first, in this order

1. `AGENTS.md`, in full.
2. The card, in full: `docs/research/2026-10-05-claude-lead/module-cards/pool.md`. It is your
   specification. Rows 267 to 269 rule its section 10.
3. `docs/core/decisions.md`: rows 267 to 269; then rows 219 to 222, 226, 230, 233, 234, 238,
   244 to 246, 255, 257 and 259 to 261.
4. The module procedure: `docs/research/2026-10-05-claude-lead/module-factory-plan.md`.
5. The two worked examples:
   - Semaphore, the nearer one. Its packet is `Test/contracts/semaphore.contract.md`. Its
     cell and steps are `src/Effect4/Modules/Semaphore/`, and its laws
     `src/Effect4/Laws/Modules/Semaphore/`. Its batteries are `Test/Program/Semaphore*.lean`.
     Read its seat's brief, design note and receipt
     (`docs/research/2026-10-06-seat-SEM-receipt.md`);
   - the Queue: `Test/contracts/queue.contract.md`, `src/Effect4/Modules/Queue/` and
     `src/Effect4/Laws/Modules/Queue/`.
6. The shared homes, which name no module: `src/Effect4/Modules/Words.lean`, and `Table.lean`,
   `Reading.lean`, `Checking.lean` and `Store.lean` under `src/Effect4/Laws/Modules/`. Seat
   MOVE's receipt lists what each holds (`docs/research/2026-10-06-seat-MOVE-receipt.md`).
7. The typing rules of a term: `src/Effect4/Laws/Program/Typing/TermIntro.lean`.
8. The host probes: `docs/research/2026-10-05-claude-lead/module-cards/pool-probes/`. Their
   outputs hold both builds' answers on the cases PP1 to PP8, and the close on three builds.
9. The machine's wake: `DeferredStore.complete` (`src/Effect4/Machine/Stores.lean`);
   `WakeMode` (`src/Effect4/Machine/Wake.lean`); `drainOwed` and the resume clause of
   `driveStep` (`src/Effect4/Machine/Fibers.lean`).
10. The builders that mint the name they bind: `Authoring.foldWith`, `bindWith`,
    `Ref.modifyWith`, `selectOptionWith` and `onExitWith`. The shared wrapper of a module that
    waits: `src/Effect4/Modules/Waiting.lean`.
11. Codex's proposed card and its review of the two modules:
    `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/roadmap-audit/modules/`.

## The ruled profile, in short

- **The surface** (row 267). A fixed size of at least 1, and one borrower for an item.
  `make size acquire` acquires every item before it answers. `use pool body` borrows one
  item, runs the body with it and returns it at every exit. Time to live, a custom strategy,
  `invalidate`, the scoped `get` and a later acquisition are excluded by name.
- **The close** (row 268). It refuses new leases, wakes every waiter, waits for every
  lease's return, and then finalizes each item once.
- **The order of reuse** (row 269). A returned item joins the front of the idle items.
- **The wake** (the card's sections 1 and 4). A helper is posted with a count: 1 at a return,
  and every waiter at the close. When the helper runs, one step selects the first waiters of
  the state that it finds, at most the count, and removes them. The helper then resolves
  each selected hint in order. A resumed borrower checks again and takes the item in its own
  step. A wake reserves nothing.

## The assignment

### 0. The design note, first

Write `docs/research/2026-10-06-seat-POOL-design.md`, one page, before the first Lean commit.

- The cell's type, an item's type and a waiter's type, with each field. Start from the
  card's section 3. Say what a lease is in the cell, and what stays outside it.
- The steps, each with its arguments and its reply. There are five: lease or enrol, return,
  one selection of the wake at a count, withdraw, and the close's first step.
- The model: its state, its transitions and its profile predicate.
- The relation: the table from a model identity to its handle and its current hint. Say
  whether the shared `Table` serves as it is.
- Each statement's shape: the typing of a step, and its agreement with the model's step.
- Each shared piece that you reuse as it is. For each rule that you need and that names no
  module, name the shared file that it goes into.

Send the note's path to the coordinator in one message, and go on with part 1 without waiting.

### 1. The cases on our machine: the first check

No Pool program ran on our machine. The card's answers are the two builds' answers and
readings of our machine's rules. Run the cases now, before the model is written.

- Write the battery `Test/Program/PoolScenarios.lean`. Its operations are test fixtures:
  a lease with a wait and a withdrawal, a return with one posted helper, and a body under
  `onExit`. Use the shared wrapper and the mask's builder where they fit.
- A fixture may hold a first form of the steps. Part 4 replaces it with the library's terms.
- Run the cases PP1 to PP5 and PP8. Each must give the profile's answer of the card's
  section 9: who holds which item, who still waits, and the cell's lists.
- State the run's settings: the fuel, the flushes and each decision of the tape.
- Add a red control for each fault of section 9 that a fixture can show. A wake that hands
  an item to each selected waiter must fail PP5. A selection made when the wake is posted
  must fail PP4. A return that puts the item at the end must fail PP2.

**If a case does not give the profile's answer, stop and report with the trace.** Do not
change the profile, and do not change the machine.

### 2. The contract packet

`Test/contracts/pool.contract.md`, in the form of Semaphore's packet. It states the profile,
the model's transitions and the invariant. It gives the cases as traces of the model, PP7
with the close that waits among them, and the faults of the card's section 9. Its falsifiers
are executable: a battery `Test/Program/PoolContract.lean`.

### 3. The model and its profile

In the law graph, `src/Effect4/Laws/Modules/Pool/`, in the namespace `Effect4.Pool.Model`.

- `Model.lean`: the state and the transitions, each total.
- `Profile.lean`: the profile's states and their closure under every transition. The
  predicate holds what the step proofs need:
  - the stamps are distinct;
  - an idle item is an item that no lease holds;
  - the idle items and the leased items together are the items;
  - no waiter is enrolled while an item is idle and the pool is open. If that fails, say why.
- State the model's facts that the public law will use, each as a theorem with its
  placement:
  - the selection takes the first waiters of the state that it finds, at most its count, and
    exactly those;
  - a return puts its item at the front and finalizes nothing;
  - after the close's first step no lease begins.

### 4. The cell and the steps

`src/Effect4/Modules/Pool/Cell.lean` and `Steps.lean`, in the form of Semaphore's two files.
Each opens with `module`, `public import` and `@[expose] public section`.

- Each step is one term for one `Ref.modify`. A step takes the source of the cell's current
  value. The module exports no row.
- Each fold is built with `Authoring.foldWith`. Keep one control with a caller's variable
  under each helper.
- A step frames every field that it does not change.
- Measure each step's size in nodes and folds.
- A word or a rule that names no module goes into its shared file at once. Put it in a
  section of its own at the file's end. Tell the coordinator each such edit in the step's
  message.

### 5. The typing

Each step term has its stated type at the cell's type, at every scope of names. Use `Types`
and the builder rules, and the capture of a minted name. State each as a theorem with its
placement.

### 6. The relation and the step goals

- `Relation.lean`: the table, and the cell's value of a model state.
- One goal for each step: the step term reads the model's reply, its next state through the
  table, and the identities that it selects. State each as a planned goal first, with its
  placement, and then prove it in place.
- Join a goal to the store by the shared connectors `step_updates`, `step_keeps_cell` and
  `cell_read` (`src/Effect4/Laws/Modules/Store.lean`).

### 7. The batteries

- Each step term against the model's step on every state of a finite universe.
- The cases of part 1 again, now on the library's step terms.
- Each fault of the card's section 9 that a step can show, red at its own property. Typing
  alone must not catch it.

### 8. The engine, last

Two cases of part 1 replay on the generated engine: one folder under `ocaml/engine/test/`
with a `write.lean` (`docs/GENERATED.md`, the row `fixtures`).

### 9. The documents

A row for the module and one for its laws in `docs/ARCHITECTURE.md`, and their roles in
`tools/Tools/ArchitectureRoles.lean`.

Where the card leaves a choice open, make it and state it in the receipt. Where the tree
proves the card wrong, stop that part and report with the evidence. Do not redesign.

**Reuse first.** Before you add a helper, name its consumer in this slice. Add no second
interpreter, no new stored binding form and no proof framework of your own.

## The files

You may add files under `src/Effect4/Modules/Pool/`, `src/Effect4/Laws/Modules/Pool/`,
`ocaml/engine/test/pool/` and `Test/Program/` (names that begin with `Pool`), and the packet
`Test/contracts/pool.contract.md`. You may add a rule that names no module to a shared file,
as part 4 says.

Edit a root only at its anchor:

- `src/Effect4.lean`: after `import Effect4.Modules.Semaphore.Steps`;
- `src/Effect4/Laws.lean`: after the last import of `Effect4.Laws.Modules.Semaphore`;
- `Test/All.lean`: after `import Test.Program.SemaphoreEngine`.

Do not edit `docs/core/decisions.md`, `lakefile.toml`, `docs/STATE.md`,
`generated/semantics.md` or `tools/Tools/SemanticsRegistry.lean`. Do not edit a file of the
Queue's or of Semaphore's folders. Do not edit `src/Effect4/Modules/Waiting.lean`. Seat PUB
holds the Queue's files and the shared wrapper. If one of them must change, send the
coordinator the change in one message, and wait for that one thing.

## The obligations and their placement

State each goal as a planned goal first, with its placement, and then prove toward it.

| Obligation | Concept, requirement | Reach | It does not establish |
| --- | --- | --- | --- |
| Each step's typing | `store-typing`, R4 | The cell's type; each step term; every scope of names | No agreement with the model |
| The profile's closure | `store-typing`, R4 | Every transition of the model, on the profile's states | Nothing about a program, and no progress of a waiter |
| Each step's agreement with the model | `translation-simulation`, R10; a part of the proposed `pool-expansion-agrees` | The profile's states and an injective table; the reply, the stored value and the selected identities | No wake's order across helpers, no cancellation law, no close that waits, no wrapper |
| The model's fact of the selection | `reactive-scheduling`, R12; its consumer is the proposed `pool-wake-selection` | One selection of the model | No statement about a run, and no liveness |
| The model's facts of a return and of the close's first step | `scope-lifetime-finalization`, R11; their consumers are the proposed `pool-lease-return` and `pool-close-waits` | One transition of the model | Nothing about a finalizer's run, and no completed close |

- The consumer of each goal is the public law, in the slice of the public operations.
- A theorem that is proved today stays proved.
- A planned goal is allowed only for a statement that this table names. Give it its
  `@[semantics …]` placement, name its consumer, and list it first in the receipt.
- Propose each claim for the semantics registry in the receipt. The coordinator adds it at
  the merge.
- Proof search is `aesop` with the named rule sets. Do not write `simp_all`, `first` or `try`.
  A hand `simp` is `simp only [...]`. Every warning is an error.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`.

## Order

Cut the work into steps that are each green and committed.

1. The design note.
2. The cases on the machine: part 1, with its red controls.
3. The packet, the model and the profile, with the closure proved or planned.
4. The cell and the step terms, and their typing.
5. The batteries of part 7. They are your net for the proofs that follow.
6. The relation, and the goals as planned goals.
7. The proofs, shortest first. Stop a proof that does not close in its step, and leave its
   goal planned.
8. The engine's two cases, the documents and the receipt.

## Messages to the coordinator

Send one short message at each of these points, and go on unless the message says you wait:

- the design note's path;
- the result of part 1, with each case's answer;
- one line for each committed step of the order, with each edit of a shared file;
- a file of another seat that must change (you wait for that one thing);
- anything red for a reason outside your slice.

## Acceptance

1. **Part 1** gives the profile's answers on PP1 to PP5 and PP8, with each red control red.
2. **The batteries** of part 7 pass, with each fault red at its own property.
3. **The engine** replays two cases on both carriers.
4. **Run these, and give each result in the receipt:**
   - the default `lake build`, with the gate lines of `Test/All.lean`;
   - `make gen-fixtures`, then `git status`;
   - `make corpus`, then `dune build` and `dune test --force engine`. Say which corpus folder
     the run read;
   - `make check-cases`: give the refusal's lines in the receipt, and do not pin the policy
     again;
   - `make check-docs`.
5. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`,
   `make check-target`, `make check-truth`, the conservativity script and
   `make gen-semantics`. The coordinator runs them at the merge. List each as "not run".

## What is not in this slice

- The public `make` and `use`, and the acquisition inside the pool's scope.
- The wake's helper as a library program, and its law across helpers.
- The close that waits, and the finalizers' runs.
- The module printed as TypeScript, and any host run of it.
- Time to live, a custom strategy, `invalidate`, the scoped `get` and a later acquisition
  (row 267).
- A hidden handle. The handle is the cell's `Ref` in this slice (row 230).

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- A stale or missing `.lake/corpus` makes one engine check fail. `make corpus` prints the
  corpus again, and `E4_LEAN_CORPUS` names another folder for one command.
- `simp` at `(x == x) = true` for a `Nat` reaches `Classical.choice`. Use `decide_eq_true` and
  `of_decide_eq_true`.
- In a battery, a docstring before a `#guard` is an error, and `scoped` is a keyword.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-06-seat-POOL-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. the changed files, by group;
4. each command with its result, and the evidence word for each claim;
5. the axiom output for the changed theorems, and each goal's `#plan_status` line;
6. each landed theorem's placement, and each planned goal with its consumer;
7. each choice you made, and each step's size in nodes and folds;
8. each shared piece that you used, and each rule that you added to a shared file;
9. the open obligations, and what the public slice needs from this one;
10. proposed decisions rows and claims for the semantics registry. Do not edit either file.

The receipt also accounts for the requirements R1 to R13, in three lists. Take them from
`generated/semantics.md` and from `#plan_status`:

- the existing claims and requirement rows that the slice advances, with each node's status;
- the goals and the premises that its theorems still rest on;
- the older open parts of the same requirements that it leaves untouched.

Keep no second list of statuses. Your last message gives the head commit, the receipt's path
and the first item of the receipt.
