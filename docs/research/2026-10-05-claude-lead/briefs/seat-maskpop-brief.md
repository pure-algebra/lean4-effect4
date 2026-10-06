# 2026-10-06 brief for seat MASKPOP: the saved mask's chain is kept through a pop of the stack

Status: a brief (history, not authority). Base: the head of `refactor/phase1-phase3` that the
dispatch message names. The coordinator dispatches it under decisions row 237. It is the
first slice of R11's open half, the mask's invariant of runs. Codex prepared its statements
and reviewed them against the source. None of them is compiled.

## Why this slice exists

The mask's law is proved at the boundaries of a region (`saved_mask_restoration`,
`src/Effect4/Laws/Program/Typed/Mask.lean`). One statement is still open: a region that
changes no flag ends with its entry flag, for an arbitrary body. It is an invariant of runs,
and the semantics registry lists it among R11's open parts.

A candidate invariant has a finite probe
(`docs/research/2026-10-05-claude-lead/mask-probes/MaskStack.lean`). On a fiber's stack the
restoring frames alternate from the negation of the flag. The flag under them is one fixed
bit, the fiber's base. A region that changes the flag pushes the frame that returns it. So
the flag is a function of the base and of the stack.

`Program.MaskInv` (`src/Effect4/Laws/Program/Means.lean`) does not state that. Its empty
stack accepts either flag, and its restoring case forgets the incoming flag. Keep that
predicate and its consumers as they are.

**The goal.** The frame machine's own pop keeps the chain. So do `FrameFiber.getCont`,
`Machine.frameExitState` and the entry of each region. The pop is `FrameFiber.popFrom`, from
an empty scratch stack, and it is the hard step. It can mask a finalizer, push a new restoring
frame and visit that frame before the older tail.

The slice ends there. It states no law of a run.

## Who and where

You are one seat of the Effect4 estate. The coordinator wrote this brief and merges your
branch. You work alone and hand back a receipt.

- **Worktree, branch and scratch folder:** the dispatch message names them.
- **The coordinator's checkout** is `/Users/pooks/Dev/lean4-effect4`. Read it freely. Write
  nothing there.
- **Lean:** run every Lean and Lake command through
  `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Never run a bare `lake build`. Never
  send a Lean command's standard error to `/dev/null`. Run one `lake` at a time.
- **Make:** write the flags `-o build -o ts/eff/node_modules` out on every `make` call. The
  shell is zsh, and it does not split a variable into words. Run `make` through the slot
  script too.
- **No install and no download.** No TypeScript run and no OCaml run is in this slice.
- **Git:** never push. Commit on your branch, by explicit paths. Use `git add -f` for a file
  under `docs/research`, in a `git add` of its own. Read `git status` before each commit.
- **Disk:** stop and report below 4 GiB free.
- **A hand-back comes early.** Check your own change with narrow builds. The coordinator runs
  the wide gates at the merge.

## Read first, in this order

1. `AGENTS.md`, in full. The section on proof search applies: `aesop` first, the named banks,
   and no `simp_all`, `first` or `try`.
2. Codex's packet, under
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/deeper-proof-support/`:
   - `semantic/candidate.md`: the statements, the reuse route and the controls;
   - `semantic/adversarial.md`: the cases of the induction, and the witness against a weaker
     premise;
   - `semantic/report.md`: why `MaskInv` does not serve, and the trap of the later lift;
   - `coordinator-filing-note.md`: the allocation.
3. `src/Effect4/Machine/Frames.lean`:
   - the definitions `Prim.ensure`, `FrameFiber.popFrom`, `FrameFiber.getCont`,
     `FrameFiber.uninterruptible` and `FrameFiber.interruptibleRegion`;
   - the equations `ensure_stack_cases`, `Prim.ensure_setInterruptible_flag`,
     `Prim.ensure_setInterruptible_stack`, `passPushed_nil` and `passPushed_fiber`;
   - the pop's existing laws `popFrom_interruptedCause`, `popFrom_fiber_cause`,
     `popFrom_continue_fiber`, `popFrom_answer_fiber`, `continueFrom_cases` and
     `popFrom_asyncFinalizer_pops_its_push`;
   - the entries' laws `uninterruptible_masks`, `uninterruptible_already_masked`,
     `interruptibleRegion_masked` and `interruptibleRegion_already`.
4. `src/Effect4/Machine/Fibers.lean`: `Machine.frameExitState`.
5. `src/Effect4/Laws/Machine/LiveStack.lean`, for the form of a law module over the frames.
6. `src/Effect4/Laws/Program/Typed/Mask.lean`: `MaskRestoration` and
   `saved_mask_restoration`, for the form of one placed theorem that holds several
   statements.
7. `docs/core/semantics.md`, the concept `scope-lifetime-finalization`, and R11 in
   `generated/semantics.md`.

## The assignment

### 0. The design note, first

Write `docs/research/2026-10-06-seat-MASKPOP-design.md`, one page, before the first Lean
commit.

- The predicate and each statement, as Lean elaborates them: the namespace, the implicit
  parameters and the instance parameters.
- The induction: its variable, its cases and the lemma that closes each case.
- Each existing lemma that a step uses, by name.
- Each difference from Codex's statements, with its reason.

Send the note's path to the coordinator in one message, and go on without waiting.

### 1. The predicate and the planned goal, placed

A new module, `src/Effect4/Laws/Machine/MaskDiscipline.lean`.

**One predicate.** Start from Codex's sketch, which is not compiled:

```lean
def MaskChain (base : Bool) : Bool → List (Prim ν σ β ε δ ι α) → Prop
  | flag, [] => flag = base
  | flag, Prim.setInterruptible saved :: rest => flag = !saved ∧ MaskChain base saved rest
  | flag, _ :: rest => MaskChain base flag rest
```

It is proof data over the existing stack. It adds no field, no instruction and no state of
the machine. Keep one definition. The probe's Boolean projection is a probe, and it is no
second authority.

**One placed theorem holds the statements**, in the form of `MaskRestoration`. A `Prop`
structure has one field for each statement below. One theorem proves the structure, and it
carries the placement:

```lean
@[semantics "scope-lifetime-finalization" (requirement := R11)]
```

State that theorem first as a planned goal, and prove it in place. If a structure is clumsy
at the polymorphic parameters, place `frameExitState_maskChain` instead, and say so in the
design note.

**The statements.**

| Name | Statement, in words | Premises |
| --- | --- | --- |
| `popFrom_maskChain` | the pop's result has the chain at the same base, over its flag and its stack | the fiber's scratch stack is empty; the chain holds over the fiber's flag and the frames |
| `getCont_maskChain` | `getCont` keeps the chain at the same base | the chain holds over the fiber's flag and its stack |
| `frameExitState_maskChain` | `Machine.frameExitState` keeps the chain at the same base | the same |
| the two entries | `uninterruptible` and `interruptibleRegion` keep the chain at the same base | the same |
| the same flag | two fibers with one base and one stack have one flag | the chain holds for each |

Every demand, every skip flag and every carried cause is in the domain. No statement asks
for a premise on a pending cause, on a deferred interrupt or on a frame's kind.

**The scratch premise stays.** `getCont` calls `popFrom` with an empty scratch stack. Without
that premise the statement is false, and `semantic/adversarial.md` gives the witness.

### 2. The proof

- Follow the induction of `popFrom_interruptedCause`. Write no second walker of the frames.
- Split a hook into three cases: a neutral hook, a restoring frame, and a finalizer that
  masks and pushes. `semantic/adversarial.md` lists what each case keeps.
- `ensure_stack_cases` does not give the flag in its case of an unchanged stack. A restoring
  frame changes the flag there. Use its two own equations for that case.
- Use `popFrom_fiber_cause` for a carried cause. Do not prove the walk twice.
- Split `getCont` once, on its branch of a deferred interrupt. That branch keeps the stack
  and the flag.
- Unfold only the two branches of `Machine.frameExitState` for the adapter.
- Take each case list from the definition that the proof is about (`fun_induction`,
  `fun_cases`). Prefer a short searched proof to a long unpacked one.
- Import no module of `src/Effect4/Laws/Program/`. The law is lower than the typed program.

Stop a proof that does not close in its step. Leave its goal planned, and report it.

### 3. The controls

A battery, `Test/Machine/MaskDiscipline.lean`, at one concrete instance of the parameters.
Each row of Codex's table of controls is one check:

- both empty stacks, each at its own base;
- one restoring frame, popped;
- a nested chain with both saved bits, and neutral frames between them;
- a cause that is pending when a restoring frame passes;
- `onExit` and `asyncFinalizer`, which mask and push during the pop.

The red controls, each red at its own property:

- a pop that drops a restoring frame without its hook;
- a finalizer that masks and pushes no restoring frame;
- the same-flag statement without the fixed base: two empty stacks with opposite flags;
- a relation that keeps the base and omits the alternation;
- the pop's statement without the scratch premise, at the witness of
  `semantic/adversarial.md`.

Pin the axioms and the plan status of the placed theorem. In a battery, a docstring before a
`#guard` is an error.

### 4. The documents

- `docs/ARCHITECTURE.md` and `tools/Tools/ArchitectureRoles.lean`: a row and a role for the
  new module.
- Propose in the receipt the claim `saved-mask-pop-discipline` for the semantics registry,
  with its role and its title. It is an open part of R11 there today.
- Propose the required property's text for `docs/core/semantics.md`.

## The files

You may add `src/Effect4/Laws/Machine/MaskDiscipline.lean` and
`Test/Machine/MaskDiscipline.lean`, and you may edit the two documents of part 4.

Edit a root only at its anchor:

- `src/Effect4/Laws.lean`: after `import Effect4.Laws.Machine.LiveStack`;
- `Test/All.lean`: after `import Test.Machine.StoreKernelBank`.

Do not edit a file under `src/Effect4/Machine/`. If a general equation of the frames is
missing, state it in your module, and propose its move in the receipt. Do not edit a file of
seat PUB or of seat POOL. Do not edit `docs/core/decisions.md`, `docs/STATE.md`,
`lakefile.toml`, `generated/semantics.md`, `docs/core/semantics.md` or
`tools/Tools/SemanticsRegistry.lean`.

## The obligations and their placement

| Statement | Concept; requirement | Reach | What it does not establish | Consumer |
| --- | --- | --- | --- | --- |
| The placed theorem, with the five statements | `scope-lifetime-finalization`; R11. The proposed helper claim `saved-mask-pop-discipline`, a step of the open run-level half of `saved-mask-restoration` | the polymorphic `FrameFiber`; every stack, demand, skip flag and carried cause; one fixed base; for the pop, an empty scratch stack | no law of a run; no completed exit; no cleanup's multiplicity; no delivery, no budget, no liveness; nothing of a host or of a printed form | the later lift through `Machine.Lift`; then the waiting wrapper under a masked caller, and Semaphore's protected permit |

- A helper names the statement that it is a step of.
- A planned goal is allowed only for the placed theorem. The receipt lists it first if it
  stays open.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. Every
  warning is an error. A hand-written `simp` names its lemmas.
- Every declaration stays at `[propext, Quot.sound]`.

## Acceptance

1. **The placed theorem is proved** at `[propext, Quot.sound]`, or its goal is planned with
   the reason first in the receipt.
2. **The controls** of part 3 pass, with each red control red at its own property.
3. **Run these, and give each result in the receipt:**
   - a narrow build of the two new modules after each step;
   - the default `lake build` once, at the end, with the gate lines of `Test/All.lean`;
   - `make check-docs`.
4. **Do not run:** `make check-gen`, `make check-slow`, `make check-corpus`,
   `make check-target`, `make check-truth`, the conservativity script and
   `make gen-semantics`. The coordinator runs them at the merge. List each as "not run".

Commit each finished step, so that the branch's head is always green.

## What is not in this slice

- **The lift to runs.** A later slice carries the chain through the commands by
  `Machine.Lift` (`src/Effect4/Laws/Machine/Lift.lean`). It needs a condition on the pending
  commands. `Cmd.exitDone` clears a stack and keeps its flag, so the chain does not survive
  an arbitrary command (`semantic/report.md`). Record what your statements give that lift,
  and state no part of it.
- The bracket of a whole region, and each fiber's base in a reachable run.
- A change of `src/Effect4/Machine/`, of the mask's boundary law or of `Program.MaskInv`.
- Any wrapper, any module's operation and any host run.

## Known, and not yours to repair

- `make check-tsdiag` and `make check-schema-ts` are red for reasons outside this work.
- `lake build Effect4Gen`, the library target, fails. It is not a gate.
- A file that imports `aesop` gets the linters of the `batteries` package. One of them
  refused an old proof line in another slice. If it refuses a line of yours, repair your line.
- `simp` at `(x == x) = true` for a `Bool` or a `Nat` can reach `Classical.choice`. Use
  `decide_eq_true` and `of_decide_eq_true`, or cases on the Boolean.

Report anything else that is red for a reason outside your slice. Do not repair it.

## The receipt

Write `docs/research/2026-10-06-seat-MASKPOP-receipt.md`, in the handoff form of `AGENTS.md`:

1. first, the one thing the coordinator must know before merging;
2. the base and head commits, and each step's commit;
3. the changed files;
4. each command with its result, and the evidence word for each claim;
5. the statements as compiled, the axiom output and the placed theorem's `#plan_status` line;
6. the placement of the placed theorem and of each helper;
7. each choice you made, each difference from Codex's statements, and each finding;
8. what the lift to runs needs from this slice, and what it still owes;
9. the proposed registry claim, its role and title, and the required property's text.

The receipt also accounts for the requirements R1 to R13, in three lists. Take them from
`generated/semantics.md` and from `#plan_status`:

- what the slice advances;
- what its theorem still rests on;
- the older open parts that it leaves untouched.

A local law of the pop closes no requirement, and R11's run-level half stays open.

Your last message gives the head commit, the receipt's path and the first item of the receipt.
