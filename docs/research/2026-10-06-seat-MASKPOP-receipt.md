# 2026-10-06 seat MASKPOP receipt: the saved mask's chain is kept through a pop of the stack

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-maskpop-brief.md`, with the dispatch message.
Design note: `docs/research/2026-10-06-seat-MASKPOP-design.md`. The coordinator sent no message
after the dispatch.

**The one thing to know before merging:** the semantics registry and its report are stale at
one line. R11's open part `saved-mask-pop-discipline` still reads "Codex's candidate, not
compiled", and `saved_mask_pop_discipline` is now a proved node placed at R11. Item 9 holds the
claim and the new text, and `make gen-semantics` rewrites the report.

Six more facts stand beside it.

- **The placed theorem is proved in place.** No planned goal of the slice is open. The goal
  gate counts 24 planned goals, as at the base. Step 1 held 25.
- **Codex's predicate and its three statements are true as written.** Lean elaborates each
  with the namespaces and the instances of item 5. No statement of the packet is false.
- **The scratch premise stays, and it is needed.** The adversarial note's witness is a theorem
  of the battery. A second witness shows that a chain over the scratch stack followed by the
  frames does not replace the premise.
- **No file outside the brief's list changed.** I edited no file of `src/Effect4/Machine/`, of
  seat PUB or of seat POOL, and none of the coordinator's six files.
- **One equation of the frames is missing in `Frames.lean`.** It is stated in the new module,
  and item 9 proposes its move.
- **R11 stays open.** A local law of the pop closes no requirement. The run-level half of
  `saved-mask-restoration` has no statement, and item 8 lists what the lift still owes.

The sections below carry the brief's item numbers. Item 1 is the bold line above.

## 2. Base, head and commits

| Item | Value |
| --- | --- |
| Branch | `seat/maskpop`, in the worktree `/Users/pooks/Dev/lean4-effect4-qsteps` |
| Base | `6b2b5cda` |
| Main-line heads taken in | none |
| Head | the commit that adds this receipt; its parent is `e925a8d6` |

Nothing is pushed.

| Commit | Step | Content |
| --- | --- | --- |
| `7ae2f9e5` | 0 | the design note |
| `4f9ad43d` | 1 | the new module with `MaskChain`, its `Decidable` instance, `MaskPopDiscipline` and the planned goal, placed; the import in the Laws root |
| `12d7703d` | 2 | the goal proved in place, with its nine steps |
| `86335bd1` | 3 | the battery and its import in `Test/All.lean` |
| `e925a8d6` | 4 | the row of `docs/ARCHITECTURE.md` and the role of the role register |
| this commit | — | this receipt, and the design note's addendum |

## 3. Changed files

`git diff --stat 6b2b5cda..e925a8d6` lists seven files. This commit adds the eighth and changes
the design note. The counts come from `grep` over the lines that open a declaration.

| Group | File | What changed |
| --- | --- | --- |
| The laws | `src/Effect4/Laws/Machine/MaskDiscipline.lean` | new: the predicate `MaskChain`, one instance, ten theorems and the structure `MaskPopDiscipline` |
| The laws | `src/Effect4/Laws.lean` | one import, after `import Effect4.Laws.Machine.LiveStack` |
| The batteries | `Test/Machine/MaskDiscipline.lean` | new: 57 guards, 11 examples, 5 theorems and 5 pinned outputs |
| The batteries | `Test/All.lean` | one import, after `import Test.Machine.StoreKernelBank` |
| The documents | `docs/ARCHITECTURE.md` | one new row |
| The documents | `tools/Tools/ArchitectureRoles.lean` | one new role |
| The notes | `docs/research/2026-10-06-seat-MASKPOP-design.md`, and this receipt | new |

The new module imports `Effect4.Machine.Fibers`, `Effect4.Laws.Auto.RuleSets` and
`Effect4.Laws.Auto.Semantics`. It imports no module of `src/Effect4/Laws/Program`. The battery
imports the new module, `Effect4.Laws.Machine.LiveStack` and `ProofGraph.Plan`.

## 4. Commands, results and evidence

Each Lean, Lake or `make` command ran through
`/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, named `SLOT` below. Each `make` took the
flags `-o build -o ts/eff/node_modules -o harness/truth/node_modules`, named `FLAGS`. The
scratch folder is
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/acf2315e-02ac-4acd-9ef9-b0734bd686a7/scratchpad/maskpop/`,
named `SCRATCH`. It holds each log. `LEAN` stands for
`SLOT lake env lean -M6144 -DwarningAsError=true`.

| Command | Result | Evidence |
| --- | --- | --- |
| `SLOT lake build`, on `6b2b5cda` | `Build completed successfully (990 jobs).` Lake restored each module from its cache, so the run gave no gate line | tested |
| `LEAN Test/All.lean`, on `6b2b5cda` | exit 0; the three gate lines of the base, in the table below | tested: a fresh run of the gates |
| `LEAN SCRATCH/probe1.lean` | exit 0; Codex's sketch of the predicate elaborates unchanged, and Lean gives its three equations | tested |
| `LEAN SCRATCH/probe2.lean` | exit 1 with one error, at the first form of the `Decidable` instance (finding F5); every statement of the design note is proved there, at `[propext, Quot.sound]` | tested: the design note's probe |
| `LEAN SCRATCH/probe3.lean`, then `LEAN SCRATCH/probe4.lean` | exit 1 each. The instance's second form elaborates. `aesop` closes the two entries. It does not close the hook law or the same-flag statement | tested |
| `LEAN SCRATCH/probe5.lean` | exit 0; the planned goal's form, both witnesses of the scratch premise, and the sweep's counts | tested |
| `SLOT lake build Effect4.Laws.Machine.MaskDiscipline`, at step 1 | `Build completed successfully (25 jobs).` | tested |
| `SLOT lake build Effect4.Laws`, at step 1 and again at step 2 | `Build completed successfully (670 jobs).`, each time | tested: the root's anchor |
| `LEAN SCRATCH/step1-goal.lean`, the module of `4f9ad43d` as a scratch copy | exit 0; the plan status "goal", with the goal's statement as its one next goal; the axioms `[propext, sorryAx]` | tested: the goal of step 1 |
| `SLOT lake build Effect4.Laws.Machine.MaskDiscipline`, at step 2 | `Build completed successfully (194 jobs).` The module takes six seconds | proved: the kernel accepts each theorem |
| `LEAN SCRATCH/census2.lean`, at step 2 | the statements, the axioms and the plan status of item 5; the two censuses of item 7 | tested |
| `LEAN SCRATCH/census3.lean` | exit 0; the census of `Effect4.Laws.Program.Typed.Mask` lists the twelve projections of `MaskRestoration` as untagged | tested: finding F7 |
| `LEAN Test/Audit/ProofStyle.lean`, at step 2 | exit 0; `proof style: 1914 recorded uses and 52 recorded unread commands in 1163 entries`, and no finding | tested: the ratchet refuses nothing |
| `LEAN Test/Machine/MaskDiscipline.lean`, at step 3 | exit 0, and no message | tested: the battery |
| `python3 SCRATCH/falsify.py`, `LEAN SCRATCH/battery-red-all.lean`, `python3 SCRATCH/compare.py` | exit 1 from Lean: 80 errors, at exactly the 77 changed checks; the comparison exits 0 | tested: each check of the battery can fail |
| `LEAN SCRATCH/battery-axioms.lean` | each declaration of the battery is at `[propext, Quot.sound]` or below | tested |
| `SLOT lake build Effect4.Laws.Machine.MaskDiscipline Test.Machine.MaskDiscipline`, at step 3 | `Build completed successfully (198 jobs).` The battery takes five seconds | tested |
| `SLOT lake build Tools.ArchitectureRoles`, at step 4 | `Build completed successfully (2 jobs).` | tested |
| `SLOT make FLAGS check-docs`, at step 4, and again with this receipt staged | `PASS check-docs: every path, link, citation and make target in 75 documents resolves`, each time | tested |
| the same, with a wrong path in the new row | `FAIL check-docs: 1 stale reference(s) in 1 of 75 documents`, at the new row; exit 2. I restored the row, and the check passes again | tested: the red control of the new row |
| `SLOT lake build`, on `e925a8d6` | `Build completed successfully (992 jobs).` in 59 seconds; the gate lines below | proved, for the laws; tested, for the batteries |
| `LEAN SCRATCH/lift-probe.lean` | three results on the sweep, in item 8 | tested: a finite probe |
| `python3 scripts/check-language.py --strict` on the design note and on this receipt | `PASS check-language: no finding`, for each | tested |
| `python3 scripts/check-language.py --show docs/ARCHITECTURE.md` | no finding at the new row; the document's older findings stay | tested |

The gate lines of `Test/All.lean`, and the proof-style line of `Test/Audit/ProofStyle.lean`:

| Tree | Jobs | API and Laws-only modules | Modules, declarations | Planned goals, declarations on goals | Proof style: uses, unread, entries |
| --- | --- | --- | --- | --- | --- |
| `6b2b5cda`, the base | 990 | 173, 302 | 740, 87690 | 24, 11 | no line: the run was `Test/All.lean` alone |
| `e925a8d6` | 992 | 173, 303 | 742, 87797 | 24, 11 | 1914, 52, 1163 |

The head's lines, from the default build:

```text
Effect4 library-root gate: 173 API/utility modules, 303 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 742 modules and 87797 declarations; [...] semantic/test axioms are [propext, Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
Effect4 goal gate: 24 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 11 declaration(s) rest on goals; no other declaration reaches sorryAx
```

The slice adds two modules and 107 declarations. The default build ran once, at the end, on a
clean tree of `e925a8d6`. Lake built `Test.Audit.ProofStyle`, `Test.All` and `Test` in that run,
and it took the other modules from the narrow builds. This commit changes two notes only, and
no build ran after it.

### The battery

`Test/Machine/MaskDiscipline.lean` evaluates the chain on real fibers at the alphabets `Nat`.
Each row of Codex's table of controls is one section.

| Row | Fiber | What the guards pin |
| --- | --- | --- |
| 1 | both empty stacks, each at its own base | a pop leaves the bit and the empty stack; an entry that asks for the fiber's flag changes nothing; the other entry pushes the frame that returns the flag; the pop after an entry returns the entry's fiber |
| 2 | flag false under `[setInterruptible true]`, at base true | every pop returns flag true and an empty stack; so does the finished frame's path, on a success and on a failure |
| 3 | both saved bits with neutral frames between them, at base true | the exact fiber after a value demand and after a cause demand; the chain after every pop, with a pending cause too |
| 4 | a cause is pending when `setInterruptible true` passes | the bit is restored, and the replacement is failure with that cause; with the skip on, the walk goes on and the chain holds at its end |
| 5 | `asyncFinalizer`, and a masking `onExit` | the drain visits the pushed frame next; with a cause pending that frame answers first; a finalizer that answers keeps the frame it pushed; the live traversal agrees |

**The sweep.** It takes every stack of at most four frames over eight frames: 4681 stacks.
With a flag, a base, a pending cause or none and a deferred interrupt or none, 22408 states
hold the chain. Each keeps it through three demands, two skip flags and a carried cause or
none. Each keeps it through the finished frame's path and through both entries. At each state
the other flag has no chain.

**The red controls.** Each is red at its own property.

| Control | Property that it breaks | Form |
| --- | --- | --- |
| a pop that drops a restoring frame without its hook | the flag after the pop | `popNoHook`: on row 2's fiber it has the real pop's stack and the wrong flag. Over the sweep it breaks the chain exactly where the dropped frame is a restoring frame |
| a finalizer that masks and pushes no restoring frame | the frame that returns the flag | `maskNoPush`: at base true it has the real hook's flag and no frame. Over the sweep it breaks the chain exactly where it changes the flag |
| the same flag without the fixed base | one base for both chains | `sameFlag_needs_base` (proved): two empty stacks with opposite flags |
| a relation that keeps the base and omits the alternation | the negation at each restoring frame | `baseOnly_two_flags` (proved): both flags stand over `[setInterruptible true]` at one base |
| the pop without the scratch premise | the empty scratch stack | `pop_needs_empty_scratch` (proved): the adversarial note's witness. `pop_needs_empty_scratch_joined` (proved): the second witness. Over 1026 loose inputs the statement fails at 165, and only where the scratch stack is not empty |

The falsified copy changes 77 checks: the 57 guards, the 5 pinned outputs, the 4 red-control
theorems and the 11 examples. Lean reports an error at each of the 77, and at no other command.

### The acceptance, item by item

| Item of the brief | Result |
| --- | --- |
| 1. The placed theorem is proved at `[propext, Quot.sound]` | yes (proved). The battery pins its axioms and its plan status |
| 2. The controls of part 3 pass, with each red control red at its own property | yes (tested): five rows, the sweep, five red controls, and 77 of 77 falsified checks fail |
| 3. Narrow builds after each step; the default build once; `make check-docs` | the table above. Each passes |
| 4. The commands that the coordinator runs | not run: the list below |

### Not run

- `make check-gen`, `make check-slow`, `make check-corpus`, `make check-target`,
  `make check-truth`, the conservativity script and `make gen-semantics`.
- `make check-semantics` and `make gen-architecture`: both need the coordinator's report.
- `make check-cases`: `Prim` is none of the nine families of the case policy (reading,
  `tools/Conform/Effect4/cases-policy.json`).
- `make check`, `make check-full`, `make check-language` and `make status`, as targets.
- Every TypeScript lane, every host run and every OCaml run. No install and no download ran.

### Red or stale for a reason outside the slice

Nothing that I ran is red. Two older states showed in the logs, and I left both:

- the proof-style gate lists 52 unread commands, as the baseline records at the base;
- `docs/ARCHITECTURE.md` carries older findings of the language checker, away from the new row.

One hook refused one command of mine. It was a `grep` over `Test/Audit` with its standard error
sent to `/dev/null`. I ran it again without the redirection.

### What is proved, and what is only tested

| Claim | Evidence |
| --- | --- |
| The pop keeps the chain at the same base, from an empty scratch stack, at every demand, skip flag and carried cause | proved: `popFrom_maskChain` |
| `getCont` keeps the chain; the finished frame's path keeps it | proved: `getCont_maskChain`, `frameExitState_maskChain` |
| The entry of each region keeps the chain | proved: `uninterruptible_maskChain`, `interruptibleRegion_maskChain` |
| Two chains at one base over one stack have one flag | proved: `MaskChain.flag_eq`, and the field `sameFlag` |
| A hook keeps the chain, and so does the drain, with no scratch premise | proved: `ensure_maskChain`, `passPushed_maskChain` |
| One drain empties what one hook pushed onto an empty scratch stack | proved: `passPushed_ensure_stack_nil` |
| The pop's statement is false without the scratch premise | proved at one input: `pop_needs_empty_scratch`. Proved at one input for the joined chain: `pop_needs_empty_scratch_joined` |
| The same-flag statement is false without the fixed base, and false without the alternation | proved at one input each: `sameFlag_needs_base`, `baseOnly_two_flags` |
| On the sweep, every state that holds the chain keeps it through every pop and entry | tested: 22408 states |
| A pop that answers nothing ends at an empty stack and at the base | tested on the sweep (item 8). No theorem states it |
| Clearing a stack keeps the chain exactly where the flag is the base | tested on the sweep (item 8). No theorem states it |
| `FrameFiber.step` pushes no restoring frame | reading (item 8) |

No evidence of the slice is host-only, and no host ran. Each guard of the battery is bounded:
its fibers are at the alphabets `Nat`, and its sweep stops at four frames. The theorems are not
bounded: they hold at every alphabet with the four instances, and at every stack.

## 5. The statements as compiled, the axioms and the plan status

`#check` prints these statements (`SCRATCH/census2.out`). The names open with `Effect4.FrameFiber`,
but for the last three, which open with `Effect4.Machine`.

```text
@MaskChain : {ν σ : Type u_1} → {β : Type u_2} → {ε δ ι α : Type u_1} → Bool → Bool → List (Prim ν σ β ε δ ι α) → Prop
@MaskChain.decidable : {ν σ : Type u_1} →
  {β : Type u_2} →
    {ε δ ι α : Type u_1} →
      (base flag : Bool) → (stack : List (Prim ν σ β ε δ ι α)) → Decidable (MaskChain base flag stack)
@MaskChain.flag_eq : ∀ {ν σ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1} {base flag flag' : Bool}
  {stack : List (Prim ν σ β ε δ ι α)}, MaskChain base flag stack → MaskChain base flag' stack → flag = flag'
@ensure_maskChain : ∀ {ν σ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1} (base : Bool) (frame : Prim ν σ β ε δ ι α)
  (fiber : FrameFiber ν σ β ε δ ι α) (rest : List (Prim ν σ β ε δ ι α)),
  MaskChain base fiber.interruptible (frame :: (fiber.stack ++ rest)) →
    MaskChain base (frame.ensure fiber).fst.interruptible ((frame.ensure fiber).fst.stack ++ rest)
@uninterruptible_maskChain : ∀ {ν σ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1} (base : Bool)
  (f : FrameFiber ν σ β ε δ ι α),
  MaskChain base f.interruptible f.stack → MaskChain base f.uninterruptible.interruptible f.uninterruptible.stack
@interruptibleRegion_maskChain : ∀ {ν σ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1} (base : Bool)
  (f : FrameFiber ν σ β ε δ ι α),
  MaskChain base f.interruptible f.stack →
    MaskChain base f.interruptibleRegion.fst.interruptible f.interruptibleRegion.fst.stack
@passPushed_maskChain : ∀ {ν σ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1} [inst : DecidableEq ε]
  [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (base : Bool) (demand : Arm) (skip : Bool)
  (fiber : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α)) (rest : List (Prim ν σ β ε δ ι α)),
  MaskChain base fiber.interruptible (fiber.stack ++ rest) →
    MaskChain base (passPushed demand skip fiber cause).fiber.interruptible
      ((passPushed demand skip fiber cause).fiber.stack ++ rest)
@passPushed_ensure_stack_nil : ∀ {ν σ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1} [inst : DecidableEq ε]
  [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (demand : Arm) (skip : Bool)
  (frame : Prim ν σ β ε δ ι α) (fiber : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α)),
  fiber.stack = [] → (passPushed demand skip (frame.ensure fiber).fst cause).fiber.stack = []
@popFrom_maskChain : ∀ {ν σ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1} [inst : DecidableEq ε]
  [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (base : Bool) (demand : Arm) (skip : Bool)
  (frames : List (Prim ν σ β ε δ ι α)) (f : FrameFiber ν σ β ε δ ι α) (cause : Option (Cause ε δ ι α)),
  f.stack = [] →
    MaskChain base f.interruptible frames →
      MaskChain base (popFrom demand skip frames f cause).fiber.interruptible
        (popFrom demand skip frames f cause).fiber.stack
@getCont_maskChain : ∀ {ν σ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1} [inst : DecidableEq ε]
  [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (base : Bool)
  (f : FrameFiber ν σ β ε δ ι α) (demand : Arm) (skip : Bool) (cause : Option (Cause ε δ ι α)),
  MaskChain base f.interruptible f.stack →
    MaskChain base (f.getCont demand skip cause).fiber.interruptible (f.getCont demand skip cause).fiber.stack
@frameExitState_maskChain : ∀ {ν σ : Type u_1} {β : Type u_2} {ε δ ι α : Type u_1} [inst : DecidableEq ε]
  [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (base : Bool)
  (f : FrameFiber ν σ β ε δ ι α),
  MaskChain base f.interruptible f.stack → MaskChain base (frameExitState f).interruptible (frameExitState f).stack
MaskPopDiscipline : Type u_1 →
  Type u_1 →
    Type u_2 → (ε δ ι α : Type u_1) → [DecidableEq ε] → [DecidableEq δ] → [DecidableEq ι] → [DecidableEq α] → Prop
saved_mask_pop_discipline : ∀ (ν σ : Type u_1) (β : Type u_2) (ε δ ι α : Type u_1) [inst : DecidableEq ε]
  [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α], MaskPopDiscipline ν σ β ε δ ι α
```

The six fields of `MaskPopDiscipline` are `pop`, `getCont`, `frameExit`, `uninterruptible`,
`interruptibleRegion` and `sameFlag`. The first five have the statements above, with each
premise as an arrow. `sameFlag` reads two fibers:

```lean
sameFlag : ∀ (base : Bool) (f g : FrameFiber ν σ β ε δ ι α), f.stack = g.stack →
  MaskChain base f.interruptible f.stack → MaskChain base g.interruptible g.stack →
    f.interruptible = g.interruptible
```

The axioms, as `#print axioms` gives them. The battery pins the last four lines by
`#guard_msgs`.

```text
'Effect4.FrameFiber.MaskChain.decidable' depends on axioms: [propext]
'Effect4.FrameFiber.MaskChain.flag_eq' depends on axioms: [propext]
'Effect4.FrameFiber.ensure_maskChain' depends on axioms: [propext]
'Effect4.FrameFiber.uninterruptible_maskChain' depends on axioms: [propext]
'Effect4.FrameFiber.interruptibleRegion_maskChain' depends on axioms: [propext]
'Effect4.FrameFiber.passPushed_maskChain' depends on axioms: [propext]
'Effect4.FrameFiber.passPushed_ensure_stack_nil' depends on axioms: [propext]
'Effect4.FrameFiber.popFrom_maskChain' depends on axioms: [propext, Quot.sound]
'Effect4.FrameFiber.getCont_maskChain' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.frameExitState_maskChain' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.saved_mask_pop_discipline' depends on axioms: [propext, Quot.sound]
```

No declaration reaches `Classical.choice`. The axiom gate holds each one at
`[propext, Quot.sound]` in the default build.

The plan status of the placed theorem, as the battery pins it:

```text
Effect4.Machine.saved_mask_pop_discipline: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
```

At step 1 the same command printed "goal", with the goal's statement as its one next goal. The
counts are of the battery's tree, which holds no step of the proof.

## 6. Each landed theorem's placement

**`saved_mask_pop_discipline`** (`src/Effect4/Laws/Machine/MaskDiscipline.lean`), tagged
`@[semantics "scope-lifetime-finalization" (requirement := R11)]`:

- Concept: `scope-lifetime-finalization`; property: the saved mask's chain through a pop
  (proposal P3).
- Question: the proposed registry claim `saved-mask-pop-discipline` (role `preservation`). It is
  a step of the open run-level half of `saved-mask-restoration`. Consumer: the later lift
  through `Machine.Lift` (`src/Effect4/Laws/Machine/Lift.lean`).
- Reach: the polymorphic `FrameFiber`, with the four instances of the pop's definitions; every
  stack, demand, skip flag and carried cause; one fixed base. The pop asks for an empty scratch
  stack. No field asks for a premise on a pending cause, on a deferred interrupt or on a
  frame's kind.
- Does not establish: a law of a run, a completed exit or a cleanup's multiplicity. It gives no
  delivery, no budget and no liveness, and nothing of a host or of a printed form. The bracket
  of a whole region and each fiber's base in a run are not stated. It is an invariant of one
  step, and no progress.
- Unlocks: nothing on the M5 to M7 spine. It serves R11 as one placed node. After the lift, it
  serves the waiting wrapper under a masked caller and Semaphore's protected permit.

Each helper carries the tag `@[semantics "scope-lifetime-finalization"]`, with no requirement.
Its docstring names the statement that it is a step of, and its consumer.

| Helper | Step of | Consumer |
| --- | --- | --- |
| `MaskChain.flag_eq` | the placed theorem | its field `sameFlag` |
| `ensure_maskChain` | `popFrom_maskChain` | the pop's answering case, and `passPushed_maskChain` |
| `passPushed_maskChain` | `popFrom_maskChain` | both shapes of `continueFrom_cases` |
| `passPushed_ensure_stack_nil` | `popFrom_maskChain` | the scratch premise of the recursive call |
| `popFrom_maskChain` | the placed theorem | its field `pop`, and `getCont_maskChain` |
| `getCont_maskChain` | the placed theorem | its field `getCont`, and `frameExitState_maskChain` |
| `frameExitState_maskChain` | the placed theorem | its field `frameExit` |
| `uninterruptible_maskChain`, `interruptibleRegion_maskChain` | the placed theorem | its two fields of the entries |

`MaskChain` and its instance are definitions, and they carry no tag.

## 7. Choices, differences from Codex's statements, and findings

### Choices

- **C1. The namespaces.** The predicate, the hook, the drain, the pop, `getCont` and the two
  entries are in `Effect4.FrameFiber`, beside the laws that they read. The adapter, the
  structure and the placed theorem are in `Effect4.Machine`, beside `frameExitState`.
- **C2. One placed theorem over a structure.** `MaskPopDiscipline` takes the seven alphabets as
  explicit parameters, with the four instances. The planned goal, `#plan_status` and the
  attribute read it as they read any theorem. So I did not place `frameExitState_maskChain`
  alone.
- **C3. The hook law has no scratch premise.** It reads the popped frame on top of the scratch
  stack and of the frames left. The drain is the same law at the scratch stack's top frame. The
  scratch premise enters at two places only: `passPushed_ensure_stack_nil` and the pop.
- **C4. The hook splits by `cases frame`, with one catch-all.** A restoring frame reads its two
  own equations. `onExit` and `asyncFinalizer` read their own equations of the mask. Every
  other hook closes by the predicate's own catch-all. A new frame with a neutral hook needs no
  new line.
- **C5. `ensure_stack_cases` serves the scratch equation only.** It gives no flag where the
  stack is unchanged, as the brief says.
- **C6. Search where it is short.** `aesop` closes the two entries with the entries' own laws
  as rules. The other proofs are by hand. `#auto_census` with `aesop` closes none of the
  module's 16 theorems from its statement.
- **C7. No bank.** The module registers no rule in a named bank. No other module asks for the
  chain's equations yet.
- **C8. A `Decidable` instance in the law module.** The battery evaluates the one definition
  with it. It is no second definition, and no Boolean projection.
- **C9. The imports.** `Effect4.Laws.Auto.RuleSets` gives `aesop`, and
  `Effect4.Laws.Auto.Semantics` gives the attribute and `proof_goal`.
- **C10. The battery's sweep and its mutants.** The two wrong functions are fixtures of the
  battery, so each red control stays in the tree.
- **C11. The same-flag check of the sweep is linear.** It asks that the other flag has no
  chain at each state. The first form compared every pair of states and took six more seconds.

### Each difference from Codex's statements

- **None in the predicate and in the three statements.** `MaskChain`, `popFrom_maskChain`,
  `getCont_maskChain` and `frameExitState_maskChain` stand as Codex wrote them, with the
  scratch premise.
- **The namespaces and the instances** are fixed (C1, item 5). Codex left both open.
- **Two general steps are new**: `ensure_maskChain` and `passPushed_maskChain` (C3).
- **One equation of the frames is new**: `passPushed_ensure_stack_nil` (finding F4).
- **The two corollaries are stated**: `uninterruptible_maskChain` and
  `interruptibleRegion_maskChain`; `MaskChain.flag_eq` on two flags, and `sameFlag` on two
  fibers.
- **The `Decidable` instance** is an addition (C8).
- **One control more than Codex's table**: the second witness of the scratch premise.

### Findings

- **F1. Codex's design holds.** The predicate elaborates unchanged, and its three statements
  are proved with no added premise. The source review's case list is the proof's case list.
- **F2. A second witness for the scratch premise.** A reader may try the premise
  `MaskChain base f.interruptible (f.stack ++ frames)` in its place. It fails at flag false,
  scratch `[setInterruptible true]`, frames `[setInterruptible false]` and base false. The pop
  ends at flag true with an empty stack (proved: `pop_needs_empty_scratch_joined`).
- **F3. The scratch premise is exact on a small sweep.** The sweep holds 1026 inputs: a
  scratch stack of at most one frame, and at most two frames to pop. The statement without the
  premise fails at 165 of them. It fails at none of the 114 whose scratch stack is empty
  (tested).
- **F4. One equation of the frames is missing.** `passPushed`'s docstring says that one drain
  step is exact, and no theorem states it as an equation of the stack.
  `passPushed_ensure_stack_nil` does, with no word of the chain. Its two alternatives are
  those of `ensure_stack_cases`.
- **F5. A catch-all arm of a plain `match` does not reduce the chain.** The first form of the
  instance failed there: `Decidable (MaskChain base flag rest)` did not match
  `Decidable (MaskChain base flag (head✝ :: rest))`. The frame is a variable while Lean
  elaborates the arm. A `cases` on the frame inside the structural recursion elaborates, and
  the compiler accepts it.
- **F6. The planned goal takes explicit alphabets.** `proof_goal` elaborates the signature with
  seven type binders and four instance binders. `#plan_status` prints the goal's statement with
  them.
- **F7. The structure's six projections are untagged theorems.** `#semantics_census` lists them
  beside the ten tagged theorems. The twelve projections of `MaskRestoration` stand the same way
  in their module's census (tested: `SCRATCH/census3.log`). The new module is in no concept's
  default modules (proposal P4).
- **F8. The slice needed no `simp`.** Each rewrite is a `rw` with a named equation. The
  proof-style baseline is unchanged.
- **F9. The base's default build gave no gate line.** Lake restored `Test.All` from its cache.
  So I ran `Test/All.lean` by itself for the base's three lines.

## 8. What the lift to runs needs from this slice, and what it still owes

The lift states that each live fiber of a reached run holds the chain at one base. It is no
part of this slice, and no statement below is in the tree.

**What the slice gives.** Each seam of the fiber machine that pops a stack or enters a region
has its field.

| Seam (`src/Effect4/Machine/Fibers.lean`, `src/Effect4/Machine/Frames.lean`) | Field |
| --- | --- |
| `evaluatePrim.finishFrame`, at a finished exit: `frameExitState` | `frameExit` |
| `evaluatePrim.finalizerOr`: its `getCont`, with a carried cause | `getCont` |
| `FrameFiber.resumeValue` and `FrameFiber.resumeCause`, inside `FrameFiber.step` | `getCont` |
| `evaluatePrim.withFiber`, the actions `setInterruptible body false` and `getInterruptible` | `uninterruptible` |
| `evaluatePrim.withFiber`, the action `setInterruptible body true` | `interruptibleRegion` |
| a region's entry and its completed exit, once their stacks are equal | `sameFlag` |

**What the lift still owes.** Each line names its evidence.

1. **Each fiber's base.** `FiberCore.start` gives a fiber its flag over an empty stack. The
   chain holds there at that flag, by the predicate's first equation (reading).
2. **`FrameFiber.step` keeps the chain.** `step` pushes the frames `onSuccess`,
   `onSuccessConst`, `onFailure`, `onSuccessAndFailure`, `exitFrame`, `onExit` and `whileLoop`.
   `Prim.armA` pushes `whileLoop` and `iterator` (reading). None is a restoring frame, so the
   predicate's third equation keeps the chain under each. No theorem states it.
3. **The fiber machine's own pushes.** `evaluatePrim` pushes `Prim.asyncFinalizer` at two
   places, and `FiberCore.pushIterator` pushes an `iterator` (reading). Both are neutral.
4. **The other fields.** The chain reads the flag and the stack only. A write of `current`, of
   the pending cause or of the deferred flag keeps it, by the predicate's form.
5. **The clear.** `RunFiber.cleared` empties the stack and keeps the flag. `Cmd.exitDone` runs
   it, and so does `exitFiber.exitStore` at a fiber with no observer. Clearing keeps the chain
   exactly where the flag is the base (tested: each of the sweep's 22408 states). So the lift
   carries a condition: a cleared fiber's stack is empty. This is the trap of Codex's report.
6. **A finished frame has an empty stack.** In `Fibers.lean`, `Outcome.finished` comes from
   `finishFrame` alone, after `frameExitState` (reading). On the sweep, each of the 10781 pops that answer nothing
   ends at an empty stack and at the base (tested). No theorem states it. Its proof would
   follow this slice's induction, with `passPushed_ensure_stack_nil`.
7. **The bracket of a region.** The body's run must return to the entry's stack. That is a law
   of a run. With it, `sameFlag` gives the entry's flag at the exit.
8. **The form of the invariant.** `Machine.Lift.StepKeeps` takes the machine and the pending
   commands. The invariant ranges over the machine's fibers, and its command condition is
   line 5's.

`Program.MaskInv` and its consumers are untouched. The slice claims no relation between the
two predicates.

## 9. Proposals (not rulings)

- **P1. The registry claim**, for `tools/Tools/SemanticsRegistry.lean`:

  ```lean
  { id := "saved-mask-pop-discipline", concept := "scope-lifetime-finalization", role := .preservation
    title := "At one fixed base bit, the frame machine keeps the chain of restoring frames on a fiber's stack: FrameFiber.popFrom from an empty scratch stack, getCont, Machine.frameExitState and the entry of each region keep it, and two fibers with one base and one stack have one flag (a local law at every demand, skip flag and carried cause; no statement of a run, of a completed exit, of cleanup or of delivery)"
    pointer := .witness `Effect4.Machine.saved_mask_pop_discipline },
  ```

  The role `preservation` is the role of `saved-mask-restoration`: a step keeps an invariant.
- **P2. R11's open part.** The line that opens with `saved-mask-pop-discipline` leaves the
  open parts, since the claim has its witness. A line for the lift may take its place:

  > the lift of saved-mask-pop-discipline to runs (scope-lifetime-finalization, serving the
  > run-level half above): each live fiber of a reached run holds the chain at its start flag;
  > it needs FrameFiber.step and each command to keep the chain, with the condition that a
  > cleared fiber's stack is empty, since Cmd.exitDone clears a stack and keeps its flag; the
  > local law is saved_mask_pop_discipline; no goal states the lift

- **P3. The required property's text**, for `docs/core/semantics.md`, concept
  `scope-lifetime-finalization`, after the property of `saved-mask-restoration`:

  > - **The saved mask's chain through a pop (`saved-mask-pop-discipline`)**: At one fixed base
  >   bit, the restoring frames of a fiber's stack alternate from the negation of the flag
  >   (`MaskChain`). The frame machine's pop keeps the chain, from an empty scratch stack.
  >   `getCont`, the finished frame's path and the entry of each region keep it too. Two fibers
  >   with one base and one stack have one flag. It is a local law of the frame machine. It
  >   states no law of a run, no completed exit and no bracket of a region.
  >   (`saved_mask_pop_discipline` (`src/Effect4/Laws/Machine/MaskDiscipline.lean`)).

- **P4. The module's default concept.** Add `Effect4.Laws.Machine.MaskDiscipline` to the
  `defaultModules` of `scope-lifetime-finalization`. Each authored theorem is tagged already.
  The six projections of the structure would then inherit the concept (finding F7).
- **P5. Move `passPushed_ensure_stack_nil` to `src/Effect4/Machine/Frames.lean`**, beside
  `popFrom_pass_no_push`, with its name and statement. It is a general equation of the frames
  (finding F4). The new module would then cite it, and its tag would go.
- **P6. The next slice.** Its first two statements are lines 2 and 6 of item 8. `step` keeps
  the chain, and a pop that answers nothing ends at an empty stack. Both stay below the typed
  program, and both follow existing inductions.

## 10. The requirements R1 to R13

The lists read `generated/semantics.md` as committed at the base, and the plan status of
item 5. The report is not regenerated here.

**What the slice advances.**

- R11 gains one placed node, proved: `saved_mask_pop_discipline`. R11 stays open.
- Of R11's seven open parts, one is now stated and proved as a local law: the helper claim
  `saved-mask-pop-discipline`. The run-level half of `saved-mask-restoration` stays open, with
  no statement.
- No requirement closes. A local law of the pop closes none.

**What the slice's theorem still rests on.**

- No planned goal: its plan status is "proved", with no next goal.
- Its premises: the chain over the input, in each field. The field `pop` also asks for the
  empty scratch stack. The field `sameFlag` asks for equal stacks.
- No bounded evidence and no host: the theorem holds at every alphabet with the four instances.

**The older open parts that the slice leaves untouched.** The counts come from the report, by
one `awk` command over its lines that open with "- Open:".

| Requirement | Open parts | The slice's relation |
| --- | --- | --- |
| R1 | 4 | none |
| R2 | 5 | none |
| R3 | 6 | none |
| R4 | 5 | none: a relation of flags gives no membership theorem |
| R5 | 2 | none |
| R6 | 7 | none |
| R7 | 4 | none |
| R8 | 6 | none: the slice states no agreement with a target |
| R9 | 1 | none |
| R10 | 12 | none yet: the waiting wrapper and Semaphore's protected form are consumers after the lift |
| R11 | 7 | one new placed node. The run-level half of `saved-mask-restoration` stays open. So do release at most once, the close order, the state at a frontier and the open scope of a finished run. The goals `cleans_once`, `cleanup_keeps` and `releases_once` stay goals |
| R12 | 8 | none: the slice states no delivery, no budget and no liveness |
| R13 | 4 | none |

The report's ten next goals are untouched: `bounded`, `cleans_once`, `committed`, `counted`,
`unauthorized_calls_nothing`, `stale_never_applies`, `cleanup_keeps`, `retries_declared`,
`releases_once` and `infrastructure_escapes`.

## 11. Open obligations

None of the brief's table. No planned goal of the slice is open. Item 8 lists what a later
slice owes, and item 9 holds six proposals. No one has ruled them.

## 12. Proposed decisions rows (proposals only)

One row, if the coordinator records the choice of the invariant:

| Topic | Proposal |
| --- | --- |
| The mask's invariant of runs | The run-level half of `saved-mask-restoration` is stated over `FrameFiber.MaskChain`, at each fiber's start flag as its base. `Program.MaskInv` stays as it is, for the reference relation. The lift's command condition is that a cleared fiber's stack is empty |
