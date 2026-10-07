# 2026-10-06 test cleanup: a census of the batteries, and the first cut

Status: a research note (history, not authority). The owner asked for it on 2026-10-06. The
ask: drop the tests that are mechanical and that the proof tooling has made unnecessary. The
work now starts to need smarter tests. Decisions row 301.

## Question

Which lines of the batteries only measure again what a gate or a report already measures?
Which of them can go now, and which need a reading first?

## What was read or run

| What | Evidence |
| --- | --- |
| Every `.lean` file under `Test/`: 312 files and 79250 lines before the cut, counted by kind of command | tested: a script over the files |
| `Test/Audit/AxiomGate.lean`: what the axiom gate and the goal gate refuse | reading |
| `scripts/`, `Makefile` and `tools/` for a reader of a printed axiom line | tested: a search finds none |
| The module times of two full builds, before and after | tested: one build each |
| The cut, by `docs/research/2026-10-06-test-cleanup-cut-pins.py.txt` | tested: the default build and the gates of the commit |

## Findings

### 1. What the batteries hold

| Kind of line | Count | What it is | Verdict |
| --- | --- | --- | --- |
| `#guard` | 7274 | a finite evaluation, or a control | keep: see section 3 |
| `def` | 3873 | fixtures and scenario programs | not read yet |
| `theorem` | 1698 | proofs that stand in a battery | not read yet |
| `example` | 751 | 49 are red controls under `#guard_msgs`; about 347 only apply one named statement (an estimate by form) | read by file: section 4 |
| `#print axioms` | 552 | 265 bare, 287 pinned by `#guard_msgs` | **cut**: 543 |
| a pinned `#plan_status` | 61 | 58 say "proved, no goal open", for 182 statements | **cut**: 58 |
| `#check` | 117 | 97 bare: a name exists. 20 pinned: a name's type | the 97 bare are the next cut |

### 2. The first cut (landed)

**What went**, in 56 batteries, 2304 lines:

- 543 `#print axioms` lines. 282 had a pin: 245 at `[propext, Quot.sound]`, 32 at `[propext]`
  and 5 at no axiom.
- 58 pinned `#plan_status` commands. Each line of each pin said `proved`, and each ended with
  `next goals: 0`.
- 21 sections that then held nothing, and the prose that named the pins.

**Why each measured nothing new.**

- The axiom gate reads every declaration of every `Effect4.*` and `Test.*` module, and it
  refuses one above `[propext, Quot.sound]`. A pin at that set says the same of one statement.
- A pin below that set promised more than the rule asks. No document states such a promise.
- A bare `#print axioms` line asserts nothing, and no script reads its output.
- The plan derives a statement's status from its proof. `generated/semantics.md` holds each
  claim's status in a tracked file, and the goal gate reads what each declaration reaches.

**What stays.** `Test/Audit` keeps its eight `#print axioms` lines and its three plan pins: they
are the gates' own controls, and three pin `Classical.choice`. `Test/Counterexamples` keeps its
one.

**What the cut gives up, stated.** A pinned "proved" refused a theorem that later came to rest
on a planned goal. For a statement that is no registry claim, no check refuses that now. The
goal gate logs the count of declarations that rest on goals, 12 today, and it does not pin it.
One pinned line in that gate would hold the same for the whole tree (proposal 2).

**Measured.** Of the touched batteries, 46 have a time in both builds: 135 s before and 89 s
after. The build log lost its 251 axiom lines but one. The axiom gate reads 804 modules and
93000 declarations, as before.

### 3. Where the time is, and why most of it stays

The batteries take 591 s of 1385 s of module time in a full build. The slowest are scenario
batteries, finite runs of the machine: `MaskRuns`, `PoolPublic`, `SemaphoreAgreement`,
`QueueAgreement` and their like. They are no
mechanical lines. The registry cites them as the finite controls of claims that are open
(`tools/Tools/SemanticsRegistry.lean`, the open parts of R10 and R11). They are the only
evidence there until the claim is proved.

So the rule for them is by claim. When a claim is proved, its finite controls shrink to its red
controls and one green instance. No slice has done that yet.

### 4. The candidates that are not cut

| Candidate | Size | Why it is mechanical | What it needs |
| --- | --- | --- | --- |
| A bare `#check` of a name | 97 lines in 12 batteries, 48 of them under `Test/Store` | a use or the build finds a renamed name | nothing: the coordinator cuts them next |
| An example that restates a statement | about 347 by form | the kernel holds the theorem | a reading by file: an example at a concrete instance is a reader, and it stays |
| A statement pinned by a frozen contract | `Test/Schema/PayloadContract.lean` holds 163 of the 347 | it guards a public statement against a silent change | the owner: a frozen contract is a promise. The registry's generated statements can hold it for a claim |
| The finite controls of a proved claim | not counted | a theorem covers each instance | one reading for each proved claim |

### 5. The rule, as it stands in `AGENTS.md`

A battery holds no `#print axioms` line, and it pins no status of a proved statement. Each line
is a reader, a control, or a finite evaluation that no theorem covers. A battery restates no
theorem. A frozen contract may pin a statement that no registry claim holds.

## Proposals (not rulings)

1. **Cut the 97 bare `#check` lines**, in one commit, with the same script form.
2. **Pin the goal gate's count** of declarations that rest on goals, in one line of
   `Test/Audit/AxiomGate.lean`. It replaces what the 58 plan pins guarded.
3. **Read the examples by file**, the proved claims' batteries first, with the test of
   section 5.
4. **The owner decides the contracts' statement pins.** One way keeps them as the promise of
   a frozen contract. The other moves each to a registry claim, whose statement the semantics
   report holds in a tracked file.
5. **Each slice that proves a claim trims that claim's finite controls** in the same slice.

## What this does not establish

- It does not say that a remaining test is needed. Only two kinds of line were read in full.
- The count of restating examples is an estimate by the form of the line.
- The times are one build each, on one machine.
- No theorem and no gate changed. The cut removes lines that asserted nothing new.

## Corrected since (2026-10-06, decisions row 302)

- **The 97 bare `#check` lines are not cut.** All of them stand in contract batteries, under the
  heading of the laws that the contract states. Each promises that a name exists, so they wait
  with the contracts' statement pins for the owner's decision (proposal 4). Proposal 1 is
  withdrawn.
- **Proposal 2 is landed.** The goal gate pins the count of declarations that rest on planned
  goals (`restingPin`, `Test/Audit/AxiomGate.lean`): 12 at the default audit root.
