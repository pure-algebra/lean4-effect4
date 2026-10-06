# 2026-10-06 brief for seat WORKQ: the workers over the public Queue

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is the first recommendation of Codex's dogfood review of 2026-10-06, with its two
small helpers. Codex mapped it; this brief points at its packet and adds the estate's rules.

## The slice

The workers scenario (`Test/Dogfood/Scenario/Workers.lean`, decisions row 254) takes its jobs
from a host row. The Queue's public operations are in the tree since seat PUB
(`src/Effect4/Modules/Queue/Ops.lean`: `bounded`, `offer`, `take`, `poll`, `size`). No
application uses them yet. **Run the two-worker crew over the public Queue**, as a second
scenario beside the first. The first stays, as the control of the host protocol.

## Read first

1. `AGENTS.md`, in full.
2. Codex's review, under
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/dogfood-review-1406/`:
   `recommendations.md` (the section "The next dogfood slice…", and friction points 1 to 4),
   and `types/review.md`, sections 1 and 2 (the two helpers, each with its connector's shape
   and its controls). Not compiled: do not run a script of that folder in place.
3. `Test/Dogfood/README.md`, `Test/Dogfood/Scenario.lean` (the script alphabet, the driver,
   `NamedRun`, `Control`, `Scenario`, `#scenario_gate`) and `Test/Dogfood/Scenario/Workers.lean`.
4. The Queue's public slice: `Test/contracts/queue.contract.md`,
   `docs/research/2026-10-06-seat-PUB-receipt.md` (its limits and its budgets; trace 7: a
   helper's budget grows with the continuation that it resumes), and decisions rows 275 and 276.

## The assignment, in three parts

**A design note first** (`docs/research/2026-10-06-seat-WORKQ-design.md`): the program, the
scripts, the observation, the claim's clauses with each one's placement, the controls, and the
list of generated files that part 1 would move. Send its path, and go on.

**Part 1, the two helpers** (Codex's friction points 1 and 2).

1. One `note` for the scenarios, through `Ref.updateWith`, in `Test/Dogfood/Scenario.lean`.
   Control: Codex's collision case (an outer `xs`), red with the fixed binder and green with
   the minted one.
2. One helper for a typed empty cell: the present `ascribe` of
   `Test/Dogfood/P3WorkerQueue.lean`, moved to an authoring home under `src/Effect4/Program/`
   with its record form unchanged. A new core module opens as decisions row 200 says. Give it
   a typing law and a reading law in the law graph, in the shape that Codex's section 2 gives.
   It is no cast: the record's check decides it. It is not `Ref.make<A>`.
3. **Measure before you migrate.** The three scenarios print, lower and run on a host and on
   the engine. A minted binder moves those bytes. List each generated file that moves. If the
   list is longer than the scenarios' own lowered text and faces, **stop and report**; the
   coordinator decides. The new scenario uses the two helpers either way.

**Part 2, the scenario** (`Test/Dogfood/Scenario/QueueWorkers.lean`; `Test/All.lean`, after
`import Test.Dogfood.Scenario.Workers`). Keep what Codex names: the workers' identities, a
failure after the commitment, the reply and cleanup observations, and a cancellation before
and after a take commits. The job's run stays a host row, so receipts and applications stay
observable. Budgets and masks are explicit premises of every run.

**Part 3, the lowered runs**, as the other scenarios have them: the faces, the tape's text,
the engine's fixture, and the keyed lane's runs that a host can perform. Seat SEMW edits
`harness/truth/Truth.lean` and the truth lane's generated files today. **Send a message before
you edit a file under `harness/`**, and wait for the coordinator's answer on the order.

## Placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| The helper's typing law | `store-typing`; R4 | the checker's judgment at every scope, under the record's check | full admission; any run | the scenarios' cells; the public `make` of a later module |
| The helper's reading law | `translation-simulation`; R10, a helper of the module expansion's reading | one evaluation of the term | typing; any store step | the same callers' attempt laws |
| The scenario's clauses | each clause names its own; an unproved general clause is a planned goal in the battery | the named runs, one script each: finite probes | the Queue's run-level law (row 275, point 2); fairness; starvation freedom; liveness | the claim `queue-expansion-agrees` (proposed, R10) and R12's open parts, as their first application |

Do not prove the Queue's run-level law here. State what the scenario needs from it, exactly,
in the receipt: that list is the next proof slice's consumer.

## The rules

- New files are yours, and the files that part 1 names. Do not edit a file of the Queue's,
  Semaphore's or Pool's folders, `src/Effect4/Modules/Waiting.lean`, or a file under
  `src/Effect4/Machine/`.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `docs/core/api-surface.md`,
  `lakefile.toml`, `generated/semantics.md`, `docs/core/semantics.md` or
  `tools/Tools/SemanticsRegistry.lean`. Propose their lines in the receipt.
- The shell's rules are in the dispatch message.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.
- A red control is red for its stated reason: say which line fails, and why.

## Acceptance

1. The helpers' laws are theorems at `[propext, Quot.sound]`. Each planned goal of the
   scenario is listed first in the receipt, with its placement.
2. `#scenario_gate` passes for the new scenario. The first scenario's observations do not
   change.
3. Narrow builds after each step. At the end: the default `lake build` with the gate lines,
   `make gen-fixtures`, `make corpus` with `dune build` and `dune test --force engine`,
   `make check-cases` and `make check-docs`.
4. Not run, and listed so: `make check-gen`, `check-slow`, `check-corpus`, `check-target`, the
   release ledger, the conservativity script, `make gen-semantics`.

## The receipt

`docs/research/2026-10-06-seat-WORKQ-receipt.md`, in the handoff form of `AGENTS.md`: the one
thing to know before merging; base, head and commits; changed files; commands with results;
axioms and `#plan_status`; each statement's placement; each generated file that moved; what
the scenario needs from the Queue's run-level law; the proposals for the coordinator's files.
One paragraph accounts for R1 to R13. Your last message gives the head, the receipt's path
and its first item.
