# 2026-10-06 brief for seat CUTS: the journal's cut and position connectors

Status: a brief (history, not authority). One page: Codex mapped this slice, and its packet
holds the statements. Base: the head that the dispatch message names. It is Codex's priority 4
of the roadmap audit, and it gates no other seat.

## The slice

`tapeFrom` (`Test/Dogfood/Scenario.lean`) reads a run's journal into positions and an unread
rest. `tape_replays` relates a whole tape to the raw replay. Nothing states what a prefix of
the journal gives. Four connectors do:

| Name | Statement, in words |
| --- | --- |
| `tapeFrom_append` | the tape of `a ++ b` is the tape of `a`, then the tape of `b` from the run after `a`, unless `a` stops |
| `tapeFrom_cut` | the journal splits into a completed prefix and the unread rest, and the prefix's tape is the same positions with no rest |
| `tapeFrom_cut_replays` | the machine after the completed prefix is the raw replay of the positions' decisions |
| `tapeFrom_position_replays` | the machine after position `i` is the raw replay of the first `i + 1` decisions |

Then one consumer: `Lowered.shown` (`Test/Dogfood/Scenario/Tape.lean`) at a fresh `Run.open`,
by the position law. An arbitrary progressed run is too broad for that consumer.

## Read first

1. `AGENTS.md`, in full.
2. Codex's packet, under
   `docs/research/2026-10-05-codex-foundation-packet/implementation-audit/roadmap-audit/`:
   `proofs/proposals.md` (the section "Journal cut and positions": the four statements, not
   compiled), `proofs/review.md` (priority 2: the existing helpers and the limits), and
   `recommendations.md`, section 2.
3. `Test/Dogfood/Scenario.lean`: `tapeFrom`, `tape_replays`, and the helpers
   `tapeFrom_frontier`, `tapeFrom_skip`, `tapeFrom_take`, `tapeFrom_stop`.
4. `src/Effect4/Laws/Run.lean`: `Run.play_append`, `play_cons`, `step_built`, `step_budget`,
   `Run.replayFrom`, `Run.machineOf`.
5. `Test/Dogfood/Scenario/Tape.lean`: `Lowered` and `Lowered.shown`.

## The assignment

1. **A short design note first**, `docs/research/2026-10-06-seat-CUTS-design.md`: each
   statement as Lean elaborates it, each difference from Codex's sketch with its reason, and
   the lemma that closes each case. Send its path, and go on.
2. **State the four connectors** beside `tapeFrom` in `Test/Dogfood/Scenario.lean`, each as a
   planned goal first with its placement, and prove each in place. Take the cases from
   `tapeFrom`'s own definition. Write no second tape reader and no new journal alphabet.
3. **The consumer** in `Test/Dogfood/Scenario/Tape.lean`: the views of `Lowered.shown` at a
   fresh open, from `tapeFrom_position_replays`. State its fresh-open premise.
4. **Controls** in the same batteries: one journal with a stopped row (the cut ends before
   it); one frontier row; a red control where the stopped row's own machine is taken for the
   cut's replay result.
5. Pin the axioms and the plan status of each connector.

## Placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| The four connectors | `translation-simulation`; R13, beside `journal_replays`; they serve R8's replay view | every `Run`, every journal; the stop conditions are `tapeFrom`'s own | the machine after a stopped row; a session ledger; resumable ownership (R12, row 226); any generated engine | `Lowered.shown` at a fresh open; later the scenario driver's laws |

A stopped row may change the machine before it reports its frontier. The prefix law says
nothing about that machine, and a second command on it is no continuation.

## The files, and the rules

- You may edit `Test/Dogfood/Scenario.lean` and `Test/Dogfood/Scenario/Tape.lean`, and add
  the design note and the receipt. Nothing else. If a general fact belongs in
  `src/Effect4/Laws/Run.lean`, state it in the battery and propose its move in the receipt.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.
- The shell's rules are in the dispatch message.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.
- A planned goal is allowed only for a statement of the table. Stop a proof that does not
  close in its step, leave its goal planned, and report it.

## Acceptance

1. The four connectors and the consumer are theorems at `[propext, Quot.sound]`, or each
   open one is a planned goal that the receipt lists first.
2. The controls pass, with the red one red.
3. Narrow builds of the two batteries after each step; the default `lake build` once at the
   end, with the gate lines of `Test/All.lean`. `make gen-fixtures` then `git status`: the
   engine's fixtures must not move.
4. Not run, and listed so: `make check-gen`, `check-slow`, `check-corpus`, `check-target`,
   `check-truth`, the conservativity script, `make gen-semantics`.

## The receipt

`docs/research/2026-10-06-seat-CUTS-receipt.md`, short, in the handoff form of `AGENTS.md`:
the one thing to know before merging; base, head and commits; changed files; commands with
results; the statements as compiled, with axioms and `#plan_status`; each difference from
Codex's sketch; what stays open. One paragraph accounts for R1 to R13: what moves (R13 and
R8's replay view), and that every other open part is untouched. Your last message gives the
head, the receipt's path and its first item.
