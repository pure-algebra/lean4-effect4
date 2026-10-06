# 2026-10-06 brief for seat QINV: the Queue model's run invariant on the first profile

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is a small independent proof slice, and it gates no other seat.

## The slice

The Queue's model (`src/Effect4/Laws/Modules/Queue/Model.lean`) runs a list of operations
through `step` and keeps two flags in its `Run`:

- `ok`: after each step the state is `within` its capacity, `tidy`, and `quiet`. `quiet` says
  that no taker stands ready without a signal, and that no peeker waits beside a message
  without one;
- `named`: each step is `accounted`. Every request that waited before the step still waits,
  or is the step's own request, or is named by a signal of the step.

A bounded exploration holds both flags today, with two mutations red. No theorem states them.
They are the model's half of two open parts of the registry: `wait-registration-no-gap` (the
decision to wait and the registration are one transition) and
`waiting-request-obligation-preserved` (a selected request's notification is not lost).

**The goal.** On the first profile, every step keeps both flags, from every state that the
profile admits. So every run of the model from the empty queue has both flags.

## Read first

1. `AGENTS.md`, in full.
2. `src/Effect4/Laws/Modules/Queue/Model.lean`: `State`, `Op`, `Run`, `within`, `tidy`,
   `quiet`, `waiting`, `accounted`, `bump`, `step`, and `Fault`.
3. `src/Effect4/Laws/Modules/Queue/Profile.lean`: `FirstProfile` and its closure, and
   `Capacity.lean` beside it.
4. The batteries that explore the model: `Test/Program/QueueContract.lean` and
   `Test/Program/QueueCapacity.lean`. Find the bounded exploration and its two mutations.
5. `Test/contracts/queue.contract.md`: the model's transitions and the connectors.
6. The registry's open parts under R12 in `generated/semantics.md`.

## The assignment

1. **A short design note first**, `docs/research/2026-10-06-seat-QINV-design.md`: the exact
   statements; the operations that the first profile admits; the invariant that the proof
   needs if the two flags alone are not inductive. Send its path, and go on.
2. **State the step law as a planned goal, placed, and prove it in place.** One statement for
   the state's three properties and one for `accounted`, or one bundle. If `quiet` is not
   inductive by itself, strengthen the invariant and say why. Do not weaken `quiet` or
   `accounted`, and change no definition of the model.
3. **The run law** follows by induction over the list of operations.
4. **Controls**: the two existing mutations stay red, each at its own flag. Add one control
   for each fault of `Fault`: the faulty step breaks the law at a named state.
5. Pin the axioms and the plan status.

A new file is yours: `src/Effect4/Laws/Modules/Queue/Invariant.lean`, with one import in
`src/Effect4/Laws.lean` after the last import of `Effect4.Laws.Modules.Queue`. One battery
is yours too: `Test/Program/QueueInvariant.lean`, with one import in `Test/All.lean` after
`import Test.Program.QueueTraces`.

## Placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| The step law and the run law | `reactive-scheduling`; R12. The model's half of the proposed claims `wait-registration-no-gap` and `waiting-request-obligation-preserved` | the model's `step` on the first profile, for every operation and state of the profile | nothing about a program or the machine; no delivery of a signal; no liveness; no fairness | the run-level law of the Queue's wrapper (decisions row 275, point 2) |

## The rules

- Edit only your two new files, the two root anchors, your design note and your receipt. If
  a general list fact is missing, state it in your module and propose its move in the
  receipt.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.
- The shell's rules are in the dispatch message.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.
  `simp` at `(x == x) = true` for a `Nat` reaches `Classical.choice`: use `decide_eq_true`.
- Take each case list from the definition that the proof is about. Prefer one lemma for each
  predicate, with catch-all alternatives.
- A planned goal is allowed only for the statements of the table. Stop a proof that does not
  close in its step, leave its goal planned, and report it.

## Acceptance

1. The laws are theorems at `[propext, Quot.sound]`, or each open one is a planned goal that
   the receipt lists first.
2. The controls pass, with each red one red.
3. Narrow builds after each step; the default `lake build` once at the end, with the gate
   lines of `Test/All.lean`; `make check-docs`.
4. Not run, and listed so: `make check-gen`, `check-slow`, `check-corpus`, `check-target`,
   `check-truth`, the conservativity script, `make gen-semantics`.

## The receipt

`docs/research/2026-10-06-seat-QINV-receipt.md`, short, in the handoff form of `AGENTS.md`:
the one thing to know before merging; base, head and commits; changed files; commands with
results; the statements as compiled, with axioms and `#plan_status`; the invariant that you
needed and why; what stays open. One paragraph accounts for R1 to R13. Your last message
gives the head, the receipt's path and its first item.
