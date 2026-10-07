# 2026-10-06 slice TABLE: the coordinator's review at the landing

Status: a research note (history, not authority). It is written for the implementer of the next
slices. Decisions row 302. The slice's own notes are its receipt
(`docs/research/2026-10-06-seat-TABLE-receipt.md`) and its design note.

**Verdict: landed, with six changes.** The slice's core holds as it came: `Node.addresses`,
`table`, `refusals`, `refusals_head`, `refusals_nil_iff` and the probe's 15 controls. The
review of slice ORDER was applied in full:

- the design note came first, and it states the choice of the first step;
- every command ran through the Lean slot;
- the receipt names each touched file and gives the statement lists;
- the battery has a namespace, no `#print axioms` line and no restated theorem;
- the frame of an edit is not stated as a goal, since its proof was not in reach.

## What the landing changed, and the rule behind each

1. **The planned goal is a theorem.** The slice proved one direction of `mem_addresses_iff`
   and left the converse as a planned goal. The landing proves it from one general law: the
   path fold collects the yields of the addressed nodes and nothing else
   (`Node.mem_foldList_iff`, `src/Effect4/Laws/Program/PathFold.lean`). The count of planned
   goals stays at 28.
   - **Rule**: a planned goal is the last choice. Before you leave one, state the law one
     level higher and try one constructor in scratch. Here the law for every yield was
     easier than the law for addresses.
   - **How it went**, since the same shapes come again:
     - One step is read back first (`Node.foldList_cases`): a member of a fold is in the
       node's own yield, or in a child's fold. The recursion then goes down `Node.child`,
       by `sizeOf` (`Node.sizeOf_child_lt`, whose case list is `fun_cases Node.child`).
     - `simp only [Node.child]` runs out of heartbeats: the function has 61 equations with
       a catch-all. At a constructor and a literal index, evaluation reduces it at once:
       `conv in (occs := *) Node.child _ _ => all_goals whnf`.
     - `any_goals (exact …)` does not choose between goals. Inside it a term that fails to
       elaborate is logged, and the goal is closed by `sorry`. Read `#print axioms` on a
       scratch proof before you trust such a line.
2. **The slot table had no law.** `Node.extSlotEnv` repeats five lines of the checker in 38
   lines, and it came with one control for five slots. The landing adds the term of a slot
   (`Node.extSlotTerm`) and the law (`hasTy_extSlotEnv`, the claim `term-slot-environment`).
   On a typed node, the slot's term has a type at the slot's environment. The proof is the
   inversion of `HasTy` at three constructors. The five environments were right as they came.
   - **Rule**: a function that restates a part of the checker lands with the law that ties it
     to the judgment. `Node.childEnv` has `NodeHasTy.child_step` for the same reason. A copy
     with no law drifts in silence at the next change of the checker.
   - **Rule**: one control for each case of a table, and a red control for its `none`.
3. **A second name of one type is cut**: `abbrev Entry := Table.Entry`.
   - **Rule**: one name for one thing. A short name in `Effect4.Program` is a claim on that
     word for the whole tree.
4. **One direction of a law is cut**: `mem_addresses_of_at`. The two-way statement holds it,
   and nothing read the direction alone.
5. **Each helper names its claim and its consumer.** The placement tags were there this time.
   The docstrings did not say which claim a helper is a step of, or what reads it
   (`AGENTS.md`, Trust, item 2). The module heads now say what the table is, its three states
   of an entry, its cost, and what it is not.
6. **The battery says what each block shows.** Each group has its colour and its evidence
   kind, as the neighbouring controls have. It has one reader of the new law, at a real
   operation (`Ref.update`).

Two small things more. `Node.addresses` wrote one function 49 times, and it is one local
function now. An import went with the goal.

## One obligation that the slice hands on

The environment of an operation's own term repeats one line of `bindTerm`
(`src/Effect4/Program/Typing/Rules.lean`): the instance of the parameter at the request's
bindings. `hasTy_extSlotEnv` holds the two together today. Slice MATCH rewrites that match.
It must give both one function of the bindings, so that the slot table calls what the row
check calls (row 302, point 5).

## What changed in the gates

The goal gate pins the count of declarations that rest on a planned goal: 12
(`restingPin`, `Test/Audit/AxiomGate.lean`; row 302, point 10). A slice that moves the count
moves the pin, and its receipt says why. `lake build Test` refuses another count.

## Process

- **A bigger chunk comes next.** `docs/research/2026-10-06-chunk-2-brief.md` maps it: the
  order of the slices, what each owes, where to stop, and how to hand back.
- **Keep the hand-back form.** This one had every part. It gave the one thing to know first,
  the files, the statements, the commands with their results, the gate's counts and the open
  obligations.
- **Say what you did not prove, as you did.** The receipt named the open converse plainly.
  That let the landing spend its time on the proof and not on finding the gap.
