# Probe: the meaning reads a definition block (PROC-5)

Status: probe note (history, not authority). 2026-10-13. The coordinator, on the owner's word to
start probing the next language slice. Decisions row 373 (1) orders it after the `Live` face (seat
LIVE, running). The design is `docs/research/2026-10-08-seat-PROC-design.md`, sections 4.3 and 8
(goal G5) and slice PROC-5 in its section 9.

## The one thing to know first

The route of the procedures note works on today's tree with no change to it. A program with a
block is given a meaning at a budget: the block's handler `mrecB` unfolds at most `k` nested
invocations, and a deeper one is the frontier. On the battery's three blocks, a budget past the
nesting gives the machine's own exit, a smaller one gives the frontier, and a body that invokes
itself without end gives the frontier at every budget, never a failure.

## What was run

| Command | Result |
| --- | --- |
| `lake env lean` on probe PROC-1, extracted from the design note's appendix A.1 | the four theorems check; `#print axioms` names no axiom for each |
| `lake env lean docs/research/2026-10-13-proc5-probe/Block.lean` | every `#guard` holds; the three `#eval` lines print the frontier table below |

Evidence word: tested, a finite evaluation at fixed budgets.

| Program (from `Test/Program/DefinitionsControls.lean`) | Budgets 0, 1, … | The machine (`Api.run`) |
| --- | --- | --- |
| `twiceProg`, one invocation | frontier, success, success | the same exit at budget 1 |
| `evenOdd 7`, mutual recursion eight deep | frontier at 0 to 7, success from 8 | the same exit at budget 8 |
| `evenOdd 6` | success from 7 | the same exit at budget 7 |
| `spinProg`, recursion without end | frontier at 0 to 19 | `.frontier` |
| a program with no block | success at every budget | — |

## What the probe defines

- `BlockSig table block`: the coproduct `RowsSig table ⊕ₛ RowSig block`. The block's rows are
  `decls.map DefDecl.row`, so an invocation is an operation of `RowSig` on the block, as the design
  says.
- `denoteBlock`: the arms of `denoteRows` (`src/Effect4/Laws/Program/DenoteRows.lean`), and one
  more: `perform (call k) r` is one node of the block's signature, its request evaluated first.
- `denoteDefs table k`: at `.defs decls bodies main _`, `mrecB` over the block, each body read at
  the one variable that is its request; elsewhere `denoteRows`, each leaf finished.
- `meaningDefs`: the meaning under a reply tape, as `meaningRows`.

## The slice, as the probe sizes it

1. **The knot in the law graph.** `mrecStep`, `mrecB`, `Approx` and probe PROC-1's three theorems
   go into a new module beside `DenoteRows`, as written; they check unchanged.
2. **The block's laws in the loop's form.** `IterLimit.lean` states DB-04's laws of a loop as
   convergence: `Conv`, `conv_fixpoint`, `conv_least`, `conv_unique`. G5 takes the same form, so a
   consumer reads one shape for both kinds of recursion:
   - `ConvB`: some budget finishes with the exit and the stores;
   - `convB_unfold`: an invocation converges exactly when its unfolding does, from
     `invoke_cofinal_left` and `invoke_cofinal_right`;
   - `convB_unique`: two finishing budgets agree, from `mrecB_refines` (a finished leaf stays).
     This is the design's owed `mrecB_limit_unique`.
3. **One denotation, not two.** The probe copies `denoteRows`'s fifteen arms. In the tree the arms
   are written once: `denoteRows` becomes the block meaning at the empty block, with an agreement
   theorem for every program that invokes nothing. A copy would need its own agreement proof per
   arm.
4. **The fragment.** `StraightRows` is generated (`tools/Effect4Gen/Fragments.lean`) and maps
   `.defs` and `perform (call k)` to `false`. A fragment `StraightBlock` admits a root block whose
   bodies and main program are `StraightRows` with invocations. The generator's table gains the
   two rows.

Sizes: steps 1 and 2 about three hours; step 3 one to three hours, by how many of H8's proofs
unfold `denoteRows` by name; step 4 one hour. The design's estimate stands, 6 to 8 hours.

## Placement of G5 (AGENTS.md, Trust)

1. Concept `translation-simulation`; a new property, the laws of a recursive handler at the limit
   of its budget chain, beside DB-04's laws of a loop.
2. Question: proposed claims `block-handler-monotone` (pointer `mrecB_refines`) and
   `block-handler-unfolds` (pointers `convB_unfold`, `convB_unique`). Consumers: the block meaning,
   and form (b) of the design's section 4.4 at the meaning.
3. Reach: the free monad over `StoreSig ⊕ RowSig table ⊕ RowSig block`, every budget, one fiber,
   the fragment `StraightBlock`. Rows 30, 41, 310 and 328; DB-04.
4. Does not establish: the frame machine's agreement with the block meaning (G4's, at the machine's
   fuel); termination; any scheduler; definitions with program parameters (row 340, `.invoke`);
   a block's module layers.
5. Unlocks: DI-69's statement with definitions, R10's laws for each definition at the meaning, and
   R2's C2 for a block.

## What this does not establish

The probe is a finite evaluation at fixed budgets on three programs. It proves nothing about the
block meaning beyond probe PROC-1's generic theorems, and it compares with the machine only at the
three exits shown. The machine counts fuel by operations and the block meaning counts nesting
depth. Their relation is G4's, unstated here.
