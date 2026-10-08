# Claude overwatch 01: Codex's fold and construction slice

Codex lands the slice that `docs/research/2026-10-08-seat-module-gaps-plan.md` plans, on its
branches. This note reviews it while it lands, for the owner to relay. The design is right. Six
findings follow, ranked; the first three cost the most later.

## Reviewed state

- Branch `codex/module-folds` at `c88f9bbf` (2026-10-08 16:19), the furthest branch.
- The uncommitted Semaphore work on `codex/module-semaphore` and Pool work on
  `codex/module-pool-data`, read at 16:10.
- Evidence kind: a reading of the source. No build ran here, since Codex's builds ran in those
  trees.

## What is right

- `Step.fold` translates to the machine's own list fold (`Term.fold`,
  `src/Effect4/Machine/Term.lean`, row 228). No new term form enters.
- A captured caller input resolves at its own scope and moves past the two fold binders by
  `Term.weaken`. Nested folds repeat the same operation on term data.
- A premise appears only where a step uses it: scope alignment where a fold occurs, the identity
  capability where a comparison occurs. Every existing module statement keeps its hypotheses.
- The identity comparison is a capability (`DeferredIdentity`). The opaque interpretation gets no
  comparison law, as slice L6 plans.
- The public terms become definitions from the data, for example
  `takeStep := Data.take.term …`. So the hand terms leave the tree.

## Findings

| ID | Finding | Evidence | Fix |
| --- | --- | --- | --- |
| CW-01 | Fold bodies and input lists select inputs by position again, the OW-03 class | see below | named inputs and binders |
| CW-02 | The reading and typing laws repeat one premise argument in each case | 88 copies at `19fd85df`, 47 more uncommitted | one premise fold per condition |
| CW-03 | The same folds are written again in each module, each with its own value equation | three removals, two `any` folds, two maps | a library of derived steps |
| CW-04 | No step consumes an option | `headStamp` folds to read a head | an option eliminator, or `headOr` in the library |
| CW-05 | `tuple3` adds one constructor for one arity | `Step.tuple3` in `47c59386` | an n-ary tuple, then named reply records |
| CW-06 | Commits are copied across five branches under different hashes | the branch logs | one linear branch for the landing |

### CW-01: positions select inputs

A fold body reads the accumulator at `.var (.here _ _)` and the element at
`.var (.there _ (.here _ _))`. An outer input sits two positions further down. An input list
names its inputs by position too. The type index refuses an input of another type. It accepts a
swap of two inputs of one type.

- `Data.awaitLatch` (`src/Effect4/Modules/Latch/Registration.lean`, `4c5caaae`) writes
  `id := .var (.here _ _)` and `hint := .var (.there _ (.here _ _))`. Both inputs have type
  `idTy`.
- Semaphore's `Data.take` (uncommitted) has `takeId` and `takeHint`, both of type `idTy`.
- Pool's branch defines a helper `under` for the outer positions. Semaphore's branch does not.

Fix: write a step with named inputs and named fold binders. The elaborator writes the same
positional data, as `field_ref%` does for fields. A sketch of the notation:

```lean
step% (need : .nat) (id : idTy) (hint : idTy) (cell : cellTy) : .prod .bool cellTy := …
fold% xs from init with acc w => …
```

The elaborator refuses an unknown name and a shadowed name. The stored data stays positional, so
every law applies unchanged.

### CW-02: one premise argument per case

`sound_core` and `typed_core` (`src/Effect4/Laws/Modules/Step.lean`) pass each child the
parent's premise through `scope_mono hs (by intro hb; simp only […] at hb ⊢; aesop)`. The file
holds 88 such copies at `19fd85df`. The uncommitted identity premise adds 47 copies of
`identity_mono`. Each copy runs its own search.

Fix: state each condition as a proposition built by a fold of the step, as `Step.Facts` is:

- the scope condition is `P` at a fold node, and the conjunction of the children elsewhere;
- the identity condition is `Q` at a comparison node, and the conjunction of the children
  elsewhere.

Each case then splits a conjunction, as it already splits the check. A fold body's scope
condition follows from the extended alignment by `scope_of_alignment`. The default proof
`by trivial` still closes both conditions on a step with no fold and no comparison.

### CW-03: derived folds per module

| Shape | Definitions | Meaning |
| --- | --- | --- |
| remove every match | `Semaphore.Data.remove`, `Pool.Data.removed` | drop each entry with the identity |
| remove the first match | `Latch.Data.removeFirst` | drop the first entry, and say whether one matched |
| any | `Pool.Data.heldBy`, `Pool.Data.outstanding` | a disjunction over the list |
| map | `Pool.Data.marked`, `Pool.Data.freed` | one entry out for each entry in |
| head or default | `Pool.Data.headStamp` | the first entry, or a constant |

Each definition needs its own value equation in its module's connector. Fix: put the shapes in
one library of derived steps (`filter`, `map`, `any`, `removeAll`, `removeFirst`, `headOr`). Prove
each shape's value equation once, for example that `removeAll`'s value filters the list's value.
The reading and typing laws already cover every derived step, since a derived step is a step.
A module's value equation then becomes rewriting.

The choice between the first match and every match is a fact of each module's model. Each use
cites the model's choice.

### CW-04: no option eliminator

`Pool.Data.headStamp` folds over `take available 1` from `0` to read "the head, or 0". `Step.head`
answers an option, and no constructor consumes one. Fix: add an eliminator if the native atoms
have one. Otherwise keep the fold as `headOr` in the library of CW-03, so no module repeats it.

### CW-05: one constructor per arity

`Step.tuple2` answers `.prod a b`, and `Step.tuple3` answers `.tuple [a, b, c]`. Both translate to
the builder `tuple`. Fix: one n-ary tuple over a typed item list, shaped like `StepFields`. Its
result type is then one rule. Queue's take reply needs three items, and a later reply may need
four.

The longer fix is named reply records for each wrapper shape. The owner's design discussion of
2026-10-08 proposes them: the wrapper then reads `result`, `resolve` and `wake` by name.

### CW-06: one landing branch

The same commit messages appear on five branches under different hashes. `codex/module-folds`
edits the three root files. `codex/queue-step-data` changes `src/Effect4/Schema/Modeled.lean`
and `src/Effect4/Store/Carrier/Image/Containers.lean`. Land one linear branch, and leave the roots
and the semantics registry to the merge.

## Not established here

This note reports a reading of the source at the stated commits. It states no build result, no
axiom result and no host result.
