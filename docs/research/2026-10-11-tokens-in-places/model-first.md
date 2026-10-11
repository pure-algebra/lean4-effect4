# Model first: the minimal representation of each structure (2026-10-11)

The owner, 2026-10-11: "we can keep pushing and using the math structure to consolidate code simply
by reasoning about what the math model indicates the minimal representations should be… then we
determine what additional functionality we need for functional language and api semantics."

This note records the loop and its current census. Claude updates the census at each scouting pass.

## The loop

1. **Name the structure.** Find the mathematical object that a family of code is about, with its
   literature.
2. **State the minimal representation.** One carrier and its laws. A second carrier stands only
   with an exact embedding into the first.
3. **Census the tree.** List every hand copy of the structure: each private traversal, ledger, sum
   or lift that restates it.
4. **Consolidate.** Each copy becomes an instance: first a connector, then the callers move, then
   the copy goes.
5. **Measure.** The merge tick's audit (`../2026-10-11-machine-models/AUDIT.md`): shared-law uses
   rise, private case analyses fall.
6. **Read the gaps.** Where the minimal model needs something that the program language or the API
   cannot express, that is the next language or API work. The model sets the work list.

## The census

| Structure | Mathematical object | Minimal representation | Status |
| --- | --- | --- | --- |
| program syntax | the free object of a signature | `Eff`, with its generated algebra and fold | landed |
| code weight | a fold into `(ℕ, +)`: potential on program syntax | the generated `Machine/Fold.lean` with a `PrimWeights` table | landed (L3) |
| fiber table | a finite map; a separating sum | `FiberSum`: the owner and the rest | landed |
| accounting | a place invariant; amortised potential | `StackLedger`, then the place ledger (P1) | stacks landed; code and data places wait for R2 |
| one evaluation | a labelled transition system with a balance law | `TracedMoves` (L2) | in progress |
| edits of other fibers | a monoid action; a trace with an independence relation | the `FiberEdit` list (R2) | foundation landed; migration in progress |
| interference | Owicki–Gries non-interference | `Interferes`, `FramesFollow` | landed |
| regions | the frame rule on stacks; scoped operations | `StackRegion`, `MaskBracket` | landed; the context region becomes an instance (F1) |
| the store | a key-indexed heap, one kernel per row, the frame rule per key | `RefKernel` | heap step landed; the machine-step lift waits on labels (below) |
| schedules | independence and commutation | DET-1 to DET-5 | landed |
| fresh names | an append-only supply; minting extends a world by a fresh pair | `AppendOnly`, `FreshSupply` (L4 to L6); `World.PBij.extend` (`../2026-10-11-handles/`) | open |
| handles | names; a world as a partial bijection of names; agreement as a fold; Reynolds' abstraction theorem | one name sort, one world, `Rel` per free object (`../2026-10-11-handles/README.md`) | probe checked on `Store.Val`; Codex item 11 |
| machine edits | a monoid of one-field writes; the frame rule per field | `Edit` with sixteen tags and one footprint `writes` | Codex's draft has the sixteen tags; item 10 |
| pointwise list relations | the relator of `List` | one `ListRel` | two copies: `ListRel` (`Laws/Machine/Book.lean`), `Pointwise` (`Laws/Step/Reading.lean`) |
| scene changes | a change structure: `a ⊕ (b ⊖ a) = b`; the live view as a fold's derivative | one keyed `Delta`; `Motion.Join` and `Retained.Patch` as readings (`../2026-10-11-view-model/README.md`) | three change types today |
| motion | a timing of a change, sampled; two folds (frames, CSS) agreeing by laws | row 354's motion value over `Delta` | per-kind samplers; slice D3 open |
| sessions | a Mealy machine: `open`, `feed`, `view`; replay as a monoid action | one session interface; row 326's `Live` face as an instance | `EditSession` and `HostSession` differ in shape |
| bound names in authoring | scope safety; a unary relation over the elaboration monad | one scoped lemma per elaboration primitive | generated: `Lifts`, `Atoms`, `Forms` and `Rows` under `Laws/Program/Authoring/` come from `tools/Effect4Gen`; no hand copies |
| names and codecs | an exact embedding | write–read pairs with retraction and exactness | landed per codec |
| refusals | a located refusal complete against its judgment | `explain` with `explain = none ↔ valid` | landed |
| a fiber's life, the interrupt state | a sum type each | one inductive each (R4, R5) | open |

**The store lift goes through the labels.** A label of `TracedMoves` records the code that a step
ran (`MoveKind.step input`). A store step's code is `sync (op o)`, so the cell it writes is
`o.refKernel`'s cell. The cells that a word writes are then a homomorphism from the label monoid to
`(Finset RefKey, ∪)`. With the heap frame rule (`RefKernel.refWriteBack_peek_other`), a cell
outside that set keeps its value across the iteration. This is P2 of `README.md`. It needs one
machine-side law: the iteration's store is the fold of its executed operations over the store
before.

## The gaps the model shows so far

Each item is a capability that the minimal model needs and that the language or the API lacks.

| Gap | What the model needs | Where it lands |
| --- | --- | --- |
| progress | a fairness assumption on the scheduler, stated as data, so that a potential bounds rounds | the scheduler's decision tape; a liveness claim form |
| confinement | a reference as a capability whose holders the census can bound | modelled: a parametric step creates no reference but a minted one, and the support is the holder census (`../2026-10-11-handles/README.md` §6) |
| context | a typed context reader and a providing region | rc.112's `context` and `provideContext` (row 349, in progress) |
| fresh names | one supply for ids, keys and tokens | L4 to L6; every counter is a name supply (`../2026-10-11-handles/README.md` §6) |
| regions | a scope's handles stay out of its result, and no step uses a closed scope's handle | a region form in the authoring surface, checked by the support; `../2026-10-11-handles/README.md` §6 |
| typed handles | a name with a type in the world | the API's `Ref`, `Deferred`, `Fiber` and `Scope`; the typed world of item 11 step 5 |

This list grows with each census pass. It is the input to the language and API work after the
consolidation.
