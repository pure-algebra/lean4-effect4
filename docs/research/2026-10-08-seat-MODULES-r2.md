# 2026-10-08 seat MODULES, revision 2: the design after Codex's review

Status: a revision with two new probes and a fixed runner, for the next review round. It revises
`docs/research/2026-10-08-seat-MODULES-design.md` (`29f369ca`) after Codex's review
`docs/research/2026-10-08-modules-review.md` (`37c1dea4`). Base: `7dee92b4`, the merge of
`codex/module-authoring` (`eff_module`). This note changes no decisions row. Its new files are in
`docs/research/2026-10-08-seat-MODULES-r2/`, and the reviewed packet stays unchanged.

## 1. The one thing to know first

Every finding of the review holds. Each control reproduces in the main checkout: the review's
command (`review.py`) passes all its checks there.

Four parts of the design change:

1. **The step language is first-order data.** Sorts, schemas and field references are data, and
   every interpretation is a fold outside the authoring syntax (MODS-9). The read law, the write law, the
   frame law and `Step.sound` are each proved once. The sorts become the schema plane's own `Ty`
   (the owner, 2026-10-08; §4).
2. **Compatibility is four separate rows**, never one inclusion: shared-model conformance,
   directed inclusion, equal observations on the pin, and signed differences (§5).
3. **Operation kinds become protocol components** with declared premises (F6, §6).
4. **The run law waits on two rulings.** Latch's wake batch is an observable difference (F3), and
   a private helper's fiber identity is an observable effect (F4). Both are owner questions
   (§8). A coalescing Latch matches Effect's batch on the review's client (MODS-10).

## 2. The findings, checked here

| Finding | What the review showed | Checked in the main checkout | What changes |
| --- | --- | --- | --- |
| F1 functions in the tree | `Field.get`, `Field.set` and `Enc.enc` live in the step syntax | yes, by reading `StepText.lean` | sorts and fields as data; interpretations outside (MODS-9) |
| F2 the frame claim is false | an encoding may drop a field, and a writer may change it unseen (`StepFrame.lean`) | yes, `review.py` | writes derived from the schema; records encoded with every field; the frame law proved for update spines (MODS-9) |
| F3 the wake batch is observable | the batch client answers `[1,9,2]` over ours and `[1,2,9]` over Effect's Latch | yes, `review.py` and `native.py` | a candidate difference row; an owner question |
| F4 helper fibers are observable | a later fiber's identifier is `2` over the library and `3` over the spinner model; a client turns it into a Boolean | yes, `review.py` | the run law's client fragment and model change; an owner question |
| F5 the tools hide failures | the search drops refusals and frontiers; the runner exits 0 on a wrong result and on a crash | yes, `review.py` | `native.py` classifies and fails (§5); the search driver is a slice |
| F6 kinds and answerers are thin | a host row and a definition of one name answer differently; kinds omit protocol distinctions | yes, `review.py` (the answerer controls) | protocol components; answer tables as a separate connector slice |
| F7 the card is a prototype | its tree comes from the earlier carrier, two steps are by hand, statuses are strings | yes, by reading `StepText.lean` | the card's step fields come from the one tree (MODS-9); statuses join their owners |

## 3. The step language as data (MODS-9)

`docs/research/2026-10-08-seat-MODULES-r2/StepData.lean` compiles with no error and no warning.

**The syntax holds no function.** Three inductive types carry it:

- `Sy`: the sorts. A schema is a sort built from `nil` and `field name sort rest`.
- `FieldRef fs s`: a field of a schema, by position.
- `Step ι s`: the steps over one input. The constructors are `input`, `bool`, `ite`, `pair`,
  `get`, `set` and `emptyLike`.

**The interpretations are folds outside it:**

| Fold | Answer |
| --- | --- |
| `Sy.I` | the Lean meaning of a sort |
| `Sy.encE` | a value's encoding, and a record's fields with their encodings: one structural fold |
| `FieldRef.get`, `FieldRef.set` | the derived read and write of a field; no author supplies them |
| `Step.term`, `Step.eval` | the library's term, and the model's value |
| `Step.writes`, `Step.json` | the fields that the updates name, and the tree as JSON |
| `Step.wf`, `Step.spine` | decidable checks: every schema canonical; the result is an update spine |

**The laws are proved once**, each at `[propext, Quot.sound]`:

| Theorem | Statement |
| --- | --- |
| `read_law` | on a canonical schema, `Machine.Record.read` of a field reads the derived read's encoding |
| `write_law` | on a canonical schema, `Machine.Record.set` of a field writes the derived write's encoding |
| `frame_law` | on an update spine, a field that no update names keeps its value |
| `Step.sound` | every well-formed step's term reads its model's value, from the input's reading alone |

The read and write laws reuse the field-order laws of `src/Effect4/Data/FieldOrder.lean`
(`canonBy_ascending`, `firstOf_canonBy`, `ascending_ext`) and `entries_frame`
(`src/Effect4/Laws/Schema/Codec.lean`). A schema is canonical when its names ascend by their
bytes, a decidable check.

**At Latch.** `release` is a value of `Step`. Its writes are `["waiters"]`, and its term is
MODS-1's hand term (with `pair` for the inner reply). Two results hold at it:

- the frame law gives "a release keeps `open`" with no proof of its own;
- the fault "release opens" names `open`, so the frame law does not apply to it.

**What MODS-9 does not cover.** Lists beyond `emptyLike`, numbers, identities and their tables,
optional fields, and the typing of a step's term. §4 takes these from the schema plane.

## 4. The sorts are the schema plane's (the owner, 2026-10-08)

The owner's steer: the module plane reuses the schema plane. The cell's types are `Ty`. The
Lean carriers and the encodings come from the schema plane's exact embeddings. TypeScript utility
types and conversion functions are generated from the same declaration. Every field and data type
is covered, and each obligation is discharged once, by a fold. A survey of the tree found the
parts below.

**What exists and is reused:**

| Part | Declarations | Path |
| --- | --- | --- |
| the sort: `Ty`, its generated algebra and fold | `TyAlgebra`, `cata_ty`, `hom_eq_cata_ty`, `TyAlgebra.prod`, `cata_fusion_ty`, `fold_of` | `src/Effect4/Program/Fold.lean`, `TyFoldExtras.lean`, `FoldOf.lean` |
| the normal form and record rules | `CTy`, `Ty.canon`, `Record.fieldOf`, `Record.setOf` | `src/Effect4/Program/Ty.lean`, `src/Effect4/Program/Record.lean` |
| membership of a value in a type | `Val.hasTy`, `Fits`, `fits_record`, `namedFit_lookup`, `namedFit_of_sublist_lookup` | `src/Effect4/Program/Typed.lean`, `src/Effect4/Laws/Program/Typed/Membership.lean`, `RecordValues.lean` |
| typing of record operations | `record_frame_fits`, `record_set_fits`, `record_fieldOf_fits` | `src/Effect4/Laws/Program/Typed/RecordOperations.lean` |
| an exact embedding of a Lean type | `Store.Image` (`ofVal_toVal`, `ofVal_exact`) with `nat`, `bool`, `string`, `option`, `list`, `pair`, `sum`, `except`, `equiv` | `src/Effect4/Store/Carrier/Image.lean` |
| an embedding with its type | `ValueModel`: an `Image`, a `CTy`, and every encoded value has that type | `src/Effect4/Laws/Program/ValueModel.lean` |
| the typing of a step's term | `types_field`, `types_recordSet`, `types_record` | `src/Effect4/Laws/Modules/Checking.lean` |
| a TypeScript type for any `Ty` | `Types.ofTy` | `src/Effect4/Codegen/Types.lean` |
| an Effect Schema value for any `Ty` | `Ty.schema` (a fold), `ofSchema_schema`, then the raw generator `moduleSyntax` | `src/Effect4/Schema/Bridge.lean`, `src/Effect4/Codegen/Schema.lean` |
| a JSON codec with laws | `Codec.encode`, `Codec.decode`, `decode_encode`, `encode_injective` | `src/Effect4/Schema/Codec.lean`, `src/Effect4/Laws/Schema/Codec.lean` |

**What is missing, and is now proved in MODS-9:**

- the laws of a field read after a write on `Machine.Record` frames: MODS-9's `read_law` and
  `write_law` on canonical frames, and `get_set_other` beneath the frame law;
- a record combinator for `Image` and `ValueModel` on `Machine.Record.frame`: its encoding is
  MODS-9's `Sy.encE` record arm, and its laws are the two above.

**What is missing, and stays open:**

- a fold from `Ty` into Lean types, so that every `Ty` has a carrier: no `TyAlgebra` into `Type`
  is defined;
- a deriving handler that relates an author's Lean structure to the record carrier. Only the
  external generator `effect4gen` exists. `Image.equiv` transports exactness along such a pair;
- an encoding context for identities (handles, references, deferred results): Codex's Q3. Each
  role has its own encoding through its table, and `Table.Injective` stays a premise;
- a TypeScript codec with a law. The generated Effect Schema code has no decoded-value law
  (`Test/contracts/schema-typescript-generation.contract.md`), and the TypeScript execution
  boundary stays at R8 and DI-49.

**The design, revised.** The step language's sorts are `CTy`: data, in the tree's normal form.
Its interpretations are folds over `Ty`:

| Fold | From | Gives |
| --- | --- | --- |
| the carrier fold | `Ty` | a `ValueModel` for each supported constructor: Lean carrier, exact embedding, membership |
| the term fold | a step | its term (MODS-9's `Step.term`) |
| the model fold | a step | its value in the carrier (MODS-9's `Step.eval`) |
| the type fold | a step | its typing, from `types_field`, `types_recordSet` and `types_record` |
| the TypeScript fold | the cell's `Ty` | the utility types (`Types.ofTy`) and the Effect Schema declaration (`Ty.schema`) |

**"Any field, any data type" becomes one theorem for each arm of the carrier fold.** The fold covers
`never`, `unit`, `nat`, `int`, `string`, `bool`, `option`, `list`, `prod`, `except`, `union`,
`lit` and `record`. Identity types (`handle`, `refOf`, `deferredOf`, `fiberOf`) take the
encoding context. `var` and `unknown` have no carrier, and the fold refuses them by name. Each arm
states three things: the embedding is exact, every encoded value has the arm's type, and the arm
is a fold step. So a cell of any supported type gets its laws by the fold, with no proof of its
own.

## 5. Compatibility as four rows

The review's set control holds: `{1}` and `{2}` both lie inside `{1,2}`, and they are not equal.
So shared-model inclusion never grades compatibility alone. The card keeps four rows for each
module and profile, each with its own evidence kind:

| Row | Statement | Evidence today |
| --- | --- | --- |
| shared-model conformance | our runs lie inside the model's runs | tested, bounded; a theorem after the run law |
| directed inclusion | Effect's runs lie inside the model's runs | tested, on the pin, one schedule |
| equal observations | our observation equals Effect's, client by client | tested, on the pin, one schedule |
| signed differences | each unequal observation is predicted exactly by a ruled row | data, joined both ways |

**The native runner** (`docs/research/2026-10-08-seat-MODULES-r2/native.py`) replaces the
reviewed `pin/run.sh`:

- It type-checks every client's printed TypeScript with the pinned tsgo, then runs it on the pin.
- It classifies each client as pass, signed, candidate, counterexample or refused.
- A difference row (`differences.json`) predicts an exact pair of results. A signed row needs a
  ruling.
- It exits 1 on a refusal, 2 on a candidate or a counterexample, and 0 otherwise.
- `--self-test` shows a wrong result, a crash and an unruled difference each reported.

Its run on 2026-10-08 (Effect `4.0.0-rc.112`, tsgo `7.0.0-dev.20260629.1`, bun `1.4.2`):

| Client | Ours | Effect's | Outcome |
| --- | --- | --- | --- |
| d1 | `[3,1,2]` | `[3,1,2]` | pass |
| d2 | `[3,1,2]` | `[3,1,2]` | pass |
| d3 | `[true,[3]]` | `[true,[3]]` | pass |
| batch (the review's) | `[1,9,2]` | `[1,2,9]` | candidate: `latch.wake-batch`, no ruling |
| batch over the coalescing Latch (MODS-10) | `[1,2,9]` | `[1,2,9]` | pass |

The runner exits 2, because the original library's batch row has no ruling. It stays red until
the owner rules (§8, question 2).

## 6. Protocol components, not kinds

The review's table names what the kinds of revision 1 omit. The revision takes it as the input
of a design slice:

| Component | What it fixes | Present in |
| --- | --- | --- |
| waiting mode | a wake that carries an answer, or a wake that asks for a retry | Queue's take; Semaphore's take |
| commit point | where a request's effect happens: at the taker's step or at the waker's | Queue; Pool |
| withdrawal | what an interrupted waiter removes, and what it still owes | Queue's withdrawal that owes notifications |
| selection | who is woken, and when it is chosen: at the wake or when the helper runs | Semaphore's walk; Pool's counted group |
| delivery and coalescing | one helper for each waiter, one walk, or one pending batch | Semaphore; Pool; rc.112's Latch |
| scoped construction and cleanup | acquisitions, failure, scope registration, ordered release | Pool's make and close; `protectedBy` |

Each component carries its own premises, and each module states the laws its policy keeps. No
producer is forced through one `wakes step` and `postAll`.

## 7. The run half

F4 changes the run law's shape. The spinner model allocates fibers that the library does not.
So a client that reads a fiber's identifier tells the two apart, with no read of the latch. A
renaming of identities in the final observation cannot repair it, because the client computes
on the identifier.

The revision takes the review's recommendation:

- **The first run law covers a checked, restricted client fragment.** Its contract names the
  excluded observations: fiber identities, interruption causes, supervision, clocks and
  scheduling.
- **The model for the run contract is an abstract transition model.** It has no runnable spinner,
  like `Semaphore.Model` (`src/Effect4/Laws/Modules/Semaphore/Model.lean`). The spinner stays as a
  finite exploration filling under a declared observation.
- **The budget-quiet premise stays explicit.** The review corrects revision 1's G6: fuel 2000 sits
  below the operation budget 2048, and more command fuel does not prevent an operation-budget
  yield. Each finite result keeps its measured trace predicate.

## 8. Questions for the owner

Each is a choice of meaning, domain or representation.

1. **The step language over the schema plane.** The steps of a module are first-order data over
   the existing `Ty`, a new sort with its signature. Its interpretations and their laws come from
   the schema plane (§4). Recommended: yes.
2. **Latch's wake batch.** Effect's Latch resumes every waiter in one pending batch, and ours posts
   one helper for each waiter. Either match the batch, a coalescing component of §6, or sign the
   difference with its witness. Recommended: match the batch. MODS-10
   (`docs/research/2026-10-08-seat-MODULES-r2/BatchLatch.lean`) adds `pending` and `scheduled`
   to the cell and one flush helper. The batch client then answers `[1,2,9]` on the Lean machine
   and on rc.112, as Effect's Latch does, and d1 and d3 keep their answers.
3. **Row 329's client fragment.** The run law covers a checked client fragment that excludes
   identity, interruption-cause, supervision, clock and scheduling observations. Its model is an
   abstract transition model. Recommended: yes, with unrestricted clients kept as a later
   contract.
4. **What compatibility means.** Four rows, each with its own evidence (§5), never one grade.
   Recommended: yes.

## 9. Slices, in the review's order

| Slice | What lands | Depends on |
| --- | --- | --- |
| R0 | the review's counterexamples as register lines | none |
| R1 | the step signature over `Ty`, field identities and the interpretation context, frozen as one contract | question 1 |
| R2 | cell deriving and typed step authoring, from the schema plane | R1 |
| R3 | the laws once: encoded agreement, the frame law and typing | R1 |
| R4 | one Semaphore step (`takeIfAvailableStep`) migrated, with connectors to its term, model, reading and typing laws | R2, R3 |
| R5 | protocol components and binding contracts | questions 2 and 3 |
| R6 | the search driver in `tools/Conform`: refusals, frontiers, budgets and tapes kept | none |
| R7 | the module card joined to the semantics registry, the plan and `Conform.Report` | R6 |
| R8 | Latch integrated, after the batch ruling | R4, R5, R7 |

R0 and R6 can start at once. R1 waits for question 1.

## 10. What this does not establish

- MODS-9 covers seven constructors and Boolean, number, list, pair and record sorts. Identities,
  tables, optional fields and typing are outside it. The carrier fold over `Ty` (§4) is a design,
  not a probe.
- MODS-10 runs three clients on the Lean machine and one on rc.112. It states no law of the
  coalescing component.
- The frame law covers update spines only. A record read out of a field is outside it.
- The native runner checks four clients, one schedule each, on one pin. It establishes no target
  execution theorem (R8, DI-49).
- No run law. Questions 2 and 3 precede it.

## 11. Reproduce

Run from the repository root:

```sh
scratch/lean-slot.sh lake env lean docs/research/2026-10-08-seat-MODULES-r2/StepData.lean
scratch/lean-slot.sh lake env lean docs/research/2026-10-08-seat-MODULES-r2/BatchLatch.lean
python3 docs/research/2026-10-08-seat-MODULES-r2/native.py
python3 docs/research/2026-10-08-seat-MODULES-r2/native.py --self-test
scratch/lean-slot.sh python3 docs/research/2026-10-08-modules-review/review.py
```

`native.py` exits 2 while the batch difference has no ruling. `review.py` rewrites its
`results.json`; restore the committed one after the run.
