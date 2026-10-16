# Recursive types: a probe, `deriving Modeled`, and the service and lowering seams

Status: research note (history, not authority). Base: `2c52f2756` on `refactor/phase1-phase3`.
Role: the coordinator's probe, at the owner's request of 2026-10-15, after decisions row 400
unparked recursive types. The probes are `probes/Recursive.lean` (Lean) and `probes/oracle/`
(rc.112 and tsgo). Two read-only surveys supplied §5 and §6.

## 1. The one thing to know first

Recursive types fit the tree with no new `Ty` constructor, and every face except one already has
its syntax. The probe shows each judgment on the real `Ty` and `Val`:

- membership unfolds a declared name at a value and recurses on the value;
- a guardedness check refuses a name that reaches itself without a value constructor;
- inhabitance is a least fixed point over the table;
- a recursive Lean inductive gets an exact `Image` by structural recursion, with both laws proved.

rc.112 decodes, persists and revives the recursive Schema. tsgo accepts the Lean printer's TypeScript
aliases after two repairs that the probe found (§3.4).

The services question has a different answer. Lean data types and service interfaces are two
declarations today, not one (§5).

## 2. Question and evidence

The questions:
- How are recursive types modeled, and is the landing small?
- What does `deriving Modeled` do, and what does recursion add to it?
- Do Lean-modeled types surface as Effect services, read and generated?
- What lowering work is open for PubSub and the stateful modules?

The evidence:
- `probes/Recursive.lean`, a finite probe (tested), output in `probes/recursive.log`;
- `probes/oracle/schema.ts` on rc.112 under bun 1.4.2, output in `probes/oracle/schema.log`;
- `probes/oracle/faces.ts`, `expr.ts` and `json-fix.ts` under tsgo 7.0.0-dev.20260629.1, output
  in `probes/oracle/tsgo.log`;
- two read-only surveys of the tree, with their claims spot-checked (§5, §6).

## 3. Recursive types

### 3.1 The representation

A **declaration table** `Δ` holds the application's type declarations, each a name and a body. A
body refers to a declaration, itself included, as `Ty.app name []`. This is row 158's nominal
reference and row 124's sketch. The probe's tables:

| Table | Declarations | Guarded | Inhabited |
| --- | --- | --- | --- |
| `treeDecls` | `Tree = {_tag: "leaf"} \| {_tag: "node", children: Tree[], label: string}` | yes | `Tree` |
| `listDecls` | `IntList = {_tag: "nil"} \| {_tag: "cons", head: Int, tail: IntList}` | yes | `IntList` |
| `jsonDecls` | `Json = null \| bool \| Num \| string \| Json[] \| map<string, Json>` | yes | `Json` |
| `mutualDecls` | `Expr` and `Stmt`, each holding the other | yes | both |
| `streamDecls` | `Stream = {head: nat, next: Stream}` | yes | none |
| `selfDecls` | `A = A` | no | none |
| `headDecls` | `B = B \| string` | no | — |
| `cycleDecls` | `C = D \| nat`, `D = C \| string` | no | — |

Monomorphic declarations come first. Parameters (`List<T>`) are the second step, and they need
regular recursion: a recursive occurrence takes the declaration's own parameters.

### 3.2 Membership

`fitsIn` is `Val.hasTy` with the table carried into every child. A declared name unfolds to its
body. A budget counts the names that may unfold before the next value constructor, and each value
constructor restores it to `Δ.length`. So the recursion is on the value, as the store's
`ShapeDoc.acceptsAt` already does for named shapes (`src/Effect4/Store/Domain/Shape.lean`).

Measured: the tree, the integer list, the expression and the JSON samples fit. The bad tree (a
string deep inside) and the bad list are refused. A value of the stream type would be infinite, so
the finite cut is refused. `A = A` admits nothing, and `B = B | string` admits the strings.

The probe takes fuel, and twice the fuel changes no answer on any sample. The landing's checker is
well founded on the value's size, then the budget, then the type's size. No fuel enters the core.

The proposition `Fits` gains one constructor: a value fits `app n []` when it fits `n`'s body. An
inductive predicate is a least fixed point by definition, so it needs no termination argument.

### 3.3 Guardedness, inhabitance and subtyping

- **Guardedness.** No declaration reaches itself through unions and names alone (`guarded`).
  Every cycle then passes a value constructor. The probe refuses `A = A`, `B = B | string` and the
  `C`/`D` cycle. The table's admission refuses an unguarded table by the name on its cycle, as
  row 398 (4) refuses a recursive document today.
- **Inhabitance.** It is the least fixed point, by iteration from no name known
  (`inhabitedNames`). `Stream` is uninhabited, since every value needs a further value.
- **Subtyping.** It stays nominal, as row 124 sketches: `app n` is below `app n` alone, with
  declared variances for arguments (`src/Effect4/Program/TyVariance.lean` reads rc.112's own).
  The probe does not exercise it. Structural subtyping between recursive types, as TypeScript does
  it, is not proposed.

### 3.4 The faces

| Face | What the probe shows | Status |
| --- | --- | --- |
| Membership and the wire | `Val` is already a finite tree, so a recursive value needs no new frame | ready |
| Schema (rc.112) | rc.112 persists `{representation: Reference "Tree", references: {Tree: …}}`, the inner occurrence as `Suspend {thunk: Reference "Tree"}`; it decodes the tree, refuses the bad tree, and does both again after a JSON round trip and revival | ready: `Representation` has `reference` and `suspend`, and `Schema/Document.lean` has the references table |
| TypeScript | tsgo accepts `Tree` and `IntList`, types their samples, and refuses both red values | ready, with two repairs below |
| OCaml | a program value is a `Val` on the engine, and the engine's membership is lowered from Lean | ready: no OCaml type is needed |
| Lean data | `Tree.image`, an exact `Image` written by structural recursion; both laws proved by induction | the deriver's new output (§4) |

The two TypeScript repairs, each measured:

1. **The map spelling.** `Readonly<Record<string, Json>>` makes tsgo refuse `Json` with TS2456
   ("circularly references itself"). A generic alias expands at once. The index signature
   `{ readonly [key: string]: Json }` is deferred and accepted. The two spellings assign to each
   other where nothing recurses (`json-fix.ts`).
2. **The class rule.** Row 120 prints a tagged record whose fields are payload types as its class
   name. In `Expr`, `{_tag: "lit", value: nat}` printed as `lit`, which nothing declares (TS2304).
   `leaf` and `node` escaped the rule only by accident. A declaration body must print its records
   as object types, or the declaration chooses its classes explicitly.

### 3.5 What the landing changes

1. The table: a field of the world beside the allocation table, written by the authoring surface
   and carried in `Built`.
2. `Fits`: one constructor. `Val.hasTy`: the budget and the measure of §3.2. The agreement
   theorem between them gains one case.
3. Formation of the table: guardedness, and every name in a body declared.
4. Inhabitance: the least fixed point. Subtyping: unchanged for `app n []`.
5. The faces. A module prints `export type N = …` per declaration, and the reader reads a declared
   name. The bridge writes and reads the references table. The map spelling and the class rule
   are repaired.
6. `deriving Modeled` on a recursive inductive (§4).

Size: one slice. The risk is item 2. `Fits` and `Val.hasTy` sit under M7's proofs, so their new
case must leave every existing statement unchanged. It does, for every table with no declarations.

## 4. `deriving Modeled`

### 4.1 What it is now

`Modeled α` ties a Lean type to a checked `Ty` by an equivalence with that type's carrier
(`src/Effect4/Schema/Modeled.lean`). The carrier comes from one fold, `Model.algAt`, which gives
each supported `Ty` constructor its Lean type and its exact `Image` together. So an instance owes
no membership proof and cannot supply a wrong one. Its image is the fold's image, carried
across `toC` and `ofC`. `Model.member` (`src/Effect4/Laws/Schema/Modeled.lean`) proves that every encoded value
inhabits the type.

`deriving Modeled` (`src/Effect4/Schema/Modeled/Derive.lean`) reads a declaration and writes the
instance:

- **A structure** becomes a record type in canonical field order. Each field needs a `Modeled`
  instance. The deriver writes the type `modeledTy` and its proof `modeled_checked`, from the
  names' order and each field instance's own proof. It writes the maps `modeledToC` and
  `modeledOfC` to and from the carrier's product, and their two inverse equations.
- **An inductive** becomes a union of tagged records, one per constructor, its name the tag. An
  inductive whose constructors have no fields becomes a union of string literals. The maps go to
  and from nested sums.
- It refuses parameters, indices, universe parameters and recursion, each at its syntax.
  It refuses a shared tag, a field named `_tag`, an unnamed field, a dependent field and a
  field with no instance. A generated declaration that fails restores the environment.

Its users today are the PubSub and PartitionedSemaphore cells (`src/Effect4/Library/PubSub/Cell.lean`)
and the battery. No service, row and no part of the to-do uses it.

### 4.2 What recursion adds

The fold cannot give a recursive declaration its carrier, since it would have to tie the knot.
So for a recursive inductive the deriver writes:

1. the declaration: the body, with each recursive occurrence as `app name []`;
2. `toVal` and `ofVal` by structural recursion, a list companion for each nested `List`;
3. the two laws by induction on the Lean value. The probe's proofs are uniform: case on the
   constructor, unfold `ofVal`, split its match. A deriver can write them;
4. the instance at `ty := .app name []`, with the table in the carrier fold's context.

The probe's hand-written output for `Tree` agrees with the declaration. `Tree.toVal` of the
sample is the probe's `tree3` value, and that value fits `Tree` under the table.

### 4.3 What would make it the core abstraction

| Step | Gain | Waits on |
| --- | --- | --- |
| Recursion | trees, lists, JSON and syntax as Lean data | the slice of §3.5 |
| A name per derived type | the printed module says `Todo`, the Schema carries its identifier, and service signatures name their types | the declaration table |
| One declaration for both faces | `deriving Modeled` replaces `eff_record`: one Lean structure gives the `Ty`, the term builders, the projections and the Lean model | row 399 (5): P1 |
| Optional fields | `Option` fields as optional keys | row 399 (5): P1 |
| Parameters | `Result α`, generic containers | regular recursion over the table |

## 5. Lean types as Effect services

The survey's answer, with the claims I checked marked.

### 5.1 What exists

- **Keys and requirements.** `ServiceKey` is a name code and a type code
  (`src/Effect4/Machine/Key.lean`). The requirement column is a row of keys.
- **Eff.** `provideLayer`, `service`, `provideService`, `provideContext` and `LayerTerm` (`succeed`,
  `effect`, `provide`, `merge`, `fresh`, `ref`, …) are program syntax. `Ty.contextOf keys` is the
  type of `Effect.context<R>()`.
- **Two routes to a service with methods:**
  - block roles (`DefRole.serviceInit`, `serviceMethod`; `Queue.serviceDefs`, `Semaphore.serviceDefs`,
    `Application.serviceDefs`). The checker, the denotation and the machine read none of them.
  - row namespaces (`eff_rows`). The key's carrier is `unit`, and the machine never reads the
    service's value.
- **Printing.** `Context.Service` keys, `Layer.effect` for block services, `Object.assign` row
  services for host implementations, and the surface's `SSchemas` and `SLive`.
- **Reading.** The Lean reader and `ts/eff/read.ts` read keys, row services, block service layers
  and the layer families. `module-defs-round-trip` covers block and row services.
- **Proved.** The requirement laws (`satisfies-*`, `provide-discharges`, `provide-closed`),
  `emission-requirements-complete`, `service-identifier-injective` and `h9_blocks` without layers.

### 5.2 The gaps

1. **Two declarations, not one** (checked). `eff_record Todo` gives the `Ty`, and the Lean model
   is a separate tuple, `abbrev Repo := Nat × List (Nat × String × Bool)`
   (`Test/Dogfood/Scenario/Todo/Data.lean`). `deriving Modeled` is used by no service.
2. **A service as a record of closures is not built** (rows 381 (3), 382 (2)). `Ty` has no function
   type (row 340 (2)).
3. **A block service's layer is no `LayerTerm`**, and a client that calls a method through the key
   is no `Eff`. So the truth fixtures `pQueueService` and `pSemaphoreService` refuse on reading
   (`provideLayer.0: shape layer`). No row rules it.
4. **The reader gate reads the truth fixtures at an empty row table** (checked:
   `ts/eff/check.ts`), so `Sql.open`, `Kv.make`, `Host.acquire` and `L.first` refuse as unknown
   heads. Lean reads the same programs at their table. No row rules it.
5. **Structured service carriers** are refused (row 114). Row 118 says it waits, and row 381 (3) says it
   is answered. The proof registry (`tools/ProofGraph/Registry.lean`) cites row 118.
6. **The surface** (`SSchemas`, `SLive`) is unread and has no law (row 373 (11)).
7. **H9 does not cover layers**; that is SCOPE-1 (rows 383 (1), 387 (5)).

### 5.3 How recursion and `Modeled` serve this

The declaration table is where a service's data types get names. With it, a method's signature
prints `Todo` by name, its Schema carries the identifier, and the reader reads the name back.
With one declaration for both faces, the to-do's `Todo` is one Lean structure that is also its
`Ty`. Gaps 2 and 3 are the service form itself; they need their own design, after P1.

## 6. Lowering, PubSub and the stateful modules

- **The rule** (DI-11, row 81): Queue, Mailbox and PubSub are composite `Eff` programs over `Ref`,
  `Deferred` and the wake lists, never new machine stores. So the OCaml engine runs them as
  programs, and they need no new lowering.
- **PubSub in Lean** is a model, a cell, its data and six pure steps, at a capacity-one,
  replay-zero profile with natural messages (`src/Effect4/Library/PubSub/`). Its law is
  `single_steps_agree`. It has no operations, no definitions and no engine lane. The plan is
  `docs/research/2026-10-09-pubsub-single-plan.md`. Its receipt still owes waiting, delivery,
  cancellation, lifetime and backpressure (claim `pubsub-single-expansion-agrees`).
- **A PubSub slice needs** the owner's profile rows first, as rows 219–222 gave the Queue. Then it
  needs operations over `Library/Waiting.lean`, definitions through `eff_module`, the laws, and an
  engine lane under `ocaml/engine/test/pubsub/` like Queue's. `make gen-lcnf` reruns only if a new `Term` or `NativeOp`
  form appears.
- **Open lowering work**, from `docs/research/2026-10-15-lowering-state/README.md`:
  - P1/LC-6, the native to-do: it compiles now. It still needs a dune executable that runs it.
    The engine instances must take the row table in place of `[]`. A host provider record and the
    one report remain.
  - LC-7, the session from LCNF: waits on P2 and P3.
  - LC-8, the carriers as Lean data: needs a design note; it retires `api_gen.ml`'s hand twins.
  - LC-9, the C face: after LC-7.
  - S3's leftovers: `OCaml5.Eff.tyO` and `tyV` as folds; the functor body checked once the
    prelude is Lean data.
- **Recursive Lean inductives already lower** to recursive OCaml types: `ocaml/eff/eff_types.ml`
  declares `ty`, `eff` and their mutual families from Lean's.

## 7. Recommendations

1. **Land recursive types as one slice** (§3.5), monomorphic first, with the two TypeScript repairs
   and the recursive deriver. Its decisions row records the table's home, guardedness and
   nominal subtyping.
2. **Then one declaration for both faces**: `deriving Modeled` as the authoring of a data type,
   retiring `eff_record` once its users move. Do it in P1, where the to-do is its consumer.
3. **Rule the two reader refusals** of §5.2 items 3 and 4. Item 4 is a gate that reads with the wrong
   table and is small. Item 3 needs the service form's design.
4. **Reconcile rows 118 and 381 (3)**, and the citation in `tools/ProofGraph/Registry.lean`.
5. **PubSub after P1**, on Queue's pattern, once the owner gives its profile rows.

## 8. What this does not establish

- The probe is finite. Its checker takes fuel; the landing's measure is stated, not built.
- No subtyping between recursive types was run.
- Parameters were not probed.
- The TypeScript results are tsgo's on hand-copied printed output; no module printer emitted them.
- The Schema result is rc.112's own Schema, written by hand to match the declaration. The Lean
  bridge does not write it yet.
- §5 and §6 rest on two read-only surveys. I checked the claims marked "checked", not every claim.
