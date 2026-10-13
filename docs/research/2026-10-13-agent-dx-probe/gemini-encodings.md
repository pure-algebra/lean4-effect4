# Comparison of JSON Encodings for Eff

Status: probe note (history, not authority). Date: 2026-10-13.
Repository: `lean4-effect4`.
Artifact: `docs/research/2026-10-13-agent-dx-probe/gemini-encodings.md`.

## 1. Summary

Two JSON encodings of `Eff` exist in the tree.
The first encoding is published in `ts/eff/eff.gen.ts`.
`tools/Drivers/TsGen.lean` generates that TypeScript file from the Lean environment.
The second encoding is the canonical program JSON print.
`Canonical.ofJsonAnyOrder` in `src/Effect4/Store/Domain/ShapeRead.lean` reads that print.
It runs over the shapes generated in `src/Effect4/Store/Domain/Derived/Program.lean`.

The two encodings agree across most AST families.
They agree on all primitive types, all-nullary enums, structures and options.
They agree on tagged sums that hold payload fields.
They agree on standard lists (`List α`) and sorted rows (`Row α`).

The two encodings differ on the mutual cons-list families.
Those families are `Terms`, `Stmts`, `Effs` and `LayerTerms`.
`eff.gen.ts` flattens every mutual cons-list into a JSON array `[...]`.
The canonical print formats every mutual cons-list as nested tagged objects.
Those objects use `{"_tag": "cons", "head": ..., "tail": ...}` and `{"_tag": "nil"}`.
Because of this divergence, the session tool refuses programs authored against `eff.gen.ts`.

This note tabulates every family reached by `EffShape`.
It records the quoted encodings, agreement status and observed differences.
It then details candidate carrier rules to unify the two encodings.
The coordinator decides which encoding wins.

## 2. Inventory of Reached Families

`EffShape` in `src/Effect4/Store/Domain/Derived/Program.lean` reaches 25 domain families.
It also reaches six primitive or standard library carriers.
Six additional package row families appear in `Derived/Program.lean` but are not reached by `EffShape`.

The table below catalogs every reached family.

| Family | TypeScript Schema Encoding (`ts/eff/eff.gen.ts`) | Canonical Print Encoding (`Derived/Program.lean`) | Agreement Status |
| --- | --- | --- | --- |
| `Eff` | `Schema.TaggedUnion` (28 cases). List fields use `Schema.Array`. | `EffC.EffShape` (`.sum "Eff"`, 28 cases). List fields use `.named`. | Diverges on nested list fields (`gen`, `defs`, `invoke`). Tags and field names agree. |
| `Stmt` | `Schema.TaggedUnion` (6 cases). List fields use `Schema.Array`. | `EffC.StmtShape` (`.sum "Stmt"`, 6 cases). List fields use `.named "Stmts"`. | Diverges on `ifElse` (`thenB`, `elseB`) and `whileTrue` (`body`). Tags agree. |
| `Stmts` | `ReadonlyArray<Stmt>` (flattened; no standalone schema). | `EffC.StmtsShape` (`.sum "Stmts"`, `nil` and `cons`). | Diverges. TypeScript uses arrays `[...]`. Canonical uses tagged cons objects. |
| `Effs` | `ReadonlyArray<Eff>` (flattened; no standalone schema). | `EffC.EffsShape` (`.sum "Effs"`, `nil` and `cons`). | Diverges. TypeScript uses arrays `[...]`. Canonical uses tagged cons objects. |
| `ActionTerm` | `Schema.TaggedUnion` (17 cases). `raceAll` entrants use `Schema.Array(Eff)`. | `EffC.ActionTermShape` (`.sum "ActionTerm"`, 17 cases). Entrants use `.named "Effs"`. | Diverges on `raceAll` and `raceAllFirst` entrants. Tags and field names agree. |
| `LayerTerm` | `Schema.TaggedUnion` (10 cases). `mergeAll` uses `Schema.Array(LayerTerm)`. | `EffC.LayerTermShape` (`.sum "LayerTerm"`, 10 cases). `mergeAll` uses `.named "LayerTerms"`. | Diverges on `mergeAll.layers`. Tags, field names and `ref.target` agree. |
| `LayerTerms` | `ReadonlyArray<LayerTerm>` (flattened; no standalone schema). | `EffC.LayerTermsShape` (`.sum "LayerTerms"`, `nil` and `cons`). | Diverges. TypeScript uses arrays `[...]`. Canonical uses tagged cons objects. |
| `Term` | `Schema.TaggedUnion` (8 cases). `app.args` and `record.values` use `Schema.Array`. | `TermC.TermShape` (`.sum "Term"`, 8 cases). Args and values use `.named "Terms"`. | Diverges on `app.args` and `record.values`. Tags and other fields agree. |
| `Terms` | `ReadonlyArray<Term>` (flattened; no standalone schema). | `TermC.TermsShape` (`.sum "Terms"`, `nil` and `cons`). | Diverges. TypeScript uses arrays `[...]`. Canonical uses tagged cons objects. |
| `CauseTerm` | `Schema.TaggedUnion` (4 cases). `interruptor` uses `Schema.NullOr(Term)`. | `CauseTermC.CauseTermShape` (`.sum "CauseTerm"`, 4 cases). Option uses `null`. | Agrees completely. Tags, field names and option encoding match. |
| `Lit` | `Schema.TaggedUnion` (`unit`, `nat`, `bool`, `str`). | `LitC.shapeDoc` (`.sum "Lit"`, 4 cases). | Agrees completely. Tags, field names and values match. |
| `NativeOp` | `Schema.TaggedUnion` (25 cases). Nullary cases use empty object `{}`. | `NativeOpC.shapeDoc` (`.sum "NativeOp"`, 25 cases). | Agrees completely. All 25 tags, field names and payload types match. |
| `Ty` | `Schema.TaggedUnion` (28 cases). Array fields use `Schema.Array`. | `TyC.TyShape` (`.sum "Ty"`, 28 cases). Standard lists use `.list`. | Agrees completely. Tags and fields match. Standard lists print as arrays in both. |
| `ForkOptions` | `Schema.Struct` (`startImmediately`, `daemon`, `maskMode`). | `ForkOptionsC.shapeDoc` (`.struct "ForkOptions"`, 3 fields). | Agrees completely. Both print as objects without `_tag`. |
| `MaskMode` | `Schema.Literals(["interruptible", "uninterruptible", "inherit"])`. | `MaskModeC.shapeDoc` (`.sum "MaskMode"`, all-nullary). | Agrees completely. Both encode as bare string literals. |
| `ObserverMode` | `Schema.Literals(["awaitValue", "joinEffect"])`. | `ObserverModeC.shapeDoc` (`.sum "ObserverMode"`, all-nullary). | Agrees completely. Both encode as bare string literals. |
| `FinalizerStrategy` | `Schema.Literals(["sequential", "parallel"])`. | `FinalizerStrategyC.shapeDoc` (`.sum "FinalizerStrategy"`, all-nullary). | Agrees completely. Both encode as bare string literals. |
| `Decision` | `Schema.TaggedUnion` (`bool`, `option`, `tag`, `recordTag`). | `DecisionC.shapeDoc` (`.sum "Decision"`, 4 cases). | Agrees completely. Tags and field names match. |
| `DefRole` | `Schema.TaggedUnion` (`plain`, `serviceInit`, `serviceMethod`). | `DefRoleC.shapeDoc` (`.sum "DefRole"`, 3 cases). | Agrees completely. Tags and field names match. |
| `ParamDecl` | `Schema.Struct` (`name`, `request`, `answer`, `error`). | `ParamDeclC.shapeDoc` (`.struct "ParamDecl"`, 4 fields). | Agrees completely. Both print as objects without `_tag`. |
| `DefDecl` | `Schema.Struct` (7 fields). `requires` and `params` use `Schema.Array`. | `DefDeclC.shapeDoc` (`.struct "DefDecl"`, 7 fields). Standard lists use `Shape.list`. | Agrees completely. Standard lists print as arrays in both. |
| `ServiceKey` | `Schema.Struct` (`name`, `service`). | `ServiceKeyC.shapeDoc` (`.struct "ServiceKey"`, 2 fields). | Agrees completely. Both print as objects without `_tag`. |
| `ServiceName` | `Schema.Struct` (`value: Schema.Int`). | `ServiceNameC.shapeDoc` (`.struct "ServiceName"`, 1 field). | Agrees completely. Both print as `{"value": n}` without `_tag`. |
| `ServiceTypeCode` | `Schema.Struct` (`value: Schema.Int`). | `ServiceTypeCodeC.shapeDoc` (`.struct "ServiceTypeCode"`, 1 field). | Agrees completely. Both print as `{"value": n}` without `_tag`. |
| `FieldReadMode` | `Schema.Literals(["required", "optional"])`. | `FieldReadModeC.shapeDoc` (`.sum "FieldReadMode"`, all-nullary). | Agrees completely. Both encode as bare string literals. |
| `Nat` | `Schema.Int` / `number`. | `(shape Nat).root` (`.nat`, binary64 finite natural up to 2^53). | Agrees completely. Both encode as JSON numbers. |
| `Bool` | `Schema.Boolean` / `boolean`. | `(shape Bool).root` (`.bool`). | Agrees completely. Both encode as JSON booleans. |
| `String` | `Schema.String` / `string`. | `(shape String).root` (`.string`). | Agrees completely. Both encode as JSON strings. |
| `Option α` | `Schema.NullOr(T)` (`T \| null`). | `Shape.option` (`some a` prints as `a`, `none` prints as `null`). | Agrees completely. Both encode absent values as `null`. |
| `List α` | `Schema.Array(T)` (`ReadonlyArray<T>`). | `Shape.list` (prints as JSON array `[...]`). | Agrees completely. Standard Lean lists print as arrays in both. |
| `Row α` | `Schema.Array(T).check(...)` (`ReadonlyArray<T>`). | `RowCanonical.instCanonicalRow` (delegates to `Shape.list`). | Agrees completely. Sorted rows print as arrays in both. |

### Note on Non-Reached Program Families

`src/Effect4/Store/Domain/Derived/Program.lean` also generates instances for six row families.
Those families are `RowKind`, `RowShape`, `Registration`, `RowArg`, `Row` and `EffTy`.
`EffShape` does not transitively reach them.
They appear in `Derived/Program.lean` because the generator CLI included them in the Program group.
In `eff.gen.ts`, they encode with the exact same conventions as the reached families.
All-nullary sums (`RowKind`, `RowShape`, `Registration`) encode as string literals.
`RowArg` encodes as a tagged union with `_tag`.
`Row` and `EffTy` encode as structures without `_tag`, using `Schema.Array` for their list fields.
Their encodings agree on every constructor and field.

## 3. Detailed Comparison by Semantic Category

### 3.1 Mutual Cons-List Families

Four families in the program AST represent lists of stored syntax nodes:
1. `Terms` (`src/Effect4/Program/Term.lean`)
2. `Stmts` (`src/Effect4/Program/Eff.lean`)
3. `Effs` (`src/Effect4/Program/Eff.lean`)
4. `LayerTerms` (`src/Effect4/Program/Eff.lean`)

In `Derived/Program.lean`, each is declared as a sum shape with two constructors:
```lean
def TermsShape : Shape :=
  .sum "Terms"
     [("nil", 0, []),
      ("cons", 1, [("head", .named "Term"), ("tail", .named "Terms")])]
```
Because constructor 1 carries fields, `Shape.allNullary` is false.
Under `Shape.printIn` in `src/Effect4/Store/Domain/Shape.lean`:
- Constructor 0 prints as `{"_tag": "nil"}`.
- Constructor 1 prints as `{"_tag": "cons", "head": <item>, "tail": <tail>}`.
Under `ShapeRead.readIn` in `src/Effect4/Store/Domain/ShapeRead.lean`:
- The reader matches `.sum _ cases`.
- It requires an object containing a `_tag` field matching `"nil"` or `"cons"`.
- It refuses a JSON array (`.arr js`) with `none`.

The header of `ts/eff/eff.gen.ts` states the generator's carrier rule:
"A family whose constructors are exactly `nil` and `cons head tail` is `ReadonlyArray<head>`."
Therefore, `eff.gen.ts` exports no schema for `Terms`, `Stmts`, `Effs` or `LayerTerms`.
Every field expecting one of these families is typed as `Schema.Array(...)`.
Under `eff.gen.ts`, an empty list is `[]`.
A two-element list is `[item0, item1]`.

This difference is the exact cause of refusal F5 in the DX probe.

### 3.2 Families Embedding Mutual Cons-Lists

Five families embed the mutual cons-list families:
1. `Eff`:
   - `gen`: field `body` is `ReadonlyArray<Stmt>` in TypeScript, but `Stmts` in Canonical.
   - `defs`: field `bodies` is `ReadonlyArray<Eff>`, but `Effs` in Canonical.
   - `defs`: field `layers` is `ReadonlyArray<LayerTerm>`, but `LayerTerms` in Canonical.
   - `invoke`: field `args` is `ReadonlyArray<Eff>`, but `Effs` in Canonical.
2. `Stmt`:
   - `ifElse`: fields `thenB` and `elseB` are `ReadonlyArray<Stmt>`, but `Stmts` in Canonical.
   - `whileTrue`: field `body` is `ReadonlyArray<Stmt>`, but `Stmts` in Canonical.
3. `ActionTerm`:
   - `raceAll`: field `entrants` is `ReadonlyArray<Eff>`, but `Effs` in Canonical.
   - `raceAllFirst`: field `entrants` is `ReadonlyArray<Eff>`, but `Effs` in Canonical.
4. `LayerTerm`:
   - `mergeAll`: field `layers` is `ReadonlyArray<LayerTerm>`, but `LayerTerms` in Canonical.
5. `Term`:
   - `app`: field `args` is `ReadonlyArray<Term>`, but `Terms` in Canonical.
   - `record`: field `values` is `ReadonlyArray<Term>`, but `Terms` in Canonical.

Every other field of these five families agrees across both encodings.
Constructor names, field names and tag discriminators match verbatim.

### 3.3 Standard Lists and Finite Rows

The tree also contains standard Lean lists (`List α`) and sorted rows (`Row α`):
- `Eff.defs.decls`: `List DefDecl` in Lean; `Schema.Array(DefDecl)` in TypeScript.
- `DefDecl.requires`: `List ServiceKey` in Lean; `Schema.Array(ServiceKey)` in TypeScript.
- `DefDecl.params`: `List ParamDecl` in Lean; `Schema.Array(ParamDecl)` in TypeScript.
- `LayerTerm.ref.target`: `List Nat` in Lean; `Schema.Array(Schema.Int)` in TypeScript.
- `Term.record.fields`: `List (String × Bool × Ty)` in Lean; array of tuples in TypeScript.
- `Term.record.presentNames`: `List String` in Lean; `Schema.Array(Schema.String)` in TypeScript.
- `Ty.record.fields`: `List (String × Bool × Ty)` in Lean; array of tuples in TypeScript.
- `Ty.tuple.items`: `List Ty` in Lean; `Schema.Array(Ty)` in TypeScript.
- `Ty.app.args`: `List Ty` in Lean; `Schema.Array(Ty)` in TypeScript.
- `Ty.contextOf.keys`: `Row ServiceKey` in Lean; `Schema.Array(ServiceKey)` in TypeScript.
- `ActionTerm.context.keys`: `Row ServiceKey` in Lean; `Schema.Array(ServiceKey)` in TypeScript.

For these fields, `Derived/Program.lean` uses `Shape.list` or `instCanonicalRow`.
`Shape.printIn` serializes `Shape.list` as a JSON array `.arr js`.
`ShapeRead.readIn` parses `Shape.list` from a JSON array `.arr js`.
Therefore, standard lists and sorted rows already agree across both encodings.
Both encodings represent them as flat JSON arrays `[...]`.

### 3.4 Structures and Objects

Six domain families are structures:
`ServiceName`, `ServiceTypeCode`, `ServiceKey`, `ForkOptions`, `ParamDecl` and `DefDecl`.
In `eff.gen.ts`, each is generated as `Schema.Struct({ ... })`.
In `Derived/Program.lean`, each has shape `.struct name fields`.
Under `Shape.printIn`:
- Structs serialize as JSON objects without a `_tag` property.
- Fields print in declaration order.
Under `ShapeRead.readIn` and `orderIn`:
- Structs parse from JSON objects matching field names.
- Keys may appear in any order when parsed through `Canonical.ofJsonAnyOrder`.
Both encodings agree on all structure types.

### 3.5 All-Nullary Enumerations

Four domain families are all-nullary sums:
`MaskMode`, `ObserverMode`, `FinalizerStrategy` and `FieldReadMode`.
In `eff.gen.ts`, each is generated as `Schema.Literals([...])`.
In `Derived/Program.lean`, each has shape `.sum name cases` where every case has empty fields.
Under `Shape.allNullary`, such sums evaluate to `true`.
Under `Shape.printIn`:
- Sums satisfying `allNullary` print as bare string literals, such as `"interruptible"`.
Under `ShapeRead.readIn`:
- Reading a string literal matches against case names directly.
Both encodings agree on all-nullary enumerations.

### 3.6 Sums with Payloads

Seven domain families are sums with payloads:
`Lit`, `NativeOp`, `CauseTerm`, `Ty`, `Decision`, `DefRole`, and non-list cases of `Eff`, `Term`, `Stmt`, `ActionTerm`, `LayerTerm`.
In `eff.gen.ts`, each is generated as `Schema.TaggedUnion({ ... })`.
In `Derived/Program.lean`, each has shape `.sum name cases` where `allNullary` is false.
Under `Shape.printIn`:
- Non-all-nullary sums print as objects with a `_tag` property.
- Nullary constructors in these families (such as `Lit.unit` or `Decision.bool`) print as `{"_tag": "unit"}`.
- Payload constructors print as `{"_tag": name, field1: ..., field2: ...}`.
Under `ShapeRead.readIn`:
- The reader matches `_tag` to case names.
Both encodings agree on tag names and field names across all payload sums.

### 3.7 Options and Numbers

`Option α` appears in four AST locations:
- `Term.fold.accTy`: `Option Ty`
- `Eff.iterate.cursorTy`: `Option Ty`
- `CauseTerm.interrupt.interruptor`: `Option Term`
- `ActionTerm.interruptAll.interruptor`: `Option Term`

In `eff.gen.ts`, each is generated as `Schema.NullOr(...)` (`T | null`).
In `Derived/Program.lean`, each uses `Shape.option`.
Under `Shape.printIn`, `some a` prints as `a`, and `none` prints as `null`.
Under `ShapeRead.readIn`, `null` reads as `none`, and any valid value reads as `some a`.
Both encodings agree on option values.

Numbers in both encodings represent non-negative finite integers.
In `eff.gen.ts`, numeric fields use `Schema.Int`.
In `Derived/Program.lean`, numeric fields use `Nat`.
`natOfBinary64` in `ShapeRead.lean` reads binary64 values exactly up to 2^53.
Both encodings agree on numeric values.

## 4. Candidate Carrier Rules for Unification

Four candidate carrier rules could resolve the divergence between the encodings.
Each rule alters specific components of the tree.
The coordinator selects the active rule.

### Rule U1: Canonical Array Projection for Mutual Cons Families

**Specification:**
Teach the Canonical shape generator and reader to treat mutual cons-lists as arrays.
Any inductive family whose constructors are exactly `nil` and `cons head tail` receives array semantics.
In `Derived/Program.lean`, its shape becomes `Shape.list (shape head).root`.
Alternatively, `Shape.printIn` and `ShapeRead.readIn` project such families to and from `.arr js`.

**Families Changed:**
- Canonical encoding of `Terms`, `Stmts`, `Effs` and `LayerTerms`.
- Indirectly changes serialization of `Eff`, `Term`, `Stmt`, `ActionTerm` and `LayerTerm`.
- TypeScript schemas in `eff.gen.ts` remain unchanged.

**Consequences:**
- Eliminates discrepancy F5 immediately.
- Programs authored in TypeScript or JSON arrays read directly into `Canonical.ofJsonAnyOrder`.
- Lean's internal AST representations remain mutual inductives.

### Rule U2: TypeScript Tagged-Cons Carrier for Mutual Cons Families

**Specification:**
Change `tools/Drivers/TsGen.lean` to generate mutual cons-lists as explicit tagged unions.
Remove the array carrier rule for `Terms`, `Stmts`, `Effs` and `LayerTerms`.
Emit recursive schemas for `Terms`, `Stmts`, `Effs` and `LayerTerms` with cases `nil: {}` and `cons: { head, tail }`.
Type fields in `Eff`, `Term`, `Stmt`, `ActionTerm` and `LayerTerm` using these cons schemas.

**Families Changed:**
- TypeScript schemas in `eff.gen.ts` for `Terms`, `Stmts`, `Effs` and `LayerTerms`.
- Fields in `Eff`, `Term`, `Stmt`, `ActionTerm` and `LayerTerm` change from `ReadonlyArray<T>` to cons types.
- Canonical Lean encoding remains unchanged.

**Consequences:**
- Canonical print remains strictly structural.
- TypeScript AST becomes unidiomatic and verbose to author by hand.
- Every list of statements or terms in TypeScript requires nested `{ _tag: "cons", head: ..., tail: ... }`.

### Rule U3: AST Unification with Standard List in Lean

**Specification:**
Refactor the Lean AST in `src/Effect4/Program/Eff.lean` and `src/Effect4/Program/Term.lean`.
Replace mutual inductives `Terms`, `Stmts`, `Effs` and `LayerTerms` with standard Lean `List`.
Fields in `Eff`, `Term`, `Stmt`, `ActionTerm` and `LayerTerm` become `List Stmt`, `List Eff`, `List Term`, `List LayerTerm`.

**Families Changed:**
- Removes `Terms`, `Stmts`, `Effs` and `LayerTerms` from the AST entirely.
- Both `Derived/Program.lean` and `eff.gen.ts` naturally treat them as standard lists (`Shape.list` and `Schema.Array`).

**Consequences:**
- Resolves divergence at the root of the data model.
- Unifies syntax across all layers.
- Requires updating inductive recursion, well-founded termination proofs and catamorphisms across the core engine.

### Rule U4: Dual-Admission Reader in ShapeRead

**Specification:**
Update `ShapeRead.lean` to accept both formats during deserialization.
When reading a sum shape with `nil` and `cons`, `readIn` checks the JSON node type.
If the JSON node is `.arr js`, it reads elements sequentially into cons cells.
If the JSON node is `.obj entries`, it reads tagged cons cells as before.
`Shape.printIn` continues to print canonical cons objects (or configurable array print).

**Families Changed:**
- Reader logic in `src/Effect4/Store/Domain/ShapeRead.lean`.
- No shape definitions or TypeScript types change.

**Consequences:**
- Provides backward compatibility for both JSON shapes.
- Allows agents to send either arrays or cons cells to `Tools.Session.programOfJson`.
- Canonical print remains asymmetric unless printer is also adapted.
