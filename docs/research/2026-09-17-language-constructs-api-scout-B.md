# Scout B — the language constructs and layers: how a program composes today, and the API I would want

Read-only scout, 2026-09-17, on `refactor/phase1-phase3` at the working tree of this session
(`7c451f58` plus the four modified `Laws/` files and the untracked `docs/*.md` of the git
status). No Lean process was started, no file under `src/`, `Test/`, `tools/`, `ts/` was
touched, no git state was changed. This note is the only file written.

**Evidence words.** *read* = I read the declaration at the cited line. *hand-evaluated* = I
computed the result from the definitions by hand and give the `#guard` that would decide it;
nothing in this note was **compiled**, **reproduced** or **proved** by me this session, because
no Lean process was allowed. *proved* is used only for theorems that exist in the tree, with
their name and file. *tested* is used only for `#guard`s that exist in the tree. *assumed* is
marked as such.

Two scouts already own halves of this ground and I do not repeat them: the printed identity of
a service key is scout D's (`docs/research/2026-09-17-scout-named-and-exact-service-keys.md`),
and the census of what rc.112's combinator surface classifies as sugar is the surface scout's
(`docs/research/2026-09-16-effect-surface-sugar-scout.md`). I cite both where they answer a
question I raise.

---

## 0. The answer in ten lines

1. Composition of *programs* is in good shape. `Src Op := Env → List Nat → Except Refusal (Eff Op)`
   (`src/Effect4/Program/Authoring.lean:78`) is scope- and path-polymorphic, so a fragment is
   reusable at any depth and any position, and 48 generated lifts plus five conveniences cover
   the alphabet an author may write.
2. Composition of *services and layers* is not. There is no declaration of a service, no way to
   check or print a layer on its own, and the carrier of a service comes from a closed six-entry
   table of numbers (`src/Effect4/Program/Native.lean:291-293`).
3. The two mechanisms that should be one are two. Services live on the `ServiceKey`/`Layer`
   plane; a package's operations live on the row plane with the receiver passed as a *value*
   (`src/Effect4/Program/Packages/KeyValueStoreMemory.lean:40-56`). `Row.requires`
   (`src/Effect4/Program/Eff.lean:203`) is the field that joins them and **no shipped row sets
   it**; the only user in the tree is a witness alphabet (`src/Effect4/Program/Provision.lean:632-644`)
   whose spelling `"db.insertFeedback"` cannot print, because nothing binds `db`.
4. An author reaching a package row writes `perform (.external i) …` with `i` a hand-written
   index into a table supplied out of band (`src/Effect4/Program/Native.lean:130`, `:321-322`,
   `:333`). The generated row wrappers cover the built-ins only
   (`src/Effect4/Program/Authoring/Rows.lean`, generated from `NativeOp.all`).
5. Shared layers are addressed by **path** (`LayerTerm.ref (target : List Nat)`,
   `src/Effect4/Program/Eff.lean:444`). Hiding the path costs a sentinel-path protocol and a
   fuelled placement loop (`Authoring.lean:155-230`), a non-fold hoist/restore pair
   (`src/Effect4/Program/Refs.lean:197-213`), a whole-tree expansion before typing
   (`Refs.lean:182-184`, used at `Typing.lean:567-570`), two `TypeReason`s and two proof
   modules. A layer *binder* deletes all of it.
6. `Layer.succeed` can provide only a literal, and not a string
   (`Eff.lean:423`, `litVal` at `Typing.lean:235-239`). The workaround already exists —
   `Layer.effect key (succeed t)` — and should be named `Layer.value`.
7. The type system knows the answer, the error and the requirement row of a program
   (`EffTy`, `Typing.lean:30-34`) and the output, error and requirement rows of a layer
   (`LayerTy`, `Typing.lean:242-246`), with the four combinator laws proved
   (`Provision.lean:70-160`). None of it is reachable from `Effect4.Api` for a layer, and
   `Api` exposes no `requires` projection at all.
8. Minted and generated binder names are not reserved. An author-chosen name equal to one of
   them captures: `Forms.tapContinuation "_answer1" …` binds the wrong variable and the
   program still types and still passes `Src.Scoped` (§4, B-9). Scope safety is "no free
   variable", not "the variable you meant".
9. Most of what I would want is free: one `Service` record, one `Package` record, six sugar
   definitions with one `*_scoped` lemma each, three `Api` projections, and one defaulted
   argument on `nativeSignature`. No constructor, no wire tag, no golden byte.
10. Exactly one new construct earns its price: the layer binder (`Eff.letLayer` plus
    `LayerTerm.var` replacing `LayerTerm.ref`). It is a net deletion of roughly 220 lines and
    two proof modules, and it belongs after R5, because it changes the printed module shape.

---

## 1. How a program is composed today

### 1.1 The alphabet

25 constructors, `src/Effect4/Program/Eff.lean:304-374`, with the one-to-one table of
constructor / public combinator / rc.112 primitive at `:524-549` and the count pinned at
`:558-559` (*tested*: `#guard constructorNames.length = 25`).

| group | constructors | line |
| --- | --- | --- |
| exits | `succeed`, `fail`, `failCause` | `:306-308` |
| thunks | `sync`, `suspend`, `perform` | `:311-313` |
| sequencing | `bind`, `gen` | `:316-317` |
| failure | `catchCause`, `matchCause`, `onExit`, `exit`, `catchIf` | `:319-322`, `:356` |
| masks | `uninterruptible`, `interruptible` | `:324-325` |
| scheduling | `yieldNow`, `awaitFiber` | `:329`, `:333` |
| fibers and scopes | `withFiber`, `scoped`, `acquireRelease` | `:335-338` |
| provision | `provideLayer`, `service`, `provideService` | `:345`, `:348`, `:351` |
| control by value | `select`, `iterate` | `:363`, `:374` |

Four side families: `Stmt`/`Stmts` for generator bodies (`:376-388`), `Effs` for race entrants
(`:390-392`), `ActionTerm` for the seventeen fiber actions (`:395-411`), `LayerTerm`/`LayerTerms`
for layers (`:421-454`). All first-order and `DecidableEq` (`:457`, receipts at `:563-569`).

### 1.2 Sequencing, control, iteration

- **`bind first rest`** (`:316`). `rest` is typed at `env ++ [f.answer]` (`Typing.lean:306`) and
  elaborated at `env.push [answer]` (`Authoring/Lifts.lean:51-55`). One binder, printed
  `Effect.flatMap(h0, (a0) => h1)` (`Codegen/Templates.lean:148`).
- **`gen body`** (`:317`) is the generator statement machine: `bindYield`, `yieldDiscard`, `ret`,
  `ifElse`, `whileTrue`, `breakLoop` (`:378-385`), typed by `stmtsTy` (`Typing.lean:449-477`),
  printed `Effect.gen(function* () { … })` (`Templates.lean:183`). **It has no authoring lift**:
  `binders.json` lists `Effect4.Program.Eff.gen` under `"readerOnly"`, so an agent cannot write a
  generator body — only read one. The owner ruled on 2026-09-17 that `gen` stays (`docs/STATE.md:62`).
- **`select scrutinee decision arm0 arm1`** (`:363`). One eliminator, three decisions
  (`Decision`, `src/Effect4/Program/Decision.lean:36-44`): `.bool` binds nothing, `.option` binds
  the payload in arm 1, `.tag t` binds the payload in arm 0 and the residual value in arm 1.
  `decide` is the runtime rule (`Decision.lean:50-59`), `arms` the checker rule (`:64-73`), and
  `arms_length` is *proved* (`:81`) so a reader's binder depth and the checker's environment
  cannot drift. Three lifts, one per decision (`Lifts.lean:153`, `:161`, `:169`), and three rows
  (`Templates.lean:161-166`).
- **`iterate cursorTy initial test step result body`** (`:374`). The language's only recursion.
  `test`, `result` and `body` see the cursor; `step` sees the cursor and the body's answer
  (`binders.json` row `"args": [[], [], [0], [0,1], [0], [0]]`; lift at `Lifts.lean:177-184`;
  typing at `Typing.lean:354-363`). `cursorTy` is optional since DI-91; `none` prints
  `let aN = initial` and `some t` prints `let aN: T` (two rows, `Templates.lean:167-168`).
- **The four loop conveniences** are Lean functions over that one lift, adding no constructor:
  `iterateWith`, `forRange`, `foldRange`, `repeatWhile` (`src/Effect4/Program/Authoring/Loops.lean:33-61`).

### 1.3 The authoring carrier

`src/Effect4/Program/Authoring.lean` is the scope reader. Its shape is the whole story:

```lean
abbrev Names  := List String                                        -- :39
abbrev Src (Op : Type) := Env → List Nat → Except Refusal (Eff Op)  -- :78
structure Env where names : Names := []; layers : LayerNames := []  -- :70-72
def Env.push (env) (xs : List String) : Env                         -- :90
def Env.closed (env) : Env                                          -- :93  (a layer body)
def var (x : String) : TermSrc                                      -- :133-137
def elaborate {Op} (src : Src Op) : Except Refusal (Eff Op) := src {} []  -- :175
```

Two reasons this is the right carrier, both *read*:

- A fragment is a function of the scope, so reusing it at two depths is applying it twice, and
  renaming consistently leaves the tree unchanged: names are read only through `Names.resolve`
  (`:42-47`, "the last position that carries it" — nearest binder wins).
- A refusal carries the path at which it happened (`Refusal`, `:61-64`), so `Api.author` can name
  the site (`src/Effect4/Api.lean:501-506`).

The 48 lifts are **generated** from one table, `tools/Effect4Gen/binders.json`, which names for
each constructor the slots it binds and, per argument, which slots are in scope for it. The
generated output is `src/Effect4/Program/Authoring/Lifts.lean` (header lines 1-6). The five
hand-written conveniences are `bindWith`, `bindName`, `flatMap`, `andThen`, `map`, `ifElse`
(`Authoring/Sugar.lean:25-45`) plus the `eff do` / `eff { … }` macro (`:106-165`) and the
literal coercions (`:49-62`).

### 1.4 The four tables everything is generated from

| table | owns | consumed by |
| --- | --- | --- |
| `tools/Effect4Gen/binders.json` | which argument is under which binders | three generated modules: `Program/Binders.lean`, `Program/Scoped.lean`, `Authoring/Lifts.lean` (all three headers name `binders.json` and `tools/Effect4Gen/Authoring.lean` as their source), plus the hoisting proofs |
| `NativeOp.all` (`Native.lean`) | the built-in rows | `Authoring/Rows.lean` (generated wrappers) |
| `Codegen.Forms.all` (`Codegen/Forms.lean:89`) | the nineteen foreign spellings | `Authoring/Forms.lean` (generated combinators, each pinned against `Template.expand`) |
| `Codegen.Templates.table` (`Templates.lean:235`) | one skeleton + one classifier per constructor | the printer (`:429-438`) and the reader |

This is the extension point the owner names, and it works: the printer is **one** generic layer
function over the table (`tableLayer`, `Templates.lean:381-424`) made an algebra by
`EffAlgebra.ofLayer` (`Program/LayerView.lean:52`), so adding a printed shape is adding a row.

---

## 2. Services and layers today

### 2.1 A service is a key, and a key is two numbers

`ServiceKey = ⟨name : ServiceName, service : ServiceTypeCode⟩`, both single-field `Nat`
(`src/Effect4/Machine/Key.lean:52`, `:65`, `:79-82`). The identity is the pair. The module
states, and *proves*, that a type cannot recover a code
(`ServiceUniverse.exists_carrier_collision`, `:384-387`), which is why the carrier is supplied
by a signature and never derived.

The carrier a key is typed at comes from `Signature.serviceTy : ServiceKey → Option Ty`
(`Typing.lean:64`). A signature may type by the full key; the native one does not:

```lean
def nativeServiceTypes : List (Nat × Ty) :=                      -- Native.lean:291-293
  [(4, .nat), (5, .bool), (6, .unit), (7, NativeOp.refTy),
   (8, NativeOp.sqlTy), (9, NativeOp.kvTy)]
```

`nativeServiceTy` (`:302-308`) answers the reserved `Scope` key for `⟨0,0⟩`, `none` for any name
below `firstFreeName`, and otherwise looks the **code** up in that six-entry list. So there are
exactly six carriers a native program can give a service, and adding a seventh means editing
`src/Effect4/Program/Native.lean`. *(read)*

An author writes a key as a raw anonymous constructor:
`def kA : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩` (`Test/Program/LayerSharingContract.lean:16`),
`def dbKey : ServiceKey := ⟨⟨10⟩, ⟨10⟩⟩` (`Provision.lean:615`).

### 2.2 Declaring a service: there is no declaration

Nothing in the tree binds a key to its carrier at the authoring site, and nothing binds a key to
its *operations* at all. A key is a pair of numbers; the carrier is decided elsewhere; the
operations, where they exist, are rows in a table with no link back to the key. Scout D reaches
the same conclusion for the carrier half and proposes `ServiceDef` with an `Agrees` check
(`2026-09-17-scout-named-and-exact-service-keys.md` §3.2). §5 below extends that record with the
operations, which scout D's question did not cover.

### 2.3 Providing

Three mechanisms, all present, all one-for-one with rc.112.

**`provideService key value body`** (`Eff.lean:351`). Types at `Typing.lean:396-402`: the value is
admitted at a subtype of the key's carrier, and `Row.diff b.requires (single key)` discharges the
key. Prints `Effect.provideService(h2, h0, h1)` (`Templates.lean:181-182`). The value is a
`Term` — a variable, a literal, or an atom application (`Eff.lean:253-261`). A service is
therefore **one value**, never a record of operations.

**`LayerTerm`** (`Eff.lean:421-454`), a one-for-one transcription of the rc.112 exports it cites:

| our constructor | line | rc.112 | `layerTy` rule |
| --- | --- | --- | --- |
| `succeed key (value : Lit)` | `:423` | `Layer.ts:1074` | `Typing.lean:412-413`, via `litVal` |
| `effect key body` | `:426` | `Layer.ts:1427`, `:1438` | `:415`, body typed at `[]`, `bodyRequires` strips `Scope` |
| `effectDiscard body` | `:428` | `Layer.ts:1512` | `:417` |
| `provide self that` | `:430` | `Layer.ts:2258` | `LayerTy.provide`, `Typing.lean:252-254` |
| `provideMerge self that` | `:432` | `Layer.ts:2704` | `LayerTy.provideMerge`, `:258-260` |
| `merge left right` | `:434` | `Layer.ts:1850` | `LayerTy.merge`, `:264-265` |
| `fresh inner` | `:436` | `Layer.ts:3850` | `:430`, signature unchanged |
| `orDie inner` | `:438` | `Layer.ts:3327` | `LayerTy.orDie`, `:268` |
| `ref target` | `:444` | `Layer.ts:411`, `:438` (memo keyed on the object) | `:434` — **`none` structurally** |
| `mergeAll layers` | `:450` | `Layer.ts:1652` | `layersTy`, `:439-445` |

**`provideLayer layer isLocal body`** (`Eff.lean:345`), `Effect.provide(self, layer, { local })`.
Types at `Typing.lean:386-389`: `Row.union l.requires (Row.diff b.requires l.out)`. Two rows,
one per `isLocal` (`Templates.lean:176-179`).

The four combinator laws are *proved* in `src/Effect4/Program/Provision.lean`: `provide_out`
(`:70`), `provideMerge_out` (`:73`), `provide_requires_subset` (`:76`), `provide_discharges`
(`:86`), `provide_closed` (`:98`), the associativity-of-rows statement `provide_provide_rows`
(`:123`), `merge_rows_comm` (`:138`), `merge_requires` (`:143` — "a merge provides nothing to a
sibling"), and `provide_requires_antitone_out` (`:149`). `build_total` (`:343`) and
`buildAll_total` (`:475`) are the construction half.

### 2.4 Consuming: two planes that never meet

**Plane one, the service.** `Eff.service key` (`Eff.lean:348`), typed
`⟨carrier, never, single key⟩` (`Typing.lean:392`), printed
`Effect.service(Context.Service<T>("k<name>_<code>"))`
(`Templates.lean:180`; `printKey`, `src/Effect4/Codegen/PrintLeaf.lean:300-306`).

**Plane two, the row.** `Eff.perform op request` (`Eff.lean:313`), typed from
`sig.rowOf op` with the request admitted at a subtype of the row's request
(`Typing.lean:298-303`). A `Row` carries `spelling`, `shape`, `trailing`, `kind`, `request`,
`answer`, `error`, **`requires : List ServiceKey`**, `cite`, `typeArgs`, `registration`
(`Eff.lean:190-213`).

The two planes were designed to meet at `Row.requires`: `effTy`'s `perform` arm returns
`Requirement.ofList row.requires` (`Typing.lean:302`). **No shipped row sets it.** Evidence,
*read*: the built-in rows are written positionally, `NativeOp.row` at `Native.lean:174-239`,
and the ninth slot — `requires` — is `[]` in every one of its arms; the two package tables use
named fields and mention `requires` nowhere (`grep requires` over `Program/Native.lean` and
`Program/Packages/*.lean` returns no line). The `kvGet` row is the shape:

```lean
{ name := "kvGet", spelling := "get", shape := .method, kind := .async,
  registration := .external, request := .prod NativeOp.kvTy .string,
  answer := .option .string, error := kvError, cite := "…KeyValueStore.ts:40-43" }
                                          -- Packages/KeyValueStoreMemory.lean:40-43
```

The receiver is the **first component of the request**, a handle value, obtained from a `kvMake`
row (`:38-40`), not from `service key`. So a package operation carries no requirement, and a
program that uses a key-value store has an empty `R`.

The other convention exists, once, in a witness alphabet:

```lean
| .insertFeedback =>
  ⟨"insertFeedback", "db.insertFeedback", .call, [], .sync, .nat, .unit, .never, [dbKey], …⟩
                                                      -- Provision.lean:632-644 (DocsOp.row)
```

Here the row *requires* `dbKey` and spells the receiver into the name. The handler's requirement
row is then exactly the two services (*tested*: the `#guard` at `Provision.lean` after
`feedbackHandler`, `(typeOf docsSig feedbackHandler).map EffTy.requires = some (Requirement.ofList [dbKey, rateKey])`).
It cannot print: `printRow` (`PrintLeaf.lean:265-276`) emits `db.insertFeedback(1)` and nothing
binds `db`. *(read)*

### 2.5 Sharing a layer: paths, sentinels, and a fuelled loop

rc.112 keys its memo map on the layer *object* (`Layer.ts:411`, `:438`), so two uses of one
`const L = …` share a build. Our model of that identity is the layer's **path in the program**
(`LayerId := List Nat`), and a second use is `LayerTerm.ref target` (`Eff.lean:440-444`).

What that costs, end to end, all *read*:

1. **Well-formedness is a separate predicate.** `Eff.layerRefsWF` (`Refs.lean:154-160`): every
   target must name a non-reference layer that precedes its reference in program order and does
   not enclose it.
2. **Typing expands before it types.** `typeOfProgram` (`Typing.lean:567-570`) checks
   `layerRefsWF`, runs `Eff.expandRefs` and types the expanded twin. `expandRefs`
   (`Refs.lean:182-184`) is `refSites.length + 1` whole-tree folds of `expandAlgebra`
   (`:131-133`). `layerTy (.ref _) = none` (`Typing.lean:434`), so an unexpanded reference is
   simply untypable.
3. **Printing is a hoist, not a fold.** `Eff.refTargets` (`Refs.lean:189-190`) sorts the distinct
   targets by `Path.declBefore` (`:88-89`); `Eff.hoistAll` (`:197-203`) walks them in descending
   order with `replaceLayerAt`, returning `Except (List Nat) …`; `Eff.restoreAll` (`:207-213`)
   walks them back in ascending order, returning `Option`. Both can fail. Their totality is
   *proved* separately: `Eff.hoistAll_exists` and `Eff.hoistAll_restoreAll`
   (`src/Effect4/Laws/Program/HoistingTotal.lean:78`, `:89`) and the ordering and round trip in
   `src/Effect4/Laws/Program/Hoisting.lean:120`, `:134`.
4. **The identifier carries the path in its digits.** `LayerTerm.refName [1,0,0] = "L_1_0_0"`
   (`Refs.lean:218-219`) and `readRefName` decodes it byte by byte with a three-function decimal
   reader (`:222-243`), because Lean's string traversals reach `Classical.choice` (`:31-32`).
5. **The author must not see any of this**, so the elaborator fakes a name scope with a sentinel
   path: `placeholderBase := 1000000000` (`Authoring.lean:155`), `placeholder k := [base + k]`
   (`:157`), `placeholder?` (`:160-162`), `Layer.ref name` resolving to a placeholder
   (`:167-170`), `placeholderSites` collecting and sorting them (`:189-194`), `placeRounds`
   placing one declaration per round under fuel `m.layers.length + 1` (`:198-208`, `:229`), and
   `pointAtPlaced` redirecting the rest (`:211-219`).
6. **Two refusal reasons and two facade branches** exist only for this:
   `Reason.unboundLayer`, `.duplicateLayer`, `.placement` (`Authoring.lean:53-58`) and
   `Api.explain`'s `referencesIllFormed` / `layerReference` arms (`Api.lean:113-117`).

The result is correct and *tested* (`Test/Program/AuthoringContract.lean:226-242` pins the
placement rule against the runtime's own `once` and `twice`), and it is a lot of machinery for
"this layer is used twice".

### 2.6 What rc.112 has here that we do not

From `vendor/effect-4.0.0-rc.112/src/Layer.ts` (*read*, export list):
`sync` (`:1191`), `succeedContext` (`:1129`), `syncContext` (`:1306`), `empty` (`:1155`),
`effectContext` (`:1479`), `suspend` (`:1543`), `unwrap` (`:1580`), `flatMap` (`:2882`),
`tap`/`tapError`/`tapCause` (`:3069`, `:3146`, `:3221`), `catchTag` (`:3401`),
`catchCause` (`:3575`), `updateService` (`:3720`), `launch` (`:3897`), `mock` (`:3994`),
the span family (`:4339`-`:4683`), and the build API (`build` `:800`, `buildWithScope` `:863`,
`buildWithMemoMap` `:645`, `makeMemoMap` `:545`).

Of these, the ones an application actually reaches for are `empty`, `sync`, `catchCause`/`catchTag`
(a layer whose build can fail and be recovered) and `launch`. We have `orDie` (`Eff.lean:438`) and
nothing else on the error channel of a layer. From `Context.ts`: `Reference` — a key with a
default (`Context.ts:485-490`, `:2002-2009`) — is modelled at the machine
(`Provision.lean:515-551`, with `satisfiesRefs_of_hard` *proved* at `:543`) and is **unreachable
from the language**: `Eff.service key` always requires the key (`Typing.lean:392`), so a
configuration read has a hard requirement where rc.112 has none.

---

## 3. What the type system knows

### 3.1 The two signatures

```lean
structure EffTy where answer : Ty; error : Ty; requires : Requirement   -- Typing.lean:30-34
structure LayerTy where out : Requirement; error : Ty; requires : Requirement -- :242-246
```

`Requirement := Row ServiceKey` (`src/Effect4/Machine/Context.lean:72`), a canonical strictly
ascending list under the name-major key order (`Key.lean:102-104`), so two rows with the same
members are equal (`Row.eq_of_mem_iff`, `src/Effect4/Data/Row.lean:228`). The requirement plane
is a genuine set, and `Row.diff`/`Row.union` are its two operations.

`LayerTy.Closed l := l.requires = Requirement.empty` (`Typing.lean:271`) with a `Decidable`
instance (`:273`) is the "this deployment is complete" predicate, and `appTy_closed_iff`
(`Provision.lean:247`) relates a program-plus-layer to it.

### 3.2 What it therefore knows

- Exactly which full keys a program performs against, after expansion (`Typing.lean:560`, `:567`).
- That `scoped` discharges only `Scope` (`bodyRequires`, `:279-280`; DI-63 note at `:376`).
- That `acquireRelease` *adds* `Scope` (`:382`).
- That a merge does not feed a sibling (`merge_requires`, `Provision.lean:143`) and that
  `provide` discharges what its dependency provides (`provide_discharges`, `:86`).
- That providing a key twice is providing it once (`effTy_provideService_twice`,
  `Typing.lean:752-774`).

### 3.3 What it does not know

- **Nothing about a service's operations.** The carrier is one `Ty`; there is no record type in
  `Ty` (`src/Effect4/Program/Ty.lean`; the constructors reachable from `Eff.lean:59-60` are
  `unit, int, bool, nat, string, lit, never, prod, union, handle, option, list, except, exitOf,
  causeOf, fiberOf`). A service's shape is therefore a `handle` — an opaque name.
- **Nothing at the fragment level.** `Src Op` is a function to `Except Refusal (Eff Op)`. It has
  no answer type, no error type, no requirement row. A composition error is found by `check`
  after `elaborate` (`Api.author`, `Api.lean:501-506`), and the located refusal names a path in
  the *elaborated tree*, not the fragment the author wrote.
- **Nothing about a layer on its own.** `layerTy` exists (`Typing.lean:411`) and `printLayerT`
  exists (`Templates.lean:437`), but `Authoring.elaborate` takes `Src`, not `LayerSrc`
  (`Authoring.lean:175`) and `Effect4.Api` mentions neither (I grepped `Layer` in `Api.lean`:
  the only hits are two docstring sentences at `:94` and `:192`).
- **Nothing about the table a program is checked against.** The row table is an argument
  (`Api.typeOf program table`, `Api.lean:97`); the bytes are the program alone
  (`bytesOf = Wire.encodeProgram`, `:176`, and `NativeOp.external i` encodes the index). Two
  tables give the same bytes two meanings. `HostSession` is indexed by both
  (`Session (program) (table)`, `src/Effect4/Api/HostSession.lean:84`), which is the right shape;
  the byte boundary is not.

---

## 4. Friction, enumerated

Each row: what it is, where, and what it costs an author. All *read* unless marked.

**B-1. A service has no declaration.** `⟨⟨6⟩, ⟨7⟩⟩` (`LayerSharingContract.lean:17`) and the
knowledge that `7` means `Ref` (`Native.lean:292`) are two separate facts an author must hold.
Cost: every service is a magic pair, and a wrong code silently types as a different carrier.

**B-2. Six carriers, closed.** `nativeServiceTypes` (`Native.lean:291-293`). An application with a
seventh service type cannot be written without editing the core. The signature field is already a
function (`Typing.lean:64`), so this is a native-alphabet choice, not a design limit.

**B-3. A service's operations are on the other plane.** §2.4. Cost: `Kv.get(store, "k")` instead
of `store.get("k")` with `R = Kv`; the requirement row of a real application is empty, so the
strongest thing the type system offers is unused.

**B-4. `Row.requires` is dead.** `Eff.lean:203`, typed at `Typing.lean:302`, set by nothing shipped.
Cost: a field that types can rot; the one convention that uses it (`Provision.lean:632-644`)
cannot print.

**B-5. Package rows have no authoring surface.** The generated wrappers come from `NativeOp.all`
(`Authoring/Rows.lean` header line 2), which excludes `.external` (`Native.lean:130`). An author
writes `perform (.external 1) (app "pair" [var "store", str "k"])` and must know that `1` is
`kvGet` in the table they will pass to `Api.check`. Cost: the extension point is an integer.

**B-6. A layer cannot be authored, checked or printed alone.** §3.3. Cost: a library that ships a
layer ships an unchecked `LayerSrc`; the first error surfaces when a program provides it.

**B-7. `Layer.succeed` takes a `Lit`, and not a string.** `Eff.lean:423`; `litVal` returns `none`
for `.str` (`Typing.lean:239`, cited as `PROV-FB-STRING-VALUE`). Cost: a string-valued service
cannot use the obvious constructor. The workaround `Layer.effect key (succeed (str s))` already
works (the body is typed at `[]`, `Typing.lean:415`, and a literal is closed) and is unnamed.

**B-8. Sharing costs a path protocol.** §2.5, items 1-6. Cost: two failure modes
(`hoistAll : Except`, `restoreAll : Option`) that need totality theorems; a fuelled placement
loop; a sentinel path; two refusal reasons; typing that folds the whole tree `n+1` times.

**B-9. Minted and generated binder names are not reserved, and capture is invisible to the scope
proof.** `bindWith` mints `"_" ++ toString env.names.length` (`Sugar.lean:26-27`); `andThen` binds
the literal `"_"` (`:37`); `iterateWith` mints `"_c<n>"`/`"_a<n>"` (`Loops.lean:34-35`); the
generated forms bind `"_answer0"`, `"_answer1"`, `"_exit0"`, `"_exit1"`
(`Authoring/Forms.lean:28`, `:48`, `:56`, `:88`). `Names.resolve` returns the **last** binding
(`Authoring.lean:42-47`). So an author-chosen name equal to a generated one captures.

*Hand-evaluated witness* (not compiled — no Lean process was allowed):

```lean
-- Forms.tapContinuation answer e c  =  bind answer e (bind "_answer1" c (succeed (var answer)))
--                                                                    Authoring/Forms.lean:47-48
#guard elaborate (Forms.tapContinuation "_answer1" (succeed (nat 1)) (succeed (nat 2)))
  = .ok (.bind (.succeed (.lit (.nat 1))) (.bind (.succeed (.lit (.nat 2))) (.succeed (.var 1))))
--                                                                                       ^ 1, not 0
```

At the outer `succeed`, the environment is `["_answer1", "_answer1"]`, and `resolve` answers the
last position, `1` — the continuation's answer, not the tapped effect's. Both trees are scoped
and both type; `Src.Scoped` says "every variable is below the scope's depth"
(`src/Effect4/Laws/Program/Authoring.lean:42-43`), which this satisfies. `bindWith_scoped`
quantifies over the callback (`Laws/Program/Authoring/Sugar.lean:22-25`), so no lemma catches it.
Cost: the one class of silent wrong program the named surface was built to remove is still
reachable through a name collision.

**B-10. `Src` has no type, so composition is checked at the end.** §3.3. Cost: an agent building a
program from five fragments gets one refusal at one path, not "fragment three answers a string
where fragment four wants a number".

**B-11. `gen` is unwritable.** `binders.json` `"readerOnly": ["Effect4.Program.Eff.gen"]`. The
owner ruled `gen` stays (`docs/STATE.md:62`). Cost: nil for an agent (the `eff do` macro covers
the idiom, `Sugar.lean:106-165`); it is worth stating so nobody looks for the lift.

**B-12. Five fiber actions cannot be printed.** `interruptScoped`, `awaitAllFailFast`,
`snapshotChildren`, `awaitNewChildren`, `setContext` are `.refuse` rows
(`Templates.lean:197`, `:202-204`, `:206`) and `binders.json` lists them under `"machineOnly"`.
Cost: `setContext` in particular means a program cannot install a whole context as a value, so
`Effect.provideContext` (`Effect.ts:11667`) has no image.

**B-13. A reference key with a default is unreachable.** §2.6. Cost: configuration is a hard
requirement; rc.112's `Config<T> extends Effect<T, ConfigError>` with no `R`
(`Config.ts:108-112`, quoted at `Provision.lean:508-511`) cannot be modelled as rc.112 models it.

**B-14. The alphabet is out of band from the bytes.** §3.3 last item. Cost: a stored program is
not self-describing; a CAS address does not determine a meaning.

---

## 5. The API I would want

### 5.1 The rule I applied

A new `Eff` constructor costs, by the select packet's own measurement, roughly 71 lines in 18
files plus a wire tag plus a generator arm plus a lemma family per fold
(quoted in `2026-09-16-effect-surface-sugar-scout.md` §6). So: everything that can be a record,
a sugar definition, a row or a signature field is one of those, and exactly one construct is
priced as a construct. Few deep modules: the additions below live in **two** new files
(`Program/Authoring/Service.lean`, `Program/Authoring/Package.lean`) plus additions to
`Effect4.Api`.

### 5.2 Already rows — zero cost, nothing to build

- Every layer combinator: `merge`, `provide`, `provideMerge`, `fresh`, `orDie`, `mergeAll`, with
  their rows (`Templates.lean:211-223`), lifts (`Lifts.lean:269-305`) and proved laws
  (`Provision.lean:70-160`).
- `Effect.provide(self, layer, { local })`: `provideLayer … isLocal` with one row per flag
  (`Templates.lean:176-179`).
- A service's operation as a method on a handle: `shape := .method`, receiver the first request
  component (`Eff.lean:181`, `PrintLeaf.lean:226-263`), demonstrated end to end by
  `Packages/KeyValueStoreMemory.lean:40-56`.
- A row declaring the key it needs: `Row.requires` (`Eff.lean:203`), typed (`Typing.lean:302`).
- Reference keys with defaults at the machine: `Refs`, `SatisfiesRefs`, `satisfiesRefs_of_hard`
  (`Provision.lean:515-551`).

### 5.3 Sugar over the existing lifts — zero constructors, zero wire tags

Each needs one `*_scoped` lemma, each a one-line application of an existing lemma in the pattern
of `Laws/Program/Authoring/Sugar.lean:38-53`.

```lean
namespace Effect4.Program.Authoring

/-- `Layer.sync` / a non-literal `Layer.succeed`: a layer that provides a value already in
hand. The body is closed, so `t` must be a literal or an atom over literals. -/
def Layer.value {Op : Type} (key : ServiceKey) (t : TermSrc) : LayerSrc Op :=
  Layer.effect key (succeed t)

/-- `Layer.empty` (`Layer.ts:1155`): provides nothing, requires nothing. -/
def Layer.empty {Op : Type} : LayerSrc Op := Layer.effectDiscard (succeed unit)

/-- Several layers as siblings, one parallel build (`Layer.mergeAll`, `Layer.ts:1652`). -/
def Layer.all {Op : Type} (ls : List (LayerSrc Op)) : LayerSrc Op := Layer.mergeAll ls

/-- `Effect.provide(self, [l₁, …, lₙ])`: provide several layers at one site. -/
def provideAll {Op : Type} (ls : List (LayerSrc Op)) (body : Src Op) : Src Op :=
  provideLayer (Layer.all ls) false body

/-- `Effect.provide(self, l, { local: true })` under its Effect name. -/
def provideFresh {Op : Type} (l : LayerSrc Op) (body : Src Op) : Src Op :=
  provideLayer l true body

end Effect4.Program.Authoring
```

**A service declaration, with its operations.** One record, one agreement check, five
projections. This extends scout D's `ServiceDef` (`2026-09-17-scout-named-and-exact-service-keys.md`
§3.2, which that scout reports as *compiled* in its probe C) with the operation half:

```lean
/-- A service an author declares once: the key, the carrier the signature must type it at,
and the operations that may be performed on a value of that carrier. An operation is a row;
its receiver is the first component of its request (`RowShape.method`), which is what the
printer already prints and the reader already reads. -/
structure Service where
  key     : Effect4.ServiceKey
  carrier : Effect4.Program.Ty
  ops     : List Effect4.Program.Row := []
deriving DecidableEq, Repr

namespace Service

/-- The declaration agrees with the signature it is used under: the carrier is the one the
signature types the key at, and every operation's receiver is that carrier. Decidable, so an
author pins it with one `#guard` at the declaration site. -/
def Agrees {Op : Type} (sig : Signature Op) (s : Service) : Bool :=
  sig.serviceTy s.key == some s.carrier
    && s.ops.all fun r => match r.request.normalize with
       | .prod recv _ => recv == s.carrier.normalize
       | t            => t == s.carrier.normalize

/-- Two declarations of one key cannot disagree on the carrier. -/
theorem carrier_unique {Op : Type} {sig : Signature Op} {a b : Service}
    (hk : a.key = b.key) (ha : Agrees sig a = true) (hb : Agrees sig b = true) :
    a.carrier = b.carrier

/-- `yield* Db` — bind the service value. -/
def use {Op : Type} (s : Service) : Src Op := Authoring.service s.key

/-- `Effect.provideService(body, Db, v)`. -/
def give {Op : Type} (s : Service) (value : TermSrc) (body : Src Op) : Src Op :=
  Authoring.provideService s.key value body

/-- `Layer.effect(Db, build)` — the layer that builds this service. -/
def layer {Op : Type} (s : Service) (build : Src Op) : LayerSrc Op :=
  Authoring.Layer.effect s.key build

/-- `Layer.succeed(Db, v)` for a value already in hand. -/
def constant {Op : Type} (s : Service) (value : TermSrc) : LayerSrc Op :=
  Authoring.Layer.value s.key value

end Service
```

`carrier_unique` is scout D's proof verbatim under a different name; it is the
"conflicting carriers for one key refuse" rule of the plan (`plan:142`) moved to a `decide` at
the authoring site.

**A package, so an author never writes a row index.** This is the answer to B-5:

```lean
/-- A block of rows installed as one unit: the rows, in table order, and the services they
belong to. Installing several packages concatenates their rows and hands back each package's
base offset; `op` turns a position within the package into an alphabet position. -/
structure Package where
  name     : String
  rows     : List Effect4.Program.Row
  services : List Service := []

namespace Package

def op (base i : Nat) : NativeOp := .external (base + i)

/-- The table to pass to `Api.check`/`Api.run`, and the base of each package in it. -/
def install (ps : List Package) : RowTable × List (String × Nat)

/-- The extra service table entries the packages declare, for `nativeSignature`. -/
def services (ps : List Package) : List (Effect4.ServiceKey × Ty)

end Package
```

The generated wrappers then take the base as their one extra argument, exactly as
`Authoring/Rows.lean` takes none today:

```lean
-- generated from a Package, beside tools/Effect4Gen/Rows.lean
namespace Kv
def get (base : Nat) (store key : TermSrc) : Src NativeOp :=
  perform (Package.op base 1) (app "pair" [store, key])
end Kv
```

No wire change: `.external i` is what it is today (`Native.lean:130`), and the base arithmetic
lives entirely in the authoring layer.

### 5.4 One defaulted signature argument — no constructor, no byte moves

B-2's fix is one parameter threaded exactly as the row table already is:

```lean
-- src/Effect4/Program/Native.lean:302, :330
def nativeServiceTy (services : List (ServiceKey × Ty) := []) (key : ServiceKey) : Option Ty
def nativeSignature (table : RowTable := []) (services : List (ServiceKey × Ty) := []) :
    Signature NativeOp
```

`nativeServiceTypes` (`:291-293`) becomes the default value of `services`, so every existing call
site and every golden byte is unchanged, and a package's services join through
`Package.services`. Scout D's N2 (a `Signature.serviceName : ServiceKey → Option String` for the
printed identifier) rides on the same parameter when the printer wants it.

### 5.5 Observing the environment as data — three `Api` projections, zero cost

```lean
namespace Effect4.Api

/-- The full keys this program performs against, in the canonical key order. -/
def requires (t : Typed table) : List ServiceKey := t.ty.requires.elems

/-- Whether the program needs nothing from its surroundings. -/
def closed (t : Typed table) : Bool := t.ty.requires == Requirement.empty

/-- A layer with its signature: what it provides, its error column, what it still needs. -/
structure TypedLayer (table : RowTable) where
  layer : LayerTerm NativeOp
  ty    : LayerTy
  ok    : layerTy (nativeSignature table) layer = some ty

/-- The agent's one call for a layer, as `author` is for a program. -/
def checkLayer (l : Program.Authoring.LayerSrc NativeOp) (table : RowTable := []) :
    Except AuthorRefusal (TypedLayer table)

/-- The printed layer (`Templates.printLayerT`, already the printer's own fold). -/
def printLayer (l : TypedLayer table) : Except PrintRefusal TypeScript.Expr

end Effect4.Api
```

`checkLayer` needs one line in the authoring module — `def elaborateLayer (l : LayerSrc Op) := l {} []`,
the exact shape of `elaborate` (`Authoring.lean:175`) — and then reuses `layerTy`
(`Typing.lean:411`) and `printLayerT` (`Templates.lean:437`). This is B-6 closed for the cost of
one definition and one structure.

With it, "what does this program require" and "what does this layer provide" are both data an
agent can read before running anything, which is what the owner's "observable" asks for.

### 5.6 The one new construct: a layer binder

**What.** Replace addressing a shared layer by its path with binding it by level, exactly as a
value is bound.

```lean
-- src/Effect4/Program/Eff.lean
/-- `const L = <layer>` in scope for `body`: the layer is built at most once per run and both
its uses share one memo key, which is what `LayerTerm.ref` says today by naming a path. -/
| letLayer (layer : LayerTerm Op) (body : Eff Op)

-- replacing `| ref (target : List Nat)` at :444
/-- The `i`-th enclosing `letLayer`, counted from the front as `Term.var` counts values. -/
| var (level : Nat)
```

**Meaning equation.** Let `ρ` be the list of layer paths in scope (the compile already keeps one:
`resolveLayer` redirects a reference to its target's path rather than expanding it,
`Program/Compile.lean`, described at `Refs.lean:22-23`).

```text
compile (letLayer l b) ρ   =  compile b (ρ ++ [pathOf l])        -- the binder introduces one memo key
compile (LayerTerm.var i) ρ =  ρ[i]                               -- the reference resolves by level
meaning (letLayer l b) env st = meaning b env st                  -- no step: the binder is provision, not control
```

The second line is `ρ[i]` where today it is `Node.layerAt target`; the third is why `letLayer`
adds no machine step. Typing:

```lean
| .letLayer l b => do
    let lt ← layerTy sig ρ l                -- ρ : List LayerTy, the layer environment
    effTy sig ρ' env b                       -- ρ' := ρ ++ [lt]
| .var i => ρ[i]?                            -- replaces the `none` at Typing.lean:434
```

and `typeOfProgram` collapses back to `typeOf` (`Typing.lean:560`, `:567-570`), because there is
nothing left to expand.

**Its row.** `LayerTerm.var` keeps `ref`'s row unchanged in shape — a bare hole
(`Templates.lean:223`, `⟨.layer, "ref", [], .tpl (h 0)⟩`) — with the printed identifier `L<level>`
instead of `L_<path>`; `refName`/`readRefName` (`Refs.lean:218-243`) become `"L" ++ toString i`
and a single `Nat` parse. `letLayer` prints as the declaration block `printModule` already emits
(`Api.lean:194`), so its row is a **declaration-level** skeleton, and that is the expensive part:
the template table's families today are `eff`, `action`, `layer`, `stmt` and the three spines
(`Templates.lean:241-245`), with no declaration family. Either `letLayer` prints only at module
level (a rule, as the layer's closedness is a rule at `Templates.lean:323-327`), or the table
gains a family. I would take the rule.

**Proof obligations.**

| obligation | shape | where it replaces something |
| --- | --- | --- |
| typing | a `letLayer` arm in `effTy` and in `HasTy`, a `var` arm reading `ρ` | replaces `layerRefsWF`, `expandRefs`, `typeOfProgram` |
| scope | `binders.json` gains a *layer* slot; `Eff.scopedAt` carries a second level | `Program/Scoped.lean` is generated from that table, so the change is a row |
| round trip | `print`/`read` of `const L<i> = …` by level, and the `readable` guard | replaces `refName`/`readRefName` and their byte decoder |
| agreement | one compile equation and one reference equation (both one line, above) | replaces `Laws/Program/Hoisting.lean`, `Laws/Program/HoistingTotal.lean` |
| wire | one new tag for `letLayer`, `ref`'s tag retired, `var` takes a fresh one | `tools/Effect4Gen/wire-tags.json`, the S1 mechanism |

**What it deletes.** `placeholderBase`, `placeholder`, `placeholder?`, `Layer.ref`,
`placeholderSites`, `placeRounds`, `pointAtPlaced`, `elaborateModule`, `Module`
(`Authoring.lean:155-230`, ~80 lines); `LayerTerm.refSite`, the seven `refSites`, `expandAlgebra`,
the seven `expandRound`, `layerRefsWF`, the seven `layerPaths`, `expandRefs`, `refTargets`,
`hoistAll`, `restoreAll`, `refName`, `readGroup`, `readGroups`, `readRefName`
(`Refs.lean:103-243`, ~140 lines); both hoisting law modules; two `Reason`s
(`Authoring.lean:53-58`); two `TypeReason`s and the two `Api.explain` branches
(`Api.lean:113-117`). Net: a deletion.

**And it unifies the authoring surface.** `Env` today has `names : Names` (a scope) and
`layers : LayerNames` (a declaration table, `Authoring.lean:70-72`) resolved by two different
mechanisms. With a binder, `Env.layers` becomes a second `Names` and `Layer.ref name` becomes
`Names.resolve` on it — the same operation as `var` (`Authoring.lean:133-137`). One name
resolver, two scopes.

**When.** After R5. It changes the printed module shape, and R4/R5 own the template table
(`docs/STATE.md:45`). Doing it before R5 means doing the reader twice.

### 5.7 Priced and not recommended: a program binder

`letProgram (p : Eff Op) (body : Eff Op)` with `Eff.var` would give programs the sharing layers
have, and would shrink the wire (the dogfood findings record 5-9 KB for small programs at nine
bytes of framing per node, `2026-09-16-dogfood-findings-applied.md:60`). I recommend against it
now: that row is classed **A**, an architecture fault, and the disposition is "the codec sweep in
the spec's performance section", not an alphabet change. A program binder also puts a
program-valued position into the value language, which is the line the design holds
(`Eff.lean:19-22`, "there is no Lean function anywhere inside it"). Revisit only if the codec
sweep does not close it.

---

## 6. Three end-to-end examples

### E1 — a service, a layer that builds it, and the layer used twice

**Today** (`Test/Program/AuthoringContract.lean:186-222`, *tested*):

```lean
open Test.Program.LayerSharingContract (kA kRef)     -- def kA := ⟨⟨4⟩,⟨4⟩⟩; kRef := ⟨⟨6⟩,⟨7⟩⟩

def counter : LayerSrc NativeOp :=
  Layer.effect kA <|
    bind "ref" (service kRef) <|
    andThen (Ref.update .incr (var "ref")) <|
    succeed (nat 5)

def onceByName : Module NativeOp :=
  { layers := [("Counter", counter)]
    main :=
      bind "r" (Ref.make (nat 0)) <|
      provideService kRef (var "r") <|
      bind "n" (provideLayer (Layer.ref "Counter") false <|
                provideLayer (Layer.ref "Counter") false <| service kA) <|
      Ref.get (var "r") }

#guard elaborateModule onceByName = .ok once           -- the path-addressed tree
```

The author must know that `4` is `nat`, that `7` is `Ref.Ref<number>`, and must route the shared
layer through a `Module` whose name table becomes a sentinel path and then a placement loop.

**Proposed:**

```lean
def Counter : Service := ⟨⟨⟨4⟩, ⟨4⟩⟩, .nat⟩
def TheRef  : Service := ⟨⟨⟨6⟩, ⟨7⟩⟩, NativeOp.refTy⟩
#guard Counter.Agrees (nativeSignature) && TheRef.Agrees (nativeSignature)

def counter : LayerSrc NativeOp := Counter.layer <| eff do
  let ref ← TheRef.use
  Ref.update .incr ref
  return 5

def once : Src NativeOp := eff do
  let r ← Ref.make 0
  TheRef.give r <| letLayer counter fun L => eff do
    let n ← provideLayer L false (provideLayer L false Counter.use)
    Ref.get r
```

Two facts stated once each at the declaration (`#guard` pins the third, the signature's
agreement); the shared layer is a Lean binder over `LayerTerm.var`, not a name table; and
`Api.requires` on the result answers `[]` (*assumed*: it follows from `Typing.lean:389` and
`:401`, but I did not compile it).

### E2 — a package operation

**Today** (the row is `Packages/KeyValueStoreMemory.lean:40-43`, position 1 in that table):

```lean
def readKey : Src NativeOp :=
  bind "store" (perform (.external 0) unit) <|                       -- kvMake
  perform (.external 1) (app "pair" [var "store", str "greeting"])   -- kvGet
-- and the author must pass exactly `keyValueStoreMemory` as the table to Api.check / Api.run
```

`.external 0` and `.external 1` are hand-written positions; nothing checks that the table the
author passes is the one those positions were counted in.

**Proposed:**

```lean
def kv := Packages.keyValueStoreMemory                 -- a Package now, not a bare RowTable
def ⟨table, bases⟩ := Package.install [kv]
def b := (bases.lookup "kv").getD 0

def readKey : Src NativeOp := eff do
  let store ← Kv.make b
  Kv.get b store "greeting"

#eval Api.author readKey table                          -- one call, one table, no index
```

The wrappers `Kv.make` / `Kv.get` are generated from the package's rows by the emitter that
already generates `Authoring/Rows.lean`.

### E3 — a two-service deployment with a shared dependency

**Today** (`Provision.lean:615-695`, *read*; there is no authoring surface for it, and its rows
cannot print — §2.4):

```lean
def dbKey : ServiceKey := ⟨⟨10⟩, ⟨10⟩⟩ ; def rateKey : ServiceKey := ⟨⟨11⟩, ⟨11⟩⟩
def dbBinding : ServiceKey := ⟨⟨20⟩, ⟨20⟩⟩ ; def rateBinding : ServiceKey := ⟨⟨21⟩, ⟨21⟩⟩

def servicesLayer : LayerTerm DocsOp :=
  .merge (.effect dbKey (.perform .makeDb (.lit .unit)))
         (.effect rateKey (.perform .makeRate (.lit .unit)))
def bindingsLayer : LayerTerm DocsOp :=
  .merge (.succeed dbBinding (.nat 1)) (.succeed rateBinding (.nat 2))
def deploymentLayer : LayerTerm DocsOp := .provideMerge servicesLayer bindingsLayer
def feedbackHandler : Eff DocsOp :=
  .bind (.perform .rateCheck (.lit .unit)) (.perform .insertFeedback (.lit (.nat 1)))
```

Written by level, in a private alphabet, with a private signature (`docsSig`, `:652`) and a
private leaf semantics (`docsSem`, `:655`). The mistake the note itself flags —
`siblingMistake := .merge servicesLayer bindingsLayer` (`:693`) — is caught only by typing the
whole application.

**Proposed** (the same deployment, with the layer checked before the program exists):

```lean
def Db   : Service := ⟨⟨⟨10⟩,⟨10⟩⟩, .handle "Db",        [dbRows…]⟩
def Rate : Service := ⟨⟨⟨11⟩,⟨11⟩⟩, .handle "RateLimit", [rateRows…]⟩
def DbEnv   : Service := ⟨⟨⟨20⟩,⟨20⟩⟩, .nat⟩
def RateEnv : Service := ⟨⟨⟨21⟩,⟨21⟩⟩, .nat⟩

def services : LayerSrc NativeOp :=
  Layer.all [ Db.layer   (eff do let e ← DbEnv.use   ; Db.make b e)
            , Rate.layer (eff do let e ← RateEnv.use ; Rate.make b e) ]

def bindings : LayerSrc NativeOp :=
  Layer.all [ DbEnv.constant 1, RateEnv.constant 2 ]

def deployment : LayerSrc NativeOp := Layer.provideMerge services bindings

def handler : Src NativeOp := eff do
  let rl ← Rate.use ; Rate.check b rl
  let db ← Db.use   ; Db.insertFeedback b db 1

-- checked before anything is provided:
#eval (Api.checkLayer deployment table).map (fun l => (l.ty.out.elems, l.ty.requires.elems))
-- => .ok ([Db, Rate, DbEnv, RateEnv], [])        -- the deployment is closed
#eval (Api.author handler table).map Api.requires
-- => .ok [Db, Rate]                              -- the program's environment, as data
```

The sibling mistake is now caught by `Api.checkLayer bindings`-then-`merge` answering a
non-empty `requires`, before a program is written. Nothing here is compiled; the two `#eval`
shapes follow from `LayerTy.provideMerge` (`Typing.lean:258-260`) and `Typing.lean:302`.

---

## 7. Open decisions, with my recommendation

**D-B1. The receiver convention for a service's operations.**
(a) receiver as a *value*: the handle is the first request component, `shape := .method`
(`Packages/KeyValueStoreMemory.lean:41`); (b) receiver as a *requirement*: `Row.requires = [key]`
and the receiver spelled into the name (`Provision.lean:632-644`).
**Recommend (a).** It prints and reads today; (b) prints an unbound identifier. It also matches
the rc.112 idiom an agent knows: `const db = yield* Db; db.query(…)`. Consequence: `Row.requires`
gains no user from this decision — see D-B2.

**D-B2. `Row.requires`: keep or delete.**
**Recommend keep, with a guard.** A row that reads an *ambient* service without taking it as a
receiver (a clock, a logger, a config provider) is the honest user of the field, and rc.112 has
exactly those. Add a shipped-row guard: every row's `requires` is `[]` or every key in it is in
the signature's service table. That turns a rotting field into a checked one for one `#guard`.

**D-B3. `Layer.succeed` with a `Term`.**
(a) widen the constructor `succeed (key) (value : Lit)` → `(value : Term)`; (b) leave it and name
the workaround `Layer.value key t = Layer.effect key (succeed t)` (§5.3).
**Recommend (b).** (a) moves every golden byte of every program that uses `Layer.succeed` and
gains one printed shape; (b) is four lines and one lemma. Revisit only if the printed
`Layer.effect(k, Effect.succeed(v))` is judged wrong for the ingest lane.

**D-B4. The layer binder (§5.6).**
**Recommend yes, scheduled after R5.** It is a net deletion of roughly 220 lines plus two proof
modules, it collapses `typeOfProgram` into `typeOf`, and it makes layer sharing use the one name
resolver the value scope already uses. It costs one constructor, one retired wire tag, one new
family rule in the printer, and a second level in `scopedAt`. If the owner would rather not spend
a constructor now, the second-best move is to leave `ref` alone and **not** invest further in the
placeholder protocol.

**D-B5. `nativeServiceTy` as a supplied table (§5.4).**
**Recommend yes, now.** One defaulted argument, no byte moves, and it removes the six-carrier
ceiling that makes every application squeeze its services into `nat`/`bool`/`unit`/three handles.
It is also the prerequisite for `Service.Agrees` to be worth writing.

**D-B6. Reserved binder names (B-9).**
(a) reserve a prefix the author cannot write (refuse a name starting with `"_%"` in `bind`, or
mint names outside the identifier alphabet); (b) make `bindWith`/`iterateWith`/the forms mint
from a counter carried in `Env` rather than from `names.length`; (c) do nothing.
**Recommend (a).** It is one check in one place (`Authoring.lean`, beside `var`), it produces a
located refusal in the existing shape, and it closes the one remaining class of silent wrong
program. (b) does not help: the collision is with an author-chosen *spelling*, not with a
counter. Whichever is taken, add the `#guard` of B-9 as the red control.

**D-B7. A type for a fragment (B-10).**
(a) do nothing, `Api.check` after `elaborate` is the contract; (b) a `TypedSrc` carrying an
`EffTy` alongside a `Src`, checked compositionally.
**Recommend (a) for now, and record (b) as the S9a question.** (b) means a second type system
over the authoring layer that must agree with `effTy`, and the agreement theorem is the whole
cost. The cheaper move in the same direction is `Api.requires`/`Api.checkLayer` (§5.5), which
gives an agent the composition facts *after* one cheap check rather than a second checker.

**D-B8. `Context.Reference` with a default (B-13).**
The machinery is proved at the machine (`Provision.lean:515-551`) and unreachable from the
language. **Recommend: no new constructor.** A reference read is `service key` under a signature
whose `serviceTy` types the key and whose deployment always provides it, i.e. it is a *rule about
the table*, not a construct — and D-B5's supplied service table is where that rule would live.
Record it; do not build it until `Config` is on the plan.

---

## 8. Receipt

**Read in full**: `src/Effect4/Program/Eff.lean` (571 lines), `Program/Authoring.lean` (232),
`Program/Authoring/Lifts.lean` (430), `Program/Authoring/Sugar.lean` (167),
`Program/Authoring/Loops.lean` (63), `Program/Authoring/Rows.lean` (166),
`Program/Authoring/Forms.lean` (172), `Program/Refs.lean` (259), `Program/Typing.lean` (789),
`Program/Decision.lean` (109), `Codegen/Templates.lean` (440), `Api.lean` (543),
`Machine/Key.lean` (389), `Test/Program/AuthoringContract.lean` (319),
`tools/Effect4Gen/binders.json`, `Packages/KeyValueStoreMemory.lean` (57), `docs/STATE.md` (75),
`docs/research/2026-09-16-core-constructs-brief.md` (199),
`docs/research/2026-09-16-dogfood-findings-applied.md` (169).

**Read in part**: `Program/Provision.lean` (§Refs 505-560, the docs witness 586-700, the law list
by grep), `Program/Native.lean` (the row alphabet, the service table, the signature, 130-365),
`Program/LayerView.lean` (the `ArgF`/`ArgSort`/`ofLayer` head, 1-120, and the declaration list by
grep), `Codegen/PrintLeaf.lean` (`printRow`, `printKey`, 220-308), `Codegen/Forms.lean` (1-89),
`Laws/Program/Authoring.lean` (1-70), `Laws/Program/Authoring/Sugar.lean` (1-60),
`Laws/Program/Hoisting.lean` and `HoistingTotal.lean` (theorem statements only),
`Api/HostSession.lean` (declaration list), `Test/Program/LayerSharingContract.lean` (1-90),
`docs/research/2026-09-17-scout-named-and-exact-service-keys.md` (§0, §1.1-1.3, §2.1-2.3, §3.1-3.2),
`docs/research/2026-09-16-effect-surface-sugar-scout.md` (§1, §2.6-2.8, §6),
`vendor/effect-4.0.0-rc.112/src/Context.ts` (1-330, 480-520, 1000-1020, 2000-2009),
`Layer.ts` (export list, the cited lines), `Effect.ts` (the provide/service export list and
`provide`'s overloads at 11383-11520).

**Not reached**: `Program/Compile.lean` (88 KB — I relied on `Refs.lean:22-23` and
`Templates.lean` for what the compile does with a reference, and marked the `letLayer` compile
equation as a proposal, not a reading of the compile), `Program/Fold.lean` (166 KB),
`Program/Derived.lean` (129 KB), `Codegen/Read.lean` beyond the `readKey` theorem names, the
OCaml face, `ts/eff`, the dogfood dispatch briefs (`docs/agents/dispatches/2026-09-15-dogfood-*.md`
**do not exist**, in the working tree or in git history — `docs/agents/dispatches/` holds two
files, `2026-09-12-part4-subsumption.md` and `2026-09-16-seat2-profile-deletion-and-structural-type-arguments.md`;
I used the three receipts, the three reviews and the findings-applied note under `docs/research/`
instead).

**Nothing in this note was compiled, run or proved by me.** No Lean process was started; the hard
rule was kept. Every `#guard` and `#eval` written above is a proposal or a hand-evaluation, marked
as such at its site. The theorems I call *proved* exist in the tree at the file and name given.
