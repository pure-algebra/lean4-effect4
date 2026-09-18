# Scout D — Effect Schema interop, dogfooded; and the applications regroup (2026-09-17)

Scouted at `d798feb2` in `/Users/pooks/Dev/lean4-effect4-scout-d`. Every claim about the tree is cited `file:line` at that commit. **Reproduced** = a `#eval` printed it in a `lake env lean` probe there; **proved** = a Lean theorem or a `#synth` failure there; nothing is assumed.

**Summary.** Interop is half built and wholly unused. The lowering half is real and proved: `Ty.schema` maps all sixteen constructors to rc.112 `SchemaRepresentation` nodes (`src/Effect4/Schema/Bridge.lean:38`), `ofSchema_schema` is a constructive retraction (`:114`), `EffTy.document`/`Row.document` build the boundary documents (`:162`, `:175`), and `Schema.Codec` encodes and decodes at a type with seven proved laws (`src/Effect4/Laws/Schema/Codec.lean:14-90`). The consuming half does not exist: `Api.schemaOf` (`src/Effect4/Api.lean:138`) has **zero** call sites in `src/`, `Test/`, `tools/`, `harness/`; `Row.document` has zero; the printer emits no document and emits **no** `Effect.Effect<A,E,R>` annotation at all for a program with a requirement (`src/Effect4/Codegen/Print.lean:70-79`); no gate checks a program's exit against its own schema. D12's enforcement sentence is true of a function nobody calls. Four defects are proved: `effDocument`'s requirement half keys on half a `ServiceKey` and emits duplicate reference keys (§7.1); a handle column publishes an opaque declaration while the value that crosses is a **number equal to the allocation counter** (§7.2); `ofSchema` silently widens refinements, brands, annotations and declaration payloads (§7.3); the program carrier's own shape document repeats reference keys (§7.4). `Ty` cannot express `Schema.Struct`, `TaggedUnion`, `Record`, `suspend`, `$ref`, three-member unions, non-string literals or any refinement, so a record is a nameless nested tuple and a sum is an `anyOf` of tagged tuples — the estate carries two incompatible sum encodings at once (§6). Keep **`Representation`/`Document`** canonical, with `Ty`, `Shape` and the TypeScript text as folds (§5). The five original applications survive only in receipts — **the five dispatch briefs exist nowhere on disk or in git** (§8) — and of the frictions that stopped them, the option eliminator and the loop are fixed today (proved), while `gen` has no authoring lift at all.

---

# Part 1 — the dogfood, concretely

**E2** of the author battery, the rc.112 key-value package (`Test/Program/AuthorContract.lean:116-121`), restated verbatim in the probe:

```lean
def kv : Package := Package.ofRows "kv" Packages.keyValueStoreMemory
def readKey : Module NativeOp := Package.install [kv]
  { main := eff do
      let store ← Row.call (kv.op "Kv.make") unit
      Row.call (kv.op "get") (app "pair" [store, str "greeting"]) }
```

`Api.Author.build readKey` succeeds. **Reproduced:** `ty.answer = Ty.option Ty.string`, `ty.error = Ty.prod Ty.string Ty.string`, `requires = []`, `closed = true`, `table.length = 5`, `bytes = 321`, `Api.ofBytes bytes = some program`, `readable = true`, and `Built.print` is `Effect.flatMap(Kv.make(), (a0) => a0.get("greeting"))`.

## 1. The program as a schema

`Api.schemaOf` answers a `Document` (`src/Effect4/Api.lean:138` = `typeOf` mapped through `EffTy.document`). **Reproduced** for E2, the root representation is the Lean value

```lean
.declaration ⟨"effect/schema/Exit", .null⟩ none
  [ .declaration ⟨"effect/schema/Option", .null⟩ none [.string none []] []
  , .arrays none [] [⟨false, .string none [], none⟩, ⟨false, .string none [], none⟩] []
  , .declaration ⟨"effect/schema/Defect", .null⟩ none [] [] ] []
```

with `references` keyed `["answer", "error"]`. Its Effect Schema spelling is `Schema.Exit(Schema.Option(Schema.String), Schema.Tuple([Schema.String, Schema.String]), SchemaRepresentation.Defect)` (`vendor/effect-4.0.0-rc.112/src/Schema.ts:10906`, `:9686`, `:4412`, `:10844`). **Computed by a Lean function** (`Bridge.effDocument`, `Schema/Bridge.lean:162`, over `Bridge.schema`, `:38`); not generated, nothing hand-typed.

**What it is not.** `Api.schemaDocument`'s docstring (`src/Effect4/Api.lean:591`) and the module note (`:60-61`) both claim "a persisted Schema document as its `Schema.Struct({…})` syntax". False: `Codegen.Schema.documentExpr` (`src/Effect4/Codegen/Schema.lean:310`) runs `printAlgebra` (`:233`), whose arms emit `{"_tag": "Declaration", "representation": {"id": …}, "typeParameters": […], "checks": []}` literals — the **persisted JSON** of a `SchemaRepresentation.Document`, reconstituted by `SchemaRepresentation.fromJson` (`SchemaRepresentation.ts:1177`), which is what `documentDecl` (`Codegen/Schema.lean:426`) writes. **No `Schema.*` combinator text is produced anywhere in the tree.** rc.112 can produce it — `toCodeDocument(document: MultiDocument): CodeDocument` (`SchemaRepresentation.ts:908`), `Code = {runtime, Type}` (`:648`) — but only for a **live** document whose declarations carry `toCode` callbacks, which a `fromJson` document lacks (`Declaration` has no such field, `:144-151`; callbacks come from revivers, `:574-598`). So the route to `Schema.Struct` text needs host revivers for the six ids the bridge mints (`effect/schema/{Option,Result,Exit,Cause,Fiber,Defect}`) plus every `handle` target — a group that does not exist and belongs beside `ts/eff/eff.gen.ts` under `tools/Tools/TsGen.lean` (D-6).

**The table.** `Built.bytes` and `Built.print` are both functions of `b.table`; `schemaOf` takes the table only to *type* the program and its document mentions no row. `Row.document` exists per row (§2) and **nothing joins them**.

**The program's own AST as a schema exists and is the stronger object.** `Canonical.shape Api.Program` is a `ShapeDoc`: **reproduced**, root `Shape.named "Eff"` with 17 definitions `[Eff, Stmt, Stmts, Effs, ActionTerm, LayerTerm, LayerTerms, Term, Terms, CauseTerm, Term, Terms, Term, Terms, Ty, Term, Terms]`, which `ShapeDoc.document` (`src/Effect4/Store/Shape.lean:468`) turns into a 156 KB persisted `Document`. On the TypeScript side the same families are **derived by a generator** as real Effect Schemas: `ts/eff/eff.gen.ts` exports `Ty`, `Lit`, `Term`, `CauseTerm`, `NativeOp`, `ServiceKey`, `Decision`, `Eff`, `Stmt`, `ActionTerm`, `LayerTerm`, `Row`, `EffTy` as `Schema.TaggedUnion` / `Schema.Struct` / `Schema.Literals`, with `export const decodeEff = Schema.decodeUnknownSync(Eff)` (`:390`), written by `tools/Tools/TsGen.lean`. **That is the one place where "a program is an Effect Schema value" is literally true today.**

## 2. The input as a schema

E2 calls positions 0 and 1 of `Packages.keyValueStoreMemory` (`src/Effect4/Program/Packages/KeyValueStoreMemory.lean:36-56`). **Reproduced**, with `kvTy = .handle "KeyValueStore.KeyValueStore"` (`src/Effect4/Program/Native.lean:157`): `kvMake` (0) is `request .unit, answer kvTy, error .never`; `kvGet` (1) is `request (.prod kvTy .string), answer (.option .string), error (.prod .string .string)`; `kvSet` (2), `kvRemove` (3) and `kvHas` (4) take `.prod kvTy …` and answer `.unit`, `.unit`, `.bool` at the same error.

`Row.document` (`Schema/Bridge.lean:175`) gives each row references `["request", "answer", "error"]` (**reproduced**). `kvGet`'s request lowers to `.arrays none [] [⟨false, .declaration ⟨"KeyValueStore.KeyValueStore", .null⟩ none [] [], none⟩, ⟨false, .string none [], none⟩] []`, i.e. `Schema.Tuple([Schema.declare(…KeyValueStore…), Schema.String])` (`Schema.ts:4412`, `:493`). **Computed by a Lean function**; not generated, not hand-typed; no such TypeScript is emitted.

**The service carriers are not in the document — that part is hand work.** `Built.requires` is a `List ServiceKey` (`src/Effect4/Api/Author.lean:88`) and the carrier is `(nativeSignature table).serviceTy k` (`src/Effect4/Program/Native.lean:302-307`), but `effDocument`'s requirement half (`Schema/Bridge.lean:167`) files per key `⟨"service_" ++ k.name.value, schema (.handle ("service_" ++ k.name.value))⟩` — a nullary declaration **named after the key**, carrying no carrier. **Reproduced** on a program requiring `⟨⟨10⟩,⟨4⟩⟩` (a `number`) and `⟨⟨10⟩,⟨5⟩⟩` (a `boolean`): both entries are `.declaration ⟨"service_10", .null⟩ none [] []`. An author who wants the carriers as schemas must call `serviceTy` and `Ty.schema` himself. Fix at `Schema/Bridge.lean:167`, which must take the signature or the `Built`; generator group: none, this is a Lean function.

## 3. The output as a schema

`Built.ty.answer = .option .string` → `Schema.Option(Schema.String)`; `.error = .prod .string .string` → `Schema.Tuple([Schema.String, Schema.String])`. Both computed by `Bridge.schema`.

**The `Observation` has no schema, and exactly two instances are missing.** `Effect4.Observation` (`src/Effect4/Run.lean:220-240`) is nine first-order fields. **Proved** by `#synth` here: seven already have `Store.Canonical` instances — `Api.HostProtocol.State`, `Api.Outcome`, `Option ExitV`, `List Program.Await`, `List Api.HostSession.Key`, `Nat`, `List Api.FrontierReason` — and **reproduced** on a live run their bytes are 19, 19, 9, 118, 9, 9, 9, 82. The failures are exactly `Store.Canonical (List (FiberId × Api.FiberStatus))`, which **fails to synthesize** (the gap is `Canonical Api.FiberStatus`; `src/Effect4/Api/Supervision.lean:197-211` is in no generator group), and `Canonical Effect4.Observation`, which does not exist. **Where they go:** two entries appended to the `Runner` group of `tools/Effect4Gen/manifest.json` after `Effect4.Api.Outcome`, as `"Effect4.Api.FiberStatus"` then `"Effect4.Observation"`, emitting into that group's existing `src/Effect4/Api/RunnerDerived.lean`. That closes run receipt O-8 with no hand codec, as `src/Effect4/Run.lean:33` anticipates.

**`Inspection` cannot cross and should not.** It holds a `Machine` (`src/Effect4/Api.lean:274-278`), hence live handles, and no `Shape` accepts a handle by construction (`src/Effect4/Store/Shape.lean:60-90`; note at `src/Effect4/Api/RunnerBytes.lean:24-26`). The `Observation` is what crosses — the right split, and why only it needs the instance.

**Reproduced end to end:** with a reactor answering both rows, `Run.runWith` reaches `Exit.success (Val.some (Val.str "hello"))` in 8 rows, `state = .terminated`, `outcome = .finished`, `applied = 2`, `awaiting = []`, `fibers = 1`, `daemonsQuiet = true` — **but only when the `kvMake` answer is a `Val.nat`**; a `Val.handle 9 0` is refused at `Phase.refused Refusal.envelope` (§7.2).

## 4. The round trip

`Ty.ofSchema` (`Schema/Bridge.lean:63`) is the only reader, and `ofSchema_schema` (`:114`) proves `ofSchema (schema t) = some t` for all sixteen constructors at `[propext]` — the lowering is injective. An arbitrary rc.112 `Representation` is another matter. Every row **reproduced**:

| input | `ofSchema` | the field where information is lost |
| --- | --- | --- |
| `String` + `Filter{minLength}`; `+ Filter{brand}` | `some .string` | `Representation.checks` — reprints as bare `.string none []` |
| `String` with `annotations{title}` | `some .string` | `Representation.annotations` |
| `Declaration{id, annotations, checks}`; `{id, payload:"v2"}` | `some (.handle id)` | both, plus `RepresentationAnnotation.payload` — reprints `payload: null, checks: []` |
| `Exit[string, bool, string]` | `some (.exitOf .string .bool)` | the third parameter is not checked against `Defect` |
| `Objects` (a `Schema.Struct`); `Literal 42`/`true`; `Union` of three or mode `oneOf`; `Number` with no checks; `Null`, `Undefined`, `Unknown`, `Any`, `BigInt`, `Enum`, `TemplateLiteral` | `none` | refused |
| `Suspend`; `Reference{$ref}` | `none` | refused — **a document's own reference table cannot be read back** |
| `Number` `[nonNeg, isInt]` (swapped); `[isInt, nonNeg, extra]` | `none` | refused — **the check list is order-sensitive** |
| `Arrays` of three, or with an optional element | `none` | refused — exactly two (`prod`) or one `rest` (`list`) |

Memory's B19 ("types as syntax, no inverse") is honoured in that `ofSchema` is partial, but **the leaves are not partial where they must be**: a refinement is accepted and erased, not refused (§7.3). A sound Schema→`Ty` pipeline already exists on the host and is not wired up: `SchemaRepresentation.toRepresentation(ast, options): Document` (`SchemaRepresentation.ts:784`) turns any live schema into a document, `toJson` (`:1134`) serialises it, `Canonical Document` exists (the `Schema` group of `tools/Effect4Gen/manifest.json`) so it crosses as canonical bytes, and `Ty.ofSchema` runs on the root. **No file under `ts/` mentions `SchemaRepresentation` at all** (grepped: zero hits).

---

# Part 2 — is it clean, is it right

## 5. One representation or several

| # | object | where | relation |
| --- | --- | --- | --- |
| 1 | `Representation` (22 tags) + `Check` | `src/Effect4/Schema/Representation.lean:701-779` | **the faithful mirror of rc.112's persisted AST**, gated tag-for-tag by `make check-schema-pins` (`Makefile:413-416`) |
| 2 | `Document` / `MultiDocument` | `src/Effect4/Schema/Document.lean:127`, `:141` | a root plus a reference table over (1) — the pinned container |
| 3 | `Ty` (16 ctors) | `src/Effect4/Program/Ty.lean:23-41` | **a fold into (1)** (`Bridge.schema`, retraction proved); a smaller language, not a copy |
| 4 | `Shape` / `ShapeDoc` | `src/Effect4/Store/Shape.lean:60`, `:121` | **a fold into (2)** (`:468`); a third type language, over `Val` not over a program's types |
| 5 | the TypeScript `Schema.*` text | `ts/eff/eff.gen.ts` | **a fold out of the Lean environment, not out of (1)** — `tools/Tools/TsGen.lean` reads the inductives directly |
| 6 | the persisted JSON literal | `src/Effect4/Codegen/Schema.lean:299-318` | **a fold out of (1)** into `TypeScript.Expr`; not `Schema.*` combinators (§1) |
| 7 | the OCaml schema AST | plan only, `docs/research/2026-09-17-runner-schema-codegen-plan.md` §3 | to be compiled from (4) through LCNF |

**Same object under a fold:** (2) over (1); (3)→(1); (4)→(2); (6) out of (1); (7) out of (4). **A second representation that can drift:** (5), generated from the environment rather than from (1) — and it is where the estate holds **two sum encodings at once**: `eff.gen.ts` spells a Lean inductive `Schema.TaggedUnion({…})` (`:62`, `:87`, `:99`, …) while `Ty.schema` spells a program's own sum as an `anyOf` of `Arrays` headed by a string `Literal` (§6). Also drifting: `harness/truth/prelude.ts`, which its own header calls a "Hand-written transcription (no generator exists for it yet)" (`:9`) and which carries **no schema at all** for the twenty atoms and two `select` heads every printed program imports.

**Recommendation — keep (1)+(2) canonical.** It is the only one pinned to rc.112 by a gate, the only one with both a `Canonical` instance and a generated fold (`src/Effect4/Schema/Fold.lean`, group `SchemaFold`), and the only one rc.112 reads back (`fromJson`). The folds that produce the rest: `Ty → Representation` exists, keep (make `ofSchema` conservative, §7.3); `Shape → Document` exists, keep (deduplicate, §7.4); **`Document → Schema.* text` does not exist** and is the missing group (D-6); `Document → the TypeScript families` should **replace** (5)'s environment read, so TsGen emits from `Canonical.shape α` — a `ShapeDoc`, hence a `Document` — and the schema a host decodes with is the shape a byte reader checks against (DI-40 one level up). `Document → the OCaml AST` unchanged.

## 6. The rc.112 Schema surface we do and do not cover

The 22 `Representation` tags are a complete, gated mirror. What `Ty` can *express* is narrower: `Ty.schema`'s image uses only **9** tags — `declaration`, `never`, `void`, `string`, `number`, `boolean`, `literal`, `arrays`, `union` — and never `reference`, `suspend`, `null`, `undefined`, `unknown`, `any`, `bigint`, `symbol`, `uniqueSymbol`, `objectKeyword`, `enum`, `templateLiteral` or **`objects`**.

| rc.112 constructor | expressible | how, or why not |
| --- | --- | --- |
| `String`, `Number`, `Boolean`, `Void`, `Never`; `Array` (`Schema.ts:4738`); `Option` (`:9686`), `Result` (`:10007`), `Exit`, `Cause`, `Fiber` | yes | direct; `list`; `declaration` with type parameters |
| `Literal` (`:2785`) | **string only** | `Ty.lit : String`; `Literal 42`/`true` refuse |
| `Tuple` (`:4412`) | **arity 2 only** | `prod`; a 3-tuple nests out, refuses in |
| `Union` (`:4923`) | **binary `anyOf` only** | `union`; 3 members and `oneOf` refuse |
| `declare` (`:493`) | **nullary only** | `Ty.handle target` is a *string*: **reproduced**, `.handle "Ref.Ref<number>"` lowers to `Declaration{id: "Ref.Ref<number>", typeParameters: []}`, so a generic handle's arguments are baked into the id. `Ty.app name args` is planned (`docs/research/2026-09-16-generation-medium-workshop.md` §5 step 3) and absent |
| **`Struct` (`:3581`)** | **no** | no `objects`; a record is a nameless nested `prod`, so field names do not exist at the boundary |
| **`TaggedUnion` (`:6470`)** | **no** | a sum is `union (prod (lit "A") T) …` with `tagIs`. **Reproduced**: the job queue's error type lowers to `anyOf [Arrays[Literal "Fatal", String], Arrays[Literal "Transient", String]]`, not what `TaggedUnion` produces |
| `Record` (`:3961`); `optional` (`:2511`), `NullOr` (`:5012`), `UndefinedOr` (`:5035`) | no | no index signature in `Ty`; `option` is rc.112's `Option`, not `A \| undefined`, and `ElementOf.isOptional` exists in (1) but refuses in |
| refinements / `check`; `brand` (`:5242`) | **no** | **dropped, not refused** (§7.3) |
| `decodeTo` (`:5585`); `Class` (`:14660`), `Opaque` (`:6537`) | no | no representation; would need a declaration plus a reviver |
| `suspend` (`:5112`) / recursion; `Enums`, `TemplateLiteral` (`:2915`) | **no** | `Suspend` and `Reference` both refuse; `Ty` is finite by construction |

Two more reproduced facts about `union`: normalisation sorts members by structural key, so the emitted `anyOf` order is canonical rather than written (`Ty.normalize`, `src/Effect4/Program/Ty.lean:434`) while `SC-DOC-07` — canonical emission order for unions — is named open at `src/Effect4/Schema/Document.lean:55-56`; and subtyping absorbs, so `union (lit "a") string` normalises to `string` and a literal member vanishes from the schema.

**What the Part 3 applications need first:** (i) **`Struct` with field names** — all five have a record-shaped request or answer, all positional today; (ii) **`TaggedUnion`** — the job queue's error column and any domain error; (iii) **refinements** — the limiter's `limit`, the pool's size, and `nat` already *is* a refinement (`isInt` + `≥ 0`), so the machinery is there; (iv) **`suspend`/`Reference`** — the ledger's recursive entries. `brand`, `Class`, transformations and `Record` are needed by none of the five. The estate's own answer to (i) and (ii) (`docs/research/2026-09-16-core-goals-and-end-state.md` §4.4) is "S9 sugar for `{ tag, payload }` and `{ a, b }` over these two, with no carrier change" — which keeps Lean simple and leaves the schema face wrong, because sugar over a nested `prod` still lowers to `Arrays`. D-1.

## 7. What is wrong

### 7.1 `effDocument`'s requirement half keys on half a `ServiceKey` (proved)

`Schema/Bridge.lean:167` builds each requirement reference from `k.name.value` alone, dropping `k.service`. Both halves are significant: `nativeServiceTy` types a key by its **code** (`src/Effect4/Program/Native.lean:291-307`), so `⟨⟨10⟩,⟨4⟩⟩` is `number` and `⟨⟨10⟩,⟨5⟩⟩` is `boolean`. **Reproduced:** a program requiring both has document reference keys `["answer", "error", "service_10", "service_10"]` — a duplicate key whose two entries are the same meaningless declaration. Nothing refuses it: reference-key uniqueness is explicitly deferred (`src/Effect4/Schema/Document.lean:106-113`, `E4-SCHEMA-CE-012`), and `fromJson` collapses the table into a map. Everywhere else the key is spelled `k{name}_{service}` — the printed class is `Context.Service<number>("k4_4")` (`Test/Program/AuthorContract.lean:104`). **Fix:** `s!"service_k{k.name.value}_{k.service.value}"`, and file the *carrier's* schema, which needs the signature threaded into `effDocument`.

### 7.2 A handle column publishes an opaque declaration; a number crosses (proved)

`kvMake`'s answer is `.handle "KeyValueStore.KeyValueStore"`, whose schema is `Declaration{id: "KeyValueStore.KeyValueStore"}` — "opaque on the host, by design" (`docs/research/2026-09-10-schema-at-boundaries.md` §3 S-1). The value that crosses is checked by `externalValue` (`src/Effect4/Program/Compile.lean:1354-1365`): the `.handle target` arm accepts `.nat index` **only when `externalHandleTarget target && index == allocated.length`**, i.e. the admissible boundary value is a natural number equal to the current allocation count — in schema terms `Schema.Number` with `isInt`, non-negative and an equality check against a counter. **Reproduced:** a reactor answering `Val.handle 9 0` is refused at `Phase.refused Refusal.envelope` (`src/Effect4/Api/HostSession.lean:172` → `src/Effect4/Program/Admit.lean:183-194` → `:59-76`), while `Val.nat 0` is accepted and the run finishes with `applied = 2`. **This is the sharpest D12 violation in the tree**: the schema the boundary publishes and the values it accepts are different sets, and the gate that would have caught it (S-5's exit decoding) was never built. D-2. Consistent with it, S-3's `isSupported` refuses `handle`, `fiberOf` and `int` outright (`src/Effect4/Schema/Codec.lean:45-49`) — the codec already knows a handle has no honest JSON image; the *document* does not.

### 7.3 `ofSchema` widens instead of refusing (proved)

`Schema/Bridge.lean:71` is `| .string _ _ => some .string` — the `checks` position is matched and discarded, as at `boolean` (`:72`), `literal` (`:73`) and every `declaration` arm (`:74-99`). The `number` arm (`:66-70`) does the opposite and is right: an unrecognised check list refuses. **Reproduced:** `String.check(minLength 3)`, `String.pipe(brand)` and `String.annotate({title})` all read as `.string` and reprint as bare `.string none []`; a `Declaration` with annotations, checks and a payload reads as `.handle id` and reprints with all three erased. As an *admission* rule that is unsound: a contract saying "a string of at least three characters" is admitted as "any string". **Fix:** every leaf arm refuses a non-empty `checks` and a non-`null` declaration payload, allowing only the two checks the bridge mints (`Schema/Bridge.lean:27-31`). Two lines per arm; `ofSchema_schema` unaffected because `schema` emits no other check.

### 7.4 The program carrier's shape document repeats reference keys (proved)

**Reproduced:** `Canonical.shape Api.Program` has 17 definitions with `Term` and `Terms` each appearing four times; `ShapeDoc.document` copies them verbatim, and the rendered JSON repeats `"Term":` four times in a 156 KB object. The four bodies are **identical** (reproduced), so a map-collapsing consumer is unharmed — but this is what `E4-SCHEMA-CE-012` exists for, `ShapeDoc.wellTagged` returns `true` on it (reproduced; it checks tags, not names), and `SC-DOC-07` is open. The duplicates come from `Canonical (α × β)` appending its components' tables, which `src/Effect4/Store/Shape.lean:25-31` documents as deliberate (`acceptsIn_mono` makes it safe for *acceptance*, not for emission). **Fix:** `ShapeDoc.document` deduplicates by key and refuses a repeated key with different bodies — one function, at `Store/Shape.lean:468`.

### 7.5 D12's enforcement has no reader (checked by exhaustive grep)

`Api.schemaOf`: **zero** call sites outside its definition. `EffTy.document`: one, that definition. `rowDocument`/`Row.document`: **zero**. `effObjectDocument`: one `#guard` (`Test/Codegen/SchemaGenerationContract.lean:528`). `Ty.schema`/`Ty.ofSchema`: only the retraction guards (`:120-168`). `Api.schemaDocument`: one `#print axioms` (`Test/Api/ApiContract.lean:348`). Against the ruling (`docs/research/2026-09-10-schema-at-boundaries.md` §1, S-4, S-5):

- "the printer emits the document beside the program" — **not done**; no `documentExpr` or `documentDecl` call in `Codegen/Print.lean`, `Codegen/Target.lean`, `Codegen/Templates.lean`.
- "always emits the `Effect.Effect<A, E, R>` annotation … with a schema for `R` that gap closes" — **not done, and total**: `declarationType` (`src/Effect4/Codegen/Print.lean:70-79`) returns `.ok none`, i.e. **no annotation at all**, whenever `ty.requires ≠ Requirement.empty`, so every service- or layer-using program's printed image is unannotated, and `Test/Program/AuthorContract.lean:201-207` shows those are the ordinary case.
- S-5's "the recorded exit of every corpus program decodes under its own `Schema.Exit(…)`" — **not done**. `make check-schema-codec` compares `Schema.Codec`'s value encoding with `Schema.toCodecJson` for the contract's cases (`Makefile:351-358`); `make check-schema-ts` checks *authored* documents through `fromJson`; neither reads `Api.schemaOf`, and `decodeUnknownSync` appears 17 times in the estate, never on a program's own exit schema.

Landed and working: S-1, S-2, S-3 (`encode_eq_some`, `encode_isSome_iff`, `encode_of_hasTy`, `decode_of_encode`, `decode_encode`, `hasTy_decode`, `encode_sub`) and the `Api.schemaOf` entry point. S-4's printer half and S-5 are open.

### 7.6 Against program-as-schema

The drift killer is healthy: the generated folds are `src/Effect4/Program/Fold.lean` (group `Fold`) and `src/Effect4/Schema/Fold.lean` (group `SchemaFold`), and `printAlgebra` (`src/Effect4/Codegen/Schema.lean:233`) is a fold that replaced nine hand recursions over `sizeOf`. The one clause not honoured is "annotations as CAS traits": a `Representation`'s annotations are dropped by `ofSchema` (§7.3) and nothing round-trips them.

---

# Part 3 — the applications regroup

## 8. The original plan, application by application

**The five briefs do not exist.** `docs/agents/dispatches/` holds exactly two unrelated files, and `git log --all --name-only` over the whole repository matches **no** `dogfood` path. `2026-09-15-dogfood-0-protocol.md` and `2026-09-15-dogfood-3-session-cache.md` are cited by the receipts (`2026-09-15-dogfood-1-receipt.md:3`, `2026-09-15-dogfood-3-receipt.md:4-5`) and were never committed. §8 is reconstructed from the three receipts, two reviews, `2026-09-16-dogfood-3-review.md`, `2026-09-16-dogfood-findings-applied.md` and `2026-09-16-dogfood-conclusions-review.md`. The five are the rate limiter, the job queue, the session cache, **the ledger** and **the connection pool**; the last two never ran (`2026-09-16-dogfood-findings-applied.md:5`).

### 8.1 Rate limiter (dogfood 1, ran)

**Needed then:** a `whileLoop` whose printing reads back; one spelling for `Effect.sleep`; a local `const` inside `gen`; semantic variable names instead of `a0`, `a1`; `Effect.all` and `Effect.forkDaemon` in the reader's head table. **Given now:** `iterate` replaces the retired `whileLoop` and round-trips (`src/Effect4/Program/Authoring/Lifts.lean:177`); `callback` is retired so `sleep` has one spelling; the authoring surface is **named** — 50 generated lifts, 22 row wrappers, 19 forms, with `Env.mint` and a reserved prefix that makes capture impossible (`Test/Program/AuthorContract.lean:294-345`); the daemon flag is at the call site (`daemon p`, `daemon p in s`, `:233-240`); supervision is data twice over — `Api.Supervision.supervision` lists every fork site of a program *before* it runs (`src/Effect4/Api/Supervision.lean:76-118`) and `Observation.fibers`/`daemonsQuiet` say who holds each fiber *after* (`src/Effect4/Run.lean:237-260`). **Still missing:** `gen` and its `Stmt` block have **no authoring lift at all** (checked: no `gen`, `whileTrue`, `ifElse`, `bindYield` or `breakLoop` in `Authoring/Lifts.lean`), so the receipt's own program shape must be re-expressed with `iterate` and `select`; `Effect.all`/`forkDaemon` remain reader gaps in `ts/eff/read.ts`, not language gaps. **Writeable as a `Module` and buildable with `Author.build`: yes** — **reproduced**: the refill loop as `iterate "i" "a" (some .nat) (nat 0) (lt i 3) (succ i) i (Ref.set used 0)` builds closed at answer `nat` and `runSync`s to `Exit.success (Val.nat 3)`.

### 8.2 Job queue (dogfood 2, ran)

**Needed then:** a three-argument `Effect.catchIf` on the host; named locals in generator loops; `Effect.retry` with a `Schedule`; `Effect.catchTag`; the host-row ceremony (build a `RowTable`, prove `LawfulTable`, register an adapter). **Given now:** the ceremony is one call — a module declares its rows and `Author.build` assembles the table in declaration order, types it and admits it (`src/Effect4/Api/Author.lean:55-70`), all three conditions decided on the module's own declarations (`Test/Program/AuthorContract.lean:150-152`), and a call resolves a **spelling** so no table position is written anywhere (`:123-133`); the hand-written driver loop is `Run.drive` over a `Reactor` (`src/Effect4/Run.lean:269-313`), and a run records its own journal so replay needs no host (`Laws/Run.lean`, `journal_replays`). **Still missing:** `Effect.retry`/`Schedule` and `catchTag` as derived forms — the findings note's D-G, **not adopted**; the 19 generated forms (`src/Effect4/Program/Authoring/Forms.lean`) include neither. **Writeable today: yes** — **reproduced**: `iterate` whose body is `catchIf "e" (tagIs "Transient" e) (Row.call work i) (succeed 0)` over a module-declared async row builds at answer `nat`, table length 1.

**A correction to record.** My first probe of this shape was refused at typing with reason `.term`; the cause was my own argument order. `tagIs` is **tag first**: `typeOf .tagIs [t, _] = if t.sub .string then some .bool else none` (`src/Effect4/Program/NativeAtom.lean:198`). The refusal names the node but not the argument types — `TypeReason.term` carries the `Term`, not what the atom was offered (`src/Effect4/Program/Typing/Blame.lean:31`) — the "diagnosing type checker" item of stage 1.

**A consequence for the output schema.** `catchIf` does **not** narrow the error column. **Reproduced:** catching `tagIs "Transient"` on `union (prod (lit "Fatal") string) (prod (lit "Transient") string)` leaves the *whole* union as the program's error, because `catchIfError` removes the body's column only for a literal `true` test or a tag test whose residual is `never` (`src/Effect4/Program/Typing.lean:219-224`, DI-17). So the published error schema of every partial-catch program is wider than what can escape — sound, not tight. D-4; the same object as memory's R-A.

### 8.3 Session cache (dogfood 3, ran)

Eleven frictions F1–F11 (`2026-09-15-dogfood-3-receipt.md:110-127`). State today:

| # | what it needed | fixed? |
| --- | --- | --- |
| F1 | eliminate `kvGet`'s `option string` | **fixed, proved.** `select` at `Decision.option` (`src/Effect4/Program/Decision.lean:41-44`, lift at `Authoring/Lifts.lean:161`) plus the `isSome`/`getOrElse` atoms (`NativeAtom.lean:37`). **Reproduced**: the lookup builds closed at answer `string`, is `readable`, and prints `Effect.flatMap(Kv.make(), (a0) => Effect.flatMap(a0.get("greeting"), (a1) => optionCase(a1, () => …, (a2) => Effect.succeed(a2))))`. D-C is landed |
| F2 | an import header from the printed handle targets | **not fixed.** `ModuleEmission.module` sets `imports := []`, stated as a limit in its own docstring (`src/Effect4/Codegen/Checked.lean:38-41`) |
| F3 | the key's carrier bound to the row's adapter class | **not fixed.** Nothing in `Codegen/` reads `Test/fixtures/target/selection.json`'s handle binding |
| F4 | unit from a row vs from a literal | **not fixed** (decided in the findings note, not landed) |
| F5 | two same-shaped keys kept apart in the printed `R` | **not fixed, and worse than the receipt says**: no annotation at all when the requirement row is non-empty (§7.5) |
| F6 | a shared layer at two sites without a hand-written path | **fixed.** `Module.layers` by name with `Layer.ref "Counter"`; `elaborateModule` places the term at the first use and points later uses at that path (`src/Effect4/Program/Authoring.lean:295-299`), pinned at `Test/Program/AuthorContract.lean:65-88` |
| F7 | a tape whose rows come from more than one fiber | **fixed.** Every row is keyed `⟨fiber, token⟩` (`src/Effect4/Api/Frontier.lean:12`; `Rows.answer s ⟨fiber, token⟩ c`, `src/Effect4/Run.lean:195-198`), and the claim is built from the machine, never written by the caller (`:140-154`) |
| F8 | an engine run of a program with host rows | **not fixed** (decision D-F, open) |
| F9 | a named environment | **fixed**, as §8.1 |
| F11 | the goldens' typing column with a layer reference | **not fixed** (generator fix) |

**Writeable today: yes** — **reproduced** end to end, including the `option` route F1 had to route around.

### 8.4 Ledger (never ran)

Its brief is gone; what follows is inference from the name and the classification. A ledger is records and sums: an entry `{id, amount, tag}`, a posting `Debit | Credit`, a running balance, often recursion (a reversal citing an entry). **Missing, named:** (i) `Schema.Struct` field names — no `objects` in `Ty`, so an entry is a nameless nested `prod` published as an `Arrays` (§6); (ii) `Schema.TaggedUnion` — a posting is `union (prod (lit "Debit") T) (prod (lit "Credit") T)`, lowering to an `anyOf` of tagged tuples (§6); (iii) recursion — `Suspend` and `Reference` both refuse (§4) and `Ty` is finite by construction; (iv) exact money — `Ty` has `nat`/`int` only, and `Ty.int` is refused by `Schema.Codec.isSupported` (`src/Effect4/Schema/Codec.lean:45-49`) **and** by admission's reserved-integer scan (`src/Effect4/Api.lean:386-388`), so an amount must be a `nat` of minor units. **Writeable today: partly** — a flat ledger with `prod` entries and a tagged posting builds and runs (the shapes §8.2's probe used); a recursive one does not.

### 8.5 Connection pool (never ran)

Needed: acquire and release, a bounded permit count, a scope that closes in parallel, a loop that re-enters the parent. **Given now:** `acquireRelease` is a lift (`src/Effect4/Program/Authoring/Lifts.lean:120`) with `releaseOne` as a form; `Scope.make` takes a `FinalizerStrategy`; `Api.Supervision` reads the pinned fibers and `daemonsQuiet` decides the close. **Missing, named:** **D-I** — `acquireRelease`'s release error column is not yet required to be `never`, and the tree still types a failing release whose failure escapes a program typed at error `never` (`2026-09-16-dogfood-findings-applied.md:47`, `:160`); and the parallel scope-close reification gap, unreached (`:63-65`). **Writeable today: yes as a `Module`**, but the release-column ruling should land before the battery is pinned, because it changes what types.

## 9. The next three dogfoods

**(1) The ledger — the record-and-sum dogfood.** The only one of the five that forces the §6 gap, and it needs no new runtime. *Program:* an append-only ledger over `Packages.keyValueStoreMemory` — post a `Debit` or a `Credit`, read the running balance, refuse an overdraft. *Schema in:* a posting as `Schema.Struct({ id: Schema.String, minor: Schema.Number.check(isInt, nonNegative), tag: Schema.Literals(["Debit","Credit"]) })` — the constructor `Ty` cannot express. *Schema out:* `Schema.Exit(Schema.Struct({ balance, count }), Schema.TaggedUnion({ Overdraft: {…} }), Defect)`. *The law:* `ofSchema_schema` extended to a record and a tagged sum — whichever of D-1's options is taken must keep the retraction — plus `decode_encode` at the new column and §7.3's conservative reader. It decides D-1 and D-3, and is the first application whose published schema a host consumer could use.

**(2) The connection pool — the resource-and-handle dogfood.** *Program:* N host connections acquired from a row into a scope, a permit count in a `Ref`, work on a borrowed connection, the scope closed in parallel, a daemon reaper interrupted at the end. *Schema in:* the pool size as `Schema.Number` with the size refinement — the first place a refinement is load-bearing rather than decorative, so it forces §7.3. *Schema out:* the connection **handle** column, whose published schema is currently a lie (§7.2): the run must show the schema and `externalValue` agreeing. *The law:* the `Envelope` (`src/Effect4/Program/Admit.lean:183-185`) against the published boundary schema — the S-5 gate for one application first — plus D-I's release column and `daemonsQuiet` after the close. It decides D-2 and D-I.

**(3) The run receipt closed — the observation dogfood.** Not one of the five, and the cheapest. *Program:* `readKey` from Part 1, unchanged. *Schema in:* `Api.Runner.Command`, which already crosses (`src/Effect4/Api/RunnerBytes.lean:78-86`). *Schema out:* `Effect4.Observation`, once the two generated instances exist (§3). *The law:* `ofVal_toVal` and `ofVal_exact` for the generated instance, `fits` against its own `ShapeDoc`, and the document read back by `SchemaRepresentation.fromJson` at the pin — what `harness/schema-host` already does for authored documents. It closes O-8, costs two manifest lines plus a regeneration, and is the only one of the three that makes the whole loop (open, play, observe, cross) schema-closed.

## 10. Decisions for the owner

**D-1. Records and sums at the Effect Schema face.** The ruling (core-goals §4.4) is sugar over nested `prod` and tagged tuples with no carrier change, which leaves the published schema an `Arrays` where the author wrote a record. (a) sugar only, as ruled; (b) `Ty.record`/`Ty.variant` lowering to `objects` and a tagged `union`; (c) keep `Ty`, put the field names in an **annotation** on the `Representation`. **Recommendation: (c), then (b) if it is not enough** — the only thing missing at the boundary is names, the shape is already right, and (c) costs one annotation key, reuses the `identifierKey` machinery (`src/Effect4/Store/Shape.lean:25-31`), keeps every retraction theorem, and reopens neither `Ty`'s `deriving` nor its wire tags.

**D-2. What a handle column publishes** (§7.2). (a) lower an external `handle` to `Schema.Number` with `isInt`, non-negative and a documented next-index check; (b) keep the opaque declaration and register a host **reviver** (`SchemaRepresentation.ts:574`) that mints the index; (c) state the exclusion. **Recommendation: (b)** — rc.112 has the mechanism, it is the same one the six `effect/schema/*` declarations need anyway (§1), and (a) publishes an allocation counter no consumer should see.

**D-3. `ofSchema` must refuse what it cannot represent** (§7.3). **Recommendation: every leaf arm refuses a non-empty `checks` and a non-`null` declaration payload**, allowing only the two checks the bridge mints — `ofSchema` is the reading side of an admission boundary, and a gate that widens is not a gate. Two lines per arm; `ofSchema_schema` unaffected.

**D-4. Whether the published error column should be tight** (§8.2). (a) leave it — sound, wider than reality; (b) narrow on a tag test with an inhabited residual, needing a first-failure membership rule. **Recommendation: (a), and say so in the document's own note** — the residual question is D-H's territory and the owner rejected D-H; a wider error schema refuses no valid value, a narrower one could.

**D-5. The consumer that makes D12 real** (§7.5). (a) the printer emits `documentDecl` beside the program, as S-4 said; (b) the S-5 truth-lane gate — every corpus program's recorded exit decodes under its own `Schema.Exit(…)` with `Schema.decodeUnknownSync`; (c) the store pins the document beside the program bytes. **Recommendation: (b) first, then (a)** — (b) is the only one that can *fail*, so the only one that turns D12 from a rendering into a claim.

**D-6. The `Document → Schema.* text` fold** (§1). (a) a `codeAlgebra` beside `printAlgebra` in `src/Effect4/Codegen/Schema.lean`; (b) rc.112's own `toCodeDocument` (`SchemaRepresentation.ts:908`) plus registered revivers; (c) do not do it. **Recommendation: (b)** — one owner for the spelling, and (a) would be a second emitter to keep in step with a vendored one. The work is the reviver table, which D-2 needs anyway.

**D-7. `Canonical FiberStatus` and `Canonical Observation`** — two entries in the `Runner` group of `tools/Effect4Gen/manifest.json` (§3). **Recommendation: land them now.** No decision content: every other field already has an instance (proved), and it unblocks dogfood (3) of §9.

**D-8. The hand-written prelude.** `harness/truth/prelude.ts` is the only TypeScript every printed program imports, is a hand transcription by its own admission (`:9`), and carries no schema for its twenty atoms or two `select` heads. **Recommendation: generate it from `NativeAtom.all` and `PrintLeaf.Head`, with an `Entry`-shaped schema per export** — the same `Entry := { name, input : Schema, output : Schema, cite }` the generation-medium note asks for (§5 there). DI-40's rule; both tables are already in the environment TsGen reads; it is the smallest place where "every boundary value carries an Effect Schema" becomes literally true.

---

## Where the tree contradicted the brief

1. **The five dogfood dispatch briefs do not exist** (§8): `docs/agents/dispatches/` holds two unrelated files and `git log --all --name-only` matches no `dogfood` path. The protocol and brief 3 are cited by the receipts and were never committed.
2. **`Api.schemaDocument` does not produce `Schema.Struct({…})`** (§1). The brief repeats the docstring at `src/Effect4/Api.lean:591` and the module note at `:60-61`; both are wrong and should say "the persisted `SchemaRepresentation` JSON".
3. **`ts/eff/eff.gen.ts`'s exports are mostly `Schema.TaggedUnion`**, not `Schema.Struct`: `Struct` for the structures (`ForkOptions`, `ServiceKey`, `Row`, `EffTy`), `TaggedUnion` for the inductives, `Literals` for the nullary ones (`eff.gen.ts:62-215`).
4. **Line numbers.** `schemaRepresentation` is at `src/Effect4/Api.lean:596`, not `:591`; `schemaDocument` is at `:592`. `Api.schemaOf` at `:138` and `Runner.schemas` at `src/Effect4/Api/RunnerBytes.lean:78` are as the brief cites.
5. **One of my probes was wrong, not the tree**: a refusal I first read as a `catchIf` defect was my argument order on `tagIs` (§8.2). Recorded so the correction travels with the finding.

## Evidence

Fourteen probes, run as `lake env lean -M 4096 <file>` in `/Users/pooks/Dev/lean4-effect4-scout-d` at `d798feb2` — no `lake build`, no `make check`, nothing written into the worktree (its only `git status` entries are 61 pre-existing `docs/` deletions from how it was created). They cover the E2 build with its document, bytes, printing and readability; the `ofSchema` table of §4; the requirement references and the `#synth` inventory of `Observation`'s fields; the driven run with per-field bytes, the duplicate shape keys, and the `envelope` refusal with its `Val.nat` control; the tagged-sum lowering and union normalisation; and the `selectOption`, `iterate` and `catchIf` builds with the `tagIs` correction. They live in the session scratchpad, not in the tree. The red control kept throughout is the `Val.handle 9 0` answer of §7.2, whose refusal is what makes the `Val.nat 0` acceptance meaningful.
