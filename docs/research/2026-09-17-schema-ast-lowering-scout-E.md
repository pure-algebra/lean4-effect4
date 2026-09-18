# Scout E — the Schema AST as Lean's canonical schema object, and the AST + LCNF as the TypeScript lowering (2026-09-17)

Worktree `/Users/pooks/Dev/lean4-effect4-scout-e`, detached at `6264983a` (one commit before the brief's `589d3e7a`; `git diff --stat 6264983a 589d3e7a -- src tools vendor` is **empty**, so every source citation holds at both). Eight `lake env lean` probes there, one TypeScript-compiler scan of the vendored sources. No source edited, no gate run, no build in the main checkout.

**Evidence words.** **proved** — a theorem with a proof term at the cited line (all are the tree's; I wrote none). **reproduced** — a `#eval`/`#guard` of mine that ran in my build. **tested** — a program of mine that ran outside Lean (the export scan). **stamped** — a gate in the `Makefile`. **assumed** — said so. Counts are counted.

## Verdict

**Coherent for a fragment; the fragment is smaller than the proposal assumes, and most of the proposal is already built under other names.** The AST-as-canonical half is sound and half-landed: rc.112's `SchemaRepresentation` (22 tags) is the persisted projection of `SchemaAST.AST` (21 kinds), Lean mirrors the projection tag-for-tag under a gate, `Ty` is already **an embedding into it with a proved retraction** (`Bridge.ofSchema_schema`, `[propext]`), and a generated fold over the 22-tag carrier already exists. Three of the brief's premises do not hold, and all three are load-bearing: `Check.holds` **does not exist** (nothing in `src/Effect4/Schema/` evaluates a check; `Schema/Check.lean` is structural field admission, and the one value-level judgment, `Arch.accepts`, states in its own header that checks are skipped and has **zero** callers); the seven `Codec` laws quantify `{t : CTy}` and mention `Ty` in **every** statement, so none restates over the AST mechanically; and `Effect4.Schema.Value` — the relational judgment a D12 theorem would be about — is cited in two docstrings and is not a module. D12 as `decode ast v = some x ↔ fits ast v` is therefore not a restatement but three new definitions, and it is false in the total direction for the same reason the S-3 amendment of 2026-09-11 exists. The TypeScript half is coherent only for a named fragment and the ceiling is hard: of **7,008** export symbols in the vendored tree, **91** (1.3%) can be an `Entry` with a fully structural AST input and output, and **none** of the 91 is from `Effect`, `Layer`, `Stream`, `Ref`, `Deferred`, `Queue`, `Scope`, `Fiber` or `Exit` — those are 0/242, 0/55, 0/243, 0/16, 0/23, 0/39, 0/13, 0/12, 0/30. "Valid Effect TypeScript by construction" is coherent for what an `Entry` table with declared type parameters and opaque `Declaration` nodes covers (1,265 + 956 exports more, each needing a reviver per id; 2,896 generic ones become entry *families*; 1,646 are type-level and are not entries), and `Program.Row` (`Eff.lean:190`) is **already that `Entry`** — `request`/`answer`/`error`/`cite`/`typeArgs` columns, 8 rows, all citing rc.112's unstable modules. The real ceiling is not the AST's expressiveness: **the Schema AST models values, the TypeScript type language models types**, and the estate already has the second object (the vendored `TypeScript.TypeRef`, which spells `Effect.Effect<A,E,R>`, function types and per-field `readonly`). So the answer is two parallel folds out of one source, never one derived from the other.

---

# Part 1 — the AST in Lean

## 1. The node type: 21 kinds, and six slots not four

`SchemaAST.AST` is 21 kinds (`vendor/effect-4.0.0-rc.112/src/SchemaAST.ts:53-74`, counted): `Declaration, Null, Undefined, Void, Never, Unknown, Any, String, Number, Boolean, BigInt, Symbol, Literal, UniqueSymbol, ObjectKeyword, Enum, TemplateLiteral, Arrays, Objects, Union, Suspend`.

**Four slots is true of `Base` only.** `Base` carries `annotations`, `checks`, `encoding`, `context` (`:636-642`). Four subclasses carry a fifth, `encodingChecks : Checks | undefined` — `Declaration` (`:693`), `Arrays` (`:1688`), `Objects` (`:2101`), `Union` (`:2917`) — and `Declaration` a sixth, `encodingRun : DeclarationRun | undefined` (`:698`), which `flip` swaps in so a declaration parses differently when encoding (`:742-744`). A Lean carrier claiming to be the AST needs all six or must say which it drops.

| slot | data | program |
| --- | --- | --- |
| `annotations : Annotations \| undefined` | an open record; `Json` payloads | host callbacks live here: `toCode`, `toJsonSchema`, `arbitrary` (`SchemaRepresentation.ts:70-145`) |
| `checks : Checks` | `Filter.aborted` (`:3212`), `FilterGroup.checks` (`:3257`) | **`Filter.run : (input, self, options) => Issue \| undefined`** (`:3209`) |
| `encoding : [Link, ...Link[]]` | `Link.to : AST` (`:402`) | **`Link.transformation : Transformation \| Middleware`** (`:403-405`) |
| `context : Context` | `isOptional`, `isMutable`, key `annotations` (`:577-581`) | **`constructorDefault : Link \| undefined`** (`:580`) — a `Link`, hence a transformation |
| `encodingChecks` | as `checks` | as `checks` |
| `encodingRun` | — | **`(typeParameters) => (input, self, options) => Effect<any, Issue, any>`** (`:666-668`) |

Pure-data payloads: `Enum.enums : ReadonlyArray<readonly [string, string|number]>` (`:1076`); `Literal.literal : string|number|boolean|bigint` (`:1317`, `:1289`); `UniqueSymbol.symbol` (`:1255`); `TemplateLiteral.parts : ReadonlyArray<AST>` plus three *derived* internal fields recomputed in the constructor (`:1157-1163`); `Arrays.{isMutable, elements, rest}` (`:1685-1687`); `Objects.{propertySignatures, indexSignatures}` (`:2099-2100`) over `PropertySignature {name : PropertyKey, type : AST}` (`:1975-1976`) and `IndexSignature {parameter, type}` with the parameter constrained to `String|Number|Symbol|TemplateLiteral|Union` of those (`:2037-2038`, `:1988-1993`); `Union.{types, mode}` (`:2915-2916`). One payload is a **thunk**: `Suspend.thunk : () => AST`, memoized (`:3146`, `:3158`).

**Foreign beside Lean-authored.** rc.112 answers this and Lean already mirrors the answer. A revived-by-id declaration or check carries `RepresentationAnnotation { id : string, payload : Schema.Json }` (`SchemaRepresentation.ts:25-28`), a check also `schemas?: ReadonlyArray<S>` (`:36-37`); revival is by id through `DeclarationReviver<P> { id, payloadSchema, revive }` (`:502-517`) or `FilterReviver`/`FilterGroupReviver` (`:518`, `:534`). In Lean that is `Representation.declaration (representation : RepresentationAnnotation) …` (`src/Effect4/Schema/Representation.lean:704`) and `Check.filter (representation : CheckRepresentationAnnotationOf Representation) …` (`:773`). A **Lean-authored** transformation is different in kind and better: `SchemaTransform` carries `program : Eff Op` with `source target error : Ty` and `requires : Requirement` (`src/Effect4/Schema/Transform.lean:22-28`), and `SchemaTransform.check` admits it only against the real judgment `effTy σ [d.source] d.program = some ⟨d.target, d.error, d.requires⟩` (`:92-96`). So "a transformation is a first-order program here" is **true and proved-by-construction** — with one correction: its endpoints are `Ty`, not AST, so making the AST canonical re-types the transform too.

The honest Lean carrier, in the tree's idiom (`Slots` factored so the six slots are stated once):

```lean
mutual
inductive Ast where
  | declaration (slots : Slots) (typeParameters : List Ast) (run : DeclRef)
      (encodingChecks : List Check) (encodingRun : Option DeclRef)
  | null (slots : Slots) | undefined (slots : Slots) | void (slots : Slots) | never (slots : Slots)
  | unknown (slots : Slots) | any (slots : Slots) | string (slots : Slots) | number (slots : Slots)
  | boolean (slots : Slots) | bigint (slots : Slots) | symbol (slots : Slots)
  | objectKeyword (slots : Slots)
  | literal (slots : Slots) (literal : LiteralValue)
  | uniqueSymbol (slots : Slots) (symbol : GlobalSymbolKey)
  | enum (slots : Slots) (enums : List EnumEntry)
  | templateLiteral (slots : Slots) (parts : List Ast)
  | arrays (slots : Slots) (isMutable : Bool) (elements rest : List Ast) (encodingChecks : List Check)
  | objects (slots : Slots) (propertySignatures : List (PropertySignatureOf Ast))
      (indexSignatures : List (IndexSignatureOf Ast)) (encodingChecks : List Check)
  | union (slots : Slots) (types : List Ast) (mode : UnionMode) (encodingChecks : List Check)
  | suspend (slots : Slots) (thunk : Ast)     -- first-order, as `Representation.suspend` is
inductive Slots where
  | mk (annotations : Annotations) (checks : List Check) (encoding : List Link) (context : Option Context)
inductive Link where | link (to : Ast) (transformation : TransformRef)
inductive Context where
  | mk (isOptional isMutable : Bool) (constructorDefault : Option Link) (annotations : Annotations)
end

inductive TransformRef (Op : Type) where
  | lean (t : SchemaTransform Op)              -- `Schema/Transform.lean:22`, checked against `effTy`
  | foreign (id : String) (payload : Json)     -- revived host-side by id
inductive DeclRef where
  | foreign (id : String) (payload : Json)     -- no `lean` leg: `DeclarationRun` answers an `Effect`
```

`Suspend.thunk` must be a plain nested `Ast`, exactly as the representation carrier already argues (`Representation.lean:693-696`, `E4-SCHEMA-CE-031`): the pin is first-order, so no closure. `DeclRef` has no `lean` leg because `DeclarationRun` returns `Effect<any, Issue, any>` over `unknown` — there is nothing first-order to hold.

## 2. The two folds out; what the 22-tag census becomes

**`toRepresentation : AST → Document` is the encoded-side collapse, and it is rc.112's.** `SchemaRepresentation.toRepresentation(ast, options): Document` (`SchemaRepresentation.ts:784`) delegates to `internal/schema/toRepresentation.ts:28`. Two mechanics decide what survives: `getCandidate` applies `SchemaAST.getLastEncoding(input)` before anything else (`:112`), so the whole `encoding` chain collapses to its final target; and the emitting function `on` (`:192-306`) **never reads `encoding`, `encodingChecks`, `Declaration.run` or `Filter.run`** — it reads `ast.checks` through `fromChecks`, the node payloads, and `context` only as the projections `isOptional`/`isMutable` plus the key `annotations` (`:250-278`). That is the whole "persisted projection" claim, confirmed line by line.

**The 22 tags are AST's 21, with `Reference` added.** `Representation` (`SchemaRepresentation.ts:406-430`) has every AST kind plus `Reference { _tag, $ref }` (`:171-175`), minted by `makeReference` (`internal/…:100-110`) under a `ReferencePolicy` (`:741`), recursion forcing one (`:60-64`). Lean mirrors the 22 exactly: `RepresentationTag` (`Representation.lean:36-81`), `census` (`:94`), `census_length : census.length = 22` **proved** `by decide` (`:167`), `census_nodup` (`:170`), `ofTagName_tagName` (`:190`), carrier at `:701-756`.

**So the census does not change; it gains a sibling.** If the AST becomes a second Lean carrier, the 22-tag census stays as the representation's and a **21-tag** census joins it, with one theorem: the tag map is total and its image is the 22 minus `reference`. If the AST *replaces* the representation, the estate loses the one thing `make check-schema-pins` holds (`Makefile:243`, inside `check-full`), because the pin is against the persisted projection — which is what `fromJson` reads back (`SchemaRepresentation.ts:1177`). **Recommendation: two carriers, the 22-tag one canonical for persistence** (E-1).

**Agreement beyond `check-schema-pins`: three gates exist, one does not.** `check-schema-pins` freezes the tag alphabet; `check-schema-ts` runs authored documents through `fromJson` (`Makefile:243`); `check-schema-host` runs `harness/schema-host`, which pins `@effect/tsgo 0.38.0` and `typescript 7.0.2` (`harness/schema-host/package.json`) — the estate's only type checker for rc.112. Missing, and what the brief's "agreement on the pinned cases" needs: a differential that takes a *live* rc.112 schema, runs the host's `toRepresentation` and the Lean `toRepresentation` on the Lean AST of the same schema, and compares the two `Document`s. One new lane, shaped like `check-schema-codec` (`Makefile:351-358`).

**The retraction on the image does not exist and cannot be total.** `toRepresentation` is lossy by design (it drops the six program slots). A retraction exists only on the sub-AST with no `encoding`, no `encodingChecks`, no `constructorDefault` and only revived-by-id declarations and checks — i.e. the AST that is already a representation. What the tree *does* prove is the smaller fold's: `ofSchema_schema (t : Ty) : ofSchema (schema t) = some t` (`src/Effect4/Schema/Bridge.lean:114`), **proved** at `[propext]` (**reproduced** by `#print axioms`; the `CTy` version `[propext, Quot.sound]`). And a generated fold over the 22-tag carrier is already there: `RepresentationAlgebra` + `cata_representation` (`src/Effect4/Schema/Fold.lean:20`, `:104`), group `SchemaFold` — **reproduced**: I wrote a 24-field tag-collecting algebra over it and it ran.

## 3. Checks with meaning, and the D12 theorem

**`Check.holds : Check → Val → Bool` does not exist.** Grep `def holds` across `src/`, `tools/`, `Test/`: no hit in any schema module (the five hits are a structure field at `Laws/Program/Authoring.lean:39-53` and two bound variables). `src/Effect4/Schema/Check.lean` (1,499 lines) is *structural field admission* — `Representation.fieldAdmissible` (`:780`), `FieldAdmissible` (`:788`), 30 per-node `_iff` lemmas, 19 witness theorems — the rc.112 field clauses, not a predicate on values. The brief's "`Check.lean` — 'a name, not a meaning'" quotes `Representation.lean:18`, which is about **tags**. Where a check's meaning *would* go is `Bridge.lean:26-31`, which mints exactly two named checks (`effect/schema/isInt`, `effect/schema/isGreaterThanOrEqualTo` with `{minimum: 0}`) and gives neither one.

**What exists is `Arch.accepts`, and it says so.** `Effect4.Arch.accepts : Document → Json → Bool` (`src/Effect4/Arch/Accepts.lean:114`) over `acceptsShape` (`:65`), fuel 64. Its header (`:19-22`): "`checks` are not evaluated: a filter's predicate is host code. So this is acceptance of the *shape*; a schema with checks accepts a superset here of what rc.112 accepts." It also refuses `declaration` and `templateLiteral` outright (`:26-28`). **Reproduced**, with the red controls that make it mean something: at `Ty.nat`'s image (`Number` + `isInt` + `isGreaterThanOrEqualTo 0`) `accepts` returns **true** for `-3.0` and for `1.5`, and **false** for `Option`'s and `Exit`'s declaration nodes against any JSON. It has **zero** callers: the only mention outside its own file is the root import `src/Effect4.lean:80`. And `Effect4.Schema.Value`, "the relational judgment this approximates" (`Accepts.lean:32`, also cited at `Document.lean:66`), **is not a module**.

**The seven `Codec` laws do not restate; they are re-founded.** The seven in `src/Effect4/Laws/Schema/Codec.lean:14-90` are `encode_eq_some`, `encode_isSome_iff`, `encode_of_hasTy`, `decode_of_encode`, `decode_encode`, `hasTy_decode`, `encode_sub` (plus `encode_injective` at `:92` and three examples). **Every one** quantifies `{t : CTy}` and mentions `t.toRaw : Ty`, `Codec.layout : Ty → Ty` (`Schema/Codec.lean:27`), `Val.hasTy _ : Ty → Bool`, and `Codec.encodeRaw`/`decodeRaw : Ty → …` (`:139`, `:176`) — all four match on `Ty`'s 16 constructors. `Codec.lean` never mentions `Representation`. So **the *shape* of the seven statements survives and none of the proofs does**; over the AST you need three new definitions: (1) `layout : Ast → Ast`, which is the same function as `getLastEncoding`; (2) `encodeRaw`/`decodeRaw : Ast → Val → Option Json`, 21 arms plus index signatures plus `oneOf`'s uniqueness against `Ty`'s 16; (3) `fits : Ast → Val → Bool`, which is `Arch.accepts` **with checks evaluated**, hence `Check.holds`, which does not exist.

**The D12 theorem, precisely.** The brief's `decode ast v = some x ↔ fits ast v` is not type-correct as written (`decode` answers a value, `fits` tests one) and, stated correctly, is false in the total direction. The honest pair, following `encode_eq_some` and `hasTy_decode`:

```lean
/-- D12-sound: nothing decodes that the schema does not accept. -/
theorem decode_fits {a : Ast} {j : Json} {v : Val}
    (h : Schema.decodeAst a j = some v) : Schema.fits a v = true

/-- D12-total, on the admitted domain: what fits and recovers exactly, decodes. -/
theorem fits_decode {a : Ast} {v : Val} (hf : Schema.fits a v = true)
    (adm : Schema.isValueAst a v = true) :
    (Schema.encodeAst a v).bind (Schema.decodeAst a) = some v
```

`adm` is not decoration: the S-3 owner amendment of 2026-09-11 exists because "every typed natural or overlapping union has an injective JSON image" is false (`Laws/Schema/Codec.lean:3-7`), and `Codec.isValue` (`Schema/Codec.lean:202`) is the executable admission that replaced it. An AST version inherits that exactly. **And nothing here replaces a harness run with a theorem**: the harness run (D-D / S-5) tests the *host's* decoder against the published schema; the theorem tests the *Lean* decoder. Different claims; the estate needs both.

---

# Part 2 — the typing, in detail

## 4. `Ty` as the checker's fragment: it is an embedding, and that design is already proved

**What the checker types.** `Ty` has 16 constructors (`src/Effect4/Program/Ty.lean:24-42`, counted): `never unit nat int string bool handle option list prod except exitOf causeOf fiberOf union lit`, consumed through `effTy`/`termTy`/`typeOf` (`src/Effect4/Program/Typing.lean:282`, `:558`), `EffTy = ⟨answer, error, requires⟩` (`:30`), rows (`Program.Row`, `Eff.lean:190`) and `Signature` (`:53`). **Reproduced**: `Ty.schema`'s image over all 16 uses exactly **9** representation tags — `never void number string boolean declaration arrays union literal` — plus the `Filter` check tag, and never the other **13**: `reference suspend null undefined unknown any bigint symbol uniqueSymbol objectKeyword enum templateLiteral objects`. (Independently reproduces scout D §6's count of 9; the tenth item in my probe is `Filter`, a `Check` tag.)

So the AST nodes the checker must **refuse** are named and counted — those thirteen, of which `Arch.accepts` independently refuses five as having no JSON inhabitant at all (`Accepts.lean:23-25`) — and the **slot** values it must refuse are: any `encoding` whose transformation is `foreign`, any `constructorDefault`, any `encodingRun`, and any check outside the two the bridge mints.

**Design A — `Ty` embeds with a left inverse. It exists and is proved.** `Bridge.schema : Ty → Representation` (`Bridge.lean:38`), `Bridge.ofSchema : Representation → Option Ty` (`:63`, total-by-refusal: `| _ => none` at `:111`), `ofSchema_schema` (`:114`) at `[propext]`, canonical companion `CTy.ofSchema_schema` (`:218`). `normalize` (`Ty.lean:434`), `sub` (`:373`), `key` (`:103`) with `key_injective` (`:196`) and the derived `IsLinearOrder` (`:335`) are untouched; the S1 wire tags untouched; `deriving DecidableEq, Repr` (`:43`) untouched; `MeaningSound.sound` (`Laws/Program/MeaningSound.lean:480`) and `LoopSound.soundB` (`LoopSound.lean:296`) untouched, both being stated `effTy nativeSignature tys e = some t` over `Ty`. Cost: `Ty` cannot *express* the other 13 nodes — D-A's subject.

**Design B — `Ty` becomes the fragment, the checker runs on AST nodes. Cost measured, with the red control that shows it is not avoidable.** **Reproduced**: `Ty` derives `DecidableEq` and `Repr` and carries an injective key (`#eval Ty.key (.exitOf .nat .string)` → `[11, 1, 2, 4]`). `Representation` derives **neither**: `#check (inferInstance : Repr Effect4.Representation)` fails to synthesize, and `deriving instance DecidableEq for Effect4.Representation` fails with *"None of the deriving handlers for class `DecidableEq` applied to `Representation`"* — because it is a mutual nested inductive over `Json`, which `Representation.lean:799-807` says in as many words; the instance that exists is ~130 hand-written lines of `beq` plus `beq_iff` (`:809-1000`). So B costs: a hand-written `DecidableEq` for the checker's type language; no `Repr` (hence no repr-based `#guard` in any battery); `key` re-derived over `Json`-valued annotations, where injectivity is **false** unless annotations enter the key — and if they do, `union` normalisation and `sub` start depending on annotation content, breaking `Ty.normalize`'s member sort, `normalize_idem` (`:567`) and every union law; the S1 wire tags re-cut from 16 to 21+; both soundness statements re-typed.

**Pick Design A, and give it the one thing it lacks: `Ty.app`.** The embedding is proved, its inverse is total-by-refusal, and the estate's rule ("one representation per kind of thing") is satisfied — types are the `Document` and `Ty` is a fold into it (scout D §5 row 3, same conclusion). The expressiveness gap that matters most is not records but **type-constructor application**: `Ty.handle target` is a *string*, so `Ref.Ref<number>` bakes its argument into the id (scout D §6). `Ty.app (name : String) (args : List Ty)` with `handle target = app target []` as the nullary case is already the workshop note's §5 step 3 and is what a generic `Entry` output needs (§9, §10). It touches `key` (one new code), `normalize` (recurse into `args`), `sub` (invariant in `args`, deferring assignability to the host checker as O17 rules), `renderRaw` (`name<a, b>`) and `Bridge.schema` (a `declaration` with `typeParameters := args.map schema`) — five small additions, no theorem restated in kind.

## 5. Records and sums at the AST level (D-A)

**Reproduced, with red controls.** `Bridge.ofSchema` refuses an `Objects` node (`Schema.struct [Schema.property "k" Schema.string]` → `none`), refuses a tagged `Union` (`anyOf [tagged "A" [], tagged "B" []]` → `none`), refuses a three-member union, and accepts the binary untagged one (`anyOf [String, Boolean]` → `some (.union .string .bool)`). So the reader is **already total-by-refusal** — the brief's "becomes total-by-refusal" is already true. What it is not is *conservative*: scout D §7.3, proved there, not re-probed here.

**What `select` reads, and why the encoding is not free.** `Decision.tag t` decides by `Val.tagPayload? t : Val → Option Val`, matching `.list [.str t, payload]` (`src/Effect4/Program/Decision.lean:31-33`, `:39-42`), the wrong-shape leg binding the whole value at the residual type (DI-39, `:44-46`). A two-element list whose head is a string literal is **exactly** what `Ty.prod (lit t) T` lowers to: `Arrays[Literal t, T]` (`Bridge.lean:49`). So eliminator and emitter already agree on one encoding, and it is **not** rc.112's `TaggedUnion` (`Schema.ts:6470`), which produces `Objects` with a `_tag` property signature. The estate holds two sum encodings (scout D §5) and `select` is bound to the positional one.

That sharpens D-A. Option (c) — field names as an annotation on the `Representation` — keeps `select` working and every retraction, and is cheapest; but it leaves the *published* schema an `Arrays`, and no annotation changes that, because `Schema.decodeUnknownSync` does not read annotations. Option (b) — `Ty.record (fields : List (String × Ty))` and `Ty.variant (cases : List (String × Ty))` lowering to `Objects` and a `_tag`ged `Union` — is what a foreign consumer needs, and forces `Val.tagPayload?` to gain an object leg. **Recommendation: (c) now, (b) before the first foreign consumer, as stages and not alternatives** — (c) need not be undone, because a `record`'s lowering can carry the same annotation key. What the checker gains from (b): `payloadOf` (`Ty.lean:607`), `diffTag` (`:591`) and `taggedColumn` (`:599`) get a named home instead of the `prod (lit t) T` convention they pattern-match today, and `catchIfError`'s residual (`Typing.lean:219-224`) becomes a list difference instead of a union difference.

## 6. Handles as a `Declaration` whose `encoding` says what crosses (D-B)

Today's node (`Bridge.lean:46`): `Ty.handle "KeyValueStore.KeyValueStore" ⟶ .declaration ⟨"KeyValueStore.KeyValueStore", .null⟩ none [] []`. What actually crosses, from `externalValue` (`src/Effect4/Program/Compile.lean:1354-1359`, `externalHandleTarget` at `src/Effect4/Program/Typed.lean:17`):

```lean
| .handle target, .nat index =>
    if externalHandleTarget target && index == allocated.length then
      some (allocated ++ [target], Value.external index) else none
```

The admissible boundary value is a **natural number equal to the current allocation count** — scout D §7.2 proved the pair (`Val.handle 9 0` refused at `Phase.refused Refusal.envelope`; `Val.nat 0` accepted). The node that says so, with the encoding slot carrying the wire side:

```lean
def kvHandleAst : Ast :=
  .declaration
    (slots := .mk (annotations := identifierKey.singleton "KeyValueStore.KeyValueStore") (checks := [])
      (encoding := [ .link
          (.number (.mk none
             [ Check.named "effect/schema/isInt"
             , Check.named "effect/schema/isGreaterThanOrEqualTo" (.obj [("minimum", .number 0)])
             , Check.named "effect4/externalHandle/nextIndex"        -- == allocated.length
                 (.obj [("target", .str "KeyValueStore.KeyValueStore")]) ] [] none))
          (.foreign "effect4/handle/allocate" (.str "KeyValueStore.KeyValueStore")) ])
      (context := none))
    (typeParameters := []) (run := .foreign "effect4/handle/KeyValueStore" .null)
    (encodingChecks := []) (encodingRun := none)
```

Read off the node: `toRepresentation` of it is `Number` with three checks (because `getLastEncoding` collapses to the link's target) and `toType` of it is the opaque declaration — exactly the split D-B asks for. But the third check is one `externalValue` enforces and no rc.112 filter expresses, so it needs a reviver, and **it is where a pure `Check.holds` first fails**: `holds (nextIndex target) (.nat i) = (i == allocated.length)` reads the store. The honest signature would be `Check → Stores → Val → Bool`, which contaminates every check. **Recommendation: keep checks pure, and make the agreement a theorem** — `externalValue_iff_fits`, relating `externalValue` to the published node — which puts the store-dependent obligation next to the machine, where `Admit.lean` already is (E-2).

---

# Part 3 — the AST as the language for generating TypeScript, through LCNF

## 7. The type fold, and the two objects it must not be confused with

**A Lean type's AST image already exists, is generated, and has 96 instances.** `Store.Canonical α` carries `shape : ShapeDoc` (`src/Effect4/Store/Canonical.lean:33`), and `ShapeDoc.document : ShapeDoc → Document` (`src/Effect4/Store/Shape.lean:468`) renders it through `Shape.render : Shape → Representation` (`:420-445`). 96 `Canonical` instances exist (counted); none is `deriving`, all are emitted by generator groups (`tools/Effect4Gen/manifest.json`). **Reproduced**: `Canonical.shape EffTy`'s root is `Shape.struct "EffTy" [("answer", named "Ty"), ("error", named "Ty"), ("requires", list (struct "ServiceKey" …))]` with `defs = ["Ty"]`, and its `document` has references `["Ty"]`.

**Which Lean types have an image.** `Shape` has 13 constructors (`Store/Shape.lean:60-83`): `unit bool nat string bytes digest list option pair struct sum ref anyRef named`. Structures → `struct` → `Objects`; inductives → `sum` → a tagged union; `List`/`Option`/`Prod` → their constructors; recursion → `named` + the `defs` table → `Reference`. **Red control reproduced**: `Shape.arrow` is an unknown constant — **there is no arrow**, so a Lean **function type has no AST image at all**, and neither does `Prop`, a universe or a `Type`-indexed family (none can have the `toVal` `Canonical` requires).

**What a function-typed value becomes.** Not a `Declaration` — a `Declaration` is opaque and a lowered function is the opposite. It becomes an **`Entry`**: a pair of ASTs (§9) plus the LCNF closure that is its body. The brief's "every lowered function's signature is a pair of ASTs" is right, but the pair is a *signature*, not a type; the thing with a type is the emitted TypeScript, whose type language is the next object.

**Against `TsGen`.** `tools/Tools/TsGen.lean` (1,141 lines) reads `Lean.getEnv` (`:440`) and emits `Schema.TaggedUnion`/`Struct`/`Literals` text from the inductives directly (`:175-197`) — a second fold from a second source, which D-J rule (1) fails. Replacing its environment read by `Canonical.shape α → ShapeDoc.document` needs nothing new: the `ShapeDoc` is already a `Document`, and `Codegen/Schema.lean:310` already turns a `Document` into `TypeScript.Expr`. The cost scout C measured stands: `Command`'s Effect Schema text is 231,660 characters (tested there) because `Header`/`Call` inline the whole `Row`/`Ty` closure — so the reference policy is a decision before either emitter runs.

## 8. The code emitter: LCNF → the TypeScript **syntax** AST

**The target is the syntax AST, exactly as the ML emitter targets `Ml.Decl`.** Both objects exist and are structurally parallel: `OCaml5.Ml.Syntax` has `Ty`/`Pat`/`Expr`/`Decl` (`src/OCaml5/Ml/Syntax.lean:75`, `:202`, …) with `translateClosure → Ml.Decl → Ml.Render → ocaml/gen/*.ml`; the vendored package has `TypeScript.TypeRef`/`Expr`/`Stmt`/`Decl`/`Module` (`.lake/packages/typescript/TypeScript/TypeRef.lean:12`, `Syntax.lean:35`, `:84`, `:261`, `:290`) with `Render.module` (`Render.lean:402`). **The Schema AST is neither**: it models values, `TypeRef` models types, `Expr`/`Stmt` model syntax.

**Where the Schema AST appears in that syntax — three places and only three.** (1) **Type annotations**: `ConstDecl.type : Option TypeRef` (`Syntax.lean:217`), from a fold out of the same *source* as the schema, never out of the schema — today `Codegen.Types.ofTy : Ty → Option TypeRef` (`src/Effect4/Codegen/Types.lean:311`). **Reproduced**: all 16 `Ty` constructors have a `TypeRef` image — `never, void, number, number, string, boolean, Scope.Scope, Option.Option<string>, ReadonlyArray<number>, readonly [string, boolean], Result.Result<number, string>, Exit.Exit<number, string>, Cause.Cause<string>, Fiber.Fiber<number, string>, string | boolean, "Boom"`. (2) **`Schema.*` runtime values**: `Expr` trees; `Codegen/Schema.lean:310` already emits a `Document`'s persisted JSON as `TypeScript.Expr`, and D-E rules the *combinator* spelling comes from rc.112's `toCodeDocument` (`SchemaRepresentation.ts:908`, `Code = {runtime, Type}` at `:648`, artifacts at `:667`). (3) **The `Entry` signatures**: data in a generated table, not syntax (§9).

**What the syntax AST keeps that a Schema AST cannot carry — all reproduced by rendering.** `TypeRef.name (qualified) (args)` gives generic *application*: `Effect.Effect<string, never, never>`. `TypeRef.function` gives function types: `(k: string) => Effect.Effect<number, never, never>`. `TypeRef.object (fields : List (String × Bool × TypeRef))` gives **per-field `readonly`**: `{ readonly id: string; n: number }`. `TypeRef.tuple _ readonly` gives `readonly [string, number]`; `TypeRef.union` gives `"a" | "b"`; `Module.imports` with `Import.all`/`Import.named` and per-binding `typeOnly` (`Syntax.lean:280-283`) gives modules and imports. A Schema AST has none of these *as types*: `Declaration.typeParameters` is application without a binder; a function type can only be an opaque declaration; `PropertySignature` + `Context.isMutable` is `readonly` as data *about a value*, not a type qualifier; and there are no imports at all. **Two gaps in the syntax AST, both concrete and both additions to `~/Dev/lean4-typescript`, not to the Schema AST**: there is no type-parameter **binder** list anywhere (`ConstDecl` and `ProgDecl` have no `typeParameters` field, `Syntax.lean:214`, `:223`), so a generic helper can be applied but not declared; and there is no intersection, conditional, mapped or `keyof` type — narrowing is expressible only through `Stmt.ifElse`/`switch` and a union `TypeRef`, which is enough for tagged unions and nothing else.

**What of the ML translator is target-independent.** Independent: reading inductives (`Lcnf/Types.lean:238` `typeInfo?`, with `isIrrelevantFieldType` `:102` and `trivialFieldIdx?` `:108` — the compiler's own erasure verdicts) and `typeParameterIndices` (`:146`); the closure walk — `St`/`TCtx`/`TM` (`Translate.lean:281`, `:333`, `:340`), `fresh`/`bindVar`/`nameOf` keyed on `FVarId` (`:355-377`, which is what makes shadowing un-capturable), the `reduceArity` wrapper handling (`:400-429`), `argExpr?`'s erased-argument filter (`:443`); `Native.rules` — *which* 12 Lean constructors are native (`Lcnf/Native.lean:18-22`); and the *shape* of `Externs` (`Lcnf/Externs.lean:127-148`) with its `_redArg`/`.spec_N` normalisation (`:97`). OCaml-specific: `Ml.Ty`'s `larrow`/`polyVariant`/`asVar` (`Ml/Syntax.lean:88-97`); `Naming.lean`'s lexical classes (OCaml `value-name` vs `constr-name`, reserved-word suffixing, `:1-30`); `Native.expression`'s spellings; `applyBuiltin`'s eta-expansion under currying (`Translate.lean:270`); the 63-bit `Nat.pow` saturation rule (`:133`).

**What TypeScript needs that ML did not — five things, three already present.** *Pattern matching → tagged-union switches*: `Stmt.switch (scrutinee : Expr) (cases : List (Nat × List Stmt))` exists (`Syntax.lean:100`) and is keyed on `Nat`, i.e. the constructor index — already the right shape for an LCNF `cases`. *Tail calls → structured loops*: `TypeScript.Structure` already does the whole reduction — reverse postorder, Cooper–Harvey–Kennedy dominators, reducibility, labelled `while(true)` with `break`/`continue`, "following the shape js_of_ocaml gives its generated code" (`Structure.lean:1-27`); **reproduced** on a self-loop graph: `rpo = [0,1,2]`, `reducible = true`, `isLoopHeader 1 = true`. *No currying → arity*: `Parameter` lists on `lambda`/`arrowBlock` carry it (`Syntax.lean:19`, `:63`, `:78`); what is missing is the *decision* that an under-applied Lean call becomes an explicit closure where ML eta-expands. Genuinely new: *`bigint` vs `number` for `Nat`* — the estate has chosen `number` (`ofTy_nat = some (.name ["number"] [])`, **proved** `rfl` in `Types.lean`), a decision not an accident, and it means `Nat`'s arithmetic laws do **not** transfer past 2^53 while the OCaml route saturates at 63 bits: two different wrong answers from one LCNF, which rung-3 vectors catch only if they reach that range. And *`Effect` values are lazy* — a lowered function returning `Effect<A,E,R>` must emit `Effect.sync(() => …)` or a generator, never a direct call; this is the one notion the ML target had no analogue for, and it is where the existing 67-row template table already lives.

**Which Conform rungs apply unchanged.** Rung 1 — `Conform/Lcnf/{Rules,Validity,Cases,Index}.lean` — is about LCNF itself: unchanged. Rung 2 — `Conform/Effect4/LcnfSemantics.lean`, the interpreter on mono LCNF against the compiled Lean function on 1,330 unary and 3,249 paired `Ty` vectors with six deliberate mutants (`:1-25`) — unchanged, because it never mentions a target. Rung 3 — `Conform/Effect4/LcnfMl.lean`, which reads the **emitted** `Ml.Decl` back into `Target.Expr` and runs the same 20,387 vectors (`:1-28`) — is a **reader per target** and does not transfer: `ofPat`/`ofExpr : Ml.Pat/Expr → Except String Target.…` (`:44`ff) must be rewritten as `TypeScript.Expr → Except String Target.Expr`, refusing by constructor name exactly as the ML one does, and then the same 20,387 vectors run against the emitted TypeScript. That reader is the highest-value single piece of the whole backend: it is what makes "the emitted TypeScript means what the Lean function means" a checked claim. `tools/target`'s tsc oracle and `harness/schema-host`'s tsgo are the *type* oracles beside it, not substitutes.

**Where type generation belongs: split, with the split named.** Three layers, three jobs, all three already in the tree. **The sugar/macro layer** (`src/Effect4/Program/Authoring/{Sugar,Forms,Lifts,Loops,Rows,Services}.lean`, 1,191 lines; 50 lifts generated over `tools/Effect4Gen/binders.json`; the one real macro, `syntax (name := daemonFork_) "daemon " term (" in " term)? : term` at `Authoring/Services.lean:151-153`) owns **what an author may write and what it elaborates to** — so type generation belongs here for *authoring-time* obligations (a lift minting a fresh name, `Sugar.bindWith:26`; a form pinned against the printer's expansion; a macro that writes an `Entry` for a row the author declares), and must **not** own the emitted TypeScript's types, because a macro's output is checked by Lean's elaborator and nothing more. **The LCNF layer** owns **semantics**, and the owner's "our LCNF is really our superpower for verified semantics" is right for a narrow reason worth writing down: LCNF is the **only** object in the estate whose meaning is certified by a differential against the Lean compiler itself (rung 2's mutants) rather than by a Lean-internal theorem; a hand-written mirror has no such certificate, and `harness/truth/prelude.ts` says so in its own header ("Hand-written transcription (no generator exists for it yet)"). **The table layer** — `Program.Row` (§9) and `Codegen/Templates.lean`'s rows (**reproduced**: `table.length = 67` = 31 eff + 20 action + 10 layer + 6 stmt) — owns **spelling and citation**. **Recommendation: types are generated at the table layer, from folds; the sugar layer writes table rows, not TypeScript; LCNF writes code, not types.** Concretely: a macro in `Authoring/` that declares a row emits a `Program.Row` with its `cite`; the `Entry`'s two ASTs and its `TypeRef` are folds of that row's three `Ty` columns (`Bridge.schema` and `Codegen.Types.ofTy`, both of which exist); the body is the LCNF closure. One owner per spelling — the rule `Codegen/Templates.lean:6-30` already states for the printer — and a new Effect module becomes a table extension, i.e. data, not new metaprogramming.

## 9. The signature of every emitted function as a pair of ASTs

**The `Entry` already exists and is called `Program.Row`** (`src/Effect4/Program/Eff.lean:190-212`):

```lean
structure Row where
  name : String
  spelling : String                -- what the printer prints (`Ref.get`, `refs.get`)
  shape : RowShape := .call ;  trailing : List String := [] ;  kind : RowKind
  request : Ty                     -- the Entry's `input`
  answer : Ty                      -- the Entry's `output`: answer / error / requirement columns
  error : Ty := .never ;  requires : List ServiceKey := []
  cite : String                    -- "the rc.112 file and lines the row transcribes"
  typeArgs : List String := []     -- the Entry's `typeParams`, as target strings
  registration : Registration := .deferred
deriving DecidableEq, Repr
```

Against the workshop note's `Entry := { module, name, typeParams, input, output, cite }` (§5 there) the only differences are: `module` folded into `spelling`/`cite`; `typeParams` as target *strings*, not holes; and the three columns `Ty`, not `Schema`. **Reproduced**: the two hand-written packages contribute **8** rows (`Packages.table.length = 8`), **0** with an empty `cite`, **0** with a non-empty `typeArgs`, and all eight cite rc.112's *unstable* modules (`unstable/sql/SqlClient.ts:95`, `unstable/sql/Statement.ts:442-445`, `unstable/sql/SqlClient.ts:39-84`, and five at `unstable/persistence/KeyValueStore.ts`). The built-in alphabet is 55 more rows (`tools/Tools/TsGen.lean:427-428`).

**Where the ASTs come from — two folds, not one.** The runtime schema is `Bridge.schema ∘ Ty.normalize : Ty → Representation` (`Bridge.lean:38`, `Ty.schema` at `:187`); the static type is `Codegen.Types.ofTy : Ty → Option TypeRef` (`Types.lean:311`). Both are folds of the same `Ty`; neither is derivable from the other, and that is correct — D-J rule (2) asks for one *source*, not one *object*: the runtime schema decodes values, the static type is what `tsc` checks. **Reproduced** for the kv program: `declarationType ⟨.option .string, .prod .string .string, ∅⟩` renders `"Effect.Effect<Option.Option<string>, readonly [string, string]>"`; **red control**, with a non-empty requirement row it answers `some none`, i.e. **no annotation at all** (`Codegen/Print.lean:70-79`, which documents the omission and why). That dropped annotation is precisely the `Entry`'s output slot, and it is F5 / D-D's second half.

**Type parameters need no 23rd node — proved, and reproduced.** A type variable can be an **unresolved `$ref`**: `Document.fieldAdmissible_danglingReference` (`src/Effect4/Schema/Check.lean:1456`) **proves** that `Document.mk (.reference ⟨"Missing"⟩) []` is field-admissible — "Field admission resolves no reference." **Reproduced**, with both red controls: an open entry `.declaration ⟨"effect/schema/Exit", .null⟩ none [.reference ⟨"A"⟩, .reference ⟨"E"⟩, defectRep] []` is `fieldAdmissible` with an **empty** table and `Arch.accepts` returns **false** for it against any JSON (an open template is not a predicate); binding it is adding table entries and it stays admissible; `.reference ⟨""⟩` is **not** admissible (the empty key cannot be named, `Document.lean:111-112`); and `Bridge.ofSchema` refuses both the open entry and a bare reference, so an open `Entry` has **no `Ty`** — which is right, and is what `Ty.app`'s holes would change.

**How a TypeScript caller decodes with them.** The `Entry` emits three artefacts into one generated module: `export const fooInput = …`, `export const fooOutput = …` (both `Schema.*` text from `toCodeDocument`), and `export const foo: (x: Input) => Effect.Effect<A, E, R> = …` whose `TypeRef` is the static fold. A caller that trusts the compiler uses the third; a caller across a process boundary uses `Schema.decodeUnknownSync(fooOutput)` on the reply. Those are the two objects `ts/eff/eff.gen.ts` already ships (`decodeEff`, `isEff` at `:390`) — the one place where "a program is an Effect Schema value" is literally true today (scout D §1).

---

# Part 4 — vendoring Effect into the LCNF

## 10. The ceiling, counted

**Scanner: the TypeScript compiler API, `typescript@5.9.2` from `ts/eff/node_modules`, driven from bun 1.4.2.** I used it, not the ingest recognizer, because the recognizer parses with `oxc-parser` (`ts/eff/ingest/oxc.ts:4`) — an ESTree parser with **no type checker**, so it cannot see a signature's parameter and return types, which is the whole question. The estate's own type oracle is `@effect/tsgo 0.38.0` + `typescript 7.0.2` in `harness/schema-host`; that is the production route and gives the same shape of answer. My scan enumerated every module's exports via `checker.getExportsOfModule` and classified each by declaration kind, then by whether every parameter and return type is expressible from the 21 node kinds without an opaque `Declaration`. Buckets: **A** monomorphic callable, every type structural; **B** monomorphic callable, some type needs an opaque `Declaration` (a class instance, a branded `~effect/…` type, `Effect<…>`, a function type); **C** callable with type parameters; **D** non-callable constant (A/B by its type); **E** type-level only (`interface`, `type`, `declare namespace`) or a re-export; **R** refused (conditional, mapped or indexed-access type).

**Stable surface — `src/*.ts`, 137 modules, 4,138 export symbols** (`index.ts`'s 143 re-exports counted separately, excluded here): A **75** (1.8%) · D-A 40 · B 703 · D-B 305 · C 2,372 (57.3%) · E 598 type-level + 44 re-export · R 1.

**Whole vendored tree — 340 modules (stable + `unstable/**` + `testing/*`; `internal/` and `index.ts` excluded), 7,008 export symbols**: A **91** · D-A 91 · B 1,265 · D-B 956 · C 2,896 · E 1,646 + 62 · R 1. By group: `unstable/ai` 518 exports (A 1), `unstable/http` 469 (A 5), `unstable/cluster` 332 (A 2), `unstable/cli` 267 (A 2), `unstable/httpapi` 254 (A 0), `unstable/rpc` 174 (A 0), `unstable/eventlog` 153 (0), `unstable/reactivity` 150 (0), `unstable/sql` 90 (1), `unstable/persistence` 89 (0), `unstable/workflow` 73 (0), `unstable/encoding` 58 (2), `unstable/schema` 51 (0), `unstable/observability` 43 (0), `unstable/socket` 39 (1), `unstable/process` 35 (2), `unstable/devtools` 30 (0), `unstable/workers` 29 (0), `testing/*` 16 (0).

**By module, for the ones the brief names** — columns A / B / C / D-A / D-B / E:

| module | exports | A | B | C | D-A | D-B | E |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `Effect` | 242 | **0** | 16 | 189 | 0 | 16 | 21 |
| `Layer` | 55 | **0** | 6 | 34 | 0 | 3 | 12 |
| `Schema` | 397 | **0** | 60 | 137 | 0 | 79 | 121 |
| `SchemaAST` | 140 | **0** | 56 | 24 | 3 | 45 | 12 |
| `SchemaRepresentation` | 67 | 1 | 14 | 3 | 0 | 0 | 49 |
| `Scope` | 13 | **0** | 6 | 4 | 0 | 0 | 3 |
| `Fiber` | 12 | **0** | 2 | 8 | 0 | 0 | 2 |
| `Ref` | 16 | **0** | 0 | 15 | 0 | 0 | 1 |
| `Deferred` | 23 | **0** | 0 | 21 | 0 | 0 | 2 |
| `Stream` | 243 | **0** | 4 | 221 | 1 | 3 | 14 |
| `Exit` | 30 | **0** | 3 | 23 | 0 | 0 | 4 |
| `Cause` | 65 | **0** | 13 | 27 | 9 | 3 | 13 |
| `Option` / `Result` | 67 / 47 | **0** / **0** | 1 / 1 | 56 / 33 | 0 | 1 / 3 | 9 / 10 |
| `Duration` | 57 | **0** | 44 | 2 | 0 | 6 | 5 |
| `Queue` | 39 | **0** | 0 | 35 | 0 | 0 | 4 |
| `Context` | 26 | **0** | 3 | 17 | 0 | 0 | 6 |
| `String` / `Number` | 64 / 30 | 18 / 6 | 32 / 20 | 8 / 0 | 1 / 0 | 1 / 4 | 4 / 0 |
| `Predicate` / `Function` | 50 / 25 | **0** / 5 | 25 / 0 | 22 / 17 | 0 | 0 | 3 / 3 |

**The 91 A-structural exports are, without exception, scalar utilities and JSON-schema plumbing.** By module: `String` 18 (`Order`, `Equivalence`, `isEmpty`, `isNonEmpty`, `length`, `stripMargin`, the nine case converters), `JsonSchema` 9, `BigInt` 8, `Number` 6, `Function` 5 (the five `const*`), `Equivalence` 4, `Order` 4, `Hash` 3, `Boolean` 3, `LogLevel` 3, `Metric` 2, `JsonPointer` 2, `Formatter` 2, `unstable/cluster/ShardId` 2, `unstable/process/ChildProcess` 2, and one each from `Array` (`range`), `BigDecimal`, `SchemaRepresentation` (`makeCode`), `Ordering`, `RegExp`, `Encoding`, `unstable/encoding/{Toml,Ini}`, `unstable/cli/{Prompt,Completions}`, `unstable/http/{HttpMethod,Etag,HttpServer,MultipartParser,Cookies}`, `unstable/ai/AiError`, `unstable/socket/Socket`, `unstable/sql/Statement`. **`ServiceMap` does not exist** as an rc.112 module; the module is `Context.ts` (26 exports).

**Is "valid Effect TypeScript by construction" coherent? Three answers; only the third is the brief's.** *For the whole surface* — **no**, and the number is 91/7,008 = 1.3%. The reason is structural, not fixable by more vendoring: `Effect.map`'s signature is `<A, B>(self: Effect<A,E,R>, f: (a: A) => B) => Effect<B,E,R>`, whose input has a *function* type and whose output is parametric in the input's parameter; a Schema AST has `Declaration.typeParameters` — application, not abstraction — so nothing in it can say "the output's first parameter is the return type of the input's second argument". *For the data-typed part* — **yes, and it is already how the estate works**: 1,008 exports (703 B + 305 D-B) become Entries once an id has a reviver; 2,896 generic ones become Entry *families* whose parameters are unresolved `$ref`s (§9, proved admissible) instantiated at the call site; and **256 exports are already Schema values** whose `.ast` can be harvested directly (**tested**: 256 exports carry both `ast` and the `~effect/Schema/Schema` brand, 171 of them class declarations, plus 76 functions returning a Schema), concentrated in `unstable/ai/McpSchema` (78), `unstable/httpapi/HttpApiError` (26), `unstable/ai/AiError` (22), `unstable/devtools/DevToolsSchema` (17), `unstable/sql/SqlError` (13) — **the unstable modules are where the harvestable schemas are**, which is the strongest argument for the owner's "vendor the unstable ones too". *For what the template table already prints* — **yes, by construction and already stamped**: 67 rows (**reproduced**), law 11 `readPrint` (`src/Effect4/Laws/Codegen/ReadPrint.lean`), the tsc oracle (`tools/target/oracle.ts`), and `make check-corpus` inside `make check` (`Makefile:241`). So the honest sentence is: **the `Entry` table makes the emitted TypeScript valid against the declared `Entry`, and tsgo makes the declared `Entry` valid against rc.112 — two claims, with 91 exports where the first suffices alone.**

## 11. The vendoring route, concretely

**"Linking the Effect modules into the LCNF" means an `Externs`-style table, and the OCaml precedent is exact and small.** `Externs` (`src/OCaml5/Lcnf/Externs.lean:127-148`) has seven maps — `fns : Name → ExternFn`, `tys`, `fields`, `elems`, `ops`, `fieldCarrier`, `cargs` — where `ExternFn = { arity, head : String, spec : List ExArg, optional }` (`:115-124`) and `ExArg` is a literal name or a positional/labelled slot (`:106-112`). It is read from a text file, one row per line (`:327`): `ocaml/engine/externs.txt` is **162 lines**, of which **30 `fn`, 2 `fn?`, 9 `ops`, 9 `field`, 1 `type`, 1 `elem`** (counted), the rest comment. Its completeness check is stated in its own header — *"the table is complete iff `api_engine.ml` compiles, and it compiles as a functor body with no instance"* — i.e. **a type-check is the completeness proof**. That is the model to copy, and the TypeScript analogue already exists: `tools/target`'s tsc oracle for per-claim diagnostics, `harness/schema-host`'s tsgo for whole-module checking.

**How the table is produced.** Not by hand and not by the recognizer: tsgo's checker walks `vendor/effect-4.0.0-rc.112/src/**` (as my scan did) and writes one row per export — `{ module, name, typeParams, input : Document, output : Document, typeRef : TypeRef, cite : "file:lines" }`. Three properties make it auditable the way `harness/trace` is: the `cite` column is a citation into the pinned vendor tree (`Program.Row.cite` already is exactly this, and **reproduced**: 8/8 rows carry one); the pin is the vendor directory plus `ts/eff/ingest/pins.ts`; and each row's bucket (A/B/C/…) is recorded, so the census is a table the gate can diff. **The guard the workshop note already names is available on day one**: `SqliteBun` and `KeyValueStoreMemory` must come out of the generated table byte-identical to `src/Effect4/Program/Packages/*.lean` — 8 rows, all cited, **reproduced** — and a hand edit to one `cite` is its red control.

**What "unstable" adds.** Measured: 2,854 export symbols across 19 groups (203 modules). Two things stable does not have: **the harvestable schemas** (§10 — 78 in `McpSchema` alone, which is 141 exports of which 114 are D-B schema constants, i.e. the MCP wire protocol as Schema values, scout C's surface), and **the rows the estate already uses** (all 8 package rows cite `unstable/sql` and `unstable/persistence`). They also carry the largest type-level share (1,048 of 2,854), being interface-heavy.

**Which modules first, and why. Not `Effect`.** (1) **`unstable/persistence/KeyValueStore` and `unstable/sql/{SqlClient,Statement}`** — the byte-identical regeneration of the two existing packages is the only guard that can fail today. (2) **`unstable/ai/McpSchema`** — 78 harvestable ASTs, no LCNF needed, and it is D-F's surface; it proves the harvest path end to end with zero emitter work. (3) **`Duration`** — 44 of 57 exports are B, the highest B density of any stable module, so the smallest place a reviver table earns its keep. (4) **`Exit`, `Cause`, `Option`, `Result`** — the four whose declarations `Bridge.schema` already mints ids for (`effect/schema/{Option,Result,Exit,Cause,Defect}`, `Bridge.lean:47-53`), so the reviver table D-B and D-E both need *is* this group. (5) **`Ref`, `Deferred`, `Queue`, `Scope`, `Fiber`** — 0 A and 0/0/0/6/2 B against 15/21/35/4/8 C: entirely an `Entry`-family exercise, needing `Ty.app` (§4) before they can be typed at all; the test of the generic route, not its first customer. (6) **`Effect`, `Layer`, `Stream`** last — 189/34/221 generic, and `Stream`'s 221 are where higher-order signatures live; the workshop note's Q-F answer ("refuse and list first, grow the forms second") is the right protocol and my counts are the list it asked for.

## 12. The worked example, twice

**(b) `readKey` through the template table, unchanged, beside its `Entry`.** The program is E2 of the author battery (`Test/Program/AuthorContract.lean:116-121`); scout D reproduced its printed image, and I **reproduced** its annotation. Source of each line: **[T]** template table, **[AST]** Schema AST, **[LCNF]** lowered code, **[syn]** syntax AST only.

```ts
import * as Effect from "effect/Effect"                                   // [syn]  Module.imports — F2, absent today
import * as Option from "effect/Option"                                   // [syn]
import * as Schema from "effect/Schema"                                   // [syn]

export const readKeyInput  = Schema.Void                                  // [AST]  Row.request = .unit
export const readKeyOutput = Schema.Exit(                                 // [AST]  Bridge.schema (.exitOf answer error)
  Schema.Option(Schema.String),                                           // [AST]  answer = .option .string
  Schema.Tuple([Schema.String, Schema.String]),                           // [AST]  error  = .prod .string .string
  SchemaRepresentation.Defect)                                            // [AST]  Bridge.defectRep

export const readKey: Effect.Effect<                                      // [T]    printDecl
    Option.Option<string>, readonly [string, string]>                     // [syn]  Codegen.Types.ofTy — REPRODUCED
  = Effect.flatMap(Kv.make(), (a0) => a0.get("greeting"))                 // [T]    rows 'call' + 'method' + eff_bind
```

Everything on the last two lines is **stamped** today — the body by the 67-row table and law 11, the annotation by `declarationType` (`Print.lean:70`), which I **reproduced** as `Effect.Effect<Option.Option<string>, readonly [string, string]>`. The two `export const …put` lines are the new AST-typed `Entry`, and their *text* is D-E's `toCodeDocument`, not a second emitter. The `import` block is F2 — `ModuleEmission.module` sets `imports := []` and says so (`src/Effect4/Codegen/Checked.lean:38-41`).

**(a) `Run.step` lowered to TypeScript with an AST-typed signature.** `Run.step (s : Run) (c : Command) : Run` (`src/Effect4/Run.lean:116`) is a Lean function over `Run` (`:49`), which holds `Api.Built` and `Api.HostSession.Session` — hence a `Machine`, hence live handles. So the *signature* is AST-typable only because `Api.Runner.Command` already crosses (`src/Effect4/Api/RunnerBytes.lean:78-86`) while `Run` cannot: `Canonical` accepts no handle by construction (`Store/Shape.lean:60-90`). The honest lowering therefore has a bytes boundary, which is what `RunnerBytes` already chose:

```ts
import { Command, Observation } from "./runner.gen.ts"                    // [syn]  from Canonical.shape — §7
export const stepInput  = Schema.Struct({ run: Schema.Uint8Array, command: Command })      // [AST]
export const stepOutput = Schema.Struct({ run: Schema.Uint8Array, observation: Observation }) // [AST] needs D-7
export const step = (input: typeof stepInput.Type): typeof stepOutput.Type => {            // [syn]
  let st = decodeState(input.run)                                         // [LCNF] Api.ofBytes — the engine root
  switch (input.command._tag) {                                           // [LCNF] Stmt.switch over the Command index
    case 0: { st = applyControl(st, input.command.decision); break }      // [LCNF] translateClosure of Run.step
    case 1: { st = applyReply(st, input.command.reply); break }           // [LCNF]
  }
  return { run: encodeState(st), observation: observe(st) }               // [LCNF]
}
```

Three things this establishes. **First, the `Effect` import would be unused**: `Run.step` is pure (`Run → Command → Run`), so the lowered function is a plain function and vendored `Effect` is called nowhere — the brief's "calling vendored `Effect` where the Lean code calls the machine" is **inverted** for the session API. The machine is already pure and first-order; what needs `Effect` is the *driver* around it (`Run.drive`, `Run.lean:269-313`), and that driver is the one piece that is a fold of nothing. **Second**, `Stmt.switch` keyed on `Nat` (`Syntax.lean:100`) is exactly right for an LCNF `cases`, so the control-flow half needs no new syntax. **Third**, scout C's cost bites here: `Command`'s Schema text is 231,660 characters because `Header`/`Call` inline the whole `Row`/`Ty` closure, so `stepInput`'s reference policy (their D7) must be decided before this emitter runs.

---

# Part 5 — verdict

## 13. The fragment, the risks, the order

**The fragment, named.** *Schema-AST-canonical* is coherent for the **encoded-side, program-free sub-AST**: the 21 kinds with `annotations` and `checks`, `encoding` present only as a Lean-authored `SchemaTransform` or a foreign id, `context` without `constructorDefault`, `Declaration` opaque by id. Up to the `Reference`/`Suspend` difference that is the 22-tag `Representation` the tree already mirrors under a gate — so the right move is **not** to make the AST canonical but to keep the representation canonical and add the AST as its *source*, with the six program slots first-order where Lean can own them. *AST-as-the-language-for-TypeScript* is coherent for the **`Entry` fragment**: monomorphic-or-`$ref`-parameterised signatures whose types are the 21 kinds plus opaque ids — 91 exports outright, ~1,100 with a reviver table, ~2,900 as families once `Ty.app` exists — and for the 67 template rows today, which is the only part that is stamped.

| # | risk | the probe that retires it |
| --- | --- | --- |
| R1 | Checks stay names, so the published schema accepts what the machine refuses and vice versa | the D-D / S-5 lane: every corpus program's recorded exit through `decodeUnknownSync` of its own `Schema.Exit(…)`. My §3 red control (`accepts` at `nat` says true for `-3.0` and `1.5`) is that lane's first expected red |
| R2 | The AST carrier costs the checker its derived instances | already measured: `deriving instance DecidableEq for Representation` fails. Retired by not doing Design B |
| R3 | `Ty.app`'s assignability leaks into Lean | one `tools/target` oracle query per generic row: `tsc` decides `Ref.Ref<number> ⊑ Ref.Ref<unknown>`, Lean records the verdict. Red control: a row the host says no to |
| R4 | The TypeScript emitter's meaning drifts from LCNF | rung 3 for TypeScript: a `TypeScript.Expr → Target.Expr` reader refusing by constructor name, the same 20,387 vectors. Red control: the six rung-2 mutants must go red through the new reader too |
| R5 | `Nat` as `number` is wrong past 2^53 and the corpus never reaches it | one vector set above 2^53 in the rung-2 `Ty` vectors; red control = the OCaml route's 63-bit saturation disagreeing with the TypeScript route on one input |
| R6 | The `Entry` table drifts from rc.112 | byte-identical regeneration of the 8 existing package rows; red control = a hand edit to one `cite` failing the gate |
| R7 | A published schema is a quarter of a megabyte | the reference-policy decision (scout C's D7), measured: `Command` = 231,660 chars, `Outstanding` = 2 references |
| R8 | Generics need a 23rd node | already retired: §9's probe, `fieldAdmissible` with an empty table, proved by `Document.fieldAdmissible_danglingReference` |

**The order of slices, smallest first, each with its gate.** (1) **`Check.holds`, or the decision not to have it** — pure, total, over the two ids the bridge mints plus a stated exclusion list; *gate*: a `#guard` battery where `-3.0` and `1.5` are **refused** at `Ty.nat`'s image, i.e. the exact red control I reproduced, going green. (2) **`fits` = `Arch.accepts` with checks, and its first caller**; *gate*: `check-schema-codec` extended with `fits (Ty.schema t) v = Val.hasTy v t` on the S-3 contract cases; retires R1's Lean half. (3) **`Ty.app`, the five additions of §4**; *gate*: `ofSchema_schema` still `rfl`-per-constructor, `key_injective` still proves, `Ref.Ref<number>` no longer a string. (4) **The scanned `Entry` table for the two package modules**; *gate*: byte-identical `Packages/*.lean`, 8 rows, `cite` intact; retires R6. (5) **`toCodeDocument` + the reviver table** (D-E, D-B); *gate*: `check-schema-host` round-trips the six `effect/schema/*` ids and the kv handle node through tsgo. (6) **`McpSchema`'s 78 harvested ASTs**; *gate*: each harvested `Document` decodes its own rc.112 fixture — no emitter work, and this is where the harvest path is proved. (7) **The TypeScript rung-3 reader** (R4); *gate*: 20,387 vectors, six mutants red — the slice that makes the backend a claim, and it should precede any emitter breadth. (8) **The emitter over the `Entry` families** (`Ref`, `Deferred`, `Queue`, `Scope`, `Fiber`), then `Effect`/`Layer`/`Stream` with a published refusal list.

## 14. Decisions for the owner

**E-1. Two carriers or one.** (a) the AST replaces `Representation` as canonical; (b) the AST is a *second* carrier whose `toRepresentation` fold lands in the pinned 22-tag one; (c) no AST carrier — keep the representation and add the six program slots to it where Lean can own them. **Recommend (b), and only after slice 5.** *Reason*: the pin (`check-schema-pins`) and `fromJson` are both about the persisted projection, so (a) discards the estate's only stamped schema claim; (c) is cheapest but makes the representation lie about its name; and the AST is needed only for the three things the projection drops, of which exactly one — a transformation — is something Lean owns better than rc.112 (§1).

**E-2. `Check.holds` — pure, store-reading, or absent.** (a) `Check → Val → Bool`, pure, over a closed id list; (b) `Check → Stores → Val → Bool`, so the external-handle counter check is expressible; (c) no `holds` — checks stay names and agreement is a theorem per boundary (`externalValue_iff_fits`). **Recommend (a) for the closed id list plus (c) for the handle counter.** *Reason*: §6 shows the one check that matters at a real boundary is not a predicate on a value, so (b) contaminates every check with the store; (a)+(c) keeps `fits` pure and puts the store-dependent obligation next to the machine, where `Admit.lean` already is.

**E-3. D12's shape.** (a) the brief's `decode ast v = some x ↔ fits ast v`; (b) the sound/total pair of §3 with `isValueAst` as the totality premise; (c) leave D12 as the S-5 harness gate. **Recommend (b) and (c), stated as two claims.** *Reason*: (a) is false in the total direction for the same reason the S-3 amendment of 2026-09-11 exists, and the Lean theorem and the host gate are about different decoders, so neither replaces the other.

**E-4. Design A vs B for `Ty`** (§4). **Recommend A, with `Ty.app`.** *Reason*: measured — `Representation` has no derivable `DecidableEq` and no `Repr`, and `Ty.key`'s injectivity (hence `normalize`, `sub`, and both soundness statements) cannot survive `Json`-valued annotations in the key. A is already proved; the only real gap is type-constructor application, which is five additions.

**E-5. D-A, sharpened** (§5). **Recommend (c) now and (b) before the first foreign consumer, as stages rather than alternatives.** *Reason*: `select` reads `.list [.str t, payload]`, which *is* `Arrays[Literal t, T]`, so annotation-only names keep the eliminator working; but a foreign `decodeUnknownSync` never reads an annotation, so a consumer of the published schema gets a positional array where the author wrote a record. Naming the first foreign consumer dates (b).

**E-6. What the emitter targets.** (a) the Schema AST directly; (b) `TypeScript.Expr`/`Stmt`, the syntax AST, with the Schema AST appearing only as annotations, `Schema.*` values and `Entry` signatures; (c) strings. **Recommend (b), unambiguously** — it is what the ML route does with `Ml.Decl`, and the vendored package already spells `Effect.Effect<A,E,R>`, function types and per-field `readonly`, which the Schema AST cannot. Two additions to `~/Dev/lean4-typescript` follow and should be scoped now: a type-parameter **binder** list on `ConstDecl`/`ProgDecl`, and `TypeRef.intersection` if any `Entry` needs it (none of the 91 does).

**E-7. Where type generation lives.** (a) the sugar/macro layer; (b) the LCNF layer; (c) split — tables own types, LCNF owns semantics, sugar owns authoring. **Recommend (c)**, with the sentence worth writing into the plan: *the sugar layer writes table rows, not TypeScript; LCNF writes code, not types; the `Entry` table's two ASTs and one `TypeRef` are folds of the row's three `Ty` columns, and both folds already exist.* *Reason*: a macro's output is checked by Lean's elaborator and nothing more, whereas LCNF's meaning is certified by a differential against the Lean compiler — that asymmetry is the owner's "LCNF is our superpower", and it argues for keeping types *out* of the macro layer.

**E-8. The scanner and the pin for the `Entry` table.** (a) tsgo in `harness/schema-host` (typescript 7.0.2); (b) the `typescript` API in `ts/eff/node_modules` (5.9.2, which I used); (c) the oxc recognizer. **Recommend (a)**, and record that **(c) cannot do it**: `oxc-parser` is an ESTree parser with no checker, so it cannot see a signature's types at all. *Reason*: the estate already pins tsgo as its type oracle; two checkers would be two verdicts.

**E-9. Which modules, in which order** (§11). **Recommend the six-step order**, whose first two steps produce falsifiable evidence with zero emitter work (byte-identical package regeneration; `McpSchema`'s 78 harvested ASTs) and whose last step publishes a refusal list rather than a claim. *Reason*: `Effect` has **zero** A-structural exports out of 242, so starting there means designing holes for shapes nobody has counted — the workshop note's Q-F warning.

**E-10. The rung-3 reader before emitter breadth.** (a) emitter first, reader after; (b) reader first, on the `Ty` closure only, then breadth. **Recommend (b)**. *Reason*: rung 3 is the only artefact in the whole proposal that can turn "the emitted TypeScript means what the Lean function means" from a hope into a checked claim; its vectors already exist (20,387) and its red controls already exist (the six rung-2 mutants). An emitter without it is a second hand-transcription with a generator in front of it.

---

## Where the tree contradicted the brief

1. **`Check.holds : Check → Val → Bool` does not exist** (§3). No `def holds` in any schema module. `src/Effect4/Schema/Check.lean` is structural field admission (`fieldAdmissible`, `:780`), not a check's meaning; the quoted "a name, not a meaning" is `Representation.lean:18` and is about **tags**. The nearest thing is `Arch.accepts` (`src/Effect4/Arch/Accepts.lean:114`), which states in its own header that checks are **not** evaluated and has **zero** callers.
2. **`Effect4.Schema.Value` is not a module.** Cited as "the relational judgment this approximates" (`Accepts.lean:32`) and at `Document.lean:66`, and absent. Any D12 theorem is about a judgment that has not been written.
3. **"every node carries four slots" is true of `Base` only** (§1). Four subclasses carry a fifth, `encodingChecks` (`SchemaAST.ts:693`, `:1688`, `:2101`, `:2917`), and `Declaration` a sixth, `encodingRun` (`:698`).
4. **The `Codec` laws do not "restate over the AST"** (§3). All seven quantify `{t : CTy}` and mention `Ty`; `Codec.lean` never mentions `Representation`. They are re-founded on three new definitions, not restated.
5. **`Ty` is already an embedding with a proved left inverse** (§4). The brief poses design 1 as an option; `Bridge.schema`/`ofSchema`/`ofSchema_schema` (`Schema/Bridge.lean:38`, `:63`, `:114`) are it, landed at `[propext]`. Likewise **`Ty.ofSchema` is already total-by-refusal** (§5) — what it is not is conservative.
6. **`SchemaTransform`'s endpoints are `Ty`, not AST** (`Schema/Transform.lean:24-25`), so restating the laws over the AST re-types the transform too.
7. **`readKey` is ambiguous in the tree**: `Effect4.Codegen.Read.readKey` (`Codegen/Read.lean:346`) is a Lean *reader* for a `ServiceKey`; the brief means E2 of the author battery (`Test/Program/AuthorContract.lean:116-121`). I used the latter.
8. **`ServiceMap` is not an rc.112 module** (question 11's list). The module is `Context.ts`.
9. **My worktree is at `6264983a`, not `589d3e7a`.** `589d3e7a` is one commit later and its only change is the brief itself; `git diff --stat 6264983a 589d3e7a -- src tools vendor` is empty, so every citation holds at both. The main checkout has since moved to `b6049b90`.

## Evidence

Eight probes, run as `lake env lean probe/P<n>.lean` in `/Users/pooks/Dev/lean4-effect4-scout-e` at `6264983a`. No `lake build` was needed (the cache was warm), no `make check`, and the worktree's only `git status` entry is the untracked `probe/` directory. **P1**: the `Ty`→`Representation` embedding, its axioms, four refusal controls. **P2**: a 24-field `RepresentationAlgebra` tag census (the image is 9 representation tags + `Filter`, against the 22-tag census) and `Arch.accepts` with the `-3.0`/`1.5` red controls. **P3**: `TypeRef` rendering of `Effect.Effect<…>`, function types, per-field `readonly`, literal unions and readonly tuples; the 67-row template table split 31/20/10/6; `TypeScript.Structure`'s reducibility and loop-header verdicts. **P4**: the derived-instance cost — `Ty.key`, and the two failures (`Repr Representation`; `deriving instance DecidableEq for Representation`). **P5**: `Canonical.shape` for `Ty`/`EffTy`/`Term` and their rendered `Document`s, with the `Shape.arrow` red control. **P6**: the unresolved-`$ref` type variable — admissible with no table, accepting nothing, with the empty-key and `ofSchema` red controls. **P7**: `Codegen.Types.ofTy` over all 16 constructors, and `declarationType` with its requirement-row red control (`some false`). **P8**: the 8 package rows, their rendered signatures and their eight rc.112 citations. Outside Lean: one TypeScript-compiler scan (`typescript@5.9.2` under bun 1.4.2) of 340 modules and 7,008 export symbols, plus a second pass counting the 256 exports that are already Schema values. The probes and the scan live in the session scratchpad, not in the tree. The red control kept throughout is the pair from §3 — `accepts` saying **true** for `-3.0` at `Ty.nat`'s image — which is what makes every other acceptance result in this note mean something.
