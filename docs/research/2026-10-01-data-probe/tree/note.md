# Seat TREE, data probe (2026-10-01): what the tree has for typed data, and what records, variants, a JSON route, structured error payloads and int would touch

**The one thing.** A `record` constructor in `Ty` is cheap; the value side is the decision.
A full copy of `Program/Ty.lean` with `record (fields : List (String × Ty))` appended compiles
with every normalization law proved (exit 0). With one hand eliminator registered, 26 of the 29
copied theorems keep their text. But the tree's structure rule for values (`ctor 0 [v₁, …]`,
positional) and TypeScript's width subtyping cannot both hold: with them, `fits_sub`
(`Laws/Program/Typed/Membership.lean:837`, proved today) becomes false (proved red control).
So the owner picks one of two coherent designs before any slice:

- **exact records**: no width rule, positional values. Every existing law shape survives.
  TypeScript accepts more assignments than Lean does.
- **width records**: name-carrying values whose unnamed entries are constrained. TypeScript
  agrees. `fits_live`, TyView's `sub_eq_args` and the JSON layout each gain a rule.

That choice goes with the DB-15 amendment and row 2. "Native schema support" today means the
rc.112 Schema AST held as data, plus a `Ty → Schema` lowering and a JSON codec with
round-trip laws. Neither is on the host reply path. A schema struct has no program type.
Row 39 (ruled 2026-09-18, not executed) deletes about half the Schema plane.

Base: `bc77e97f` on `refactor/phase1-phase3`. During the probe the coordinator committed
`ba9783c3` (01:25), which touches documents only: `docs/STATE.md`, `docs/core/decisions.md`,
`docs/core/system-map.md` and the architecture map. The code measured here is the same at both
commits, and none of those edits touches a row this note cites. Built artefacts: the `Effect4` and `Effect4.Laws`
oleans date from 01:04 and 01:15 today, after HEAD's commit time (01:02), and `OCaml5`, `Tools`
and `Conform.Effect4` from 01:23. The `Test` oleans predate `90df5d21`, so no probe here imports
`Test`, and `Test/` is read, not run. Every Lean probe in this folder ran through the
one-compiler lock with `-M6144 -DwarningAsError=true`; logs are beside the probes (§7).

Evidence words: **proved** means a kernel theorem run here, with its axioms printed at
`[propext, Quot.sound]` or fewer; **tested** means a finite check run here (`#guard`, an
instrument's printout, a grep); **reading** means read in code or notes, not run; **assumed**
means not checked. A finite probe is reported as one.

---

## 1. What exists

### 1.1 The type language (`src/Effect4/Program/Ty.lean`)

- **Twenty constructors; no record, no variant, no field spine** (reading, `Ty.lean:37-75`):
  `never unit nat int string bool handle option list prod except exitOf causeOf fiberOf union
  lit refOf deferredOf var unknown`. They hold wire tags 0–19 in
  `tools/Effect4Gen/wire-tags.json`, with `retired: {}`.
- **The carrier rule is in the header** (reading, `Ty.lean:11-23`). Every field must be a
  `Shape` (`Conform.Source.readShape`, `tools/Conform/Source/Description.lean:35-54`). The
  header warns that "a `List Ty` argument would make `Ty` nested and cost the derived equality
  and every `induction` on it". A constructor is appended, never inserted.
  `List (String × Ty)` is a legal `Shape`: `.list (.prod .string (.nominal Ty))` (reading,
  `Description.lean:46-48`).
- `normalize` (`:607-628`) recurses through every constructor and distributes products over
  union factors (`productMembers`, `:603`). Unions become sorted maximal antichains through the
  generic row library (`normalizeRow`, `:590`; `Effect4.Row`, `Data/Row.lean:30-33`).
- `Normal` (`:631-655`) is an erased invariant. Its `prod` arm needs `isFactor` on both sides
  (`:643`), and `isFactor` (`:571-573`) is false only at `union`. `normalize_idem` (`:752`)
  follows from `Normal.fixed`. `CTy` (`:842`) is the canonical subtype.
- `sub` (`:437-456`) is well-founded on `sizeOf a + sizeOf b`. It is covariant on structural
  arms and invariant on `refOf`/`deferredOf`, has `unknown` as the top, and puts
  `lit ≤ string`.
- Variants exist only as **tagged tuples**: `prod (lit tag) payload` members of a union. They
  carry the tag decision (`isTagged`, `diffTag`, `taggedColumn`, `payloadOf`, `payloadTy`;
  `Ty.lean:774-807`) and the `tagIs` atom (`Machine/Term.lean:157`, `tagHit` `:361-363`). This
  is decisions row 2's option (c) (reading).

### 1.2 The typing signature (`src/Effect4/Program/Typing/Rules.lean`)

- `Signature Op` (`:49-66`) has six fields: `rowOf`, `atomOf : String → List Ty → Option Ty`,
  `scopeKey`, `serviceTy`, `dom` and `constAtom`.
- Terms are typed by the fold `argTy`/`argsTy` (`:89-102`). `Term` is `var | lit | app atom
  args` (`Machine/Term.lean:100-106`), so a term has no record construction, no field
  projection and no object literal (reading).
- Literals are typed by `litArgTy` (`:77-81`). `Lit` is `unit | nat | bool | str`
  (`Machine/Term.lean:87-92`), with no signed literal.
- Causes are typed by `causeTy` (`:147-161`). Its `fail` and `die` leaves require
  `admittedErrTy` (`Program/Eff.lean:56-68`).
- Rows are typed by `rowTy` (`:114-117`).

### 1.3 Values and their exact codecs

- **`Store.Val`** (`Store/Carrier/Val.lean:150-167`) has the frames `unit bool nat str bytes
  list pair none some ctor ref handle`; tag bytes 1–12 are identity (`:57-72`). It is a
  **nested** inductive, so the tree already pays the nested bill here: a hand `Repr`
  (`:173-198`), a hand `beq`/`DecidableEq` (`:1109-1154`), and a hand single-motive induction
  principle `Val.ind` (`:270-287`). The byte codec is exact: `decode_encode`, `decode_exact`
  and `encode_injective` (`:1040-1066`, reading).
- **A record already has a value encoding, and no new frame is needed.** "a structure is
  `ctor 0 [fields…]`, a case of a sum is `ctor i [args…]`" (`Machine/Value.lean:31-37`; the
  generated rule of `Store/Domain/Derived/Program.lean`). The CAS shape checker reads exactly
  that (`Store/Domain/Shape.lean:173-176`). Field names are erased; this matters in §4.4
  (reading).
- **`Canonical`** (`Store/Domain/Canonical.lean:32-44`) is the exact embedding class: `shape`,
  `toVal`, `ofVal`, `ofVal_toVal` and `ofVal_exact`, with no normaliser needed. `Store.Image`
  (`Store/Carrier/Image.lean:39-47`) is its structure form (reading).
- **The program's own encodings** in `Fits`/`Val.hasTy`: a product is `list [x, y]`; a Result
  is `ctor 0 [err] | ctor 1 [val]`; an exit is `ctor 0 [v] | ctor 1 [cause image]`; an option
  is `none | some x`; a context is `ctor 5 entries` (`Membership.lean:99-148`,
  `Program/Typed.lean:34-101`, `Machine/Value.lean:199-219`). All of these are type-directed,
  so `ctor 0 [x]` means different things at different types (reading).
- **Numbers**: `Val.nat (n : Nat)` is the only number. No frame holds a signed or fractional
  value (reading).

### 1.4 The value judgment (`src/Effect4/Laws/Program/Typed/Membership.lean`)

- **One clause per `Ty` constructor** (`Fits`, `:87-148`):
  - `never`: `False`.
  - `unit`, `nat`, `string`, `bool`: the exact frame.
  - `int`: `False` (`:91`).
  - `handle`: `HandleFits` reads the world's declaration tables (`:52-59`), or the context
    arm (`:97-98`).
  - `option`: absent, or present with the payload recursively.
  - `list`: an ordinary list or a fiber snapshot, every element recursively.
  - `prod`: `list [x, y]`, both columns recursively.
  - `except`: `ctor 0`/`ctor 1`, the selected arm recursively.
  - `exitOf`: success recursively; failure through `causeImage` and `CauseFits`.
  - `causeOf`: `CauseFits`.
  - `fiberOf`, `refOf`, `deferredOf`: declared in the world (covariant, invariant,
    invariant).
  - `union`: one branch.
  - `lit`: the exact string.
  - `var`: `False`.
  - `unknown`: `Live`.
- **Exit and cause**: `FitsExit` is `Fits` at the reified exit at `exitOf` (`:150-153`).
  `CauseFits` (`:80-83`) asks that every `Fail` reason's image (`valOfErr`) fit the error
  column; defects and interrupts sit outside it.
- **Laws**: `fold_of Fits` (`:248`, the generated connector `Fits.eq_cata`), `fits_hasTy`
  (`:269`), `fits_live` (`:520`), `fits_map` (`:729`), `fits_mono` (`:829`), `fits_sub`
  (`:837`, by `fun_induction Ty.sub`, cases `case1`…`case16`), `fitsExit_sub` (`:951`) and
  `fits_list_iff` (`:999`). `fits_sub` and `fits_hasTy` are at `[propext, Quot.sound]`
  (proved, `SchemaProbe.log`).
- **Is `Fits` structural on `Ty`?** Yes, at every arm but one. The context arm reads its
  services' types out of a table (`ServicesFit` → `FlatFits` on `nativeServiceTy key`,
  `:61-77`). Those types are not subterms of the type being judged. Today they are flat, so
  `FlatFits` "needs no recursion" (`:61-63`), and decisions row 114 refuses non-flat
  carriers. A structured service carrier (row 118, open) would need recursion through the
  service table, not through `Ty`. The structural way to get it is a stratified judgment: a
  carrier-level `Fits` that is structural on the carrier type, called from the context arm,
  with admission keeping context handles out of carriers (shape; reading).
- **A record arm is a different case.** Field types are subterms of the record type, so the
  arm recurses structurally with one companion over the field list (proved in §4).

### 1.5 The Schema module, and what "native schema support" means today

| Module | Owns | Laws (sample, axioms printed here) | Fate already ruled |
| --- | --- | --- | --- |
| `Schema/Representation.lean` (1,250 lines) | rc.112's persisted Schema AST: the 22-tag alphabet, and `Representation`/`Check` as a mutual nested inductive (`declaration`, `reference`, `suspend`, 12 keywords, `literal`, `enum`, `templateLiteral`, `arrays`, **`objects`** (property and index signatures), `union` anyOf/oneOf; `:701-778`). Equality is by hand: "`deriving DecidableEq` has no handler for a mutual nested inductive" (`:797-806`) | 55 theorems (tag censuses and injectivity, the private `beq_iff`) | stays |
| `Schema/Payload.lean`, `Schema/Document.lean` | leaf carriers; `Document`/`MultiDocument` containers. Reference semantics unopened (SC-DOC-01..05) | `Document.toMulti_injective` `[propext]` (proved) | stays |
| `Schema/Fold.lean` (generated, group SchemaFold) | `RepresentationAlgebra`, its fold, uniqueness | `hom_eq_cata_representation` `[propext]` (proved) | stays |
| `Schema/Authoring.lean` | constructors: `struct`, `tagged`, `variant`, `tuple`, `array`, `property`, `Check.named` | 6 `Predicate` laws | stays |
| `Schema/Annotations.lean` (1,193) | typed annotation keys as exact partial isomorphisms; traversals | 41 theorems; `AnnotationKey.Lawful.encode_injective` with no axioms (proved) | row 39: cut to the carrier and two keys |
| `Schema/Check.lean` (1,499) | field admission `fieldAdmissible` | 69 theorems; `Representation.fieldAdmissible_iff` `[propext]` (proved) | row 39: delete ("called by nothing") |
| `Schema/Accepts.lean` (117) | structural acceptance of a JSON value by a document, objects included | none; no caller (tested, grep) | row 39: delete ("the third value-fits checker") |
| `Schema/EffectfulField.lean` (960) | annotation-carried field-effect specs, an exact annotation codec, and a resolver into the standalone `Effects` package's `Program` | `EffectfulFieldSpec.annotationKey_lawful` with no axioms (proved) | row 39: delete **first** (a second effect algebra in the core closure) |
| `Schema/Image.lean` + `Laws/Schema/Image.lean` | `ProgramImage α t`: a `Canonical` image refined to a `Ty`, with JSON encode/decode | `decode_of_encode`, `decode_exact` `[propext, Quot.sound]` (proved) | row 39: delete |
| `Schema/Bridge.lean` (S-1/S-2) | `Ty.schema` (`:38-59`), `ofSchema` (`:79-135`), the `EffTy`/`Row` documents (`:209-227`) | `ofSchema_schema` `[propext]`, `CTy.ofSchema_schema` `[propext, Quot.sound]` (proved): **retraction only** | the documents' one caller `Api.schemaOf` (`Api.lean:137`, zero consumers) is deleted by rows 9 and 39 |
| `Schema/Codec.lean` (S-3) | type-directed JSON, rc.112's `toCodecJson` profile | `decode_of_encode`, `decode_encode`, `hasTy_decode`, `encode_sub`, `encode_injective` `[propext, Quot.sound]` (proved, `Laws/Schema/Codec.lean:55-96`) | stays (row 4: "`Codec.isValue` … remain") |
| `Codegen/Schema.lean` | prints a `Representation`/`Document` as rc.112 `Schema.*` TypeScript | finite host checks `make check-schema-ts`, `check-schema-codec` (reading, `docs/GENERATED.md`) | stays |

Outside `Schema/` sits **`Store/Domain/Shape.lean`**, the CAS's own data description. It has
`struct (name) (fields : List (String × Shape))` and `sum (name) (cases : …)`; it is nested
and therefore has a hand `Repr` (`:60-118`). Its checker is `ShapeDoc.accepts`, and it renders
to `Representation` through `Store.render`. **Three data descriptions exist (`Ty`, `Shape`,
`Representation`), and only `Shape` has records and variants.**
`Test/Schema/DialectContract.lean:31-51` pins `Bridge.ofSchema ∘ Store.render`: a `struct`, a
`sum`, `named` and `anyRef` all have no `Ty`; `nat` reads back as `int`; `unit` and `option`
are lost. It says "No theorem relates them" (reading). Fact 5 of `SchemaProbe.lean` reruns the
struct row (tested).

**What "native schema support" means, framed by AGENTS.md's sentence.** AGENTS.md says:
"Schema is a data language; every effectful slot in it is a hole filled by an `Eff` program
with a typing certificate; `Ty` and the schema carriers never mention `Eff`; a foreign
transformation is a name with a typed signature that any meaning-needing operation refuses."

Measured against that sentence:

1. **The data language exists as data.** `Representation`, `Document`, the authoring
   helpers, the generated fold and the TypeScript printer are all present, and `Ty` and the
   carriers never mention `Eff` (reading).
2. **No effectful slot is filled by an `Eff` program.** The one slot mechanism,
   `Schema/EffectfulField.lean`, is filled by an `Effects.Program` with no typing certificate,
   and row 39 deletes it (reading).
3. **The plane does not type program data.** The only arrow from Schema to programs is
   `ofSchema`. It reads exactly the nodes `Ty.schema` writes and refuses every struct and
   tagged struct (tested, Fact 2), so a schema's record has no program type.
4. **The exact embedding AGENTS.md lists for `Ty.schema`/`ofSchema` is only a retraction.**
   The retraction is proved. Exactness is unproved (`docs/core/coherence-principle.md:179`,
   "exactness absent") and false at `number`: `ofSchema` reads only check ids (`checkId`,
   `Bridge.lean:62-65`), so `integer ≥ 5` reads back as `nat` and reprints as `integer ≥ 0`
   (tested, Fact 1).
5. **Decision 12 ("every boundary value carries an Effect Schema", 2026-09-10) exists as
   functions nothing on the reply path calls.** S-1 (`Ty.schema`), S-2 (the documents) and
   S-3 (the codec) exist; no Schema import appears under `Api/` or in `Program/Admission.lean`
   (tested, grep). The S-5 host gate is not started (decisions row 5: "every recorded corpus
   exit decodes under its published `Schema.Exit`").

So native schema support today is rc.112's Schema AST as first-order data with a printer, a
lowering of program types into it, and a type-directed JSON codec with retraction laws. It is
not yet a typing of data and not yet a boundary check.

---

## 2. Where data crosses

### 2.1 Host rows and replies

- **What a host row may declare** (reading, `Program/Admission.lean:8-24`, `:143-171`).
  Admission passes a table whose types contain no `int` anywhere (`findInt`, `:33-44`). The
  answer and error columns may contain no internal handle kind (`internalHandleScan`,
  `:58-78`; the targets `Ref`/`Deferred`/`Scope`/`Context`, `Program/Typed.lean:12-13`;
  `fiberOf`/`refOf`/`deferredOf`; row 97 interim). Every row must be external and async
  (`checkTable`, `Program/Native.lean:345-352`), and the table must be lawful. Any other `Ty`
  is admitted as a column.
- **What a host may answer.** The reply check is `externalValue`
  (`Program/Compile.lean:1354-1365`). At a handle-typed row, a `nat` is an allocation request.
  Otherwise the value must pass `Val.hasTy` and carry no handle; the handle-free check landed
  in `90df5d21` (E4-HOST-CE-007). Failures must fit the row's error column through the `Err`
  image (`errAdmits`).
- **The JSON → `Val` step is not in the library.** `Api/HostSession.lean:3-9` says "This module
  owns no JSON decoder". The harness does the decoding:
  - `jsonToVal` (`harness/truth/Truth.lean:749-764`) is a `partial def` and untyped. It accepts
    `null`, booleans, strings, arrays and naturals, plus objects only of the forms
    `{"external"}`, `{"some"}` and `{"none"}`; any other object is "no value".
  - A failure crosses as `[tag, message]` → `Err.tagged` (`tapeAnswer`, `:770-782`).
  - **A JSON object reply has no decode route today** (reading).
- **The `Err` alphabet**: `boom | tag (nat) | tagged (tag message) | text`
  (`Machine/Alphabets.lean:34-40`).
  - `errOf` maps `nat ↦ tag`, `str ↦ text`, `list [str, str] ↦ tagged`, and everything else
    `↦ boom` (`Machine/Term.lean:27-31`). `valOfErr` (`:34-38`) is its inverse off `boom`.
  - Admitted error types are `never | nat | string | lit | prod(tag, tag) | union` of those
    (`rawSupportedErrTy`, `Program/Eff.lean:56-62`).
  - **DI-62's `Err.value` refusal lives in text, not code**: `docs/DESIGN-BASIS.md:655-656` and
    the DI-62 row. In code it shows up as the absence of a constructor. Its stated reason is
    "a handle inside a cause would extend the minted-handle invariant into causes". The
    handle-free check `90df5d21` added for replies answers exactly that reason for a
    handle-free payload (reading; the owner would have to rule it).

### 2.2 JSON: three images of a value, none with an object layout for program data

1. **The truth wire** (`harness/truth/Truth.lean:407-438`, `:749-764`): untyped, partial, in
   the harness. It is the route host replies actually take.
2. **The Schema codec** (`Schema/Codec.lean`): type-directed, with laws, on rc.112's
   `toCodecJson` profile.
   - Its only consumers are `harness/truth/schema-codec/Emit.lean` and the `ProgramImage`
     wrappers (tested, grep).
   - Its layout has no object for program data: a pair is an array, and an object at a pair
     type refuses (tested, Fact 3).
   - Its read is exact only modulo object field order: it accepts `{"value":1,"_tag":"Some"}`
     and writes `_tag` first (tested, Fact 6). No normaliser is named.
3. **The CAS printer** `Store.printIn : Shape → Val → Json` and the `Json`-as-value
   `Canonical` instance (`Store/Domain/Derived/Json.lean`). These are shape-directed,
   positional for structs, and on the storage side (reading).

### 2.3 TypeScript

- **Types print through `Codegen.Types.ofTy`** (`Codegen/Types.lean:268-305`, a private
  20-arm match) into the vendored `TypeScript.TypeRef`.
  - `TypeRef` already has `object (fields : List (String × Bool × TypeRef))`
    (`.lake/packages/typescript/TypeScript/TypeRef.lean:17-18`), rendered as
    `{ readonly a: A; … }` (`TypeScript/Render.lean:62-64`). A record type therefore prints
    with one `ofNormalized` arm (reading).
  - `nat` and `int` both print as `number` (`Types.lean:273`; `Ty.renderRaw`, `Ty.lean:99`).
  - `parseLegacy` refuses object types (`Types.lean:20-21`).
  - The reader matches a service's declared type by comparing `ofTy ty` with the parsed
    `TypeRef` (`Codegen/Read.lean:356`). A record row type then needs the source ingest to
    produce `TypeRef.object` (reading; not traced further).
- **Values**: the vendored TypeScript `Expr` has `object` literals and `member` access
  (`TypeScript/Syntax.lean:46`, `:70`). The program has no term to print them from: records
  need either atoms in the `pair`/`fst`/`snd` pattern (`Machine/Term.lean:217-222`,
  `:374-376`) or a `Term` form (reading).

### 2.4 OCaml

- **`Ty` reaches the LCNF-generated engine.** `ocaml/gen/api_gen.ml:614-633` declares
  `type ty`, and `:8849-9902` lowers `Ty.members`, `factors`, `productMembers`, `ctorIdx`, the
  derived `decEq`, `sub`, `key`, `normalizeRow`, `normalize`, `Val.hasTy`, `externalValue`,
  `errAdmits` and `externalAdmits`. `ocaml/engine/api_engine.ml` holds the same 55 references.
  A new constructor re-cuts both through `make gen-lcnf`, which `check-gen` diffs but does not
  re-cut (`docs/GENERATED.md`, lcnf row) (tested, grep; reading).
- **Nested lists and products already lower**: `Val_list of val_ list`,
  `Val_ctor of int * val_ list` (`api_gen.ml:121-133`). `(string * ty) list` is a supported
  `Shape` (reading).
- **Risk, assumed and not run**: the probe's width-subtyping `sub` arm uses `List.attach`.
  Whether LCNF's translator lowers it, or refuses it as an extern without a table row
  (`docs/core/lcnf-route.md` §2), is untested. The exact-record design needs no `attach`.
- **Hand-written OCaml mirrors** need edits: `ocaml/engine/e4_program.ml:119-153` (`of_ty` and
  `assert (List.length Eff_types.ctor_names_ty = 20)`) and `ocaml/eff/test/prop_wire.ml:155+`
  (`rand_ty`) (reading).

---

## 3. The bill, measured

### 3.1 Counts (tested unless marked)

| Alphabet | Matches reading it (`Effect4.*`, definitions) | With no catch-all (refuse an append) | Instrument |
| --- | --- | --- | --- |
| `Ty` | **65** (63 at `7cae243a`) | **27** (was 25) | `#exhaustive_gate` (`TyBillProbe.log`) |
| `Ty`, private definitions | 1 | 1: `Codegen.Types.ofNormalized`, the TS type printer | probe sweep (`TyBillPrivateProbe.log`); the gate drops `Name.isInternal` (`Laws/Auto/Traversals.lean:155`) |
| `Ty`, outside `Effect4` | 8 | 6: `OCaml5.Eff.tyO`, `tyV`; `Tools.ProfileJson.tyJson`; `Conform.Effect4.LcnfMl.tyOcaml`, `tyT`; `LcnfSemantics.tyValue` | `#exhaustive_gate … under OCaml5\|Tools\|Conform` (`TyBillOutsideProbe.log`) |
| `Ty`, `Test/` | 3 | 1, the deliberate fixture `ExhaustiveFixture.catchAllAbsent` | reading (stale oleans) |
| `Ty`, proofs | **147** authored theorems eliminate a `Ty` directly, **32** by induction | — | `#ty_theorem_census2` (`TyBillPrivateProbe.log`) |
| `Err` (structured error payload) | 6 | 6: `Err.image`, `instReprErr.repr`, `Defect.ofError`, `valOfErr`, `Codec.encodeErr`, `RunnerGen.ErrC.toVal` | `AlphabetBillProbe.log` |
| `Lit` (a signed literal) | 7 | 7: `Lit.toVal`, `instReprLit.repr`, `Lit.ty`, `litVal`, `litArgTy`, `printLit`, `LitC.toVal` | same |
| `NativeAtom` (integer or record atoms) | 3 | 3: `row`, `eval`, `spec` (plus the generated inventory and prelude) | same |
| `Store.Val` (a new frame, e.g. signed) | 241 | 16 (`encode`, `payload`, `tag`, `WF`, `wf`, `render`, `printIn`, `cata_val`, `foldMap_val`, `ValC.toValVal` and their `.hom`s) | same |

Notes on the counts:

- The `Ty` delta since `7cae243a` is exactly row 96's landing: `HandlesFit` (with a catch-all)
  left, and `Fits`, `Fits.hom` (no catch-all) and `FlatFits` (catch-all) arrived (tested,
  diff of the two logs).
- The 147 are the theorems re-elaborated with one more case, not the set that fails. §4.2
  measures how many of `Ty.lean`'s own theorems keep their text.
- Two proofs name `sub`'s arms by number: `fits_sub` (`Membership.lean:838`, `case1`…`case16`)
  and `cata_admits_sub` (`Laws/Program/Admits.lean:38`). Three more split by
  `fun_cases Ty.sub`/`Ty.sameHead`: `TyView.lean:160,278,294`, `TypeAlgebra.lean:904`. A new
  `sub` arm renumbers them; the probe shows the record arm as `case16` and the catch-all moved
  to `case17` (tested).

### 3.2 By module and kind

| Where | Kind | What a `record` costs |
| --- | --- | --- |
| `Program/Ty.lean` | hand arms | `renderRaw`, `members`, `key`, `isMember`, `isNever`, `closed`, `instantiate`, `sub`, `normalize`, `Normal`, plus a companion over the field list for every recursive one. A hand `DecidableEq` (C only) and a hand `Repr` (both B and C); a registered eliminator |
| `Program/Ty.lean` | catch-all classifiers to review | `isFactor` (a record is a factor), `factors`, `infer`, `isTagged`, `payloadOf`, `taggedColumn` (a tagged record is a new member shape for the tag decision) |
| `Program/Typed.lean` (`Val.hasTy`), `Laws/Program/Typed/Membership.lean` (`Fits`, `Fits.hom`) | hand arm and proofs | one clause each; `fits_hasTy`, `fits_live`, `fits_map`: one arm each; `fits_sub`: one numbered case (§4.4 decides its shape) |
| `Program/Admission.lean` | hand arm | `findInt` (no catch-all); `internalHandleScan` is a `TyAlgebra`, so it gets a generated field |
| `Program/Eff.lean` | hand arm | `rawSupportedErrTy` (no catch-all): whether a record may be an error payload is DB-15/DI-62's ruling |
| `Schema/Bridge.lean`, `Schema/Codec.lean` | hand arms | `schema` (no catch-all) → `Schema.struct`; `ofSchema` gains an `objects` read (and exactness, §6); `layout`, `encodeRaw`, `decodeRaw` (catch-alls) and `isSupported` (explicit `false`): an object layout |
| `Codegen/Types.lean` | hand arm (private) | `ofNormalized` → `TypeRef.object` |
| `Laws/Program/Template.lean`, `TyView.lean` (generated), `TypeAlgebra.lean`, `Typed.lean` | proofs | per the census; under width subtyping TyView's `sub_eq_args` needs a rule exception (§4.4) |
| `Program/Fold.lean` | generated (group Fold) | a `TyAlgebra` field. The generator supports `List (Prod String Ty)` (`tools/Effect4Gen/Fold.lean:208-245`), but "a block with a composite position emits no monadic half and no `foldMapAt`" (manifest, SchemaFold note). `foldM_ty`, `foldMap_ty` and `foldMapAt_ty` have no consumer (tested, grep), so the loss is on paper only |
| `Store/Domain/Derived/Program.lean` | generated (group Program) | `TyC.toValTy` and its laws: the stored form of a `Ty` |
| `Laws/Program/TyView.lean` | generated (group TyView, from `variances.json`) | `args`, `sameHead` and the law shape |
| `tools/Effect4Gen/wire-tags.json` | stage-0 table | append `record: 20` (C); with B, also a new family `Fields` |
| `ocaml/eff/*` (group eff), `ocaml/gen/*` + `api_engine.ml` (group lcnf), `ts/eff/{eff,json,wire}.gen.ts` (group ts) | generated | 16 generated artefacts mention the `Ty` alphabet, plus the stage-0 tag table (tested, grep for `deferredOf`: `Program/Fold.lean`, `Derived/Program.lean`, `TyView.lean`, `eff_types/wire/json/layout.ml`, `eff_manifest.txt`, `program-structure.json`, `e4_program_layout.ml`, `api_gen.ml`, `api_engine.ml`, `eff/json/wire.gen.ts`, `variances.json`) |
| `ocaml/engine/e4_program.ml`, `ocaml/eff/test/prop_wire.ml` | hand mirrors | `of_ty` and the `= 20` count; `rand_ty` |
| `tools/Conform/Effect4/mirrors.json` | mirror census | 17 artefacts restate `Ty`'s alphabet, two of them frozen baseline files with 16 constructors (`Test/fixtures/baseline/66ee4657/families.json`) |
| DI-47's gate | none runs | §5 |

---

## 4. The feasibility probe (finite and proved)

### 4.1 Lean 4.33.1's instruments on the two shapes (tested)

The tests are `explore/E1Instruments.lean` (exit 1 by design: the refusals are the
measurement) and `explore/E2Eliminator.lean` (exit 0).

| Instrument | A: today | B: mutual `Ty`/`Fields` spine | C: nested `record (fields : List (String × Ty))` |
| --- | --- | --- | --- |
| `deriving DecidableEq` | works | **works**, also at full size (`RecordSpine.lean`) | **refused**: "None of the deriving handlers for class `DecidableEq` applied to `Ty`" |
| `deriving Repr` | works | **`partial`**: four `opaque` members | **`partial`**: `instReprTy.repr` is `opaque` |
| `induction t` | works | **refused**: "…because it is mutually inductive" | **refused**: "…because it is a nested inductive type" |
| structural recursion that reduces by `rfl` | works | one `Fields` companion | one `List (String × Ty)` companion; **no `Prod` companion** |
| a hand eliminator with `@[induction_eliminator]` | — | **gives back `induction t with \| record fields ih`** (proved) | **gives back `induction t with \| record fields ih`** (proved) |

The last row overturns the cost model of the type algebra note (2026-09-18 §0, §1.2). That note
priced each `Ty` induction at "two theorems" for B and "a mutual block, one theorem per
container position" for C, both marked assumed. With one registered eliminator, about 30 lines
in the shape of `Store.Val.ind`, existing `induction ty with` scripts keep their text.

### 4.2 Option C in full: `RecordNested.lean` (exit 0)

`RecordNested.lean` copies `Ty.lean`'s inductive and everything normalization and its laws
need, in namespace `DataProbe.Nested` (1,287 lines with the additions), and appends
`record (fields : List (String × Ty))`. Probe choices, not recommendations:

- Fields are canonical when strictly ascending by the name's UTF-8 key, the rule `Ty.key`
  already uses for strings.
- `normalize` keeps the first field of a repeated name.
- `sub` is TypeScript's width-and-depth rule.

Axioms printed in the log (proved):

- `beq_iff`, `key_injective`, `named_width_sound`, `width_admits_unnamed_handle`,
  `fitsFields_exact_mono`: `[propext]`.
- `Ty.ind`: none.
- `normal_normalize`, `Normal.fixed`, `normalize_idem`, `sub_unknown`, `fitsV_iff_hasTyV`,
  `user_normalize`, `ada_fits`, `swapped_not_fits`, `square_fits`, `positional_width_unsound`,
  `fitsN_sub`: `[propext, Quot.sound]`.

The `#guard`s on `sub`, on width and depth, and on the canonical union of two tagged records
ran (tested).

What the record cost, against the copied text:

- **26 of the 29 copied theorems kept their text unchanged** (tested: a block-by-block text
  comparison against `Ty.lean`; the six not copied are `le_iff`, `matchTemplateArgs_length`,
  `sub_union_right`, `sub_union_left`, `sub_lit_string`, `render_toRaw`). They include `members_isMember`,
  `Normal.members` and `sub_unknown`, which the eliminator's record case and their existing
  wildcards absorb.
- Three gained one arm or case each: `key_injective` (+2 lines), `normal_normalize` (+4) and
  `Normal.fixed` (+2).
- New code, about 270 lines:

  | Part | Lines |
  | --- | --- |
  | hand `DecidableEq` (`beq`, `beqFields`, two iff theorems, the instance) | 32 |
  | the eliminator | 31 |
  | three companions (`renderFields`, `keyFields`, `normalizeFields`) | 17 |
  | arms | about 15 |
  | `lookupField` and `sizeOf_field_lt` (for `sub`'s termination) | 12 |
  | `FieldsAscending` and `insertField` | 10 |
  | 12 lemmas: the field insertion's laws, `keyFields_injective`, `normalizeFields_fixed` and the `ltKey` order facts | about 140 |
  | edits to existing proofs | 8 |

- The value judgment's record arm and companion (`FitsV`/`FitsFields`) and the executable check
  (`hasTyV`/`hasTyFields`) are 10 lines each. The connecting lemma `fitsV_iff_hasTyV` is the
  host-boundary §4.4 pattern: "one executable check and its proof-side mirror … joined by a
  connecting lemma". It is proved by the eliminator, with a 20-line record arm.

### 4.3 Option B, the spine: `RecordSpine.lean` (exit 0)

- Derived `DecidableEq` works on the full block, which saves C's 32 lines.
- `Repr` is still `partial`.
- The eliminator is the same size, and `key_injective` keeps its text plus one bullet
  `[propext]` (proved).
- **Every spine function used by a law needs a list twin and a bridge**: `insertField` on
  `Fields`, `insertFieldL` on the view, and `toList_insertField`, plus the `toList`/`ofList`
  round trips. List lemmas from core (`Pairwise`, membership, `attach`) do not apply to
  `Fields` directly.
- B also adds a second family to every generated table: a `Fields` wire family, a two-member
  `TyFam`, `and fields = …` in OCaml, and a second member in the exhaustive gate's family.
- So B trades a 32-line hand equality for a view-and-bridge layer plus a second core family
  (measured on the pieces above; a full B port was not run).

### 4.4 The decisive finding: the record's value encoding (proved)

- **`positional_width_unsound`.** Take a = `{ id: number; name: string }` and
  b = `{ id: number }`. Then `sub a b = true`, the value `ctor 0 [7, "Ada"]` fits a, and it does
  not fit b. **Under the tree's structure rule plus TypeScript's width rule, `fits_sub` is
  false.**
- **`fitsN_sub`.** With a name-carrying encoding (entries `pair (str name) value`; extra entries
  allowed, as a JavaScript object has them), membership is closed under `sub` again. It is
  proved by `fun_induction Ty.sub` exactly as `Membership.lean:837` proves it; the record case
  is about 20 lines. The IH Lean generates is
  `∀ n t, (n, t) ∈ gs → ∀ s, (n, s) ∈ fs → s.sub t = true → …`
  (`explore/E3Case16Trace.log`, an exploration that fails by design after printing the state).
- **`width_admits_unnamed_handle`.** Under the width encoding, an unnamed entry is
  unconstrained, so a value fitting `{ id }` can carry a handle no declaration covers.
  `fits_live` (`Membership.lean:520`), which `fits_sub` uses at `unknown`, then needs the
  record arm to constrain unnamed entries too: live, or handle-free as host replies already are.
- **`fitsFields_exact_mono`.** With exact records (same names in the same canonical order,
  each field below), the positional rule keeps `fits_sub`'s record case as a short lemma over
  the fields.
- **TyView** (reading, `Laws/Program/TyView.lean:291-341`). `sub_eq_args` says `sub` between
  members is "the variance-wise comparison of corresponding arguments" under `sameHead`
  ("same constructor and equal non-recursive payload"). Exact records fit that law with the
  names as payload. Width records do not: `sub` answers true at different name sets, so the
  generated view needs a width rule beside `litRule`/`topRule`.

### 4.5 Which tree declarations need an arm (reading)

- **Refused until given an arm**: the 28 + 6 definitions in §3.1, by name in the logs.
- **Proofs with induction that gain one arm**: the 32 listed in `TyBillPrivateProbe.log`
  (for example `key_injective`, `normal_normalize`, `ofSchema_schema`, `fits_hasTy`,
  `fits_live`, `fits_map`, `hasTy_normalize`, `cata_admits_instantiate`, the `Template`
  closedness lemmas, `hom_eq_cata_ty`, `TyC.fitsTy`). They keep their text once the
  eliminator is registered (§4.2 measured 26/29 in `Ty.lean`).
- **Proofs that name `sub`'s arms**: the 2 by number and 3 by `fun_cases` in §3.1's notes.
- **Classifiers with catch-alls** to review so a record does not default into a positive
  class (the type algebra note's §7.3 lesson): `isFactor`, `Codec.layout`, `infer`,
  `taggedColumn`, `isTagTy`, `projectProduct`, `Decision.arms`, `fiberTy`, `exitOf?`,
  `listOf?`, `externalValue`.

---

## 5. What the tree already decided in code (refusals, with their lines)

- `Ty` has no record. Its carrier rule prices a `List Ty` field and requires appends only
  (`Ty.lean:11-23`, `:37-75`).
- **DB-15** (`docs/DESIGN-BASIS.md:664-666`): "A `json` leaf in `Ty`… A record type in `Ty`:
  columns are pairs. `.int` stays uninhabited". `Err.value` is refused (`:655-656`).
- **`int`** is refused at admission, anywhere in a table, the program tree or its type
  (`Admission.lean:33-44`, `:143-171`, refusal `uninhabited` at a path, `:123`; DI-67).
  It is uninhabited in the judgments (`Membership.lean:91`, `Program/Typed.lean:96`) and
  unsupported by the codec (`Codec.lean:51-55`). It still has a schema and reads back (tested,
  Fact 4). There is no signed literal (`Machine/Term.lean:87-92`) and no signed frame
  (`Val.lean:150-167`). Subtraction truncates in both the model and the prelude
  (`Machine/Term.lean:402`, `:283-285`).
- **Numbers** (row 108, open, recommended): DI-56's bounded profile with refusal outside it,
  intermediate values included. The integer question is DB-15's and DI-67's, not row 108's.
- **Errors**: the `Err` alphabet (`Machine/Alphabets.lean:34-40`), `errOf`'s collapse to `boom`
  (`Machine/Term.lean:27-31`), and the admitted introductions (`Program/Eff.lean:56-62`,
  `Typing/Rules.lean:147-153`).
- **Host replies** must be handle-free and fit `Val.hasTy` (`Compile.lean:1354-1365`). Answer
  and error columns refuse internal handles (`Admission.lean:58-93`). Service carriers are
  flat (`Membership.lean:61-71`; row 114 ruled; row 118 open).
- **Schema**: `ofSchema` refuses objects and everything `schema` does not write
  (`Bridge.lean:79-135`). Row 39 (ruled 2026-09-18, **not executed**) deletes `Check`,
  `Accepts`, `Image`, `EffectfulField` and `Api.schemaOf`, cuts `Annotations` to its carrier
  and two keys, and moves `Store.render`. Row 2 (open): "(c) now, (b) before the first foreign
  consumer". Row 5 (open, not started): D12's shape and the S-5 gate.
- **DI-47's compatibility gate does not run.** Commit `243ca0dd` (2026-09-19, the owner's
  testing ruling) deleted the compatibility lane. The baseline README still cites
  `scripts/check-compatibility.py`, which no longer exists. The policy file names `Ty.lit` as an
  addition but not `refOf`, `deferredOf`, `var` or `unknown`. `docs/core/system-map.md` §1.1
  still calls DI-47's relation "a finite gate" (tested, git log and ls; reading).

---

## 6. Open, for the owner (recommendation beside each)

1. **The record value encoding and subtyping**, one decision with DB-15's amendment and row 2:
   - exact records, positional values: every law shape kept; TypeScript accepts more than
     Lean, which row 68's assignability lane would classify as incomplete;
   - width records, name-carrying values with unnamed entries constrained: TypeScript-faithful;
     `fits_live`, TyView and the codec layout each gain a rule.

   *Recommendation: exact records first, written so width can be added later. Every proof
   shape the tree has today survives (§4.2, §4.4).*
2. **C or B.**
   *Recommendation: C, `List (String × Ty)`, with a registered eliminator.* The measured gap is
   a 32-line hand equality against B's view and bridge layer plus a second core family in
   every generated table (§4.3). The type algebra note's reason for B rested on an assumed
   proof fan-out that the eliminator removes.
3. **Duplicate field names**.
   *Recommendation: a located refusal at formation, so `normalize` never meets one.* The probe
   keeps the first occurrence, which is a choice, not a ruling.
4. **Variants**: a union of records with a literal `_tag` field normalizes and fits (tested,
   `square_fits`, `#guard`s), so no `variant` constructor is needed. The tag decision
   (`taggedColumn`, `payloadOf`, `diffTag`, `tagHit`) must learn the record discriminant.
5. **Structured error payloads**: admit a handle-free payload. This answers DI-62's stated
   reason. The cost is the `Err` bill (6 definitions plus engine and wire) and `errOf`.
6. **`int`**: a signed value needs either a new frame (the `Val` bill: 16 definitions plus the
   CAS tag byte and every codec) or `Int`'s generated `ctor 0/1 [nat]`. The `ctor` route
   collides with `Result`'s encoding in unions, because encodings are type-directed (reading).
   *Recommendation: decide after row 108's numeric profile.*
7. **JSON decode route**: a typed `Json → Val` at the reply path. Two pieces exist —
   `Schema.decode` with `hasTy_decode` (proved), and an object layout once records exist. What
   is missing is the call on the reply path and the S-5 gate (row 5).
8. **`ofSchema`'s exactness**: compare check payloads, not just ids, or say what the read is
   exact modulo. AGENTS.md lists it as an exact embedding (§1.5).
9. **The mirror and baseline discipline**: either restore an executable DI-47 comparison for
   core appends or amend system-map §1.1 and the baseline README to say none runs (§5).

---

## 7. Receipt

Commands, each through `bash …/scratchpad/serial.sh lake env lean -M6144
-DwarningAsError=true <absolute path>`, from the repository root:

| Probe | SHA-256 | Exit | Log |
| --- | --- | --- | --- |
| `TyBillProbe.lean` | `41586cd7…` | 0 | `TyBillProbe.log` (65/27, theorem census) |
| `TyBillOutsideProbe.lean` | `5b41dbdb…` | 0 | `TyBillOutsideProbe.log` (OCaml5 2/2, Tools 3/1, Conform 3/3) |
| `TyBillPrivateProbe.lean` | `13c63169…` | 0 | `TyBillPrivateProbe.log` (private 1; 147/32) |
| `AlphabetBillProbe.lean` | `bead9072…` | 0 | `AlphabetBillProbe.log` (`Err` 6/6, `Lit` 7/7, `NativeAtom` 3/3, `Val` 241/16) |
| `SchemaProbe.lean` | `1af0dfb3…` | 0 | `SchemaProbe.log` (16 axiom lines, six facts as `#guard`s) |
| `RecordNested.lean` | `dd6b8ca0…` | 0 | `RecordNested.log` (axioms of 17 theorems) |
| `RecordSpine.lean` | `b649d3ba…` | 0 | `RecordSpine.log` (four `opaque` `Repr` members; axioms) |
| `explore/E1Instruments.lean` | `429ff89b…` | 1 by design | the refusals are the measurement |
| `explore/E2Eliminator.lean` | `df88d6cf…` | 0 | eliminator on both shapes |
| `explore/E3Case16Trace.lean` | `1383181e…` | 1 by design | prints the record case's IH; superseded by `RecordNested.lean` |

Every probe that exits 0 stays at or below `[propext, Quot.sound]`, with no `sorryAx`; the two
explorations that exit 1 by design carry no claim beyond the messages and the printed state
quoted above.

- No tracked file was edited. No `lake build`, `make`, generator, `git add` or `git commit` was
  run. `/Users/pooks/Dev/lean4-effect4-slice6` was not touched.
- **Bounded or host-only**: everything here is Lean-side. The C and B probes are copies, not
  the tree edit. The `#guard`s are finite. The OCaml lowering of the width `sub` arm is
  assumed, not run.
- Notes read and superseded in part: the type algebra note (2026-09-18) §0–§1, whose cost
  model is corrected by §4.1–§4.2; the model probe synthesis R3 (2026-09-30), whose 63/25 is
  now 65/27 + 1 private; post-Phase C §11.2 W1/W9; decisions rows 1–6, 9, 12, 39, 41, 61, 68,
  108, 111–118.
