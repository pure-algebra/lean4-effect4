# Verifier of seat TREE, data probe (2026-10-01)

**The one thing.** Every seat probe reruns identically, but the bill undercounts and the
recommendation does not hold.

- **"Exact records first, every law shape survives" is false on the seat's own model.** Its
  positional record arm reads fields in written order, while `normalize` sorts them and drops
  repeated names. So the shape of `hasTy_normalize` fails (proved). That law is at
  `Laws/Program/TypeAlgebra.lean:309`, and seven other `Laws` modules use it.
- **The exact-versus-width choice leaves out the design rc.112 itself uses.** An rc.112 struct
  decode drops the keys its type does not name (`SchemaAST.ts:445`). That design keeps
  positional exact values and treats width as a projection. Its law, `fits_coerce`, is proved
  on a small model. The owner's 2026-09-10 boundary rule favours it, but that rule is written
  only in a research note.
- **The seat's C changes a tracked line.** Requirement R3 (`system-map.md` §8) already names the
  `Ty`/`Fields` spine, which is option B.
- **"Native schema support" is not decided.** Decisions rows 1, 2, 5, 10 and 11 are open, and
  row 39 is ruled but not carried out.

Base: `refactor/phase1-phase3` at `ba9783c3`, which touches documents only on top of `bc77e97f`.
Oleans: `Effect4` 01:04 and `Effect4.Laws` 01:15. The `Test` oleans were built 01:15–01:22 by
the landing build (`landing-C-build.log`, 103 "Built Test" lines). The seat said the `Test`
oleans predate `90df5d21`; they do not, so `Test` can be measured, and §1 (D01) does so. Every Lean
run went through the one-compiler lock with `-M6144 -DwarningAsError=true`.

Evidence words: **proved** means a kernel theorem run here, with axioms printed at
`[propext, Quot.sound]` or fewer. **Reproduced** means the seat's probe was rerun and its log
matched, the seat's appended `time` line aside. **Tested** means a finite check or an
instrument's printout run here, or a grep. **Reading** means read in code or notes, not run.
**Assumed** means not checked.

---

## 1. Verdicts

| id | verdict | evidence |
| --- | --- | --- |
| TREE-D01 | partly | **Reproduced:** `Effect4` 65/27 and outside 8/6 (`verify-rerun-TyBillProbe.log`, `verify-rerun-TyBillOutsideProbe.log`); a grep for `Ty` arms in `tools/`, `src/OCaml5/` and `harness/` finds no other file. **Refuted for `Test/`:** the gate runs and gives 5 matches, 2 with no catch-all: `ExhaustiveFixture.catchAllAbsent` and `ValueMembership.ExactSpelling.FitsInv` (20 arms), not one fixture (tested, `verify-TyBillCensus.log`). The stale-oleans premise is wrong. Of the 27, 11 are made by a tool: 5 `fold_of` `.hom`s, 4 in the Fold group, `TyC.toValTy` and `Ty.args`. `instReprTy.repr` is derived, so the hand bill is 15 definitions plus `ofNormalized` (reading, `Laws/Program/Folds/Ty.lean:23-38`) |
| TREE-D02 | confirmed | Rerun reproduced. `Traversals.lean:155` drops `isInternal` names, and `bodiesUnder` attributes helpers only to non-internal owners (`Exhaustive.lean:167-185`) (reading). Tested: the same sweep over `Err`, `Lit`, `NativeAtom` and `Store.Val` finds no other authored private definition, only generated splitters (`verify-TyBillCensus.log`). The cited range `Types.lean:268-299` stops early; the match runs to `:314` |
| TREE-D03 | partly | 147/32 reproduced, but census2 reads only a theorem's top-level term. It misses every proof whose case list comes from `fun_induction`/`fun_cases`, or whose eliminator sits in a well-founded auxiliary. With auxiliaries attributed and principle users added there are **183**, not 147 (tested, `verify-TyProofCensus.log`). The proofs split by `sub`'s, `sameHead`'s, `cata_ty`'s or `infer`'s own principle are **8**, not the 6 that D03 names (2 by case number, 4 by `fun_cases`) nor the 5 of the note's §4.5: `fits_sub`, `cata_admits_sub`, `cata_admits_extend` (`Admits.lean:196`), `sub_eq_false_of_not_sameHead`, `sub_eq_argsBelow_of_sameHead`, `sameHead_trans`, `sub_normalize_of_sub` and `infer_widens`. The prefix rule `"eq_"` also drops the authored `Ty.eq_of_sameHead`. The case16/case17 renumbering is reproduced (`fitsN_sub`) |
| TREE-D04 | confirmed | `E1Instruments` (exit 1 by design), `E2Eliminator` and `RecordSpine` reproduced: the same refusal messages, 4+1 opaque `Repr` members, the eliminators at `[propext, Quot.sound]`. Toolchain `v4.33.1` (`lean-toolchain`) |
| TREE-D05 | partly | My block comparison reproduces 26 of 29 kept, 3 changed (+2, +4, +2) (tested). `Ty.lean` has 36 theorems; 7 were not copied, and the seat's list of six omits `CTy.key_injective`. **But the sample is weak.** Of the 29, only 4 induct on `Ty` (`key_injective`, `members_isMember`, `normal_normalize`, `sub_unknown`), and 4 more do `cases` on it; the rest are key-order and list lemmas. The hard proofs were not copied: `sub_trans_core`, `sub_antisymm_normal`, `sub_normalize_of_sub` and `hasTy_normalize`. Two of the three changed proofs (`key_injective`, `Normal.fixed`) contain `try`, which AGENTS.md bars in a touched proof, so they would not land with their text. The type algebra note's cost model was marked assumed (its §0); the one-arm-per-induction correction stands |
| TREE-D06 | partly | Exit 0 and the axioms of 17 theorems reproduced. The size reproduces: 272 non-comment lines of the probe's `Ty` part are not in `Ty.lean` (tested, a line-multiset diff). Not shown: (1) the probe's `sub` is the **width** rule, while the recommendation is exact; no exact arm was written. (2) The ~270 lines leave out the subtyping algebra, which goes through `TyView.sub_eq_args` (`TypeAlgebra.lean:40-121, 618, 883`), and `hasTy_normalize`, which fails for the probe's encoding (D08). They also leave out the TyView generator, which refuses a composite field: `View.lean:162-168` throws "which `sameHead` does not know how to compare" (reading). (3) The probe's proofs use unqualified `simp`, `simp_all` and `try`, which AGENTS.md bars in new proofs under `src/`; the line counts are probe-grade |
| TREE-D07 | confirmed | `RecordSpine` reproduced: derived `DecidableEq` at 21+2 constructors, 4 opaque `Repr` members. Generated tables: reading. Add: the TyView generator refuses a `Fields` field too (`n == root` fails, `View.lean:157-166`), so B and C both need it extended. And the tracked R3 line names the spine (B); see "missed" |
| TREE-D08 | partly | `positional_width_unsound` and `fitsN_sub` reproduced. **"Exact records: every law shape survives" is refuted on the seat's own model:** `FitsV`'s record arm reads arguments in written order, while `normalize` sorts and deduplicates. `hasTyV_normalize_fails`, `positional_not_normalize_invariant` and `positional_dup_not_invariant` are proved at `[propext, Quot.sound]` (`verify-RecordRed.log`). That is the shape of `hasTy_normalize`. The probe's header intends "canonical field order" (`RecordNested.lean:22`), but its arm reads written order. Honouring that intent makes the arm read through a sort, so it is no longer structural, or else formation must refuse non-canonical field lists. Either way it is a ruling, and the seat did not price it. **A third design is missing:** positional exact values with width as a projection at subsumption and decode. This is rc.112's default, `onExcessProperty: "ignore"` strips unknown keys (`SchemaAST.ts:445`, applied `:2250-2290`) (reading). Its law `fits_coerce` is proved on a small model at `[propext]` (`verify-CoerciveWidth.log`). "The tree's structure rule" is the generated image of a *Lean* structure, in declaration order (`Machine/Value.lean:31-37`, `Shape.lean:71`), not a ruling on program record values; reading. The width bill also leaves out the subtyping algebra; `fits_live`'s break is reading-level |
| TREE-D09 | confirmed | Reading of tracked text: DB-15 "Status: adopted 2026-09-08", refusals at `DESIGN-BASIS.md:655-666`; row 2 open (`decisions.md:23`). The tracked R3 line (`system-map.md` §8) belongs beside them: it names "the `Ty`/`Fields` spine" |
| TREE-D10 | confirmed | Row 39 status: "ruled 2026-09-18 … nothing deleted yet" (reading, `decisions.md:85`). The files exist (tested, `ls`). "About half" is tested by `wc`: about 3,700 of the 7,462 lines in `src/Effect4/Schema/` go (49%). Row 39 still names `Arch/Accepts.lean`; the file is `Schema/Accepts.lean` |
| TREE-D11 | partly | The four parts check out (`SchemaProbe` Facts 2 and 5 reproduced; reading). **Wrong:** "only Shape has records". `Representation` has `objects`, with property and index signatures, as the seat's own §1.5 table says (`Representation.lean:701-778`). **Breaks the owner's rule:** "five deliverables" is a capability list, not theorem shapes over the open signature. **Missing:** dictionary records (`Schema.Record`), recursive types (R3: "untracked"), and decisions rows 10 and 11 |
| TREE-D12 | confirmed | Fact 1 reproduced (`#guard`s pass); `checkId` reads ids only (`Bridge.lean:62-65, 79-87`); `coherence-principle.md:179` says "exactness absent"; row 6 itself defers exactness to row 41 (reading). A second slip, tested: `schema (.var i) = schema (.handle "effect/schema/TypeParameter")`, and `ofSchema` reads it back as that handle. The docstring at `Bridge.lean:56-57` says it does not read back |
| TREE-D13 | partly | Laws and axioms reproduced; Facts 3, 4 and 6 reproduced; the consumer grep reproduced (tested). **Overlooked:** the keyed session wire already has an object image for `Val.ctor`, `{"ctor":n,"args":[…]}` (`harness/truth/session/Keyed.lean:84-107`, reading). The codec **refuses** an extra field (tested), which rc.112's decoder **strips**. An object layout for records must choose between them, and stripping needs a second normaliser (drop unnamed keys) beside field order |
| TREE-D14 | partly | `HostSession.lean:7` and `Truth.lean:749-764, 770-782` are as cited (reading). But the versioned session reader decodes `{ctor,args}`, `{handle}`, `{some}` and `{none}` objects, untyped (`Keyed.lean:84-107`), so the note's §2.1 line "a JSON object reply has no decode route today" is wrong; "no *typed* route" stands. The recommendation puts the `Ty`-directed codec on the reply path. Row 10 (open) recommends the shape-directed `ShapeDoc.print` as the one `Val → Json`, and the seat never cites it |
| TREE-D15 | confirmed | Every cited line read: `findInt` (`Admission.lean:33-44`); `internalHandleScan` (`:58-78`, `fiberOf`/`refOf`/`deferredOf` refused outright); `checkTable` (`Native.lean:345-352`); `externalValue` (`Compile.lean:1354-1365`); the refusal `uninhabited` (`:121-123`) |
| TREE-D16 | partly | Reading confirmed; the `Err` bill of 6/6 reproduced, and no private `Err` definitions exist (tested). **Too strong:** the reply check of `90df5d21` covers payloads a *host* sends. A program's own `fail` can carry a value built in the program, so DI-62's stated reason needs a **type-level** condition at every introduction: a handle-free error type, with `unknown` excluded. The reply check is not that condition |
| TREE-D17 | confirmed | DI-67 (ruled, tracked) and DB-15 are read; `Val` 241/16 reproduced; only a generated splitter is private (tested). The collision inside unions is reading-level |
| TREE-D18 | partly | `git show 243ca0dd` deleted `scripts/check-compatibility.py`, `scripts/lib/compatibility.py`, `scripts/test-compatibility.py` and `tools/Compatibility/Extract.lean` (tested). The policy file and `system-map.md` §1.1 read as cited. **Wrong count:** both frozen baselines list **15** `Ty` constructors, not 16 (tested: `families.json` and the supplement's `snapshot.json`). **Overstated:** "a rule, not a gate, guards a `Ty` append". The tag table's loader still refuses a tag or a name given twice in a family, and an active name that is not declared (`tools/Tools/WireTags.lean:12-18`, reading), so the wire half of DI-47 is still executable. What is gone is the comparison against the frozen baseline. Two more stale lines: `wire-tags.json`'s comment still lists `scripts/lib/compatibility.py` as a reader, and `docs/GENERATED.md:89` says "the compatibility snapshot" holds constructor order |
| TREE-D19 | partly | The generated-artefact grep reproduces (tested). **Missed:** (a) the TyView generator does not regenerate a record; it refuses it (D06). (b) The LCNF case-site pin `tools/Conform/Effect4/cases-policy.json` has 36 `Ty` rows, 25 of them default-mode with explicit cover lists, and `unlisted: refuse`. That pin is the gate an append trips (`make check-cases`, AGENTS.md "Working") (tested: read with python). (c) Two more hand tables with one row per `Ty` constructor, which the gate cannot see because they are lists, not matches: `OCaml5/Eff/Metadata.lean:52-60` (`types`, one example each, feeding `ocaml/eff/goldens/coverage-metadata.txt`) and `tools/Tools/Variances.lean:~360-388` (the per-head variance source behind `variances.json`). A record head of variable arity does not fit the second table's shape (reading) |
| TREE-D20 | confirmed | `Membership.lean:61-77, 87-148` read; `fitsV_iff_hasTyV` reproduced at `[propext, Quot.sound]`. The recommendation for row 118 is a shape, not a capability list |
| TREE-D21 | confirmed | `TypeRef.lean:12-19`, `Render.lean:62-64`, `Syntax.lean:46, 70`, `Term.lean:100-106, 217-222` and `Types.lean:20-21` read as cited. Add: `eq` at a record must stay refused, because DI-35 widens `eq` only where `===` compares faithfully, and `===` on two objects compares references (`Term.lean:215-216` prelude) |
| TREE-D22 | partly | The function list is tested by grep: `program_ty_members` (`api_gen.ml:8851`) through `program_err_admits` (`:9895`); `type ty` is at `:614-634`. "55 Ty references" does not reproduce: 176 lines mention `Ty_` in each file, 205 mention `Ty` (tested). `List.attach` appears nowhere in `api_gen.ml` (tested), so the risk stays assumed, as the seat says |
| TREE-D23 | partly | `square_fits` reproduced. **Missed:** the probe's `normalize` does not distribute a union-typed field. `{_tag: "A" \| "B", x}` stays one member, while a product with the same union factor becomes two (tested, `#guard`s in `verify-RecordRed.lean`). The tag decision assumes "no union under a `prod` head" (`diffTag`, `Ty.lean:778-783`), and the 2026-09-10 rule T3 made distribution canonical (research note). So records must distribute discriminant fields, or the decision functions must split members |
| TREE-D24 | confirmed | Strengthened: a repeated name breaks normalization invariance in **both** encodings. `positional_dup_not_invariant` and `named_dup_not_invariant` are proved (`verify-RecordRed.log`), so the formation-time refusal is forced by `hasTy_normalize`, not a matter of taste |

---

## 2. What the seat missed

1. **The owner's boundary rule and rc.112's own struct decode.** The 2026-09-10 decisions say
   "never break host code because a type at a boundary was declared narrower … overload rather
   than refuse". They name four boundaries: B-tape admits a host value "at any subtype of the
   column", and B-accept says Lean accepts what rc.112 accepts or refuses by a named refusal
   (`docs/research/2026-09-10-boundary-decisions.md` §1). Exact records with an exact-field
   codec refuse a host object with extra keys, which rc.112 accepts by stripping them
   (`SchemaAST.ts:445`). The coherent exact design is therefore "exact positional values, width
   as a projection at decode and at subsumption, a named refusal at B-accept". Its law is
   `fits_coerce`, proved on a small model (`verify-CoerciveWidth.lean`). The rule is ratified in
   a research note and in memory; no tracked file carries it (tested: `git grep` for B-tape,
   B-accept and the rule's wording finds nothing under `docs/`, `AGENTS.md` or `README.md`). The
   coordinator should ask the owner whether it stands as a ruling. This design has a cost no one
   has measured. Projecting at subsumption *inside* a program means the checker inserts a
   coercion term, which changes the stored program. The cheaper variant projects at decode only
   and gives width inside a program a named refusal. That variant is assumed, not probed.
2. **Positional order against canonical order.** The generated rule the seat cites orders
   fields by **declaration** (`Shape.lean:71`, `Machine/Value.lean:31-33`). The seat's
   canonical record orders them by **name**. Its arm reads the **written** order. Three orders,
   and `hasTy_normalize` holds only if the value is read in canonical order (proved red
   controls, D08). That is a design ruling the owner must make with the encoding.
3. **The tracked R3 line names the spine.** `system-map.md` §8 R3 (tracked, 2026-10-01) says
   "the type language closed under records and variants through the `Ty`/`Fields` spine; each
   constructor brings its `Fits` clause, embeddings, folds, assignability and inhabitance".
   Recommending C amends a tracked line, not only the type algebra note. Of R3's own list, the
   seat leaves two items open:
   - **Inhabitance.** `record [("a", never)]` is canonical and uninhabited, and it is not
     `never`, against DI-67's invariant (`emptyRec_canonical`, `emptyRec_uninhabited`,
     proved). The same gap exists today: `normalize (prod never nat) = prod never nat` (tested,
     `#guard` in `verify-TyBillCensus.lean`). So inhabitance is an open obligation of R3, not
     one the record adds.
   - **Recursive types**, which R3 marks "untracked", are not addressed.
4. **The subtyping algebra and the view generator.** `sub_trans_core`, `sub_antisymm_normal`
   and `sub_normalize_of_sub` all go through `TyView.sub_eq_args`. `fits_sub`'s invariant arms
   use `sub_trans` (`Membership.lean:835-836`). The TyView generator refuses any field that is
   neither a `Ty` nor a `String`/`Nat` payload (`View.lean:162-168`), and it pins a fixed
   variance list per constructor (`:39`). A record has variable arity. None of this was probed
   for either design.
5. **The gate an append actually trips.** The LCNF case-site policy pin, with 36 `Ty` rows, is
   the gate (the header of `Exhaustive.lean`: "the compiled-LCNF case-site policy … is the
   gate"). Its 25 default-mode cover lists are exactly the catch-all classifiers the seat's
   §4.5 asks to review. The seat does not connect the two.
6. **Instrument undercounts.** The proof census misses at least 36 theorems: 183 against 147,
   with 8 proofs split by a function's own principle. The `Test` bill is 5/2 (`FitsInv`), not
   3/1, and the `Test` oleans were fresh (§1).
7. **The JSON route is decided elsewhere.** Decisions row 10 (open, owner) chooses the one
   `Val → Json` and recommends the shape-directed `ShapeDoc.print`; row 11 decides where
   `Schema.*` text comes from. There are at least five `Val → Json` images today:
   - `Truth.valJson` (`:407`)
   - `Keyed.valJson` (`:109`)
   - `Codec.encode`
   - `ShapeDoc.print` / `Store.printIn`
   - `Image.encode`
   The seat counts three and proposes the `Ty`-directed codec for the reply path without
   citing row 10.
8. **Record terms meet two rulings the seat does not cite.**
   - DI-35: `eq` at a record must stay refused; JS `===` compares references.
   - DI-78: term forms and collection atoms need a frozen contract with falsifiers before
     implementation.
9. **Demand evidence from the ingest census.** In the 34-project corpus,
   `docs/research/2026-09-08-ingest-census.md` counts these unknown heads:
   - `Schema.Struct`, 2,032, the most common;
   - `Schema.decodeUnknown*`, about 700;
   - `Schema.Union`, 265;
   - `Schema.Record`, 48;
   - `Schema.TaggedStruct`, 44;
   - `Schema.TaggedUnion`, 20.

   `Schema.Record` is a dictionary type (an index signature), a need the fixed-name record
   proposal does not cover. The census supports doing records and the typed decode; it does
   not choose between the designs (reading).
10. **The arrow to `Shape`.** `Shape.struct`/`Shape.sum` already describe records and sums for
    the CAS, with fields in **declaration** order, and `DialectContract.lean:48` pins
    `shapeTy (.struct …) = none`. Once `Ty.record` exists (fields canonical by **name**), the
    vocabulary asks for the kind of that arrow: an exact embedding, a widening, or a located
    refusal. Otherwise there are two record descriptions with nothing joining them. The seat
    names no such arrow.
11. **Top of the abstraction tree.** C's registered eliminator would be the third hand
    single-motive eliminator, after `Store.Val.ind` (`Val.lean:270-287`) and `Json`'s. Under
    the owner's "build the instrument the second time" steer and the rule that folds are cut
    from the generated families, the eliminator belongs with the generator, not in hand-written
    `Ty.lean` code.
12. **The reply check does not settle `Err.value`** (D16): a program-made payload needs a
    type-level handle-free condition.
13. **The schema bridge's `var` slip** (D12): `schema` is not injective outside the closed
    domain, and the docstring says otherwise.
14. **No conservativity statement for the append.** Per §1.1, `Σ_core` grows by constructor
    appends under DI-47, whose baseline comparison no longer runs (D18). The requirement shape
    the owner's rule asks for is two things:
    - on record-free types, `sub`, `normalize`, `key`, `Fits` and `hasTy` restrict to today's
      (an append changes nothing old);
    - old bytes decode to the same values.
    Neither is stated or probed. Both are plausible here, because the record arms touch only
    record subterms; that is assumed, not checked.

---

## 3. Judged against the owner's two rules

- **Requirements as theorem shapes.** D08 and D20 are stated as law shapes (`fits_sub`,
  `fits_live`, `sub_eq_args`, a stratified `Fits`), which passes. D11's "five deliverables" and
  D14's "put a typed decode at the session boundary" are capability lists. In R3's terms they
  read:
  - **embedding:** `ofSchema r = some t → r ≈ₐ schema t` over the extended `Ty`, where ≈ₐ is
    equality up to annotations;
  - **codec:** `decode t j = some v → Fits t v` and
    `decode t j = some v → encode t v ≈ₒ j`, where ≈ₒ is equality up to a named normaliser:
    field order, and dropped keys if the decode strips;
  - **reply:** every reply the session accepts at row `r` fits `r.answer` in the new world;
  - **S-5:** a host gate, not a theorem.
- **Top of the abstraction tree.** The seat names the constructor's signature and most arrows:
  the judgment `Fits`, the embedding `schema`/`ofSchema`, the codec embedding, the TypeScript
  projection and the relation `sub`. It misses three things:
  - the kind of the arrow to `Shape`, the CAS's record description (missed item 10);
  - the generator extension "folds cut from it" requires (TyView; the eliminator);
  - the case-site pin.
  Without them, records do not come from the one datum at the top.

---

## 4. Probes and commands

Every command is `bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true
<absolute path>`, run from the repository root, one at a time; logs are beside the probes.

| Probe | Exit | What it shows |
| --- | --- | --- |
| `verify-rerun.sh` (reruns all ten seat probes; `verify-rerun-summary.txt`) | 0, 0, 0, 0, 0, 0, 0, 1, 0, 1 | each log matches the seat's, the `time` line aside (tested, `diff`) |
| `verify-TyBillCensus.lean` | 0 | the gate over `Test` (5/2); census2 recomputed (147); the `"eq_"` drop (1); principle users (7 top-level); private sweeps of `Err`/`Lit`/`NativeAtom`/`Store.Val`/`Ty`; `#guard`s: `var`'s schema reads back as a handle, the codec refuses an extra field, a product distributes, `prod never nat` is canonical |
| `verify-TyProofCensus.lean` | 0 | with auxiliaries attributed: 177 direct, 8 principle users, 183 either; the 36 theorems census2 misses, by name |
| `verify-RecordRed.lean` (the seat's `RecordNested.lean` byte for byte, plus red controls) | 0 | `positional_not_normalize_invariant`, `hasTyV_normalize_fails`, `dup_normalize`, `positional_dup_not_invariant`, `named_dup_not_invariant`, `emptyRec_canonical`, `emptyRec_uninhabited` (all at `[propext, Quot.sound]` or `[propext]`); the `#guard`s on the undistributed `_tag` union |
| `verify-CoerciveWidth.lean` | 0 | the third design: `fits_coerce`, `fitsF_coerceF`, `find_fits` at `[propext]`; `projected_fits`, and the red control `unprojected_not_fits` |

Other commands (tested):
- `git show --stat 243ca0dd`; `ls scripts/check-compatibility.py` (absent).
- python reads of `Test/fixtures/baseline/66ee4657/families.json` and of the supplement's
  `snapshot.json` (15 constructors each).
- A python read of `tools/Conform/Effect4/cases-policy.json` (36 `Ty` rows).
- `wc -l` over `src/Effect4/Schema/*.lean`.
- `grep -c` over `ocaml/gen/api_gen.ml` and `ocaml/engine/api_engine.ml`.
- `git grep` for the 2026-09-10 boundary rule's wording.
- A python block comparison of `Ty.lean` against `RecordNested.lean`, in the scratchpad.

**Bounded or host-only.**
- Every proof here is on a model: the seat's world-free copy, or my three-constructor model.
  None is on the tree's `Fits`.
- `fits_coerce` shows that the third design is coherent at the value judgment. It does not
  show TypeScript agreement: TypeScript keeps extra keys on objects that are never decoded,
  and no term here can observe them.
- The two censuses are instruments; their numbers depend on the stated name rules.

No tracked file was edited. No `lake build`, `make`, generator, `git add` or `git commit` was
run. `/Users/pooks/Dev/lean4-effect4-slice6` was not touched.
