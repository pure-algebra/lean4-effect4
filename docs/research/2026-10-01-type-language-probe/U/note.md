# Seat U: cash the initial algebra — every `Ty` traversal as an algebra of one fold

Type-language probe, 2026-10-01. Worktree `/Users/pooks/Dev/lean4-effect4-probe-U`, branch `probe/U`,
base `630e6c37`. Research only: nothing here is a ruling until it is written into a tracked file.
The receipt is at the foot. Paths are relative to the worktree; `U` is this folder. Every Lean
check ran as `LEAN_NUM_THREADS=1 lake env lean -DwarningAsError=true`, one compiler at a time,
through `U/run-lean.sh`; `sh U/rerun.sh` reruns all of them (3 min 41 s on the last run, every log
ending as required).

**Evidence words.** **Proved**: a kernel theorem checked here, its `#print axioms` in the log
named. **Reproduced**: a byte comparison against a fresh producer run. **Tested**: a finite check
run here (a `#guard`, an instrument, a `dune` test, a script), with its red control where one
exists. **Reading**: read in code or notes, not run. **Assumed**: not checked.

## The one thing

**Every per-constructor traversal of `Ty` in the tree, except the semantic algebras and the two
walks over two types, is one generic fold over one of two per-constructor tables or over the
signature alone.** The generic folds are emitted from the declaration of `Ty` by a +303/−1-line
patch to `tools/Effect4Gen/Fold.lean`, the tables from JSON by a 133-line emitter that refuses a
missing or an extra row by name. 24 agreement theorems prove 22 of the tree's hand traversals
equal to folds of `cata_ty` (21 to the generic families, `Val.hasTy` to its own algebra), each the
generated `hom_eq_cata_ty` with definitional fields. Proved: `Ty.renderRaw`,
`Bridge.schema` and `Ty.key` are the three columns of one face table; `varsOf`, `closed`,
`Codec.isSupported`, `handleFree`, `valueVars`, `templateAdmissible`, `findInt` and
`internalHandleScan` are four generic folds reading the five Boolean columns of one classifier
table or, for the two located searches, a hit predicate (three hand `TyAlgebra` literals are these
generic algebras by `rfl`); `members`, `isTagTy`, `rawSupportedErrTy` and
`projectProduct` are one union-spine fold at four atoms; `tyJson`, `tyV`, `tyO`, `tyT` and `tyValue`
are one reflection at five carriers.

At twenty constructors this is level in lines (353 hand lines in the 22 Lean traversals the
families replace, against 347 lines of generic interpreters written once and 69 lines of table
data). What it changes is the next constructor. Under the families an appended constructor costs
one field in each of eight algebra literals that carry real per-constructor content (`Val.hasTy`,
`Fits`, `inhabited`, the codec's encode and decode, and the transformers `normalize`,
`instantiate` and `layout`, which row 56's pending clause keeps compile-forced) and one row in
each of the two tables. Today it costs an arm in each of 17 hand definitions whose matches have no
catch-all, a review of 23 whose matches have one, edits to 8 mirrors, 4 enumerations that miss it
silently, and a new case in each of the 73 theorems that recurse or case on `Ty`. The laws move to
one statement each over the family: `hasTy_normalize` is two fusion squares (98 lines today, 19
after); `key` is injective for every face table with distinct codes, proved once, whatever the
alphabet.

**One constraint before commit 4 relies on this (tested).** The tree's LCNF translator refuses
`TyAlgebra R` ("unsupported parameter R"), so the definitions the OCaml engine and the conform
rungs lower (`Ty.key`, `members`, `normalize`, `sub`, `Val.hasTy`, `render`) cannot simply become
`cata_ty alg`. Either the generator writes each table-driven fold expanded into a plain structural
definition beside its `eq_cata` connector, or the fold carries `@[specialize]` and the layer
algebras `@[inline]`; under the second, the table-driven renderer lowers to exactly the four
externs the hand `renderRaw` lowers to. The choice is the owner's (D-U1, §8.5).

---

## 1. The inventory (question 1)

### 1.1 Where the rows come from

| Source | Command | What it reports at `630e6c37` |
| --- | --- | --- |
| `#traversal_census Effect4.Program.Ty` | `U/probes/Census.lean` → `U/logs/census.log` | 122 definitions take a `Ty` (3 private): fold 5, generated 8, structural 22 (15 with a fold beside them, 1 instance), wf 1, one-level 14 (2 with a fold beside them), delegates 49, opaque 23 (tested) |
| `#exhaustive_gate Effect4.Program.Ty` | the same file; split by `python3 U/scripts/gate-join.py` → `U/logs/gate-join.log` | 66 matches, 28 without a catch-all and 38 with one (the brief's 65/27 predates the instrument seeing the private `ofNormalized`; census §7.11 records the same move). Of the 66, 9 are `fold_of` `.hom` rows, 14 sit in generated modules (`Fold`, `TyView`, `Derived/Program`) and 43 in 40 hand definitions: 17 with a match that has no catch-all (compile-forced at an append), 23 with catch-alls only (to review) (tested) |
| the same two instruments `under OCaml5`, `under Tools`, `under Conform` | `U/probes/CensusMirrors*.lean`, one file per module set (two modules that declare a `main` cannot be imported together) → `U/logs/census-mirrors.log` | six structural mirrors, each a 20-arm match with no catch-all (`tyO`, `tyV`, `tyJson`, `tyT`, `tyOcaml`, `tyValue`); `TyVectors.subMutant` one-level with a catch-all; `RowTypes.request` three matches with a catch-all (it takes a `Row`, so only the gate lists it); `valueTy?` is `partial` and invisible to both instruments (tested; reading for `valueTy?`) |
| the same, `under Test` | `U/probes/CensusTest.lean` → `U/logs/census-test.log` | 33 takers; 16 matches, 4 without a catch-all: two planted fixtures and two frozen counterexample models (tested) |
| the narrow proof census (the programs seat's verifier, rerun) | `U/probes/ProofCensusNarrow.lean` → `U/logs/proof-census-narrow.log` | 73 theorems: 44 by `Ty`'s recursor, 29 more by case analysis only. The synthesis counted 62 at `ba9783c3`; 15 of today's 73, among them `fits_normalize` and the inhabitance laws, are not in that commit by `git grep` (tested) |
| the broad proof census (the tree seat's verifier, rerun) | `U/probes/ProofCensusBroad.lean` → `U/logs/proof-census-broad.log` | 211 theorems eliminate `Ty` directly (auxiliaries attributed), 9 through a `Ty`-shaped principle, 218 either (183 at `ba9783c3`) (tested) |
| the OCaml mirrors | reading `ocaml/engine/e4_program.ml:127-154`, `ocaml/eff/test/prop_wire.ml:155-171`; their reach tested in §4 | `of_ty`: 20 arms and a count pin; `rand_ty`: 15 constructors chosen by index, then `\| _ -> Ty_union` |
| the hand tables | reading; the enumerations' reach tested (`U/probes/Enumerations*.lean`) | `cases-policy.json`: 36 `Ty` rows (25 default cover lists, 5 exhaustive, 6 site lists); `Variances.heads`: 10 rows; `Metadata.lean:52-60`: 20 samples, not in declaration order (`unknown` second); `wire-tags.json`: 20 tags (each the declaration index and the key's code); the conform vectors, in two copies, reach 15 of 20 constructors (no `lit`, `refOf`, `deferredOf`, `var`, `unknown`); `TyVectors.core` reaches 18 of 20 (no `int`, by its docstring's design; no `var`) |

### 1.2 The inventory, one row per site, with its family

The full table is `U/inventory.tsv` (106 rows, written by `python3 U/scripts/inventory.py` from the
logs above, `U/logs/inventory.log`). The `today` column comes from a log or, for files the
instruments cannot read, from the file and lines named; `computes` and `family` are this seat's
reading (question 2's classification). Rendered here without its 15 `Test` rows; `(gate)` marks a
definition only the exhaustive gate lists, with the census line omitted.

| site | name | today | computes | family |
| --- | --- | --- | --- | --- |
| `Laws/Program/Typed/Membership.lean:96` | `Typed.Fits` | structural (fold_of connector); catchAll false | the membership judgment (world, value) | a |
| `Program/Admission.lean:78` | `inhabited` | fold; no matcher (a fold or generated) | the type has a member (DI-67, row 127) | a |
| `Program/Fold.lean:446` | `foldM_ty` | generated; catchAll false | the monadic fold | a |
| `Program/Typed.lean:20` | `Val.hasTy` | structural (fold_of connector); catchAll false | Boolean membership (value, allocation table) | a |
| `Schema/Codec.lean:151` | `Schema.Codec.encodeRaw` | structural (fold_of connector); catchAll true | the JSON encoder (type, value) | a |
| `Schema/Codec.lean:179` | `Schema.Codec.decodeRaw` | structural (fold_of connector); catchAll true | the JSON decoder (type, json) | a |
| `Program/Ty.lean:471` | `Ty.instantiate` | structural; catchAll false | substitution of template parameters | a-id |
| `Program/Ty.lean:606` | `Ty.normalize` | structural (fold_of connector); catchAll false | the canonical form | a-id |
| `Schema/Codec.lean:24` | `Schema.Codec.layout` | structural (fold_of connector); catchAll true | the wire layout: a literal as a string; union, fiberOf, refOf, deferredOf kept as written (`\| t => t`, Codec.lean:34) | a-id |
| `Laws/Program/Template.lean:256` | `Ty.varsOf` | structural; catchAll false | template parameters in occurrence order | b |
| `Laws/Program/Template.lean:264` | `Ty.templateAdmissible` | structural; catchAll false | no parameter under a union head | b |
| `Laws/Program/TypeAlgebra.lean:1219` | `Ty.valueVars` | fold; no matcher (a fold or generated) | template parameters only under value formers | b |
| `Laws/Program/Typed/Membership.lean:2286` | `Typed.handleFree` | fold; no matcher (a fold or generated) | no handle former anywhere | b |
| `Program/Admission.lean:122` | `findInternalHandle` | fold; no matcher (a fold or generated) | path to the first internal handle former | b |
| `Program/Admission.lean:35` | `findInt` | structural (fold_of connector); catchAll false | path to the first int | b |
| `Program/Fold.lean:237` | `foldMapAt_ty` | generated; catchAll false | the monoid fold with the path threaded | b |
| `Program/Fold.lean:282` | `foldMap_ty` | generated; catchAll false | the monoid fold | b |
| `Program/Ty.lean:197` | `Ty.closed` | structural; catchAll false | no template parameter | b |
| `Schema/Codec.lean:42` | `Schema.Codec.isSupported` | structural (fold_of connector); catchAll true | the JSON codec has an arm | b |
| `Program/Eff.lean:43` | `isTagTy` | structural (fold_of connector); catchAll true | a union of strings and string literals | b2 |
| `Program/Eff.lean:49` | `rawSupportedErrTy` | structural (fold_of connector); catchAll false | the error profile Err represents (DI-15, DI-62) | b2 |
| `Program/NativeAtom.lean:43` | `NativeAtom.projectProduct` | structural (fold_of connector); catchAll true | the selected column of a product or a union of products | b2 |
| `Program/Ty.lean:119` | `Ty.members` | structural (fold_of connector); catchAll false | the union members, flattened | b2 |
| `Program/Ty.lean:563` | `Ty.factors` | one-level; catchAll true | members, or [never] | b2 |
| `Program/Ty.lean:785` | `Ty.taggedColumn` | one-level; catchAll true | every member a tagged pair or a scalar | b2 |
| `(gate)` | `methodArgsRow` | match with catch-all; Effect4.Program.methodArgsRow.match_1 alts 2 | prism on prod (a method row's arguments) | b3 |
| `(gate)` | `Authoring.ServiceDef.receiver` | match with catch-all; Effect4.Program.Authoring.ServiceDef.receiver.match_1 alts 2 | prism on prod (the receiver) | b3 |
| `(gate)` | `selectRefusal` | match with catch-all; Effect4.Program.selectRefusal.match_1 alts 3 | dispatch on Decision; the type is passed through | b3 |
| `(gate)` | `Ty.Variance.holds` | match with catch-all; Effect4.Program.Ty.Variance.holds.match_1 alts 3, Effect4.Program.Ty.Variance.holds.match_1 alts 3 | dispatch on Variance; the types are passed through | b3 |
| `Laws/Program/Signature.lean:972` | `flatCarrier` | fold; no matcher (a fold or generated) | a flat service carrier (scalar or a non-context handle), at the root only | b3 |
| `Laws/Program/TyView.lean:30` | `Ty.args` | generated; catchAll false | children with the variance the order reads them at (variances.json) | b3 |
| `Laws/Program/TyView.lean:56` | `Ty.sameHead` | generated; catchAll true | same constructor and payload (the order's head test) | b3 |
| `Laws/Program/TyView.lean:80` | `Ty.litRule` | generated; catchAll true | the literal-below-string rule | b3 |
| `Laws/Program/TyView.lean:86` | `Ty.topRule` | generated; catchAll true | the unknown-is-top rule | b3 |
| `Laws/Program/Typed/Membership.lean:71` | `Typed.FlatFits` | one-level; catchAll true | membership at a flat carrier (one level) | b3 |
| `Program/Checker.lean:104` | `Checker.exitOf?` | one-level; catchAll true | prism: the columns of an exit | b3 |
| `Program/Checker.lean:99` | `Checker.listOf?` | one-level; catchAll true | prism: the element type of a list | b3 |
| `Program/Compile.lean:1368` | `externalValue` | one-level; catchAll true | prism on handle (allocate an external), else membership | b3 |
| `Program/Decision.lean:61` | `Decision.arms` | one-level; catchAll true | the branch types a decision binds (option prism, tagged column) | b3 |
| `Program/NativeAtom.lean:36` | `causeInputError?` | one-level; catchAll true | prism: the error column of a cause or an exit | b3 |
| `Program/Ty.lean:190` | `Ty.isNever` | one-level (fold_of connector); catchAll false | tag test: never | b3 |
| `Program/Ty.lean:402` | `Ty.isMember` | one-level (fold_of connector); catchAll false | tag test: neither never nor union | b3 |
| `Program/Ty.lean:570` | `Ty.isFactor` | one-level; catchAll true | tag test: not a union | b3 |
| `Program/Ty.lean:772` | `Ty.isTagged` | one-level; catchAll true | prism: prod (lit tag) _ | b3 |
| `Program/Ty.lean:797` | `Ty.payloadOf` | one-level; catchAll true | prism: the payload of prod (lit tag) p | b3 |
| `Program/Typing/Rules.lean:183` | `fiberTy` | one-level; catchAll true | prism: the columns of a fiber | b3 |
| `tools/Tools/RowTypes.lean:44` | `Tools.RowTypes.request` | three matches with a catch-all (gate only: it takes a Row, so the census lists no row; census-mirrors.log) | a row's request split by its shape (prisms on unit and prod) | b3 |
| `Codegen/Types.lean:268` | `Codegen.Types.ofNormalized` | structural; catchAll false | the TypeScript TypeRef spelling (Option monad) | c |
| `Program/Ty.lean:142` | `Ty.key` | structural (fold_of connector); catchAll false | the injective structural key (codes = wire tags) | c |
| `Program/Ty.lean:93` | `Ty.renderRaw` | structural (fold_of connector); catchAll false | TypeScript text | c |
| `Schema/Bridge.lean:37` | `Schema.Bridge.schema` | structural (fold_of connector); catchAll false | rc.112 SchemaRepresentation | c |
| `tools/Effect4Gen/variances.json` | `variances.json` | generated from Variances.heads and rc.112 | the variance column read by the TyView group | c |
| `tools/Effect4Gen/wire-tags.json` | `wire-tags.json (Ty)` | hand data, 20 active tags | the wire tag of each constructor (= declaration index = key code) | c |
| `tools/Tools/Variances.lean:368-388` | `Tools.Variances.heads` | hand table, 10 rows (refuses a head with no row) | each parametrised head's rc.112 declaration or printer spelling | c |
| `ocaml/engine/e4_program.ml:130-154` | `E4_program.Make.of_ty` | hand OCaml match, 20 arms, count pinned by `assert (... = 20)` (:127) | Eff_types.ty to the engine's A.ty (two generated declarations of one signature) | c' |
| `Program/Ty.lean:75` | `instReprTy.repr` | structural; catchAll false | the derived Repr | c' |
| `Store/Domain/Derived/Program.lean:1091` | `Store.ProgramGen.TyC.toValTy` | generated; catchAll false | the Canonical byte image (generated) | c' |
| `src/OCaml5/Eff/Emit.lean:366` | `OCaml5.Eff.tyO` | structural, no catch-all (census-mirrors.log) | a Ty value as OCaml constructor syntax (Eff_types.ty) | c' |
| `src/OCaml5/Eff/Goldens.lean:89` | `OCaml5.Eff.tyV` | structural, no catch-all (census-mirrors.log) | a Ty value as the golden value tree V (.ctor name args) | c' |
| `tools/Conform/Effect4/LcnfMl.lean:164` | `Conform.Effect4.LcnfMl.tyT` | structural, no catch-all (census-mirrors.log) | a Ty value in the target evaluator's value domain | c' |
| `tools/Conform/Effect4/LcnfMl.lean:270` | `Conform.Effect4.LcnfMl.tyOcaml` | structural, no catch-all (census-mirrors.log) | a Ty value as OCaml syntax for the LCNF-cut types (strings not escaped) | c' |
| `tools/Conform/Effect4/LcnfSemantics.lean:40` | `Conform.Effect4.LcnfSemantics.tyValue` | structural, no catch-all (census-mirrors.log) | a Ty value in the LCNF interpreter's value domain | c' |
| `tools/Conform/Effect4/LcnfSemantics.lean:63` | `Conform.Effect4.LcnfSemantics.valueTy?` | partial (invisible to the census), if-chain by name | the inverse of tyValue | c' |
| `tools/Tools/ProfileJson.lean:21` | `Tools.ProfileJson.tyJson` | structural, no catch-all (census-mirrors.log) | a Ty value as tagged JSON {_tag, binder: ...} | c' |
| `ocaml/eff/test/prop_wire.ml:155-171` | `Prop_wire.rand_ty` | hand OCaml generator on the index, `\| _ -> Ty_union` | a random Ty for the wire properties: 15 of 20 constructors (no lit, refOf, deferredOf, var, unknown) | c'' |
| `src/OCaml5/Eff/Metadata.lean:52-60` | `OCaml5.Eff.Metadata.types` | hand table, 20 rows | one sample per constructor for the metadata fixtures | c'' |
| `tools/Conform/Effect4/LcnfMl.lean:192-207` | `Conform.Effect4.LcnfMl.leaves/layer/vectors` | hand enumeration | the rung-3 vectors: 15 of 20 constructors (no lit, refOf, deferredOf, var, unknown; EnumerationsMl.log) | c'' |
| `tools/Conform/Effect4/LcnfSemantics.lean:93-110` | `Conform.Effect4.LcnfSemantics.leaves/layer/vectors` | hand enumeration (a second copy) | the rung-2 vectors: the same 15 of 20 (EnumerationsSemantics.log) | c'' |
| `tools/Tools/TyVectors.lean:59-63` | `Tools.TyVectors.core` | hand table | one type per head for the assignability lane (no int, by its docstring's design; no var) | c'' |
| `Codegen/Types.lean:316` | `Codegen.Types.ofTy` | delegates (census.log) | ofNormalized after normalize | d |
| `Laws/Program/TypeAlgebra.lean:1066` | `Ty.subN` | delegates (census.log) | sub between normal forms (the checker's order) | d |
| `Program/Admission.lean:81` | `admitColumn` | delegates (census.log) | normalize = never, or inhabited | d |
| `Program/Eff.lean:64` | `supportedErrTy` | delegates (census.log) | rawSupportedErrTy after normalize | d |
| `Program/Ty.lean:526` | `Ty.matchTemplate` | delegates (census.log) | infer, then sub against instantiate | d |
| `Program/Ty.lean:602` | `Ty.productMembers` | delegates (census.log) | factors of both sides, paired | d |
| `Program/Ty.lean:755` | `Ty.render` | delegates (census.log) | renderRaw after normalize (TypeScript text of the canonical form) | d |
| `Program/Ty.lean:763` | `Ty.join` | delegates (census.log) | normalize of a union (the canonical join) | d |
| `Program/Ty.lean:778` | `Ty.diffTag` | delegates (census.log) | members filtered by isTagged | d |
| `Program/Ty.lean:802` | `Ty.payloadTy` | delegates (census.log) | payloadOf over members, normalized | d |
| `Program/Ty.lean:809` | `Ty.Canonical` | delegates (census.log) | normalize t = t | d |
| `Program/Ty.lean:846` | `CTy.ofRaw` | delegates (census.log) | normalize into the canonical subtype | d |
| `Program/Typing/Rules.lean:109` | `rowTy` | delegates (census.log) | instantiate at matchTemplate's bindings, normalized | d |
| `Program/Typing/Rules.lean:214` | `catchIfError` | delegates (census.log) | join and diffTag of normal forms | d |
| `Schema/Bridge.lean:243` | `Ty.schema` | delegates (census.log) | Bridge.schema after normalize | d |
| `Schema/Codec.lean:215` | `Schema.Codec.isValue` | delegates (census.log) | encodeRaw/decodeRaw at layout of normalize, with membership | d |
| `Schema/Codec.lean:229` | `Schema.encode` | delegates (census.log) | encodeRaw at layout of normalize, membership and exact recovery checked | d |
| `Schema/Codec.lean:238` | `Schema.decode` | delegates (census.log) | decodeRaw at layout of normalize, membership checked | d |
| `Program/Ty.lean:431` | `Ty.sub` | wf; catchAll true | the subtype order (two values, well-founded) | e |
| `Program/Ty.lean:496` | `Ty.infer` | structural; catchAll true | bindings a request fixes for a template (two values) | e |
| `tools/Tools/TyVectors.lean:46` | `Tools.TyVectors.subMutant` | one-level, catch-all (census-mirrors.log) | sub with the refOf arm swapped: the assignability lane's red control | e |
| `tools/Conform/Effect4/cases-policy.json` | `cases-policy.json (Ty)` | seeded pin of compiled case sites, 36 Ty rows (25 cover lists, 5 exhaustive, 6 sites) | what the compiled code does at each case site today | pin |

Plus 15 definitions under `Test/` (family e): the instruments' planted fixtures
(`ExhaustiveFixture`, `TraversalFixture`) and the frozen counterexample models
(`FitsOrder.Reviewed.Fits`, `ValueMembership.ExactSpelling.FitsInv` and `FlatFits`,
`Reviewed.HandlesFit`, `InvocationContract.requestFor`). The 73 theorems are `U/theorems.tsv`
(question 5).

---

## 2. The classification (question 2)

Ten families. Each generic definition reads the **emitted one-level view** of §3.2 — `TyCtor` (the
tags, with `name`, `binders` and `all`), `tyCtor`, `TyLeaf`/`tyLeaf` (the payload by sort),
`tyKids`, `tyBuild` with `tyBuild_view`, the table type `TyTable α` (one field per constructor,
`get` by tag) and the layer algebra `TyAlgebra.ofLayer (layer : TyCtor → TyLeaf → List R → R)` —
which the patched generator writes from the declaration alone
(`U/generated/ProbeU/TyFoldExtras.lean`). Hand lines are measured by `python3 U/scripts/hand-lines.py`
(`U/logs/hand-lines.log`).

| Family | Generic definition | Agreement law | A new constructor costs | Members (hand lines today) | Evidence |
| --- | --- | --- | --- | --- | --- |
| **(a)** semantic catamorphism | a `TyAlgebra` literal with every field written: `cata_ty alg` | `hom_eq_cata_ty` (generated): a function with `alg`'s twenty equations is `cata_ty alg`; two such agree when their algebras do | one field, compile-forced, with real content: the wanted failure | `Val.hasTy`, `Fits`, `inhabited`, `Codec.encodeRaw`, `Codec.decodeRaw`; `foldM_ty` (generated) | proved: `Laws.hasTy_eq_cata` (`Val.hasTy` is the fold of `hasTyAlg`, the production-shaped algebra; the two cause arms through `causeAdmits_discard_ty`); `inhabited` is a fold already; `Fits`, `encodeRaw`, `decodeRaw` have `fold_of` connectors in the tree (reading) |
| **(a-id)** transformer `Ty → Ty` | a `TyAlgebra (fun _ => Ty)` literal; the generated identity algebra (`TyAlgebra.id`, `cata_id_ty`) says which of its fields are rebuilds | fusion (`cata_fusion_ty`): a law through the transformer states only the squares at the fields that are not rebuilds (`TyAlgebra.Commutes`, every other square `rfl`) | one field each under row 56's pending clause (a transformer names every container constructor), which this note follows; nothing for a natural map if the owner relaxes it (D-U3) | `normalize` (18 rebuilds; overrides `prod` and `union`, `Program/Ty.lean:607-628`), `instantiate` (19 rebuilds; overrides `var`, `:474-494`), `layout` (overrides `lit`; returns `union`, `fiberOf`, `refOf`, `deferredOf` as written through `\| t => t`, `Schema/Codec.lean:26-34`: a paramorphism) | proved: `Laws.normalize_commutes` states two squares and its eighteen defaults close by `rfl`; reading for `instantiate` and `layout` |
| **(b)** head fold over a classifier column | `TyAlgebra.headAlg op g` = `ofLayer fun c l kids => nodeThen op (g c l) kids`; the Boolean case `allHeads col`; the parameter list `paramsAlg`; the located search `firstAlg hit`, each child reached at its binder name; the pair `varsUnder col` (no parameter; parameters only below the column's heads) | `foldMap_head_eq_cata` (emitted once): `foldMap_ty` at a hook that reads only the layer is the head fold; `foldMap_eq_cata` for a hook that reads the node (paired); `cata_ofLayer_inv`, `allHeads_mono` | one row of the classifier table (`U/tables/ty-classes.json`): every column answered there or the table does not generate; the recursion is generated, so no traversal can skip a child | `varsOf` (6), `closed` (6), `templateAdmissible` (7), `isSupported` (5), `handleFreeAlg` (21), `valueVarsAlg` (21), `findInt` (11), `internalHandleScan` (21) | proved, `U/probes/MonoidFolds.lean`: 11 theorems; `handleFreeAlg`, `valueVarsAlg` and `internalHandleScan` are the generic algebra at a table row by `rfl`; `findInt`'s path segments (`inner`, `left`, `right`, `error`, `value`) are the constructors' binder names (`Program/Ty.lean:45-64`) |
| **(b2)** union-spine fold | `spineFold bot join atom`: `never` the bottom, `union` the join, every other node an atom read whole (a paramorphism through `union` only) | `hom_eq_cata_ty` on the paired carrier; the spine's catch-all ("every other constructor is an atom") is the semantics of the free join-semilattice reading, not a default | nothing in the fold; the atom classifier keeps row 56's rule (positive arms, an explicit negative), so a new constructor is a member, and in every negative class until its arm says otherwise | `members` (21), `isTagTy` (4), `rawSupportedErrTy` (7), `projectProduct` (8); `factors`, `taggedColumn`, `diffTag`, `payloadTy` read `members` | proved, `U/probes/UnionSpine.lean`: 4 theorems. Tested: the spine is structural, not `members` read through a monoid; `isTagTy`'s bottom `false` is not the unit of `&&`, so `isTagTy (never ∪ string) = false` while `members` reads `[string]`; normal forms never meet it |
| **(b3)** one-level view | the emitted view (`tyCtor`, `tyLeaf`, `tyKids`, `tyBuild`); per-constructor prisms `as<C>? : Ty → Option args` (proposed for the emitter, not in the measured patch); table columns | the prism laws (`as<C>? (C x) = some x`, `as<C>? t = some x → t = C x`), one `cases` each; not traversals (row 143) | nothing: a prism's catch-all is exactly "not this constructor", right for every future one; a tag test is a column or a comparison of `tyCtor` | `isNever`, `isMember`, `isFactor`, `listOf?`, `exitOf?`, `fiberTy`, `causeInputError?`, `payloadOf`, `isTagged`, `methodArgsRow`, `receiver`, `RowTypes.request`, `externalValue`'s handle arm, `Decision.arms`'s option arm, `flatCarrier`, `FlatFits`; the generated `TyView` rows | reading (of the census's 14 one-level rows, 12 are prisms, tag tests or `FlatFits`; `factors` and `taggedColumn` read `members`, b2); `tyBuild_view` proved (`U/logs/olean-TyFoldExtras.log`) |
| **(c)** spelling fold | one interpreter per face over one column of the face table (`U/tables/ty-faces.json` → `tyFaces : TyTable FaceRow`): `tsAlg`, `schemaAlg`, `keyAlg` | `hom_eq_cata_ty` with definitional fields; `key_injective_of_table` (proved once, §5) | one row of the face table: the TypeScript text, the Schema node and the code in one place; a `module` row names the rc.112 module `M` once and the emitter writes `M.M<…>` and `effect/schema/M` from it | `renderRaw` (22), `Bridge.schema` (21), `key` (21); `ofNormalized` (the `TypeRef` face, private: a fourth column, proposed); `Variances.heads`' printer spellings; `wire-tags.json` (the code column) | proved, `U/probes/SpellingFolds.lean`: `renderRaw_eq_table`, `schema_eq_table`, `key_eq_table`, each `[propext]`; tested: the printed `TypeRef` face equals `Ty.render` on every vector it spells, except a literal holding a quote (RED, §7) |
| **(c')** generic reflection | `cata_ty (reflectAlg r)` with `r : Reflection X` = how a carrier spells an application (tag, arguments named by their binders), a string and a number: three fields, no per-constructor content | `hom_eq_cata_ty`, definitional | nothing: the constructor is reflected in every carrier with no edit | `tyJson`, `tyV`, `tyO`, `tyT`, `tyOcaml`, `tyValue` (21 each), `valueTy?` (25, the inverse), `of_ty` (OCaml, 21), the derived `Repr`, the generated `TyC.toValTy` | proved, `U/probes/Reflections*.lean`: `tyJson_eq`, `tyV_eq`, `tyO_eq`, `tyT_eq`, `tyValue_eq`; tested: `tyOcaml` on every rung-3 vector and four constructors the vectors miss, with its unescaped-string RED (§7); `of_ty` emitted and tested in OCaml (§4) |
| **(c'')** unfold | the generic enumerator `enumTy` from `TyCtor.all`, the shape view and a sample-payload column; generators emitted from the family description | coverage: `missing (enumTy …) = []` (tested) | nothing: an enumeration read off the tag list cannot omit a tag | `rand_ty` (OCaml, 17), the conform vectors in two copies, `Metadata.types`, `TyVectors.core` | tested: `rand_ty` and both vector copies reach 15 of 20; the emitted `rand_ty` reaches 20 of 20 (§4) |
| **(d)** composition | stays `cata alg₂ ∘ cata alg₁` where the outer fold reads the inner one's result whole (`renderRaw ∘ normalize`, `schema ∘ normalize`, `key ∘ normalize`): the inner transformer's `union` arm rebuilds and re-sorts its members, so one fused fold would recompute the inner value at every node; fusion (`cata_fusion_ty`) and the banana split (`cata_prod_ty`) act on the laws | inherited from both connectors; a law about the composite is a fusion through the inner transformer | inherited | the 18 `delegates` rows (`render`, `Ty.schema`, `ofTy`, `supportedErrTy`, `join`, `subN`, the codec's public pair, …) | proved: the two corollaries of uniqueness (`U/logs/olean-TyFoldExtras.log`) and `closed = isEmpty ∘ varsOf` by fusion of a monoid homomorphism (§5); reading for the composites |
| **(e)** not a fold of one value | `sub` and `infer` walk two types; under W2's commit 2 they are generated from the view (`sameHead`, `args` with their variances) and one table of the rules that are not congruences (`litRule`, `topRule`, the union's distribution and choice) | the order laws through `TyView.sub_eq_args` (in the tree) | a variance row and, for a rule across heads, a row of the exceptional table | `sub`, `infer`, the derived `DecidableEq`, the `Test` fixtures and counterexample models, `subMutant` | reading; `sub_eq_args` is in the tree; the fixtures and models stay hand-written by purpose (§6.2) |

**Against the brief's grouping.** The brief puts `sub`'s congruence arms, `instantiate` and `closed`
under (a), and `isNever` and `members` under (b). Read on the definitions: `closed` is a head fold
at the parameter column (proved, `closed_eq`), with no semantic content; `instantiate` is a
substitution, nineteen rebuilds and one override (a-id); `sub`'s congruence arms are the variance
table read through the generated view, and `sub` itself walks two values (e); `isNever` is one
level (b3); `members` recurses through `union` only, so it is the spine fold (b2), not a `foldMap`
(which visits every node). The mirrors the brief lists under (c) — `tyJson`, `tyOcaml`, `tyT`,
`tyO`, `tyV`, `of_ty` and `rand_ty`'s generator — need no spelling table: they reflect names,
binder names and payload sorts, which the declaration holds (c', c''). The spelling folds proper,
whose per-constructor content is a spelling, are `renderRaw`, `ofNormalized`, `Bridge.schema`,
`key` and the wire tags.

**Exhaustiveness, the point of the families.** An algebra record has one field per constructor,
so a new constructor fails every algebra literal at compile time — the wanted failure, kept where
the field has real content. A table has one field per constructor and no default, so a new
constructor fails the one table it belongs in, and the emitter refuses a JSON table without its
row, by name (`U/logs/gen-tables-red-missing.log`, `gen-tables-red-extra.log`). A catch-all
survives only where it is the semantics: a prism's "not this constructor", the spine's "every
other constructor is an atom". Each of today's 23 catch-all definitions becomes a column, a prism,
a spine atom classifier or a full literal.

---

## 3. What the generator emits (question 3)

### 3.1 Today

- `tools/Effect4Gen/Fold.lean` (`emitBlock`, `:325-617`) writes, for `Ty`, `TyAlgebra`, `cata_ty`,
  `TyHom`, `hom_eq_cata_ty`, the identity algebra and `cata_id_ty`, `foldMapAt_ty`, `foldMap_ty`,
  and the monadic half with its laws (reading). Reproduced: rerun into `U/generated/`, its output
  is byte-identical to `src/Effect4/Program/Fold.lean` (`U/logs/gen-fold-zero.log`). It writes
  **no** connector from `foldMap_ty` to `cata_ty`, no view, no table type, no layer algebra, no
  fusion.
- `tools/Effect4Gen/View.lean` already reads one per-constructor table for `Ty`: the variances
  (`variances.json`, produced from rc.112 and the hand list `tools/Tools/Variances.lean:368-388`,
  which refuses a parametrised head with no row) (reading). It is the precedent for a
  per-constructor table read by a generator.
- `tools/Effect4Gen/LayerView.lean:121-281` writes the layer algebra (`EffAlgebra.ofLayer` over
  `ArgF`) for `Eff` only, with `Eff`'s names written into the emitter (reading).
- `src/OCaml5/Tools/EffGen.lean` writes the OCaml types, the wire codec, the JSON printer and
  `eff_manifest.txt`, one line per family with its constructors, arities and carriers (reading);
  the eight mirrors are hand copies of what it and `tools/Drivers/TsGen.lean` already know how to
  emit.

So for families (b), (c) and (d) no tool emits the algebra from the description and a table
today; (c') and (c'') need only the description, which two tools already read.

### 3.2 With a small change: the generic families, emitted (measured)

`U/patches/Fold.lean` is `tools/Effect4Gen/Fold.lean` with one function added
(`Extras.emitExtras`) and two flags (`--extras`, `--namespace`): **+303 / −1 lines**, 292 of the
added lines non-blank (`U/patches/Fold.lean.patch`, `U/logs/measure-generator.log`; the generator
goes from 1,385 lines to 1,687). Without the flag it still reproduces the committed `Fold.lean`
byte for byte (`U/logs/gen-fold-patched-zero.log`, reproduced). With it, from the declaration of
`Ty` alone,

    lake env lean -M 4096 --run U/patches/Fold.lean --extras --group TyFoldExtras \
      --imports Effect4.Program.Fold --out U/generated/ProbeU/TyFoldExtras.lean \
      --namespace ProbeU Effect4.Program.Ty

writes 522 lines (`U/generated/ProbeU/TyFoldExtras.lean`; `rerun.sh` regenerates it and checks it
unchanged): the tags with their names and binders, the payload by sort, `tyBuild`, `tyKids`,
`tyBuild_view`, `TyTable` and `TyTable.get`, `TyAlgebra.ofLayer`, `cata_ofLayer_view`,
`sizeOf_tyKids`, **`cata_ofLayer_inv`**, `headAlg` and **`foldMap_head_eq_cata`**, `paraAlg` and
**`foldMap_eq_cata`**, `TyAlgebra.Commutes` and **`cata_fusion_ty`**, `TyAlgebra.prod` and
**`cata_prod_ty`**, with their receipts: `[propext]` for five, `[propext, Quot.sound]` for two, none
for `cata_ofLayer_view` (proved, `U/logs/olean-TyFoldExtras.log`). Every worked instance below
compiles against this generated module, not against a hand copy.

### 3.3 With a new emitter: the tables (measured)

`U/patches/TableGen.lean` (133 lines) reads `U/tables/ty-faces.json` (35 lines) and
`U/tables/ty-classes.json` (34 lines), checks the rows against the constructors of the declaration,
refuses a constructor with no row and a row for no constructor, each by name (two RED tables,
exit 1), and writes `tyFaces : TyTable FaceRow` and `tyClasses : TyTable ClassRow` (34 lines each;
`U/logs/gen-tables*.log`, tested). The hand part that stays is the generic interpreters, written
once: `ProbeU/Faces.lean` (the template pieces and the three face algebras), `Classes.lean` and
`ClassRow.lean` (the head folds and the row type), `Reflect.lean` (the reflection) and `Enum.lean`
(the unfold), 347 lines.

**Lines, measured.** The 22 Lean traversals the families replace hold 353 hand lines (c 64, b 98,
b2 40, c' 151) and the two OCaml mirrors 38 (`U/logs/hand-lines.log`). Against them: 347 lines of
generic interpreters written once, 69 lines of table data, and 590 emitted lines nobody edits.
That is level at twenty constructors. What moves is the per-constructor cost: today an arm in each
of the 22 and in both OCaml mirrors; under the families, one row in each table.

### 3.4 The worked instances, one per family

| Family | Instance | Where | Result |
| --- | --- | --- | --- |
| (c) | `renderRaw` as the TypeScript column; `Bridge.schema`, `key` as the other two | `U/probes/SpellingFolds.lean`, `U/logs/SpellingFolds.log` | proved, `[propext]`; tested on the 22 per-constructor samples and every native and package row's columns; RED held |
| (b) | `varsOf` as `foldMap` (`varsOf_eq_foldMap`) and as the parameter column's head fold; seven more | `U/probes/MonoidFolds.lean`, `U/logs/MonoidFolds.log` | proved (11 theorems) |
| (b2) | `members` and three more as one spine fold | `U/probes/UnionSpine.lean`, `U/logs/UnionSpine.log` | proved (4); tested (the bottom's difference) |
| (c') | five Lean mirrors as one reflection; `tyOcaml` tested | `U/probes/Reflections*.lean` | proved (5), tested (1) |
| (c'') | the unfold reaches every tag; the hand lists measured | `U/probes/Enumerations*.lean` | tested |
| (c'), (c''), OCaml | `of_ty` and `rand_ty` emitted from the family description | §4 | tested with `dune` |
| (d) | fusion and the banana split from uniqueness; `closed = isEmpty ∘ varsOf` | emitted; `U/probes/Laws.lean` | proved |

### 3.5 The boundary: the wave's nested `Ty`

On a copy of `Ty` with row 119's `record (fields : List (String × RecordTy))`
(`U/probes/ProbeU/RecordTy.lean`), the committed generator's nested path emits and compiles 517
lines (`TyAlgebra` gains `List (String × R .ty) → R .ty`; positional helpers and `foldMap`; no
monadic half and no path fold; 30 receipts, `U/logs/olean-RecordFold.log`,
`RecordFoldReceipts.log`), and `--extras` refuses by name: "holds a member under a container; its
layer is `ArgF`'s" (`U/logs/gen-record.log`, tested). So commit 2 (W2) must give the extras emitter
the position language the nested path of `Fold.lean` already has, with `LayerView`'s `ArgF` as the
layer's argument type: the view, the layer algebra, the head and paired folds, the reflection and
the key all read a field list as `List (String × R)`. The probe's own layer functions are written
for today's arities (no child, one, two): `varsUnderLayer`, `firstLayer` and the test reflection
`ocamlR` give a fixed answer at three or more children, never reached on today's `Ty`; at the
wave's variable arity they fold the child list instead, which the `ArgF` form forces. Size of the
extension **assumed** at 150 to 200 lines, by reading the two emitters it merges.

---

## 4. The mirrors as the same algebra (question 4)

**The rung, stated.** A mirror of `Ty` is *the same algebra interpreted elsewhere* when (1) its
arms are produced from the family description — constructor names, binder names, argument
carriers — by a generator (Effect4Gen for Lean, EffGen for OCaml, TsGen for TypeScript) or by the
LCNF route from the Lean definition, never by hand; and (2) the conform lane checks it on vectors
drawn from a generated enumeration that reaches every constructor (`missing (enumTy …) = []`). For
a reflection the observation is the round trip through the carrier's reader (`marshalRoundTrip` in
`LcnfSemantics`, the wire goldens in `make check-ocaml`); for a lowered fold it is rung 2's and
rung 3's comparison (`render`, `key`, `members`, `isNever`, `join`). Its gates are the existing
ones: `make check-gen` holds the emitted bytes, `make check-ocaml` and the conform rungs hold the
behaviour. Nothing new is gated; what changes is that no mirror is kept by hand.

**The eight, measured.**

| Mirror | Needs a spelling table? | Today | Under the rung | Evidence |
| --- | --- | --- | --- | --- |
| `tyJson` (`Tools.ProfileJson`) | no: names and binders | hand, 21 lines | the generic reflection at a JSON `Reflection` | proved (`tyJson_eq`; its `Classical.choice` is the definition's own, `tyJson`'s and `tagged`'s, printed beside it) |
| `tyV` (`OCaml5.Eff.Goldens`) | no | hand, 21 | the reflection at `V` | proved (`tyV_eq`, `[propext]`) |
| `tyO` (`OCaml5.Eff.Emit`) | no | hand, 21 | the reflection at OCaml syntax, one template per arity | proved (`tyO_eq`; `Classical.choice` from `tyO`'s and `ostr`'s own definitions, printed) |
| `tyT` (`Conform.Effect4.LcnfMl`) | no | hand, 21 | the reflection at the target's values | proved (`tyT_eq`; `Classical.choice` from `tyT` itself, printed) |
| `tyOcaml` (`LcnfMl`) | no | hand, 21, strings unescaped | the reflection with `ostr`'s escaping, which `tyO` uses and `tyOcaml` does not | tested on the rung-3 vectors and four constructors they miss; RED: an unescaped quote (§7) |
| `tyValue` (`Conform.Effect4.LcnfSemantics`) | no | hand, 21 (and the `partial` inverse `valueTy?`, 25) | the reflection at the interpreter's values; the inverse read off the same view | proved (`tyValue_eq`, `[propext]`) |
| `of_ty` (`ocaml/engine/e4_program.ml`) | no: the two OCaml declarations are generated from one signature | hand, 20 arms and a count pin | emitted from `eff_manifest.txt` (or deleted with `E4_program` by the runner plan's step 1, as its own comment says) | tested: the engine tests give the same summary with the emitted one (`U/logs/ocaml-engine-compare.log`) |
| `rand_ty` (`ocaml/eff/test/prop_wire.ml`) | no: arities and carriers | hand, 15 of 20 constructors | emitted from `eff_manifest.txt` | tested: 20 of 20, and the 6,250 wire checks pass with the five constructors the hand generator never produced now among them (`U/logs/ocaml-emitted-eff.log` against `ocaml-zero-coverage.log`) |

None of the eight carries per-constructor content: all eight fit the rung today with no table, only
the description the generators already read. None of them is the LCNF cut's. The cut's copies of
`Ty` (`and ty` at `ocaml/gen/api_gen.ml:613` and `ocaml/engine/api_engine.ml:824`) and the lowered
`Ty.key`, `members`, `normalize`, `sub` and `Val.hasTy` in the engine are generated already and on
rungs 2 and 3 (reading); `tyT`, `tyOcaml`, `tyValue` and `valueTy?` are the rungs' own hand
marshalling of `Ty` values into and out of that cut.

**The OCaml run** (`bash U/scripts/ocaml-copy.sh`; `dune` only through `opam exec
--switch=effect4`, inside `U/ocaml-copy`, a copy of `ocaml/`). `U/scripts/emit-ocaml-ty.py` (107
lines) reads the `Ty` line of `ocaml/eff/eff_manifest.txt` and writes `of_ty` and `rand_ty` into
copies of their files (`U/ocaml/emitted/`; the diffs are `U/ocaml/*.diff`: the emitted `of_ty`
differs from the hand one in its variable names and a dropped comment only). Zero control: the
unmodified copy builds, `prop_wire: 6250 checks, 0 failures (seed 42)`, and an appended instrument
reports `rand_ty coverage: 15 of 20 constructors; missing: [lit; refOf; deferredOf; var; unknown]`.
Emitted: it builds, `prop_wire: 6250 checks, 0 failures`, `20 of 20`; `dune test engine` gives the
same summary as with the hand `of_ty` once the lines are sorted (the output is parallel) and the
wall-clock figure dropped. Both arms carry one environmental FAIL ("the Lean corpus is present":
`make corpus` writes under the worktree's `.lake`, not the copy's) (tested).

**The LCNF finding** (`U/probes/ProbeU/Lowering.lean`, `U/logs/lcnf-lowering.log`, tested). Lowering
`renderTable := cata_ty (tsAlg tyFaces)` with the tree's route (`src/OCaml5/Tools/LcnfGen.lean`,
output under `U/ocaml/lowered/`) stops with `uncaught exception: Effect4.Program.TyAlgebra:
unsupported parameter R at 0` (run 1) — the refusal coherence principle §6.1 records for
`EffAlgebra Op R`. `@[specialize]` on the fold alone does not help (run 2). With the fold
specialized **and** the layer and face algebras `@[inline]`, the closure is built (run 3: 33
constants) and stops at four extern todos (`String.ofList`, `USize.repr`, `Array.getInternal`,
`System.Platform.getNumBits`); the hand `Ty.renderRaw` alone stops at the same four (run 4, the
control: they come from `toString` on a parameter's index). So a table-driven fold reaches the
OCaml side with no new extern, but only under those two attributes; the alternative is for the
generator to expand the table into a plain structural definition. `cataS_eq` proves the
specialized copy is the generated fold (`[propext]`). The log records `exit 0` after runs 1 and 2;
the refusal is the `uncaught exception` line, and no OCaml was written in any run.

---

## 5. The laws once (question 5)

Lines today are non-blank lines of the source span; the generic form's lines are the probe's
(`U/probes/Laws.lean`, `KeyInjective.lean`; `U/logs/Laws.log`, `KeyInjective.log`).

| Law | Today | Once over the family | Lines today → after | A new constructor, today → after |
| --- | --- | --- | --- | --- |
| `hasTy_normalize` (membership is invariant under normalization) | an induction with eight helper theorems, one per constructor `normalize` overrides or whose `hasTy` arm needs a congruence (`TypeAlgebra.lean:212-320`) | **fusion**: `cata_fusion_ty normalize_commutes`, where `normalize_commutes` states the two squares `normalize` overrides (`prod`, `union`, each the existing three-lemma chain) and the eighteen others are the `Commutes` record's `rfl` defaults | 98 → 19 (16 for the two squares, 3 for the statement; `Commutes` and `cata_fusion_ty` are emitted, 73 lines of `TyFoldExtras`) | a congruence helper and an arm → nothing, unless `normalize` overrides it (`record`: its square, the canonical field order) |
| `fits_normalize` | twenty explicit arms (`Membership.lean:1126-1229`) | the same fusion on `Fits`, with five squares: `prod`, `union`, and the three handle formers whose arm reads the declared type (`Fits` is paramorphic there) | 104 → about 40, **assumed** (by reading; not proved here) | an arm → nothing unless overridden |
| `key_injective` | a case split over the square of the alphabet (`induction a generalizing b <;> cases b`, then `all_goals try …` and a bullet per constructor with a payload or children, `Ty.lean:244-276`) | `key_injective_of_table`: the fold of `keyNode` is injective for **every** face table whose codes are distinct; the premises are table facts (codes distinct by `decide`, a tag fixes its node's shape, payload encodings injective, no string payload beside children) | 32 → 105 once (64 lines of helpers, 13 of them per-tag shape facts the view emitter would write, and the 41-line theorem) + 6 per table: **no saving at twenty constructors** | a bullet per constructor, and list-encoding lemmas for every variable-arity one → nothing; the generic proof names the condition a variable-arity row must meet: its arity in the key and its names length-prefixed |
| `templateAdmissible_of_closed` | `induction t <;> aesop` (`Template.lean:276-278`) | `varsUnder_of_closed`: one invariant proved per **layer shape** (four cases: no child, one, two, more) by `cata_ofLayer_inv`, at every column; at `positional` it is this law (`templateAdmissible_of_closed'`), at `valueFormer` the same law for `valueVars`, which the tree does not state | 3 → 20 once + 5 per column | nothing today *if* `induction` and `aesop` keep working on the nested `Ty` (they need the generated eliminator) → nothing, and no induction |
| monotonicity of a fold whose algebra is fieldwise monotone | stated nowhere | `allHeads_mono`: a column-wise weaker class gives a weaker fold, for every pair of columns (the banana split, then the per-layer invariant) | — → 19 once | — |
| a new law from it: a codec-supported type holds no handle | stated nowhere | `handleFree_of_isSupported`: `allHeads_mono` at the column inclusion `codec ⊆ handleFree` (`decide` per tag) | — → 5 (+ 4 for the column inclusion) | — |
| `varsOf_eq_nil_of_closed` | `induction t <;> aesop` (`Template.lean:280-281`) | `closed = isEmpty ∘ varsOf` by fusion of a monoid homomorphism (fourteen squares `rfl`, six by `isEmpty_append`), then one line | 2 → 2 (+ 10 once for `isEmpty_append` and the six squares) | as above |

Every one of these is proved at `[propext]` or `[propext, Quot.sound]` (`U/axioms.tsv`).

**The 73 theorems that recurse or case on `Ty`**, read one by one (`U/theorems.tsv`, written by
`python3 U/scripts/theorem-lines.py` from the narrow census; the reading column is this seat's):
18 are generated already or are prism inversions the view emitter would write (382 lines: `Fold`,
`TyView`, `Derived/Program`, Lean's `brecOn.eq`, and the two `Checker` inversions); 7 are fusion
instances through `normalize` or `instantiate` (268 lines: `hasTy_normalize`, `fits_normalize`,
`fits_instantiate_widens`, `cata_admits_instantiate`, `closed_normalize`, `instantiate_closed`,
`instantiate_of_noVars`); 22 are invariant or table instances (183 lines: the `members` and
`factors` lemmas, `key_injective`, the template-calculus laws); 8 follow `sub`'s own principle and
become generic once `sub` is generated from the view (82 lines: W2's commit 2); 18
carry genuine per-constructor content and stay (958 lines: `fits_hasTy`, `fits_live`, `fits_map`,
`inhabited_of_fits`, `fits_of_inhabited_fresh`, `normal_normalize`, `ofSchema_schema`, …), their case
lists read off the algebra. Beyond those first 18, 37 of the 73 (533 lines) stop growing with
the alphabet (reading, with the four proved instances above as the evidence that the reading
holds).

---

## 6. The rule for the wave's commit 4

### 6.1 The rule, and its check

**No hand case analysis on `Ty` outside the generated folds and
`Laws/Program/Typed/Membership.lean`.** A reviewer checks it with the tree's own instruments: run
`#traversal_census Effect4.Program.Ty` and `#exhaustive_gate Effect4.Program.Ty` (and both `under
OCaml5`, `under Tools`, `under Conform`) and pass the logs to
`python3 U/scripts/check-commit4-rule.py <census.log> <census-mirrors.log>`:

- **R1** no `structural` or `wf` row: every recursive traversal is a `fold` row (through `cata_ty`
  and a named algebra) or a `generated` row;
- **R2** a `one-level` row only in a generated module or in `Membership.lean`;
- **R3** an exhaustive-gate row only there, so no hand catch-all decides a new constructor's class;
- **R4** no `structural` row in the mirror modules (`OCaml5`, `Tools`, `Conform`). The one-level
  reads there (`RowTypes.request`'s three prisms, `subMutant`'s red control) are consumers, left to
  the emitted prisms and not counted.

The check exempts by name the derived `Repr` (§6.2) and two pass-through matchers, where a `match`
on another type carries the `Ty` as a discriminant bound to a variable in every arm
(`selectRefusal.match_1`, `Decision.arms.match_4`): the gate lists them though nothing is cased,
and it does not print whether every arm binds the discriminant, so they are named. At `630e6c37`
the check reports **78 violations** (R1 21, R2 13, R3 38, R4 6; exit 1:
`U/logs/commit4-rule-baseline.log`) — the distance from the rule. On its green fixture, which
includes a pass-through row, it reports none (`U/logs/commit4-rule-green.log`). The acceptance of
commit 4 is zero.

What the commit does to get there, in the order the dependencies run:

1. **The tables.** One face table (TypeScript text, `TypeRef`, Schema node, code) and one
   classifier table (every Boolean column a hand classifier answers today, and the atom columns of
   the union spine), as JSON in the tree, emitted into Lean. Each new constructor is one row in
   each, with its wire tag and, if it is parametrised, its variance row beside them.
2. **The generated view and families** (W2's commit 2, with the `ArgF` positions of §3.5): the
   view, the prisms, the table type, the layer algebra, the head and paired folds, the reflection,
   the unfold, fusion, the banana split and the per-layer invariant.
3. **The spelling folds and the classifiers** as the tables read by the generic interpreters. On
   the LCNF route they are either expanded by the generator into structural definitions with their
   `eq_cata` connectors, or written through `cata_ty` with `@[specialize]` and the layer algebras
   `@[inline]` (D-U1).
4. **The algebra literals**, every field written: `Val.hasTy`, `inhabited`, the codec's `encodeRaw`
   and `decodeRaw` (a new constructor's field refuses by name until its own commit, row 162), and
   the transformers `normalize`, `instantiate` and `layout` (row 56's pending clause); `Fits` in
   `Membership.lean`.
5. **The two-type walks** `sub` and `infer`, from the view and the table of rules that are not
   congruences.
6. **The mirrors and enumerations**, emitted (EffGen, TsGen, the reflection, the unfold).
7. **The laws** in their family form (§5), with the per-constructor helpers they subsume deleted in
   the same commit and listed by name in the receipt (the landing style's cut-over).

### 6.2 The hand matches that remain, with their reasons

| Definition | Why it stays a hand case analysis |
| --- | --- |
| `Typed.Fits`, `Typed.FlatFits` (`Membership.lean`) | the membership judgment is the semantics: a `Prop` every typed-state proof reads through its equations; paramorphic at the handle formers (it reads the declared type); the typed state's one module (row 132) |
| `instReprTy.repr` | the derived `Repr`, until the generator emits one for the nested `Ty` (a nested `deriving Repr` goes `partial`, which the trust gate refuses; synthesis §3.3); it is a reflection, so the emitter is §3.2's |
| `instDecidableEqTy` | derived (opaque to the census); until the generated equality (seat Q's question 1) lands, then a generated two-type walk |
| the `Test` fixtures (`ExhaustiveFixture`, `TraversalFixture`) | the instruments' planted red controls: they must not track the tree |
| the counterexample models (`FitsOrder.Reviewed.Fits`, `ValueMembership.ExactSpelling.FitsInv` and `FlatFits`, `Reviewed.HandlesFit`, `InvocationContract.requestFor`) | frozen witnesses of a reviewed or proposed definition: tracking the tree would erase what they witness |
| `TyVectors.subMutant` | the assignability lane's red control: one arm deliberately wrong |

Not on the list because they are not `Ty` case analyses: `selectRefusal` and the outer match of
`Decision.arms` (pass-throughs, exempt by name in the check), `Bridge.ofSchema` (it reads a
`Representation`: the K2 read, row 128), the algebra literals of families (a) and (a-id) (an algebra
is not a match), and `Variances.heads` (a table, generated into `variances.json`).

### 6.3 Brief text for W2 and W4 (proposed)

> **W2 (commit 2), add:** the fold generator's `--extras` emission (probe U §3.2,
> `U/patches/Fold.lean`, +303/−1) extended to nested blocks with `ArgF` positions (§3.5), the
> prisms beside the view, and the table emitter (`U/patches/TableGen.lean`) for the face and
> classifier tables; one decision recorded for the LCNF route (D-U1: expansion by the generator,
> or `@[specialize]` on `cata_*` and `@[inline]` on the layer algebras). Acceptance: the generated
> module compiles; every probe U agreement theorem holds against it on today's `Ty`; the two RED
> tables are refused by name.
>
> **W4 (commit 4), add:** the rule of probe U §6.1 as the commit's acceptance —
> `check-commit4-rule.py` over the census and gate logs reports zero violations; each new
> constructor lands as one field in each of the eight algebra literals and one row in each table;
> the mirrors and enumerations are emitted (`rand_ty`, the conform vectors and the metadata samples
> reach every constructor, by `missing (enumTy …) = []`).

---

## 7. Findings on the way

1. **`Ty.renderRaw` does not escape a literal** (tested, RED in `SpellingFolds.lean`).
   `renderRaw (.lit "a\"b") = "\"a\"b\""`, which is not a TypeScript literal type; the `TypeRef`
   face escapes it (`Render.quoted`). The printed module goes through the `TypeRef` face
   (`Codegen/Print.lean:72`), so modules are unaffected; `Ty.render` text reaches the
   `typeSpelling` error messages (`Codegen/Print.lean:74`), `chunkTarget` (`Program/Ty.lean:760`),
   `generated/row-types.tsv` (`tools/Tools/RowTypes.lean`) and the assignability lane's `tsgo`
   queries (`tools/Tools/TyVectors.lean`). Latent: no vector holds such a literal. One face table
   with one escaping rule removes the second answer.
2. **`tyOcaml` writes strings unescaped** where `tyO` escapes them through `ostr` (tested, RED in
   `ReflectionsLcnfMl.lean`): the two OCaml-syntax reflections disagree on `"` and `\`. Latent: the
   rung's handles are `Ref.Ref<number>` and `Scope.Scope`.
3. **`rand_ty` never produces `lit`, `refOf`, `deferredOf`, `var` or `unknown`** (tested,
   `U/logs/ocaml-zero-coverage.log`): the wire properties have never seen five of the twenty
   constructors. The emitted generator closes it and the properties still pass. `mirrors.json`
   already records it as "a declared hole".
4. **Both copies of the conform vectors reach 15 of 20 constructors**, the same five missing
   (tested); `TyVectors.lean`'s header already extends that enumeration by hand.
5. **`Metadata.types` has one sample for each of the 20 constructors, out of declaration order**
   (`unknown` second) (reading): one more order a reader must not rely on.
6. **`Codec.layout` decides four constructors by a default** (reading, `Schema/Codec.lean:26-34`):
   its `| t => t` keeps `union`, `fiberOf`, `refOf` and `deferredOf` as written, so a literal under
   them is not widened. The docstring gives the reason for `union`; for the other three, and for
   every constructor the wave appends, the default decides. Row 56's pending clause would make it
   explicit.
7. **The LCNF translator refuses `TyAlgebra R`** (tested, §4): the constraint commit 4 must design
   around.
8. **The union-spine bottom is not a unit** (tested, §2, b2): `isTagTy (never ∪ string) = false`
   while `members` reads `[string]`. Harmless on normal forms, and the reason the spine fold is
   stated structurally rather than through `members`.
9. **Two hand `TyAlgebra` literals restate a column** (`handleFreeAlg`, `valueVarsAlg`) and one
   restates a located search (`internalHandleScan`): each is the generic algebra at a table row, by
   `rfl` (proved, `MonoidFolds.lean`).

---

## 8. Proposed lines

### 8.1 `docs/core/coherence-principle.md` (a dated addition; the file is a record)

> **Probe U (2026-10-01), for `Ty`.** C1 can be met in full for the type sort: every traversal of
> `Ty` is an algebra of `cata_ty`, with the hand exemptions traversal census §7.12 names. The
> semantic ones (`Val.hasTy`, `Fits`, `inhabited`, the
> codec's encode and decode) and the transformers (`normalize`, `instantiate`, `layout`) are
> `TyAlgebra` literals; the spelling, classifier, union-spine, reflection and enumeration
> traversals are one generic fold each over a per-constructor table (`ty-faces`, `ty-classes`) or
> over the signature alone, emitted with the one-level view from the declaration. Two traversals
> agree when their algebras do (`hom_eq_cata_ty`; 24 agreement theorems over 22 of the tree's own
> definitions). C2's fusion needs no generation of its own: fusion and the banana split are
> corollaries of uniqueness, emitted with an algebra-morphism record whose fields default to
> `rfl`, so a law through a transformer states only the transformer's overridden squares. A mirror
> is the same algebra emitted (EffGen, TsGen, Effect4Gen) or lowered (LCNF), never kept by hand;
> the LCNF route needs the fold specialized and the layer algebra inlined, or the table expanded by
> the generator (§6.1's refusal of a type-family parameter).

### 8.2 `docs/core/traversal-census.md` (a new §7.12)

> ### 7.12 The families of `Ty` (probe U, 2026-10-01)
>
> At `630e6c37` the census reads 122 takers of `Ty` (fold 5, generated 8, structural 22, wf 1,
> one-level 14) and the gate 66 matches (43 of them in 40 hand definitions, 23 of which have
> catch-alls only). Probe U places every row in one of ten families
> (`docs/research/2026-10-01-type-language-probe/U/inventory.tsv`) and proves 21 of the hand
> traversals equal to a generic fold over the emitted view, and `Val.hasTy` equal to the fold of
> its own algebra: the spelling folds are a face table read by one interpreter per face; the
> classifiers, four generic folds reading the columns of a classifier table or, for the two
> located searches, a hit predicate; the union-spine folds, one fold at four atoms; the mirrors,
> one reflection at five carriers. The rule for a constructor append is "no hand case analysis on `Ty` outside the
> generated folds and `Laws/Program/Typed/Membership.lean`", checked by `check-commit4-rule.py`
> over this instrument's output (R1–R4); its distance at `630e6c37` is 78 rows (R1 21, R2 13, R3 38,
> R4 6). The named exemptions for `Ty` are `Fits` and `FlatFits` (the typed state's module), the
> derived `Repr` and `DecidableEq` until generated, the two pass-through matchers
> (`selectRefusal`, `Decision.arms`' outer match), and the `Test` fixtures and counterexample
> models.

### 8.3 Decisions row 143 (an addition to its status)

> **Probe U (2026-10-01)**: the instrument's columns, read with the exhaustiveness inventory, give a
> constructor append its acceptance check (`check-commit4-rule.py`, R1–R4; 78 rows at `630e6c37`).
> Row 143's named exemptions for `Ty` (`closed`, `instantiate`, `infer`, `varsOf`,
> `templateAdmissible`, `sub`, `ofNormalized`) are subsumed: `closed`, `varsOf` and
> `templateAdmissible` are head folds at a classifier column (proved); `instantiate` is a
> transformer literal whose nineteen rebuilt fields the generated identity algebra names; `sub`
> and `infer` go through the generated view; `ofNormalized` would be the `TypeRef` column of the
> face table (proposed; tested only in that its printed text equals the text column's on every
> vector it spells, outside a quoted literal). The instrument would serve the rule better if it
> printed whether every arm of a match binds a `Ty` discriminant to a variable (a pass-through):
> two are named by hand today. Row 56's pending clause (a transformer names every container
> constructor) is consistent with the families: `normalize`, `instantiate` and `layout` become full
> `TyAlgebra` literals, and the identity algebra states which of their fields are rebuilds
> (fusion's `rfl` squares).

### 8.4 The new row (numbered by the coordinator; 168 would be next at this base)

> **Every `Ty` traversal an algebra; the spelling folds table-driven and generated; the mirrors the
> same algebra.**
> *Question.* Commit 4 appends the wave's constructors to `Ty`. Today each costs an arm in 17 hand
> definitions whose matches have no catch-all, a review of 23 whose matches have one, edits to 8
> mirrors, 4 enumerations that miss it silently, and a new case in each of 73 theorems. Probe U
> proves that all but the semantic algebras, the transformers and the two-type walks are generic
> folds over two per-constructor tables or the signature alone.
> *Options.* (a) Land commit 4 under probe U's rule: the tables as JSON emitted into Lean, the
> generated view and families (W2, with `ArgF` positions), the semantic algebras and transformers
> as literals, the mirrors emitted, the laws in family form; acceptance `check-commit4-rule.py` at
> zero. (b) Tables and generic folds only off the LCNF route; the definitions the LCNF cut lowers
> keep their hand arms beside `fold_of` connectors. (c) Land commit 4 by hand arms, the synthesis
> §3.3 bill.
> *Recommendation.* (a), with D-U1 decided first; (b) is the fallback if neither LCNF mechanism is
> accepted.
> *Row.* "Every traversal of `Ty` is an algebra of `cata_ty`: the semantic ones and the transformers
> as `TyAlgebra` literals; the spelling and classifier ones as one generic fold over a
> per-constructor table (`ty-faces`, `ty-classes`, generated from JSON); the reflections and
> enumerations from the signature alone. A mirror is the same algebra emitted or lowered, never kept
> by hand. A constructor append is accepted when the census and the gate show no hand case analysis
> on `Ty` outside the generated folds and `Membership.lean`."

### 8.5 Decisions for the owner

- **D-U1 — How a table-driven fold reaches the LCNF route.** (a) The generator expands the table
  into a plain structural definition and emits its `eq_cata` connector (the form the tree's lowered
  definitions have today; no compiler attribute). (b) `cata_ty` carries `@[specialize]` and the
  layer algebras `@[inline]` (tested to reach exactly the hand `renderRaw`'s externs; its effect on
  the compile time and size of the lowered engine is **not measured**). (a) puts a structural
  traversal in generated code, a fold by its emitted connector rather than by construction, which
  coherence principle §5's rule (1) admits only through that connector; (b) keeps the fold an
  algebra by construction. *Recommend (a)* for the definitions on the LCNF cut, because it is the
  form the lowered definitions already have and (b) is unmeasured; (b) nowhere until measured.
- **D-U2 — The tables as JSON or as Lean.** JSON keeps coherence principle §5's rule (a
  metaprogram's input is data in the tree) and lets EffGen and TsGen read the same rows; Lean
  literals need no emitter. One gap to close for JSON: the face table's Schema column carries Lean
  source for its constants today (`Schema.never`, `.number none [...]`), which another emitter
  cannot read; they become `Representation` values in the table. *Recommend JSON*: the emitter is
  133 lines and its red controls are its value.
- **D-U3 — Row 56's pending clause for transformers, against an identity default.** Row 143's
  receipt asks row 56 for a clause: a `Ty → Ty` transformer recursing into containers names every
  container constructor, so the next append is compile-forced there. The families can meet it (each
  transformer a full `TyAlgebra` literal) or relax it for natural maps (the generated
  `TyAlgebra.id` with named overrides, a new constructor rebuilt around its transformed children).
  *Recommend the clause as written*: `layout` shows why, since its default keeps `union`, `fiberOf`,
  `refOf` and `deferredOf` as written, a decision a default would also make silently for `record`.
  The identity algebra stays useful as the statement of naturality (the `Commutes` squares that
  close by `rfl`), not as a default.

---

## Receipt

**The one thing the coordinator must know before merging.** Probe U's generic families are proved
on today's `Ty` and emitted by a small generator patch, but the wave cannot put the definitions the
LCNF cut lowers (`Ty.key`, `members`, `normalize`, `sub`, `Val.hasTy`, `render`) behind `cata_ty`
as they stand: the translator refuses `TyAlgebra R`. D-U1 must be decided before W2's commit 2 is
briefed. D-U3 (row 56's pending clause) decides whether the three transformers are full literals;
this note assumes they are. Nothing else here waits on the owner.

**Base and head.** Branch `probe/U`, base `630e6c37`. Commits: `5ffe7f1d` (question 1), `50f14e51`
(question 2), `c18c3b60` (question 3), `cab20786` (question 4), `96172b5c` (question 5), then the
note's commit (the head; the hand-back names it). Every path was added with `git add -f` by name.
No refused permission is recorded in this seat's work.

**Changed paths.** Only `docs/research/2026-10-01-type-language-probe/U/`: `note.md`,
`inventory.tsv`, `theorems.tsv`, `axioms.tsv`, `run-lean.sh`, `rerun.sh`; `probes/` (32 Lean files,
of them `probes/ProbeU/` the importable modules); `generated/ProbeU/` (the patched generator's and
the table emitter's outputs, and the record copy's fold group); `patches/` (`Fold.lean`,
`Fold.lean.patch`, `TableGen.lean`); `tables/` (two tables, two RED tables); `scripts/`
(`inventory.py`, `gate-join.py`, `hand-lines.py`, `theorem-lines.py`, `axioms.py` with its red
fixture, `check-commit4-rule.py` with its green fixture, `emit-ocaml-ty.py`, `ocaml-copy.sh`); `ocaml/` (the
two emitted OCaml files, their diffs, the coverage instrument); `logs/`. Not committed (build
products and copies, recreated by the scripts): `olean/`, `ocaml-copy/`, `scratch/`,
`generated/Fold.zero.lean`, `generated/Fold.patched-zero.lean`. No tracked file of the tree was
edited, and no file outside this folder was written (`git status --short --ignored`, filtered to
paths outside `.lake/` and this folder, is empty).

**Commands and results** (from the worktree root; `U` = this folder; Lean with
`LEAN_NUM_THREADS=1`, warnings as errors).

| Command | Result |
| --- | --- |
| `lake env lean -DwarningAsError=true U/probes/Census.lean > U/logs/census.log` | exit 0; §1.1 |
| the same for `U/probes/CensusTest.lean` and the seven `U/probes/CensusMirrors*.lean` (one log) | exit 0 each; the first `OCaml5` run joined three imports on one line and failed at 4:26 (recorded in `census-mirrors.log`), rerun after the split |
| the same for `U/probes/ProofCensusNarrow.lean`, `ProofCensusBroad.lean` (the data probe's two verifiers, namespaces renamed) | exit 0; 44 + 29 = 73; 211 and 9, 218 either |
| `lake env lean -M 4096 --run tools/Effect4Gen/Fold.lean --group Fold --imports Effect4.Program.Eff,Effect4.Program.Ty --out U/generated/Fold.zero.lean --header-out src/Effect4/Program/Fold.lean --append tools/Effect4Gen/guards/fold.lean Effect4.Program.Ty Effect4.Program.Term Effect4.Program.CauseTerm Effect4.Program.Eff`, then `cmp` with `src/Effect4/Program/Fold.lean` (`--header-out` only names the path printed in the header) | exit 0; byte-identical (reproduced) |
| the same with `U/patches/Fold.lean` | exit 0; byte-identical (reproduced) |
| `diff -u tools/Effect4Gen/Fold.lean U/patches/Fold.lean > U/patches/Fold.lean.patch`, counted with `grep -c` and `wc -l` (`U/logs/measure-generator.log`) | 292 non-blank lines added (303 with blank lines), 1 removed; 1,385 → 1,687 |
| `sh U/rerun.sh`: the extras generator and its idempotence check, the table emitter and its two RED tables, 12 modules to oleans, 13 probes, one compiler at a time | every log ends `exit 0` except the two RED table runs (`exit 1`, as required); `gen-extras: idempotent`; 3 min 41 s |
| `lake env lean -M 4096 --run tools/Effect4Gen/Fold.lean --group RecordFold --imports ProbeU.RecordTy … ProbeU.RecordTy`, and `U/patches/Fold.lean --extras` on the same copy (`U/logs/gen-record.log`) | exit 0, 517 lines, compiled with 30 receipts (`olean-RecordFold.log`, `RecordFoldReceipts.log`); exit 1, refused by name |
| `lake env lean -M 4096 --run src/OCaml5/Tools/LcnfGen.lean --out U/ocaml/lowered/… --import ProbeU.Lowering --cap 400 <roots>` for `renderTable`, `renderTableS`, `renderTableI` and `Ty.renderRaw` (`U/logs/lcnf-lowering.log`) | refused (`TyAlgebra R`) twice; then closures of 33 and 14 constants that stop at the same four extern todos; no OCaml written |
| `bash U/scripts/ocaml-copy.sh` (`opam exec --switch=effect4 -- dune build`, `dune test eff`, `dune test engine`, in `U/ocaml-copy`) | §4: 15 → 20 of 20 constructors; 6,250 checks pass in both arms; engine summaries equal; one environmental FAIL in both |
| `python3 U/scripts/inventory.py`; `gate-join.py`; `hand-lines.py`; `theorem-lines.py`; `axioms.py`; `axioms.py U/scripts/fixtures/axioms-red` | 106 rows; 66 = 9 + 14 + 43, 17 and 23; 353 + 38 lines; 73 theorems read; 97 receipts and no theorem without one, exit 0; the red fixture refused, exit 1 |
| `python3 U/scripts/check-commit4-rule.py U/logs/census.log U/logs/census-mirrors.log`, and on `U/scripts/fixtures/census-green.log` | 78 violations, exit 1 (the red baseline); 0, exit 0 |
| `grep -rn -E` for `sorry`, `native_decide`, `partial`, `unsafe`, `simp_all`, `implemented_by`, `extern`, `first \|`, `try` over `U/probes`, `U/generated/ProbeU`, `U/patches/TableGen.lean`, and for `simp` without `only` | one hit, the word `partial` in a docstring; every hand `simp` is `simp only`. The generator copy `U/patches/Fold.lean` keeps the committed generator's own `partial` definitions; the patch adds none |

**Axioms.** 97 declarations of the probe carry a receipt (`U/axioms.tsv`, by
`python3 U/scripts/axioms.py`): 49 `[propext]`, 30 none, 15 `[propext, Quot.sound]`, and 3
`[propext, Classical.choice, Quot.sound]` — `tyJson_eq`, `tyO_eq` and `tyT_eq`, each inheriting
`Classical.choice` from the tools-side definition it is about (`Tools.ProfileJson.tyJson`,
`OCaml5.Eff.tyO`, `Conform.Effect4.LcnfMl.tyT`), whose own receipts are printed in the same logs;
those modules are outside the axiom gate's `Effect4.*`/`Test.*` audit. `axioms.py` also refuses a
theorem in the probes or the generated modules whose receipt no log prints: none in 36 files
(`U/logs/axioms.log`); its red fixture is refused (`U/logs/axioms-red.log`, exit 1).

**Bounded or host-only.** The agreement theorems and the laws are universal (proved for every
`Ty`). Tested and bounded: the printed-face agreement and `tyOcaml` on finite vector sets; the
enumerations' reach; the OCaml runs (seed 42, host `dune` under the `effect4` switch, one
environmental FAIL in both arms); the LCNF runs stop at extern todos, so no OCaml from the table
fold was compiled or run. Assumed: `fits_normalize` at five squares; the size of the `ArgF`
extension (150 to 200 lines); the effect of `@[specialize]` on the lowered engine.

**Proposed decisions rows and brief text.** §8.3 (row 143), §8.4 (the new row), §8.5 (D-U1 to
D-U3), §6.3 (W2 and W4 brief text); the coherence-principle and traversal-census lines in §8.1 and
§8.2.

**Open obligations.** The nested extension of the extras emitter (§3.5); the prisms in the emitter;
`fits_normalize` by fusion, proved; a generated `Repr` for the nested `Ty`; D-U1's measurement if
(b) is chosen; the Schema column of the face table as data (D-U2); the two escaping defects (§7)
belong to whichever commit lands the face table.
