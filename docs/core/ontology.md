# The do-now set probed, what to wipe, and the estate's ontology stated formally (2026-09-17)

Owner's asks, after the one list: probe the "do now, no rulings needed" rows to see whether they
are that simple; say honestly where starting from scratch is easier ("`Api.schemaOf`, I'm fine
wiping that, and any other services that are more trouble than they're worth; we do not want to
be wedded to arbitrary gates and tests passing versus getting the core constructs coherent"); and
address the ontology note pasted mid-turn ("The Grand Architectural & Semantic Ontology") and
frame it formally. Tree at `e6724a05`. Every count below was measured on the tree, not read from
a note.

## 1. The answer in one paragraph

Of the fourteen do-now rows, six are as simple as the list said (6, 8, 13/36, 23 as a *delete*,
24, 37), one is mechanical but a little larger (17), and seven are not what the list said: row 3
has no consumer and touches 24 match arms in 11 files; row 5's exactness law for the JSON codec is
*false* as stated (object field order), and its gate is a day of TypeScript harness work that
would be the only consumer of the whole schema line; row 16 is a proof-churn refactor (206
references in 47 files, most of the Laws tree); row 34's honest exemption count is about twenty,
not six, once Laws is counted; row 35 is already gated by the cases policy; rows 2(c) and 6
contradict each other; row 18 waits on an owner row. The thing to start from scratch is the
**Schema layer**: 7,743 lines under `src/Effect4/Schema` of which the rest of the estate calls
about 1,200; the other 6,500 (`Check`, `EffectfulField`, `Endpoint`, `Transform`, `Image`, most of
`Annotations`, the generated `Fold`) are the September-11 cutover wave's contract machinery,
called by nothing outside their own tests, and the value layer (`Store/Shape.lean`) imports all
of it for one function. Wipe them with their twenty test modules, three harnesses and one gate;
keep the five files that carry the estate's two real schema claims. Then the ontology note's
frame is right in its two halves (syntax initial, behaviour observed) and wrong in its
conclusion (adopt all 37): under "one free object per sort, everything else an exact embedding
or a fold", the measure of coherence is the number of representations per sort, and the note's
plan *raises* it in the type sort. §5 gives the frame as a signature, five arrow kinds with
their obligations, and the per-sort census as it stands.

## 2. The do-now rows, probed

| row | what the list said | what the tree says | verdict |
| --- | --- | --- | --- |
| 3 `Ty.app` | "five additions and one wire tag" | a new `Ty` constructor is matched in 24 arms across 11 files (`Codegen/Types`, `TypeAlgebra`, `Admission`, `Derived`, `Eff`, `Fold`, `Ty`, `Typed`, `Typing`, `Schema/Bridge`, `Schema/Codec`) plus `key_injective` (`Ty.lean:196`), `Codec.layout`/`isSupported`, the S1 wire tag and the corpus pin. Its only consumer is row 32 step 5 (`Ref`/`Deferred`/`Queue` vendored as `Ty.app`), which is months away | **defer to the consumer** — adding a constructor with no user is the definition of speculative structure |
| 5 D12 pair + S-5 gate | "the pair and the gate, as two claims; do" | Lean side: soundness exists (`Laws/Schema/Codec.lean:61 decode_encode`, and `encode_injective`, `hasTy_decode`). The *exactness* direction `decode t j = some v → encode t v = some j` is **false**: `Codec.fields?` (`Codec.lean:70`) is order-insensitive, so `{"value":…,"_tag":"Some"}` decodes and re-encodes as `{"_tag":"Some","value":…}`. rc.112's decoder is also order-insensitive, so refusing non-canonical order would diverge from the host. The true statement is exactness modulo `Json` canonical order, or nothing beyond soundness. The S-5 gate (every recorded corpus exit decodes under its program's published `Schema.Exit`) is real work in `harness/truth`: generate the `Exit` schema text per corpus program through `Codegen/Schema`, run rc.112's `decodeUnknownSync` on the recorded exit JSON — about a day | **restate, then do the gate only if the schema line survives §3** — it is that line's only consumer |
| 6 `ofSchema` refuses | "do first" | `Bridge.ofSchema` (`Bridge.lean:63-110`) — add `checks = []` / payload guards, about twenty lines; `ofSchema_schema` (`:113`) is unaffected. **But** row 2(c) puts record names in *annotations*, and exactness (`ofSchema r = some t → r = schema t`) forces `ofSchema` to refuse or strip annotations. The two rows contradict unless exactness is stated modulo annotations | **do, with exactness stated modulo annotations** — one theorem, not two rows |
| 8 `effDocument` key, `ShapeDoc.document` dedup, docstrings | "fix all three now" | `Bridge.lean:162` keys `s!"service_{k.name.value}"` — half a `ServiceKey`, confirmed; `Shape.lean:468` repeats keys, confirmed | **do** — thirty lines |
| 13 / 36 vocabulary | "write it into `AGENTS.md`" | writing | **do**, with §5 as the text |
| 16 `Await` a structure | "do — the most-read field prints as nested arrays" | `abbrev Await := FiberId × Nat × NativeOp × Val` (`Admit.lean:37`); 206 references in 47 files, 30 of them in `Laws/`; 351 `.2.1`/`.2.2`-style projections in `src` (not all `Await`, but the Laws tree's guard and simulation files are where they concentrate). `Prod.mk.injEq`, anonymous-constructor patterns and projection lemmas all change | **not a do-now** — a multi-day proof refactor. The boundary benefit costs nothing if `Observation.awaiting` carries a *view* (`structure AwaitView`, a fold out of the tuple) — which the principle permits: a view is an algebra, not a second free object |
| 17 `Canonical FiberStatus` / `Observation` | "two manifest lines" | `Observation` lives in `Effect4.Run`, above `Api.RunnerDerived`, so it is a new manifest group (`Run`, importing `Effect4.Run`), not two lines in `Runner`; `Key` and `FrontierReason` need instances too; the manifest comment says a group is "an entry here and no code change in the driver" | **do** — half a day with regeneration |
| 18 tying proofs | "do with rows 14 and 16" | `digest_inj` needs `Built.digest`, which is row 14 (owner). `observe_inspect`, `observe_daemonsQuiet` are unfoldings. `build_check` is unnecessary if row 23 is a delete | **two of four now**; the rest follow their owner rows |
| 23 `Api.author` beside `Author.program` | "two verbs, one pipeline, tied by `build_check`; no cut" | `Api.author` (`Api.lean:504`) returns `Typed table` (typing only); `Author.program` returns `Built` (typing + admission). Callers of `Api.author`/`AuthorRefusal`: two test files, ten sites | **delete `Api.author` and `AuthorRefusal`** — one verb, no tying proof owed |
| 24 minted spellings | "one regeneration; the red control is pinned" | `Sugar.lean:26,37`, `Loops.lean:34-35`, `tools/Effect4Gen/Forms.lean` → regenerate `Authoring/Forms.lean` and `Laws/.../Forms.lean`; `var_push_minted` then covers every convenience | **do** — half a day; `make check-gen` after |
| 34 traversal census + fusion | "one generated table and one generator change; six exemptions" | The census is a new meta instrument (walk the environment, keep definitions whose domain is an `Eff` family, check the body's head is `cataFam`), ~150 lines in the style of `Laws/Auto/Census.lean` — not a table. Definitions in `src` that match on `NativeEff`: **26, of which 21 are in `Laws/`** (`denoteR`, `evaluateR`, `interpR`, the guard-state functions, …). F's six counts only non-Laws. Fusion for `Eff`: the `Doc` pattern in `tools/Effect4Gen/Fold.lean` transfers, half a day | **do as an instrument first** (`#traversal_census`, like `#auto_census`), print the honest number, and decide about a gate after seeing it |
| 35 fragments by exclusion | "a new constructor silently leaves both fragments today" | `Straight`'s `| _ => false` is registered in `tools/Conform/Effect4/cases-policy.json:1080` with a thirteen-name cover list; a new constructor changes the absorbed set and `check-cases` refuses until the policy names it. `Looped` (`DenoteB.lean:123`) has no default arm — its last clause delegates to `Straight` | **already gated**; the rewrite is a ten-minute style choice, not a coherence gap. Drop the row |
| 37 CI | "repaired" | Every run since `78684a8` fails with "workflow file issue" — no job has started (`gh run view 35163097427`). The commit added `LAKE_CACHE_KEY: lake-${{ runner.os }}-${{ hashFiles(...) }}` at **workflow-level `env`**, where `hashFiles` (and `runner`) are not available; that is the parse failure. Move the key into each job's cache step | **do** — one edit; the owner pushes |

Two contradictions the list did not see, both in group A: row 2(c) against row 6's exactness
(annotations), and C3's exactness against the JSON codec's order-insensitivity. Both resolve the
same way: exactness is stated *modulo* a named normalisation (annotations stripped; JSON fields in
canonical order), which is the ordinary form of the law for a codec whose reader is deliberately
lax (Rendel–Ostermann's partial isomorphisms are stated up to the normaliser).

## 3. Where to start from scratch: the Schema layer

### 3.1 What is there

`src/Effect4/Schema/` is 7,743 lines in thirteen files, plus `Codegen/Schema.lean` (472),
`Codegen/EffectfulField.lean` (192), `Arch/Accepts.lean`, the generated
`Store/Derived/Schema.lean`, twenty test modules (`Test/Schema/*`, `Test/Counterexamples/Schema/*`,
`Test/Codegen/SchemaGeneration*`), three harnesses (`harness/schema-annotations`,
`harness/schema-effectful-field`, `harness/schema-generation`), a pinned host
(`harness/schema-host`) and four Makefile gates (`schema-codec`, `schema-ts`, `schema-pins`,
`schema-host`).

### 3.2 What the rest of the estate calls

Measured by grep from outside `src/Effect4/Schema/` and outside tests:

| called | by | lines |
| --- | --- | --- |
| `Bridge.schema`, `ofSchema`, `effDocument`, `rowDocument` (`Ty → Representation` and back) | `Api`, `Codegen`, the batteries | 223 |
| `Codec.encode`/`decode` (`Ty`-directed JSON; the `schema-codec` gate against rc.112's `toCodecJson`) | `Api`, `harness/truth` | 249 |
| `Store.render`, `ShapeDoc.document` (`Shape → Representation`) | `Store/Shape.lean:425-470` | ~50 |
| `Codegen.Schema.representation`/`documentExpr` (`Representation → Schema.* text`; the `schema-ts` gate, three fixtures) | `Api.schemaDocument`, the harness | 472 |
| the `Representation` carrier, `Document`, `Payload`, and their generated `Canonical` instances | everything above | ~700 of `Representation.lean`'s 1,250 (the rest is the tag census's 46 theorems), 103, 425 |
| `Authoring.lean`'s smart constructors (`Schema.struct`, `Schema.property`, `Check.int`, …) | `Store.render` | ~120 of 241 |
| `Annotations.identifierKey`, `refKey`, `Representation.nodeAnnotations` | `Store/Shape.lean`, `Derived/Schema` | ~60 of 1,193 |

About 1,200 lines carry the estate's two real schema claims: the `Ty` codec agrees with rc.112
(`schema-codec`), and a `Document` printed as `Schema.Struct` text decodes in rc.112 (`schema-ts`).

### 3.3 What nothing calls

| file | lines | what it is | who calls it outside its own tests |
| --- | --- | --- | --- |
| `Check.lean` | 1,499 | the SC-REP-04 "persisted/decode-side field admission" judgment (`fieldAdmissible`, Prop + Bool + agreement), 64 theorems | nobody — `Store.render` uses the *constructors* `Check.int`/`Check.pattern`, which are `Authoring.lean`'s, not this file's |
| `EffectfulField.lean` | 960 | effectful getters over annotations; **imports the standalone `Effects` package** (`Effects.Algebra.Laws`, `Effects.Flow.Block`) — a second effect algebra inside the core's import closure | `Codegen/EffectfulField.lean` and its harness only |
| `Endpoint.lean` (deleted 2026-09-18) | 383 | `Endpoint`/`ApiSpec`/`SchemaFn`/`SchemaTransform`: a second authoring plane ("fluent metadata and typed ports to machine `Row`s"), written before `ServiceDef`/`Row.host`/`Author.build` existed | exported from `Api.lean:603`; no application, one test |
| `Transform.lean` (deleted 2026-09-18), `Image.lean` | 151 | `Transform σ Γ A B E R` (a certified `Eff` in a wrapper), `ProgramImage` | exported from `Api.lean:605`; `Laws/Schema/{Transform,Image}` (four theorems); no application |
| `Annotations.lean` (most) | ~1,130 | typed annotation keys with `Optic`s, the "annotation data plane" | see 3.2: two keys and one optic |
| `Fold.lean` (generated) | 1,066 | `RepresentationAlgebra`, `cata_representation` | `Check`, `Annotations`, `EffectfulField`, and one printer (`Codegen/Schema.lean:236 printAlgebra`) |
| `Arch/Accepts.lean` | — | `accepts : Document → Json → Bool`, a **third** value-fits-schema checker beside `Check.fieldAdmissible` and `Codec.isValue` | the `Runner` battery |
| `Api.schemaOf` (`Api.lean:138`) | 3 | `(typeOf …).map EffTy.document` | nobody (`RunnerBytes.schemaOf name` is a different function with the same name) |

And the import direction is backwards: `Store/Shape.lean` — the value layer — imports
`Schema.Authoring → Check → Document → Annotations → Fold → Representation`, five thousand lines,
for `render`. The value sort sits *above* the schema sort because one algebra out of `Shape`
was written into `Shape.lean`.

### 3.4 The recommendation

Wipe, in one commit series with narrow builds:

- `Schema/Check.lean`, `Schema/EffectfulField.lean`, `Schema/Endpoint.lean`,
  `Schema/Transform.lean`, `Schema/Image.lean`, `Codegen/EffectfulField.lean`,
  `Arch/Accepts.lean`, `Laws/Schema/{Transform,Image}.lean`, `Api.schemaOf`, the two `export`
  lines in `Api.lean:603-605`;
- their tests: `Test/Schema/EffectfulField*Contract.lean`, the predicate half of
  `Test/Schema/AuthoringContract.lean` (`Predicate.decide/and/contramap`, `Schema.check` — they
  are `Check`'s), `Test/Counterexamples/Schema/*` (eleven), and the `Endpoint`/`Transform`
  sections of `Test/Codegen/SchemaGenerationContract.lean`;
- `harness/schema-annotations`, `harness/schema-effectful-field`, the `schema-host` gate and its
  two scripts. `harness/schema-host` (the pinned host, TypeScript 7 + tsgo) **stays**: it is what
  `scripts/check-schema-typescript-generation.sh:6` runs the kept `schema-ts` gate on;
- `Annotations.lean` cut to the carrier (`AnnotationEntry`, `Annotations`), `AnnotationKey` with
  its two laws, `identifierKey`, `refKey`, `nodeAnnotations` — about 150 lines; the `Optic` import
  goes with the rest;
- `Schema/Fold.lean` regenerated only if `Codegen/Schema.lean`'s printer keeps using it (it is
  one fold; a hand `match` over 22 constructors is honest and the cases gate covers it) —
  otherwise the `SchemaFold` manifest group is deleted;
- `Store.render`/`ShapeDoc.document` move out of `Store/Shape.lean` into `Schema/OfShape.lean`,
  so `Store` no longer imports `Schema`; `Codegen/Schema` and `Api` import `OfShape`.

Keep: `Representation.lean` (trim the tag-census theorems to `tagName_ofTagName` and its
inverse), `Payload`, `Document`, `Authoring` (constructors), `Bridge`, `Codec`,
`Codegen/Schema`, `Derived/Schema`, the `schema-codec`, `schema-ts` and `schema-pins` gates,
`Test/Schema/{Representation,Payload,SubAlphabet,Dialect,AnnotationDataPlane}Contract.lean`
(`SubAlphabet` is the tag census's battery; `Dialect` pins the one square that relates the
store's `Shape` to the program's `Ty` through `Representation` — keep it; the last trimmed with
`Annotations`), `Test/Codegen/SchemaGeneration{Contract,Coverage}.lean`.

What this costs: 64 theorems about a judgment nobody uses; the effectful-getter dogfood; a
second authoring plane the real one replaced; four theorems about `Transform`. What it settles
without a ruling: row 4 (three checkers become one — `Codec.isValue`, with `Shape.fits` on the
value side), row 12 (`Transform` gone; its category laws become the three `denote` equations of
§5.4, stated at `Eff` where they belong), the `Transform` half of row 13, and row 9 (deleted; the
publisher of the exit schema is `EffTy.document` and its consumer is the S-5 gate). Row 1 (the
AST carrier) then waits for the first *foreign* schema actually read, which is row 32 step 2.

Two smaller from-scratch candidates, for their owner rows: `Api.lean` (row 19 — the three root
modules should be written fresh and `Api.lean` left with what they import, rather than moved), and
`Await` (row 16 — a view, never a refactor).

## 4. The ontology note, checked

The pasted note is grounded: `hom_eq_cata_eff` is at `Fold.lean:1172`; `run_eq_meaning` at
`Laws/Program/Agreement/Machine.lean:1896` (the note drops `Laws/Program/`); `Val.tagPayload?` is
`Decision.lean:31` (the note's "`Decision.tag`" is that function); the race literal
`⟨true, true, .interruptible⟩` is in `Laws/Program/Guard/Core.lean:3604-3616` (nine sites, as the
list said); `Machine/Supervision.lean` exists. Its two halves — syntax as initial algebras,
behaviour as coalgebras — are scout F's principle with the second half named correctly (Rutten
2000 is the right citation; F said "observed, not constructed" without the name). Four places it
overreaches, each fixed in §5:

1. **"Two objects, three kinds of arrow."** It then uses four (fold, exact embedding, simulation,
   monoid action) and drops elaboration, which is neither: `Src → Except Refusal Eff` is a
   Kleisli arrow whose obligation is a *located* refusal (`explain_none_iff`). Five kinds, as F had.
2. **"Graded Freyd category."** A Freyd category is a pure category with a premonoidal structure
   and an identity-on-objects functor into the effectful one; a *graded* one (Katsumata 2014)
   indexes arrows by a monoid of effects. Today `Transform.id`/`andThen` have **no laws** (row 12
   is exactly that they are missing), so what exists is a typed quiver, not a category. The
   claim is a target, and it is a target for `Eff` itself, not for a wrapper: §5.4 states it.
3. **"Uniqueness needs no pairwise agreement proofs."** True for two *folds* out of the free
   object. The 1,900-line proof is `compileEff` (not a fold, kept exempt by the note itself)
   against `denote`: a simulation, which uniqueness never touches.
4. **"Idempotence with respect to committed truth."** `check-gen` checks that the committed tree
   is a *fixed point* of the generator; idempotence (`gen ∘ gen = gen`) is not the property.

And its conclusion — adopt all 37 — is additive on every row. Under its own principle the measure
of coherence is the number of representations per sort; its plan keeps `Representation` and adds
the AST, keeps `Check`/`Accepts`/`Codec.isValue`/`hasTy` and adds `Check.holds`, keeps `Transform`
beside `Eff`, restructures `Await`. §3 is what the principle actually asks for.

## 5. The frame, formally

### 5.1 Sorts and free objects

Six sorts. For each, one free object, presented by a signature Σ written as data where the
generator can read it:

| sort | free object | signature as data | fold |
| --- | --- | --- | --- |
| program | `Eff` (`Program/Eff.lean:301`) | `binders.json` → `LayerView` (`ArgSort`, `argSorts`, `makers`) | `cataFam`, unique by `hom_eq_cata_eff` |
| type | `Ty` (`Program/Ty.lean:23`) | its inductive (no data signature yet) | hand folds; a `TyAlgebra` is one generator run |
| value | `Store.Val` | its inductive; `Kind`/`Shape` classify it | `Canonical` instances are the algebras |
| syntax | `TypeScript.Expr` (vendored) | vendored | `print`/`read` calculus over the template table |
| code | LCNF (Lean's) | Lean's | `translateClosure` |
| run | `List Command` (free monoid on `Command`) | `Runner` group | `Play` — the monoid action |

The machine's *state* (`Machine`, `Run`) is not a free object; it is a coalgebra `S → Ω × S^Command`
(observe, step) — a Moore machine. The two halves meet at the journal: `replay_unique` and
`journal_replays` say every reachable state is the image of a unique word of the free monoid, so
the run face is on the initial-algebra side after all, and only the machine's internal `step` is
coalgebraic. That is why `Run` can be data (the journal) while `Machine` cannot.

### 5.2 Five arrow kinds and their obligations

| kind | shape | obligation | proved instances | instances lacking their obligation |
| --- | --- | --- | --- | --- |
| K1 fold | `cataFam alg : F → A` | being an algebra (uniqueness is free) | ten algebras (F §3.1) | `denote`, `effTy`, `compileEff`, `explain`, and ~20 Laws-side traversals — the honest exemption list |
| K2 exact embedding | `write : A → F`, `read : F → Option A` | total; `read (write a) = some a`; `read v = some a → v ≡ write a` *modulo a named normaliser* | `Canonical` (`ofVal_toVal`, `ofVal_exact`); `read_print`, `read_exact` on the readable domain | `Ty ↪ Representation` (exactness, row 6, modulo annotations); `Val ↔ Json` via `Codec` (exactness modulo field order — false without the modulus) |
| K3 simulation | two behaviours, one observation `obs`, `obs ∘ f ≈ obs ∘ g` on a named fragment | the fragment named by exclusion or by policy | `run_eq_meaning` on `Straight`, `loopAgreement` on `Looped` | LCNF → target (tested on 20,387 vectors, no theorem — row 28); machine → rc.112 (the truth lane, tested) |
| K4 elaboration | `Src → Except Refusal F` (Kleisli) | refusal located and complete: `explain = none ↔ wellTyped` | `explain_none_iff`, `authoring_scoped`, `open_total` | none known |
| K5 monoid action | `List Command × S → S` | `replay_unique`, `journal_replays` | both | none |

### 5.3 Coherence as a census

For each sort, count representations. The principle allows exactly: one free object, plus any
number of K2 embeddings *with all three laws*, plus folds (which are views, not representations).
Anything else is a leak. The census at `e6724a05`:

- **program**: `Eff`; `Transform` (a wrapper — a second spelling of the hom-sets, §3 deletes it);
  `NCode` (K3 image, fine); `Src` (K4 source, fine).
- **type**: `Ty`; `Representation` (K2 without exactness — row 6); `TypeRef` (a fold, fine);
  `EffTy`, `Document` (folds, fine). The AST would be a second K2 target.
- **value**: `Val`; `Json` by four images (C4 — row 10, owner's); `Shape` is a classifier, fine.
- **value fits type** (a relation, but it is where the water pools): `Val.hasTy` over `Ty`;
  `Codec.isValue` over `Ty` × `Json`; `Schema.Check.fieldAdmissible` over `Representation`
  (unused); `Arch.accepts` over `Representation` × `Json` (unused); `Shape.fits` over `Shape`.
  Five predicates over three type-representations. §3 leaves two (`hasTy` and `Shape.fits`,
  one per classifier) plus `Codec.isValue`, which is `hasTy` conjoined with the round trip.
- **syntax, code, run**: one each.

So the leak is entirely in the type sort and its checkers, which is where §3 cuts.

### 5.4 The program category, stated at `Eff` (what "graded Freyd" would mean)

Objects: `Ty`. For a signature σ and context Γ, `Hom(A, B)` is the set of `p : Eff` with
`effTy σ (Γ ++ [A]) p = some ⟨B, E, R⟩`, *graded* by `(E, R)` in the join-semilattice
(`Ty.union`, `Requirement.union`) — the grade of a composite is the join. Identity is
`succeed (var 0)`; composition is `bind`. The three laws, at the meaning:

```
denote (bind (succeed x) f)  =  denote (f x)
denote (bind p succeed)      =  denote p
denote (bind (bind p f) g)   =  denote (bind p (fun x => bind (f x) g))
```

These are statable today on the `Looped` fragment (`Denote` is compositional in `bind` by
definition) and become one-line consequences of `denoteAlg` once row 30 lands. The *pure*
subcategory a Freyd category needs is the image of `sync` (Lean functions `Val → Val`), which is
what `SchemaFn` was reaching for; it needs no wrapper. The premonoidal structure is `select`'s
tagged pairing. None of this needs `Transform`, `Endpoint` or `SchemaFn` to exist.

### 5.5 Metaprogramming

Stage 0 is the tables (`binders.json`, `manifest.json`, the template table, `cases-policy.json`);
stage 1 is the generated Lean; the obligation is that the committed tree is a fixed point of the
generator (`check-gen`), and every generated declaration is a fold or an embedding of §5.2 —
which is what keeps the sugar inside the proofs (the LCNF survey §5: the sugar is upstream, it
writes Lean; the roots list is its only contact with lowering).

## 6. The order I would take

1. **§3's wipe**, one commit per deleted family with a narrow build of each importer and one gate
   sweep at the end; the three harness gates and their scripts go from the Makefile in the same
   series. `Store.render` moves out of `Shape.lean` first (it is the import cycle's cause).
2. **The simple six**: rows 6 (with exactness modulo annotations), 8, 23 as a delete, 24, 37, 17.
3. **Row 5 restated**: exactness modulo canonical field order (or soundness only, said so), and
   the S-5 gate as the schema line's consumer — now the only thing the kept 1,200 lines are for.
4. **Row 34 as an instrument**: `#traversal_census`, the honest number, then the gate question.
5. **Skip** 3 and 35; row 16 as a view; row 18's two unfoldings with 17.
6. Then group B's owner rows (14, 15) with the observation dogfood as their receipt.
