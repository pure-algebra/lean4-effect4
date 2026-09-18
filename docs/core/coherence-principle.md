# The organizing principle: initial algebras for syntax, observations for behaviour, coherence as uniqueness (scout F, 2026-09-17)

**The answer, in one paragraph.** The estate has exactly two universal properties and is already
living off them without saying so. Everything the owner calls a *representation* is either a **free
object for a signature given as data** (`Eff`, `Ty`, `Term`, `CauseTerm`, `Representation`, `Val`,
`List Command`, LCNF `Code`) or a **retract of one** (`Ty` in `Representation`, a `Canonical`
carrier in `Val`, the readable programs in TypeScript `Expr`). Everything the owner calls a
*translation* is either an **arrow out of a free object**, whose obligation is that it *be* an
algebra — after which uniqueness (`hom_eq_cata_eff`, `Fold.lean:1172`; `replay_unique`,
`Laws/Api/Runner.lean:157`) equates any two arrows with the same algebra, with no proof per pair —
or an **arrow into a behaviour**, whose obligation is a relation preserved by every step and
reflected in the observation (`run_eq_ref`, `RuntimeR.lean:211`; `run_eq_meaning`,
`Agreement/Machine.lean:1896`). So "coherent" means one checkable thing: **every traversal of a free
object is a declared algebra, and every square of such traversals commutes by uniqueness rather than
by a proof of its own.** The water is held not by adding proofs but by moving arrows onto the fold:
the three traversals carrying the most meaning — the denotation (`Laws/Program/Denote.lean:66`), the
checker (`Program/Typing.lean:284`), the compile (`Program/Compile.lean:549`) — are hand-written
`match`es containing the string `cata_eff` zero times, so nothing structural forces them to cover
the same 25 constructors, and each new constructor costs three independent edits and a fresh
agreement proof. Thirteen arrows in §2 lack the obligation their kind demands and three more carry a
differential in place of one; §3 proposes seven commuting squares as the gate; §4 defends
initial-algebra semantics (Goguen–Thatcher–Wagner–Wright 1977) against the three plausible
alternatives; §4b rules for **(ii)** — Schema is a data language whose effectful slots are holes
filled by our programs — because a `SchemaGetter.Getter` is a host closure with no initial-algebra
presentation, and adopting it as our program language would delete every fold in the estate.

**Evidence words.** *Proved* = a Lean theorem here whose statement I read. *Stamped* = I ran a probe
and hold the output. *Tested* = a finite run recorded in the tree. *Assumed* = no proof, no check.
*Reproduced* is unused: I re-ran nothing the tree already claims.

## 0. What is stamped

One probe in `/Users/pooks/Dev/lean4-effect4-scout-f` on the warm cache: `#print axioms` on the
headline theorem of every arrow kind; all twenty-eight are at or under the ceiling. `[propext]`:
`hom_eq_cata_eff`, `cata_build`, `build_view`, `ofSchema_schema`. `[propext, Quot.sound]`:
`effTy_sound`, `effTy_complete`, `effTy_eq_hasTy`, `hasTy_unique`, `run_eq_meaning`, `loopAgreement`,
`meaning_typed`, `meaning_never_wrong`, `run_typed`, `meaningB_typed`, `meaningB_never_wrong`,
`run_eq_ref`, `read_print`, `read_exact`, `print_of_readable`, `roundTrip_of_readable`,
`readable_of_Readable`, `printModule_roundTrip`, `emitModule_complete`, `decode_of_encode`,
`decode_encode`, `encode_injective`, `replay_unique`, `journal_replays`, `drive_eq_play`. No `sorry`
and no declared `axiom` under `src/` or `tools/`. Counts stamped: 67 template rows over 4 families,
18 classified (`Codegen/Templates.lean:240`); 25 `Eff` constructors, 7 families (`Eff.lean:559`,
`LayerView.lean:187`); 400 corpus programs, 127 printing a declaration, of those 121 agreeing on the
run and 110 on the type (`harness/truth/corpus-results.tsv`).

## 1. The kinds of object

Not six kinds. **Two**, plus a construction on them.

**(A) Free objects for a signature given as data.** A signature is families × constructors ×
argument sorts. The estate writes it down twice: as Lean inductives, and as *data* — `ArgSort`
(`LayerView.lean:33`), `argSorts` (`:120`), `ctorNames` (`:187`), `makers` (`:204`) — with the
structure map `build` (`:278`), its inverse `view` (`:609`), and the two theorems that make the pair
a presentation of the initial algebra: `build_view` (`:620`) and `cata_build` (`:481`, the fold of a
built node is the algebra on the folded arguments). That is a *universe of descriptions*
(Benke–Dybjer–Jansson 2003; Chapman–Dagand–McBride–Morris 2010), and `view`/`build` is Wadler's view
(1987) with Gill–Launchbury–Peyton Jones's `build` (1993) — the fusion equation those two exist for
is still missing (§2 row 19).

| object | free object | signature as data | uniqueness |
| --- | --- | --- | --- |
| programs | `Eff Op` + 6 families, 25+6+2+2+16+10+2 ctors (`Program/Eff.lean:301`) | `LayerView.lean:120-274` | `hom_eq_cata_eff` (`Fold.lean:1172`), one per family |
| types | `Ty`, 16 ctors (`Program/Ty.lean`) | `TyAlgebra` (`Fold.lean:31`) | `hom_eq_cata_ty` (`Fold.lean:89`) |
| pure values | `Term`/`Terms`, `CauseTerm` (`Eff.lean:251`, `:271`) | `TermAlgebra`, `CauseTermAlgebra` | `hom_eq_cata_term`, `…_cause` |
| schemas | `Representation`, 22 tags (`Schema/Representation.lean`) | `Schema/Fold.lean` (1,066 lines) | fold exists; **no `hom_eq` law** |
| stored values | `Val` (`Store/Val.lean`) | `Shape`/`ShapeDoc` (`Store/Shape.lean`) | `Val.decode_encode`, `Val.decode_exact` |
| journals | `List Command`, free monoid, one generator | — | `replay_unique` (`Laws/Api/Runner.lean:157`) |
| code | LCNF `Code .pure` | Lean's compiler | outside our trust; `Conform.Lcnf.Semantics` is our reading |
| target syntax | `TypeScript.Expr`, `Ml.Syntax`, `Target.Expr` | vendored / `Conform.Lcnf.Target` | none: codomains, not sources |

**(B) Behaviours — observed, not constructed.** The machine, the term reference and a `Run` are not
free objects. They have an *observation* (`obs`, `classify`, `Run.observe`, `behaviour` at
`Laws/Api/Runner.lean:168`), and the only statements available about two of them are relations
preserved by steps and reflected in that observation. `run_eq_ref` is exactly that: `classify` and
`obs` agree because `ReplayRel` holds at the load and is preserved by every command. This is
universal coalgebra (Rutten 2000; Jacobs 2016) and forward simulation (Lynch–Vaandrager 1995), and
the estate is right to state it as a relation. Where it does give an equation (`run_eq_meaning`,
`loopAgreement`) that is a simulation collapsed at the exit, on a named fragment.

**(C) Retracts and exact embeddings.** Every "same thing in another form" is a (write, read) pair
between objects of (A), with one to three laws. `Canonical` states all three as *class fields*, so an
unlawful instance cannot land (`Store/Canonical.lean:32-46`: `ofVal_toVal`, `ofVal_exact`, `fits`) —
a lawful `Prism` (Pickering–Gibbons–Wu 2017). `Ty` inside `Representation` is an *ornament* (McBride
2011): information added, forgetful fold back (`ofSchema`). Print/read is the same kind in the syntax
direction, and is exactly Rendel–Ostermann's invertible syntax description (2010).

The brief's other candidates are not separate kinds. Free monads and Elgot iteration are models, not
objects: `Eff` is syntax with **no equations**, and the monad and iteration laws live in the carriers
it folds into — Plotkin–Power's distinction (2003) between a free algebra and a theory with equations.
It explains the one surprise here: `Transform.andThen Transform.id f` is not `f` in `Eff` and cannot
be, so `Transform`'s category laws can only be stated at the meaning (§2 row 25).

## 2. The kinds of arrow, and the obligation of each

| kind | obligation | why it suffices |
| --- | --- | --- |
| **K1 fold** — out of a free object | be `cataFam alg` for a *named* algebra | uniqueness then equates any two arrows with the same algebra, no proof per pair |
| **K2 exact embedding** — write/read | (a) total on a stated domain; (b) `read ∘ write = id`; (c) `read v = some a → v = write a` | (b) alone permits silent widening; (c) makes the image decidable, so the writer is a subobject and the square commutes both ways |
| **K3 simulation** — into a behaviour | a relation inhabited at the start, preserved by each step, implying equality of the observation | the only sound statement about two machines; an equation is the collapsed case |
| **K4 total-by-refusal** — partial elaboration | every refusal *located*; `refusal = none ↔ success` | makes "it did not refuse" usable as a premise (DI-85/86's shape) |
| **K5 monoid action** — journal on a state | homomorphism from the free monoid, unique on generators | gives replay, resumption and splitting at once |

`✔` proved (statement read, axioms stamped); `▣` gated (recorded differential, no theorem); `✘` absent.

| # | arrow | kind | status |
| --- | --- | --- | --- |
| 1 | `cata_eff`…`cata_layers`, `hom_eq_cata_*`, `cata_id_*`, `foldM_eq_cata_*`, `foldM_natural_*` | K1 | ✔ generated, 60 `#print axioms` receipts in the emitted file (`Fold.lean:3252-3311`) |
| 2 | `build`/`view`, `cata_build`, `makers_cata` | K1 | ✔ `LayerView.lean:443`, `:481`, `:620` |
| 3 | `print` = `cataFam (printAlg sig)` (`Templates.lean:434`) | K1+K2 | ✔ fold by definition; totality `print_of_readable` |
| 4 | `read` over the 67-row table | K2 | ✔ `read_print` (law 11), `read_exact` (law 12) |
| 5 | `printModule`/`readModule` | K2 | ✔ `printModule_roundTrip`, `emitModule_complete` |
| 6 | `Readable` = `cataFam (readableAlg sig)` (`ReadPrint.lean:423`) | K1 | ✔ |
| 7 | `Eff.weaken` | K1 | ✔ `weaken_eq_cata_eff` (`Fold.lean:3125`) |
| 8 | `scopedAt` = `cata_eff (scopedAlgebra Op)` (`Scoped.lean:20`) | K1 | ✔ with `elaborate_scoped` |
| 9 | `size` (`sizeAlg`), `supervision` (`superAlg`) | K1 | ✔ with `supervision_static` |
| 10 | authoring lifts over `binders.json` into `Src = Env → List Nat → Except Refusal (Eff Op)` (`Authoring.lean:113`) | K1+K4 | ✔ generated, scope-safe by construction |
| 11 | `elaborate`, `elaborateModule` (`Authoring.lean:306`) | K4 | ✔ located `Refusal` (path + reason) |
| 12 | `explain`/`blame` | K4 | ✔ `explain_none_iff` (`Typing/Blame.lean:768`) |
| 13 | `Author.build` (`Api/Author.lean:55`) | K4 | ✔ refusals; `build_check` still owed (consolidation §3.2) |
| 14 | `admitProgram` | K4 | ✔ `admitProgram_certificate`, `admitted_unique` |
| 15 | `effTy` + 7 siblings (`Typing.lean:284`) | K1 claimed | **✘ not a fold** (0 uses of `cata_eff`); `HasTy` agreement ✔ |
| 16 | `denote` (`Denote.lean:66`) | K1 claimed | **✘ not a fold**; soundness ✔ (`meaning_typed`, `meaning_never_wrong`) |
| 17 | `compileEff` (`Compile.lean:549`) | K1 claimed | **✘ not a fold**; agreement ✔ only on `Straight`/`Looped` |
| 18 | `Straight` (`Fragment.lean:20`), `Looped` (`DenoteB.lean:123`) | — | **✘ no obligation**: they end `_ => false` / `e => Straight e`, so a new constructor silently leaves the fragment and every theorem stays true over less |
| 19 | `cata_fusion` / `AlgMap` for `Eff` | K1 | **✘ absent**: `print ∘ weaken`, `read` then `effTy` have no composition law |
| 20 | `Canonical α` (`Store/Canonical.lean:32`) | K2 | ✔ all three laws, as fields |
| 21 | program bytes `Wire.encodeProgram`/`decodeProgram` | K2 | ✔ `decode_encode` + `decode_exact` |
| 22 | `Schema.encode`/`decode` (JSON, `Schema/Codec.lean:224`) | K2 | **✘ (c) absent**: nothing says `decode t j = some v → encode t v = some j` |
| 23 | `Ty.schema`/`Ty.ofSchema` (`Bridge.lean:38`, `:63`) | K2 | **✘ (c) absent and false**: `.never ann checks` reads as `.never` for any annotations and checks; a declaration with a payload reads as `.handle` and reprints without it |
| 24 | `ShapeDoc.document` (`Shape.lean:468`), `effDocument` (`Bridge.lean:162`), `Row.document`, `Api.schemaOf` | K2 | **✘ no reader at all**, hence no law; `Api.schemaOf` (`Api.lean:138`) has zero call sites — the `RunnerBytes.schemaOf` of the same name (`:89`) is a different function, used twice in `Test/` |
| 25 | `Transform.id`/`andThen`/`dimap` (`Schema/Transform.lean:39-77`; deleted 2026-09-18) | composition | **✘ no identity, no associativity**; only `andThen_typed` (the signature) |
| 26 | `SchemaTransform.check` (`Transform.lean:92`; deleted 2026-09-18) | K4 | **✘ no completeness**: a refusal is not tied to ill-typedness |
| 27 | `replay`/`replayPlay`, `behaviour` | K5 | ✔ `replay_unique`, `replay_append`, `replay_skip_refused` |
| 28 | `journal_replays`, `drive_eq_play` | K5 | ✔ |
| 29 | `HostSession.advance` | K3 | ✔ `advance_step` trichotomy (`Laws/Run.lean:769`), `open_total` (`:210`) |
| 30 | frame machine vs term reference | K3 | ✔ `run_eq_ref`, empty table, no oracle (DI-57 names its four gaps) |
| 31 | compile+machine vs meaning | K3 | ✔ `run_eq_meaning`, `loopAgreement` (`Agreement/Loop.lean:839`) |
| 32 | LCNF → `Ml.Decl` → OCaml (`Lcnf/Translate.lean:1006`) | K3 | **▣** 20,387 vectors, 6 mutants; no simulation |
| 33 | LCNF → TypeScript | K3 | **✘ does not exist** |
| 34 | printed TypeScript → rc.112 runtime | K3 | **▣** 121 agree / 6 differ of 127 |
| 35 | `effTy` vs `tsc`'s inferred type | K3 | **▣** 110 agree / 8 refused / 9 mismatch of 127 |
| 36 | `read` on *foreign* TypeScript | K4 | **✘ no domain statement**: laws 11/12 speak only of the reader's image and the printer's output |
| 37 | the four JSON images of one `Val` | K1/K2 | **✘ no square**: `Schema.encode` (`Codec.lean:224`), `ShapeDoc.print` (`Shape.lean:539`), `Canonical.print` (`Canonical.lean:111`), the harness's `valJson` (`harness/truth/Truth.lean:404`, again at `harness/truth/session/Keyed.lean:104`) — four definitions, no theorem relating any two |
| 38 | run observations | K5 / final | **✘ no finality**: nothing says equal observations imply equal runs, so `obs` projects without reflecting |

### 2.1 Where the water leaks

**Thirteen arrows lack the obligation their kind demands**: 15 `effTy`, 16 `denote`, 17 `compileEff`,
18 the `Straight`/`Looped` fragments, 19 the missing fusion law, 22 the JSON codec's exactness,
23 `ofSchema`'s exactness, 24 the document projections, 25 `Transform`'s category laws,
26 `SchemaTransform.check`'s completeness, 36 the reader's foreign domain, 37 the four `Val`-to-JSON
images, 38 the absent finality law. **Three carry a differential instead**: 32, 34, 35. **One does
not exist**: 33.

The thirteen are three problems. (1) **Three semantic traversals are off the fold** (15–17; 19 makes
it costly). No object says what a traversal of `Eff` *is*, so each is a fresh 25-arm `match` and each
pair needs its own agreement theorem: `run_eq_meaning` is ~1,900 lines of `Agreement/Machine.lean`
for one pair. (2) **Half the write/read pairs miss exactness** (22, 23, 24, 37). A retraction without
exactness is a lossy round trip that type-checks: `ofSchema` widens by design today (consolidation
§2.5 registers it), and four JSON images of `Val` coexist because no law forbids a fifth.
(3) **The most-used partial functions have no domain statement** (18, 26, 36). A fragment defined by
inclusion with a `_ => false` tail is a theorem that quietly narrows, and the reader's acceptance set
is unstated, so "the reader is complete" cannot be said of foreign text.

## 3. Coherence as commutation

| square | status | where |
| --- | --- | --- |
| `Eff → view → algebra → R` vs `Eff → cataFam alg → R` | **proved** generically | `cata_build`, `makers_cata` |
| `effTy` vs the `HasTy` relation | **proved** both ways | `effTy_sound`, `effTy_complete`, `effTy_eq_hasTy` |
| `Eff → print → Expr → read → Eff` | **proved** on `Readable` | `read_print` |
| `Expr → read → Eff → print → Expr` | **proved** on the reader's image | `read_exact` |
| `Program → printModule → readModule → Program` | **proved** | `printModule_roundTrip` |
| `Eff → compile → machine → exit` vs `Eff → denote → meaning` | **proved** on `Straight`; at a budget on `Looped` | `run_eq_meaning`, `loopAgreement` |
| frame machine vs term reference (classify + obs) | **proved** at the empty table | `run_eq_ref` |
| `Run → journal → replay → Run`; `drive` vs `play` | **proved** | `journal_replays`, `drive_eq_play` |
| `α → Val → bytes → Val → α` | **proved** both ways | `Canonical.decode_encode`, `decode_exact` |
| `Val → Json → Val` | retraction proved, **exactness absent** | `Laws/Schema/Codec.lean` |
| `Ty → Representation → Ty` | retraction proved, **exactness absent** | `ofSchema_schema` |
| `Eff → TS → tsc → type` vs `effTy` | **gated** 110/127 | `scripts/check-corpus.py` |
| `Eff → TS → rc.112 → exit/schedule` vs the machine | **gated** 121/127 | `harness/truth/` |
| LCNF meaning vs emitted-target meaning | **gated**, 20,387 vectors, 6 mutants | rungs 2/3 |
| `Ty.schema` vs rc.112's `toRepresentation` | **gated** | `make check-schema-pins` |
| `Val → bytes → Val` vs `Val → Json → Val` | **assumed** | nothing |
| `Schema.encode` vs `ShapeDoc.print` vs `Canonical.print` vs `valJson` | **assumed** | nothing |
| `Module → elaborate → Eff` free of name capture, end to end | **assumed** beyond scope safety | `Env.mint`, `var_reserved` are the mechanism, not the statement |
| compile vs meaning outside `Straight`/`Looped` | **assumed** | the fragment is the scope |

### 3.1 The seven squares I propose as the gate — each discharging a *family* of agreements

**C1 — the traversal census (the keystone).** *Every function in `src/` whose domain is a family of
the `Eff` signature is `cataFam alg` for a declared algebra, or is on a named exemption list with a
reason.* The generator already reads the signature from the environment (`tools/Effect4Gen/Fold.lean`);
the census is one more generated table plus a `check-gen` refusal, as `generated/corpus-index.tsv`
already refuses a moved verdict. The declared algebras today are ten — `EffAlgebra.id`
(`Fold.lean:1344`), `EffAlgebra.onRef` (`:1631`), `frontierMap`/`weakenAlg` (`:3006`, `:3062`, applied
by `cata_frontier_eff` at `:2924`), `printAlg` (`Templates.lean:434`), `readableAlg`
(`ReadPrint.lean:423`), `sizeAlg` (`Size.lean:24`), `superAlg` (`Laws/Api/Supervision.lean:111`),
`scopedAlgebra` (`Scoped.lean:20`), `expandAlgebra` (`Refs.lean:131`), the generated authoring lifts
— plus the monoid folds `foldMap_eff`/`foldMapAt_eff`. The exemption list starts at six: `effTy`,
`denote`, `compileEff`, `Straight`, `Looped`, `explain`. With C1 two traversals agree iff their
algebras agree, and a new constructor is a compile error in every algebra at once.

**C2 — fusion.** `cataFam alg' ∘ cataFam algToTerms = cataFam (fused)`. The law C1 needs to make
composition free; generated for `Doc` already, absent for `Eff` (row 19).

**C3 — exactness wherever a read exists.** The JSON codec's `decode t j = some v → encode t v = some
j` on the admitted domain; and `ofSchema` refusing non-empty `checks` and non-`null` payloads so that
`ofSchema r = some t → r = schema t` becomes provable (the refusal is scheduled as consolidation
§2.5; C3 is the theorem it unlocks). This turns `Ty` from a retract into a subobject of
`Representation`, which makes "one representation per kind of thing" a theorem.

**C4 — one value image.** There is one `Val → Json` and every other is proved equal to it. Four
images is exactly "everything turns into everything": the highest-value square for the complaint.

**C5 — the fragment by exclusion.** `Straight` and `Looped` stated as "every constructor except
these, named". Five lines; the adversarial review already asked for it.

**C6 — the boundary square with a consumer.** Every recorded corpus exit decodes under the schema its
program published. This is D-D's S-5 gate, the only formulation of D12 that can fail; without it
`Api.schemaOf` stays a projection nobody reads.

**C7 — the code square, gated with rule coverage.** Keep the rungs' differential and add the
obligation the mutants nearly state: every translator rule has a mutant that turns the differential
red. Six mutants exist for a twelve-row code walk plus a 50-row builtin table; a rule with no red
mutant is a rule the corpus does not exercise, which is a finding about the corpus.

With C1–C7 the answer to "where do we go to make this coherent" is **nowhere new**: coherence becomes
a property of the generator's tables plus six theorems, and a future representation is admitted by
naming its signature, its algebras, and which of K1–K5 each of its arrows is.

## 4. The one principle

**Statement.** *Each kind of thing has exactly one free object, presented by a signature written as
data. Every other representation of that kind is an algebra of the signature, reached by the unique
fold, or an exact embedding into the free object — a write/read pair with retraction and exactness.
Every behaviour is observed, not constructed, and the only statements about two behaviours are
simulations agreeing on the observation. Coherence is the uniqueness of the fold: two arrows out of a
free object are equal as soon as they are the same algebra, so the gate is a census of algebras
rather than a catalogue of agreements.*

```
              signature-as-data  (ArgSort / argSorts / makers / build / view)
                       │  cata_build, build_view            [LayerView.lean]
                       ▼
 Src ──elaborate──▶ ┌────────┐ ──cataFam printAlg──▶ TS Expr ──read──┐  K2: read_print
 (K4, located)      │  Eff   │ ──cataFam readableAlg──▶ Bool          │      read_exact
                    │ (free) │ ──cataFam scopedAlg──▶ Bool            └──▶ Eff
                    └───┬────┘ ──cataFam size/super/expand/weaken──▶ …
  exemptions today ─────┤
  (effTy, denote,       ├──effTy───▶ EffTy ═════ HasTy        (effTy_eq_hasTy)
   compileEff,          ├──denote──▶ meaning ══════════════════════════════ run_eq_meaning
   Straight, Looped)    └──compile─▶ NCode ──▶ machine ──obs──▶ observation ═ run_eq_ref
                                                    ▲
 List Command ══K5══▶ Play ──acts on──▶ Runner ─────┘   replay_unique, journal_replays

 Ty ──schema──▶ Representation ──ofSchema──▶ Ty        K2 with (c) missing        [C3]
 Val ◀──toVal/ofVal──▶ α  (Canonical: K2 complete)     Val ──?──▶ Json ×4         [C4]
 LCNF Code ──translate──▶ Ml / TS ──▶ target meaning   K3, gated by the rungs     [C7]
```

Single arrows are folds (K1) whose only obligation is to be in the census; `═══` is an agreement
proved as a relation or simulation (K3); `K2` labels a write/read pair; `K5` the monoid action.
Everything the estate does is on this picture; the four things off it are §2.1's `✘` families.

**Against the alternatives.** *A single multi-sorted algebraic theory with six sorts* fails on (B):
a machine is not a term of any sort, and forcing it to be one means quotienting by observation —
precisely the `Quot.sound` the estate would rather spend once than build on; and it fails again on
the arrow sort, since `Transform` has no equations in `Eff`, so a theory-with-equations would be a
*different* object from the syntax the printer prints and the estate would hold two. *A fibration of
types over programs* is locally correct — `Transform σ Γ A B E R` (`Schema/Transform.lean:39`) is a
fibre over a pair of types, `TypedProgram` (`CheckedTyping.lean:19`) over a program — but says
nothing about printers, codecs, the journal or the lowering, which is where the mass is; keep it as
§4b's local reading. *A compiler pipeline, every object a language and every arrow a translation with
a simulation* (Leroy 2009) is right for `Eff → LCNF → target` and wrong globally: `effTy`,
`Readable`, `size`, `supervision`, `weaken`, `scopedAt` are folds into non-behavioural carriers, and
demanding a simulation for each is unstatable and unnecessary — uniqueness is stronger and cheaper.
The pipeline reading survives as K3, one kind of five. The chosen principle is initial-algebra
semantics with coalgebraic behaviour on the other side; it is not imposed on the estate but describes
what the generator already emits, and naming it turns "how do we organize this?" into a finite
checklist: *what is the signature, which algebra is this arrow, which of K1–K5 is that one.*

## 4b. The schema/program overlap

**Ruling: (ii). The two-sorted shape is arrows indexed by objects — programs over types, not types
over programs.**

The facts that decide it. rc.112's `Link` pairs a target AST with a `Transformation` or a `Middleware`
(`SchemaAST.ts:401-415`); a `Transformation<T,E,RD,RE>` is a *pair* of `SchemaGetter.Getter`s in
opposite directions (`SchemaTransformation.ts:143-146`); a `Getter<T,E,R>` is `Option E →
ParseOptions → Effect<Option T, Issue, R>` (`SchemaGetter.ts:64-78`) — a Kleisli arrow of the Effect
monad, partial in `Option`, with a fixed issue type and a requirement column.
`Transformation.compose` composes decode forwards and encode backwards (`:159-164`), and `Encoding`
is a non-empty chain of such links (`SchemaAST.ts:432`). So rc.112's Schema is genuinely
**two-sorted**: AST nodes are objects, encoding chains are composable effectful arrows between them —
and rc.112 imposes **no round-trip law**: `flip()` exists, `decode ∘ encode = id` is claimed nowhere.

Three consequences, each fatal to (i). **(1) A `Getter` has no initial-algebra presentation.** It is
a host closure: it cannot be folded, printed, digested, typed by `effTy` or read back. Adopting
Schema's effectful semantics as *our* program language would put an opaque function where `Eff` is,
and every arrow out of `Eff` in §4's diagram — ten algebras, the printer, the reader, the wire codec,
the machine — loses its source. It is the same reason `Eff` forbids Lean functions inside itself
(`Eff.lean:20-24`). **(2) Schema's arrows carry no law, so they cannot carry a semantics we prove.**
Ours do: a `Transform σ Γ A B E R` holds `effTy σ (Γ ++ [A]) program = some ⟨B, E, R⟩` as a field
(`Transform.lean:39-41`), checked at construction; trading that for an unlawful pair trades a
certificate for a convention. **(3) The estate already implements (ii).** `SchemaTransform` holds
"only first-order program data" by its own header; `Schema/EffectfulField.lean` and
`Schema/Endpoint.lean` follow; under scout E's proposal the AST's `encoding` link *is* such a
program. Nothing must change to adopt (ii); what must change is that its obligations get stated
(rows 25, 26).

**Where the sort of programs lives** — the arrow position of a two-sorted signature whose object sort
is the schema AST: objects `AST` (data, free for the 21-kind signature); arrows
`Transform σ Γ A B E R` (a program indexed by two objects and two columns); identity `Transform.id`
(`Transform.lean:47`); composition `Transform.andThen` (`:57`) with `E` joined and `R` unioned;
`PureMap` (`:44`) the value category. That is an **effectful (Freyd) category graded by (E, R)**,
with `Transform.pure` the identity-on-objects functor from values to computations (Power–Robinson
1997; Levy–Power–Thielecke 2003) and the columns as a graded monad's grades (Katsumata 2014;
Orchard–Petricek–Mycroft 2014). Two things follow. *Types over programs is the wrong direction*: an
arrow is indexed by objects, so the dependency runs programs → types — `Ty`/AST must not mention
`Eff`, `Eff`'s typing may mention `Ty`. The tree respects this (`Program/Ty.lean` imports nothing of
`Eff`) and scout E's question 4 should preserve it: `Ty` an embedding into the AST, not the AST
re-indexed by programs. *The category laws belong at the meaning*: `andThen id f` is
`.bind (.succeed (.var Γ.length)) (weaken f.program)`, not `f.program`, so unit and associativity are
statements about `denote` — the first consumers of a `denote` that is a fold (C1), and how the estate
learns whether its arrow composition is real.

**What Effect's effectful schema surface is on the TypeScript side** — two classes, divided by
whether Lean holds the arrow. *The printed image of a Lean `Transform`*: we authored it, it is an
`Eff` program, the printer prints it, the emitted `Link` carries that printed function; it has a
type, round-trips through laws 11/12 and the corpus can run it. This is the only class in which
"generating valid Effect TypeScript by construction" means anything. *A foreign opaque program*: a
`Getter` from rc.112 or user code, which Lean holds as a **name with an AST-typed signature** and
nothing more — `Check` is already "a name, not a meaning" (`Schema/Representation.lean` header) and
`Link.transformation` gets the same treatment. `toRepresentation` drops transformations, right for
persistence; the Lean mirror should **refuse** rather than drop when a transformation is present and
the caller asked for a Lean-checked arrow (C3 applied to `ofSchema`).

**Separation, by three rules.** (1) The object sort is pure data with a decidable `accepts`
(`Check.holds`, `ShapeDoc.accepts`) and no `Eff` in it. (2) The arrow sort is `Eff` plus a
certificate, and its only semantics is `denote` — no second interpreter for transformations, which is
"no semantics duplicated outside the machine" applied to schemas. (3) A foreign arrow is a name, and
any operation needing its meaning refuses. Under those the effectful transformations are not lost:
they are ours, in the one program language, typed by the one checker, printed where rc.112 expects.

## 5. Where the metaprogramming sits

**A third thing: a compiler from a table to declarations, whose obligation is a fixed point, not a
law.** Not an arrow of §2 (its source is a table, its target Lean text) and not an object (nothing
folds it). The account is staged metaprogramming (Taha–Sheard 2000; Kiselyov 2014): `binders.json`,
the template table, the manifest and `argSorts` are stage-0 *data*; the generator is the stage-0
program; `Fold.lean`, `LayerView.lean`, `Authoring/Lifts.lean`, `Store/Derived/*` are stage-1 code.
The *only* obligation staging gives is **idempotence with respect to the source of truth** —
regenerating from unchanged inputs gives byte-identical output — which is exactly what
`make check-gen` decides (`refuse_drift`, `Makefile:248`). That is why the metaprogramming is already
inside the proofs: the emitted declarations are ordinary Lean, kernel-checked, with their laws
generated beside them and acceptance guards appended (`tools/Effect4Gen/guards/*.lean`, 17 files).

So the owner's "another location for very powerful expression" resolves as: **the power belongs in
the tables, and the generator stays a total function from tables to declarations with no semantics of
its own.** Three rules keep it inside the proofs. (1) *A metaprogram may emit an algebra; it may not
emit a traversal that is not one* — C1 at stage 0, and the rule that makes type generation safe,
since a generated checker, printer or codec is then an `EffAlgebra` value plus `cataFam` and its
coverage is a type error rather than a review. (2) *A metaprogram's inputs are data in the tree,
never the Lean environment* — `TsGen` reads the environment (1,141 lines) and is the one generator
whose output cannot be re-derived from a committed table, which is why D-J rule (1) fails it. (3)
*Every emitted group carries its acceptance guards and `#print axioms` receipts in the emitted file*
— `Fold.lean:3252-3311`, 60 receipts, appended verbatim.

The sugar layer specifically: `Src = Env → List Nat → Except Refusal (Eff Op)` with the generated
lifts is a *binding-signature algebra on the scope-reader carrier* — Fiore–Plotkin–Turi (1999),
implemented generically exactly as Allais–Atkey–Chapman–McBride–McKinna (2018) do it: one description
of the binding structure, one generic traversal, semantics and proofs for free. It is the strongest
theory the estate already owns and the template for the rest: the author never counts binder levels
because the *signature* says which argument abstracts which binders, and scope safety is by
construction because the carrier is a reader. The same move on types gives the type generation the
owner wants with no new language: a binding signature for `Declaration` with type parameters, and
lifts over it.

## 6. LCNF as the instrument

**Under the principle the LCNF closure is the code object, and its two evaluators make it the one
place where a K3 obligation is *statable* rather than only testable.** `Conform.Lcnf.Semantics`
(561 lines) is a total fuelled interpreter for mono `Code .pure` whose only assumption is a nine-row
`PrimTable`; `Conform.Lcnf.SemanticsTarget` (606 lines) is a total interpreter for `Target.Expr`, the
emitted intersection language, read back from a backend's syntax by a reader that refuses by
constructor name. Both are Lean functions, so the CompCert-shaped statement is writable today:
`∀ decl args, validity decl = ok → evalT (read (translate decl)) (marshal args) ≈ marshal (evalCode
decl args)`, up to the marshalling and the word model, with `outOfFuel` and `stuck` kept distinct.
**The cost:** twelve code-walk rules plus a 50-row builtin table plus `Types`' closure; one induction
on fuel with a case per rule; the hard cases are where the target's domain differs — `Word.wrap` at
63 bits, byte-versus-UTF-16 strings, `Nat.sub` truncation, `Nat.pow` clamping. The literature's trade
at this size is unambiguous: CompCert's simulation proofs are the bulk of ~100k lines (Leroy 2009),
while Csmith-style differential testing found 300+ bugs in mature compilers for a fraction of the
effort (Yang–Chen–Eide–Regehr 2011), and translation validation (Pnueli–Siegel–Singerman 1998) sits
between, checking the *pair* per run. **Recommendation: both** — keep the differential and add C7's
rule coverage now; prove the simulation for the *scalar and constructor* fragment, where the word and
string mismatches live and a theorem beats vectors; leave closures and join points to the
differential until a bug is found there.

### 6.1 The addendum: LCNF as a general instrument

It generalizes, and **it is the instrument this principle predicts** — with one limit first.

*Proofs do not cross.* `AdmittedProgram` extends `TypedProgram`, whose `typed` field is a `Prop`
(`Admission.lean:88-95`, `CheckedTyping.lean:19-21`), and LCNF erases `Prop`. A lowered
`Author.build` on bun therefore computes every check (they are `Bool`/`Option` computations), refuses
exactly where Lean refuses, and returns a `Built` whose certificate slot is `◾`. The honest
obligation for any lowered checker is **decision agreement, not certificate transport**:
`lowered_f x = erase (f x)` on the data part, `Prop` erased on both sides. That inverts scout C's
"`program.build` cannot exist on bun" only halfway — the *decision* can live there, the *evidence*
cannot, and a host wanting evidence must send the program to a Lean checker. Said that way, D-F's
"only a Lean host gets `open_total`" stays true while the agent-facing build becomes admissible.

| root | its laws today | lowering obligation | gate |
| --- | --- | --- | --- |
| `HostSession`/`Run` transitions | `open_total`, `advance_step`, `journal_replays`, `drive_eq_play` | decision + state agreement on generated tapes | rungs 2/3 on tape vectors, then the truth harness |
| `Schema.Codec` | the seven codec laws | value agreement on the admitted domain; **C3 first**, or the lowering lowers the inexactness | rung 3 over `Ty × Val`, rc.112 `decodeUnknownSync` as oracle |
| `Supervision` | `status_persists`, `daemonsQuiet_iff`, `supervision_static` | decision agreement per fiber status | rung 3 + the corpus schedules |
| checker `typeOfProgram`/`explain` | `effTy_eq_hasTy`, `explain_none_iff` | decision agreement (type is data, derivation erased) | rungs 2/3 on the 400-program corpus, `tsc` as second oracle |
| `Author.build` + authoring lifts | `var_reserved`, `Row.call_scoped`, `elaborate_scoped` | decision agreement; `Src` is a function type, so the lifts lower as closures | rung 3 on generated `Module` vectors |
| `Canonical` instances | `ofVal_toVal`, `ofVal_exact`, `fits` | byte agreement | rung 3 + the existing `#guard` byte pins |

The addendum's two classes are right and the principle endorses them: **modelled** (lowered from
Lean, rc.112 the oracle, obligation K3 gated by the rungs and the harness) and **vendored** (an
`Externs` row with an AST-typed `Entry`; typed, not verified; obligation only that the signature
type-checks under `tools/target`'s tsc oracle). A vendored row must never acquire a modelled row's
vocabulary — the discipline of `Check` being a name, not a meaning. What the principle adds: (1) the
lowering is a K3 arrow, so laws proved in Lean about a root do **not** transfer to its lowered image
by themselves — each needs its decision-agreement row; (2) the right roots are those whose
interesting content is *decidable* (checkers, codecs, transitions, status queries), because there
decision agreement is the whole content; (3) the wrong roots are those whose content is a `Prop`
(`AdmittedProgram`, `TypedProgram`, every `Laws/` theorem) or a `Type`-parameterised algebra —
`EffAlgebra Op R` is already refused by the ML translator ("unsupported parameter `R`"), the honest
signal that the *algebra* form is a Lean-side construct whose host image is TypeScript's own
indexed-access types (the workshop note's `algebra.gen.ts`), generated from the signature table
rather than lowered from LCNF.

## 7. The map, redrawn

**P** proved, **G** gated, **M** missing. Read with §4's diagram.

| object | mark | note |
| --- | --- | --- |
| `Eff` + 6 families; `Ty`, `Term`, `CauseTerm` | P | signature as data, uniqueness generated |
| `Representation`/`Document` | G | fold exists, no uniqueness law |
| Schema AST (21 kinds) | M | not in Lean (scout E) |
| `Val` | P | with `Shape`/`ShapeDoc` |
| `List Command` | P | `replay_unique` |
| LCNF `Code .pure` | P | read by `Conform.Lcnf.Semantics` |
| machine / reference / `Run` | P for `obs`, **M** for finality | no reflection law |
| `Doc` / visual layout | M | specification only (`docs/ALGEBRAIC-LAYOUT-SPECIFICATION.md`) |

| arrow | kind | mark |
| --- | --- | --- |
| the ten declared algebras (id, onRef, frontierMap/weaken, print, readable, size, supervision, scoped, expand, lifts) + the monoid folds | K1 | P |
| `effTy`, `denote`, `compileEff` | K1 claimed, hand-written | **M** (each has a separate agreement theorem instead) |
| `cata_fusion` | K1 | **M** |
| print/read, module print/read | K2 | P (both laws) |
| `Canonical`, program bytes | K2 | P (three laws) |
| `Conform.Layout` `encodeAt`/`decodeAt` (2,468 lines) | K2 | P, with **proved counterexamples** for each dropped side condition (`Layout/Laws.lean:82`, `:89`) — the model to copy |
| JSON codec, `ofSchema`, the document projections, the four `Val` images | K2 | **M** (exactness) |
| `elaborate`, `explain`, `admitProgram`, `build` | K4 | P |
| `read` on foreign text, `SchemaTransform.check` | K4 | **M** (domain / completeness) |
| compile↔meaning, frame↔reference, `advance_step` | K3 | P on named fragments / the empty table |
| LCNF→OCaml, TS→rc.112, `effTy`↔tsc | K3 | **G** |
| LCNF→TypeScript | K3 | **M** |
| journal→plays, drive→play | K5 | P |
| `Transform` composition laws | composition | **M** |

Order for the **M** column, each unlocking the next: C1 → C2 → C5 → `denote` onto the fold →
`Transform`'s laws at the meaning → C3 → C4 → C6 → C7 → the Schema AST as a free object in Lean →
LCNF→TypeScript.

## 8. Decisions for the owner

**F-1 — Adopt the traversal census (C1) as a gate.** *Yes.* It is the one change that makes coherence
structural instead of a growing catalogue of agreement theorems, at the cost of one generated table;
the exemption list's length is then the honest measure of distance from the principle.

**F-2 — Generate the fusion law for `Eff` (C2).** *Yes, right after F-1.* Without it every two-stage
pipeline is a fresh induction. A generator change, not a proof effort.

**F-3 — Move `denote` onto the fold first, `effTy` second, `compileEff` last.** `denote`'s carrier
`List Val → Effects.Program StoreSig ExitV` and `effTy`'s `TyEnv → Option EffTy` are exponential
carriers the fold already supports, and `effTy_eq_hasTy` survives the move unchanged. `compileEff`
carries `Point` with fuel and risks the ~1,900-line agreement proof, so it goes last and only if
F-1's exemption list is judged too long. *Decide explicitly whether `compileEff` stays exempt.*

**F-4 — State `Straight` and `Looped` by exclusion (C5).** *Yes.* Today a new constructor silently
leaves both fragments and every soundness theorem stays true over less.

**F-5 — One `Val → Json` (C4).** *Recommend `ShapeDoc.print` as the survivor*, `Schema.encode` proved
equal to it on the admitted domain, the harness's two `valJson`s deleted. The shape-directed image
survives any change to `Ty` (including `Ty.record`/`Ty.variant` under D-A); the type-directed one
does not. If the boundary must stay type-directed, invert the choice but still prove the equality.

**F-6 — Exactness wherever a read exists (C3).** *Yes; `ofSchema`'s refusal first* (scheduled as
consolidation §2.5), the JSON codec's exactness second. With exactness `Ty` becomes a subobject of
`Representation` and "one representation per kind of thing" becomes a theorem.

**F-7 — Write 4b's rule into the vocabulary.** Schema is a data language; every effectful slot is a
hole filled by an `Eff` program with a typing certificate; a foreign `Transformation` is a name with
an AST-typed signature, and any operation needing its meaning refuses.

**F-8 — `Transform`'s category laws at the meaning, or drop the composition API.** *Prove them* once
`denote` is a fold (F-3). An unlawful composition API in the schema layer is how a second program
language starts; if the proof is too costly, rename the operations so they do not read as a category.

**F-9 — Adopt the LCNF per-module recipe with decision agreement as its obligation, and record that
certificates do not cross.** *Yes.* §6.1's limit is a fact about `Prop` erasure, not a policy. Root
order: codecs (after F-6), the checker, the `Run` transitions, the authoring lifts.

**F-10 — Rule coverage for the rungs (C7); the scalar-fragment simulation only.** *Yes* to coverage
and the partial simulation, *no* to a full CompCert-shaped proof: six mutants for a twelve-row walk
plus a 50-row table is an under-covered control.

**F-11 — Two things the theory says should not exist.** (a) **`Api.schemaOf` as it stands**
(`Api.lean:138`) — a projection with no reader, no law, zero call sites: give it C6's consumer or delete it, because a
published schema nobody decodes under is a claim, not a boundary. (b) **`TsGen`'s environment read**
— the one generator whose output cannot be re-derived from a committed table. Replace it with a fold
from the signature table: a metaprogram whose input is not data has no idempotence obligation a gate
can check.

**F-12 — Record the vocabulary in `AGENTS.md`.** "Free object", "algebra", "fold", "exact embedding
(three laws)", "simulation", "located refusal", "monoid action", and the rule that a new
representation is admitted by naming its signature and the kind of each of its arrows. The owner
asked where to *go*; there is nowhere to go, and the vocabulary is what makes that usable.

## Literature, and what each result is used for

- **Goguen–Thatcher–Wagner–Wright, "Initial Algebra Semantics and Continuous Algebras", JACM 24(1), 1977** —
  §4's principle: a semantics is the unique homomorphism out of the initial algebra, so two semantics agreeing
  constructor-wise are equal. `hom_eq_cata_eff` is an instance; why C1 is the key.
- **Meijer–Fokkinga–Paterson, "Bananas, Lenses, Envelopes and Barbed Wire", FPCA 1991** — the calculational fold
  laws: C2, and `foldM_eq_cata_*`/`foldM_natural_*` as the monadic-fold laws.
- **Hutton, "Universality and expressiveness of fold", JFP 9(4), 1999** — why "express it as a fold" strengthens
  rather than restricts: the argument for F-3.
- **Wadler, "Views", POPL 1987; Gill–Launchbury–Peyton Jones, "A short cut to deforestation", FPCA 1993** —
  `view`/`build` in `LayerView.lean` is this pair; their missing fusion equation is C2.
- **Benke–Dybjer–Jansson, APAL 2003; Chapman–Dagand–McBride–Morris, "The Gentle Art of Levitation", ICFP 2010;
  Abbott–Altenkirch–Ghani, "Containers", TCS 2005** — signature-as-data as a universe of descriptions with a
  generic fold: what makes C1 checkable by a generator.
- **Fiore–Plotkin–Turi, LICS 1999; Allais–Atkey–Chapman–McBride–McKinna, PACMPL 2(ICFP) art. 90, 2018** — §5: a
  binding signature plus one generic traversal yields scope safety and its proofs; the template for type
  generation.
- **Plotkin–Power, ACS 11, 2003; Plotkin–Pretnar, LMCS 9(4), 2013; Hyland–Plotkin–Power, TCS 357, 2006** — free
  algebra versus theory-with-equations: why `Eff` has no equations and every algebraic law here is a statement
  about a fold (§1, F-8).
- **Elgot 1975; Adámek–Milius–Velebil, "Elgot algebras", LMCS 2, 2006** — `iterate`'s budgeted meaning:
  fixpoint, uniformity, compositionality are laws of the *model*, the obligations `meaningB` should satisfy.
- **Swierstra, "Data types à la carte", JFP 18(4), 2008; Cartwright–Felleisen, TACS 1994** — rows as extension
  points: a signature coproduct with per-row algebras, the shape the layers steer wants.
- **Rendel–Ostermann, "Invertible Syntax Descriptions", Haskell 2010; Matsuda–Wang, "FliPpr", ESOP 2013** — one
  table, two directions, two laws: the template table with laws 11/12, and the "partial isomorphism" vocabulary
  K2's obligations come from.
- **Foster–Greenwald–Moore–Pierce–Schmitt, TOPLAS 29(3), 2007; Pickering–Gibbons–Wu, "Profunctor Optics",
  Programming 1(2), 2017** — `Canonical`'s three fields are the lawful-Prism laws; GetPut/PutGet is why
  exactness is not optional (F-6).
- **McBride, "Ornamental algebras, algebraic ornaments", 2011; Dagand–McBride, ICFP 2012** — `Ty` versus
  `Representation` as an ornament with a forgetful fold (`ofSchema`); the frame in which "the checkable
  fragment" is precise rather than a slogan.
- **Power–Robinson, MSCS 7, 1997; Levy–Power–Thielecke, I&C 185, 2003; Katsumata, POPL 2014;
  Orchard–Petricek–Mycroft 2014** — §4b's shape: `Transform σ Γ A B E R` as an arrow of an effectful category
  graded by its error and requirement columns, `PureMap` the value category.
- **Rutten, "Universal coalgebra", TCS 249, 2000; Jacobs, "Introduction to Coalgebra", CUP 2016;
  Lynch–Vaandrager, I&C 121(2), 1995** — the behaviour side: why `run_eq_ref` is a relation, and what the
  missing finality law (row 38) would say.
- **Leroy, "Formal verification of a realistic compiler", CACM 52(7), 2009** — §6's CompCert-shaped option and
  the cost evidence against doing it whole.
- **Pnueli–Siegel–Singerman, "Translation validation", TACAS 1998; Yang–Chen–Eide–Regehr, PLDI 2011** — the two
  alternatives to a full simulation, and the basis for §6's recommendation.
- **Bahr–Hutton, "Calculating correct compilers", JFP 25, 2015; Hutton–Wright, MPC 2004** — `run_eq_meaning` is
  the equation these papers *derive*; the lesson for F-3 is that a compile calculated from the denotation needs
  no separate agreement proof.
- **Taha–Sheard, TCS 248, 2000; Kiselyov, "BER MetaOCaml", FLOPS 2014** — §5's staging account: the generator is
  a stage-0 program over tables whose only obligation is idempotence, decided by `check-gen`.

## Where the tree contradicted the brief

1. **Law 12.** The brief reads laws 11/12 as "read ∘ print = id on the readable domain, and readable
   programs print". The tree's law 12 is `read_exact` — *what the reader accepts prints back to
   exactly the tree it read* (`Laws/Codegen/Read.lean:887`) — and "readable programs print" is
   `print_of_readable` (`PrintReadable.lean:606`), which carries no law number. This matters: the
   pair is a genuine two-law partial isomorphism (K2b **and** K2c), which makes print/read the
   estate's only complete exact embedding in the syntax direction, and the model F-6 asks the codecs
   to copy.
2. **`cata_build` is not in `Program/Fold.lean`.** It is at `LayerView.lean:481`; `Fold.lean` has
   `hom_eq_cata_*`. Different theorems: `hom_eq_cata` is uniqueness, `cata_build` the one-layer
   structure-map equation a generic reader needs. Both matter, for different squares.
3. **`LoopAgreement` is proved on all of `Looped`.** Memory `soundness-landing-2026-09-17` records it
   as open; `Agreement/Loop.lean:839` proves it, stamped at `[propext, Quot.sound]`. What remains
   open is the machine's `TypedState`, not the agreement.
4. **`Conform.Layout` is not visual layout.** `tools/Conform/Layout/*` (2,468 lines) is *data* layout
   — how a target represents Lean types — and is the estate's third complete K2 instance, with a
   proved counterexample for each dropped side condition. The visual `Doc` algebra of
   `docs/ALGEBRAIC-LAYOUT-SPECIFICATION.md` has no implementation in the tree at `14f8d4d4`.
5. **"Codecs as partial isomorphisms (`encode ∘ decode ⊆ id`)" is not what the tree proves.**
   `Laws/Schema/Codec.lean` proves `decode ∘ encode = id` on the admitted domain and nothing in the
   other direction; the `⊆ id` half is row 22's missing obligation, not an existing law.
