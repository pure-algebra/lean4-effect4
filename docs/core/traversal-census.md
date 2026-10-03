# The traversal census — how every definition reads each free object (2026-09-17)

> **Record of 2026-09-17/18, with its §1 counting rule and §7.11 restated on 2026-10-01 (row 143).**
> Current status: the census at HEAD (`lake build Test.Audit.TraversalCensus` prints it; §7.11 holds
> the latest measured table) and `docs/core/system-map.md` §5; this document and the instrument
> `Laws/Auto/Traversals.lean` are the census's one owner (row 142).

Owner: "do the census; we're smarter now, we can use Lean's metaprogramming to do these
refactors fast if we know what we're shooting for. Lack of a consumer isn't the metric;
coherence of the algebra is — modelled on the universal initial algebra. Build in parallel, a
second file, then slot it in; delete once we're at a good place." Instrument:
`src/Effect4/Laws/Auto/Traversals.lean` (`#traversal_census`); driver:
`Test/Audit/TraversalCensus.lean` (`lake build Test.Audit.TraversalCensus` prints it). Tree at
`58f31703` plus the instrument.

## 1. What the instrument measures

For an inductive and everything mutual with it (the *family*), every authored definition of the
`Effect4.*` modules that takes a family value — private definitions included, under the name
they were written with — classified by what its *own code* does with the value:

| class | meaning |
| --- | --- |
| `fold` | through a declared fold (`cataFam`, `cata_eff`, `cata_ty`, …); the algebra is named |
| `generated` | its own case analysis, in a module `tools/Effect4Gen/manifest.json` writes from the signature (`foldMap_*`, `foldM_*`, `view_*`, the `Canonical` encoders) |
| `structural` | its own case analysis under structural recursion (a `brecOn`) — a hand traversal |
| `wf` | its own case analysis under well-founded recursion (`WellFounded.fix`, `WellFounded.Nat.fix`) — a hand traversal |
| `one-level` | its own case analysis with no recursion: a `match` on the value |
| `delegates` | never looks inside: hands the value to other rows (named) |
| `opaque` | neither looks inside nor hands it on (stores or returns it) |

A definition's own code is its value and the helpers the compiler made for it, followed
transitively: the matcher, the sparse `casesOn` a `match` with a catch-all compiles through
(shared across definitions and named after whichever needed it first:
`Ty.isFactor.match_1` uses `Ty.infer._sparseCasesOn_13`), the `_unary`/`_mutual` helper of a
well-founded definition of two or more arguments, the `_f` functional of a structural one. Never
a definition a person wrote (handing a value to one is `delegates`), never the family's own
recursors, never a derived `sizeOf`. The recursion may be on the family value, on another
argument the value is read in step with (`Typed.Fits` reads a `Val` in step with its `Ty`), or
on fuel (`runStmts`); the instrument does not ask which, and §7.4 gives the reason for each row
without a fold. A definition that reads two families is a row in each. Helpers the compiler
makes (`noConfusion`, `ctorIdx`, `brecOn.go`, a derived `decEq_n`, a match splitter — 77 of the
first run's 157 "structural" rows for `Eff` were these) are not rows. Nothing is asserted about
the tree; the instrument's own red controls are (`Test/Audit/TraversalCensus.lean`, over the
planted shapes of `Test/Audit/TraversalFixture.lean` and four definitions of the tree).

**The distance.** The `structural` and `wf` rows are the hand traversals; their count, less the
members of the two fold definitions (`Checker.check`'s seven, `argTy`/`argsTy`, §7.8–§7.9), is
the distance from "every traversal is a fold or generated".

**What the census counts** (decisions row 143, ruled 2026-10-01): recursive traversals only,
structural or well-founded, private definitions included. A one-level case analysis is a
classifier under row 56 and is not counted as a traversal; the instrument reports it in its own
column, `one-level`, by name, so AGENTS.md's "a hand `match` is an exemption the census lists by
name" still holds. The reasons the ruling rests on: a case analysis that does not recurse is
already a fold whose arms ignore the recursive results (`fold_of` reads it as one, pairing the
value in — the paramorphism of §7), so converting it changes its spelling and nothing else, and
the principle is about recursion; what a new constructor costs a `match`, with or without a
catch-all, is measured by the exhaustiveness inventory (`#exhaustive_gate`, read from the
matcher's own type) and governed by the case-site policy (row 56, `make check-cases`), so
counting matches here as well would give that fact a second owner; and until 2026-10-01 the
census counted a one-level match only when the compiler encoded it through the family's own
`casesOn` (an exhaustive `match`, `Ty.isNever`) and missed it when the encoding went through a
sparse `casesOn` (a catch-all, `Ty.isFactor`), so the old `structural` counts mixed the two; now
every one-level match is a `one-level` row, whatever its encoding.

## 2. The numbers

| free object | family | takers | fold | generated | **structural** | delegates | opaque | declared folds |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `Program.Eff` | Eff, Stmt, Stmts, Effs, ActionTerm, LayerTerm, LayerTerms | 343 | 22 | 40 | **40** | 173 | 68 | `cataFam`, `cata_eff` … `cata_layers` (8) |
| `Program.Ty` | Ty | 106 | 0 | 4 | **17** | 43 | 42 | `cata_ty` |
| `Program.Term` | Term, Terms | 116 | 0 | 8 | **14** | 18 | 76 | `cata_term`, `cata_terms` |
| `Representation` | Representation, Check | 36 | 5 | 4 | **5** | 8 | 14 | `cata_representation`, `cata_check` (+ 4 positional) |
| `Store.Val` | Val | 235 | 0 | 27 | **17** | 117 | 74 | **none** |

Scout F's exemption list for `Eff` was six names. The honest number is **40 definitions in
nine root traversals** (a traversal of the mutual family is one definition per member), and
`Ty`, `Term` and `Val` — which F did not count — have **no fold in use at all**: `cata_ty` and
`cata_term` exist and nothing calls them; `Val` has no fold declared.

## 3. Every hand traversal, by root

### 3.1 `Eff` — nine root traversals, 40 definitions

| root | members | where | carrier shape | convertible? |
| --- | --- | --- | --- | --- |
| `effTy` | `effTy`, `layerTy`, `layersTy`, `stmtsTy`, `effsTy`, `actionTy` | `src/Effect4/Program/Typing.lean` | `Signature → TyEnv → Option EffTy` — an environment threaded through continuations (`Γ ++ [A]`) | **yes**: carrier `R .eff := TyEnv → Option EffTy`, the standard fold-returning-a-function; the continuation arm extends the environment before applying the child result |
| `explain` | `explainEff`, `explainLayer`, `explainLayers`, `explainStmts`, `explainEffs`, `explainAction` | `Program/Typing/Blame.lean:119-303` | as `effTy` plus a path | **yes**, same shape; carrier `TyEnv → List Nat → Option TypeRefusal` |
| `compileEff` | `compileEff`, `compileLayer`, `localBinds`, `actionAt`, `actionAt.entrants` | `src/Effect4/Program/Compile.lean` | `Point` (fuel, addresses) threaded; `actionAt` also resolves | **exempt this wave** (F-3; the 1,900-line agreement proof is stated against it); carrier `Point → NCode` is expressible |
| `Provision` | `build`, `buildAll`, `docsLayer`, `docsLayers` | `Program/Provision.lean:295-762` | over `LayerTerm(s)` only | **yes**, `R .layer`/`R .layers` carriers, the other five families trivial |
| list projections | `LayerTerms.toList`, `LayerTerms.length`, `Stmts.toList`, `Effs.toList` | `src/Effect4/Program/Eff.lean` | pure | **yes**, and better *generated* — they are the list view of the `nil`/`cons` families the generator already knows |
| `Straight` | `Straight` | `src/Effect4/Program/Fragment.lean` | `Bool`, `| _ => false` wildcard | **yes**, `R _ := Bool` with `&&`; the algebra names every constructor (row 35 settled for real) |
| `denote` | `denote`, `denoteB`, `denoteBWith`, `denoteWith`, `Looped` | `Laws/Program/{Denote:64,DenoteB:121,185,LoopSound:52,MeaningSound:43}` | meaning into the semantic domain; `With` variants take a parameter | **yes** for `denote`/`Looped` (F-3 first); the `With` variants are the same algebra at a parameter — one algebra with the parameter in the carrier, three definitions become projections |
| `Sched` | `entrantPoints`, `inlineYield`, `denoteEffBody`, `denoteLayerBody`, `denoteLayerZero` | `src/Effect4/Laws/Program/DenoteR.lean` | the R-side evaluator's helpers | **later**: they exist for the simulation proof and follow `compileEff`'s shape |
| `Agreement` | `depth`, `steps`, `depthB`, `boundB` | `Laws/Program/Agreement{,.Loop}.lean` | `Nat` measures | **yes**, and `sizeAlg` (`Laws/Program/Size.lean`) already is this fold — `depth`/`steps` are `EffAlgebra.ofLayer` one-liners |

Folds in use today, with their algebras (22 definitions): `superAlg` (`Api.supervision`),
`fastForwardAlgebra`/`dilateAlgebra` (`TestClock`), `printAlg` (`printT`, `printLayerT`),
`readableAlg` (`Readable`, `moduleReadable`), `expandAlgebra` (`expandRound`, seven members),
`scopedAlgebra` (`scopedAt`, eight members). `sizeAlg`, `frontierMap`/`weakenAlg`,
`EffAlgebra.id`/`onRef` are declared but reach the census only through generated or theorem-side
uses.

### 3.2 `Ty` — 17 hand traversals, `cata_ty` unused

`Ty.lean`: `instReprTy.repr`, `renderRaw`, `members`, `key`, `isNever`, `isMember`, `normalize`;
`Eff.lean`: `isTagTy`, `rawSupportedErrTy`; `Admission.findInt`; `NativeAtom.projectProduct`;
`Typed.Val.hasTy`; `Schema/Bridge.schema`; `Schema/Codec.{layout,isSupported,encodeRaw,decodeRaw}`.
All pure, all on one non-mutual inductive of 16 constructors when this census was taken (20 since
2026-09-18: `refOf`, `deferredOf` and `var` at `7db30c8a`, `unknown` at `0a2cb898`): the cheapest family to convert
wholesale, and the one where a new constructor (`Ty.app`, row 3; `Ty.record`/`variant`, row 2)
costs 17 hand edits today and one algebra field each after.

### 3.3 `Term` — 14 hand traversals, `cata_term`/`cata_terms` unused

`printTerm`/`printTerms` (`Codegen/PrintLeaf`), `Terms.names?`/`noRow` (`Codegen/Read`),
`Terms.toList`, `Term.scoped`/`Terms.scoped`, `Term.weaken`/`Terms.weaken` (`Eff.lean`),
`evalTerm`/`evalTerms` (`Native`), `termTy`/`termsTy`/`argTy` (`Typing`). Same verdict as `Ty`.

### 3.4 `Representation` — 5 hand, 3 fold

Hand: `withChecks?` (`Authoring`), `Bridge.checkId`, `Bridge.ofSchema`, `Representation.tag`,
`Check.tag`. Fold: the printer (`Codegen/Schema.printAlgebra`); `fieldAdmissible`
(`Check.lean`) and `effectfulFieldProperties` (`EffectfulField.lean`) were deleted on
2026-10-01 under row 39. The two `tag` projections
are what the generator's `ctorIdx`-style view gives for free; `ofSchema` is the K2 read (row 6)
and stays a hand definition until exactness is stated — then it is the *inverse* of the fold
`schema`, which is its specification.

### 3.5 `Store.Val` — 17 hand, no fold declared

`Val.lean`: `render`, `encode`, `tag`, `payload`, `handles`, `WF`, `wf`, `beq`; `Node.lean`:
`refs`, `malformedRef`; `Shape.lean`: `acceptsAt`, `printIn`; `Machine`: `reasonsOfVal`
(`Stores`), `Val.keys`, `Val.validIn`, `valCode` (Laws); `Config.Val.ofStore`. `Val` is the value
sort's free object and has **no** `ValAlgebra`/`cata_val` — the generator's `Fold` group lists
`Eff`, `Ty`, `Term`, `CauseTerm` and `Representation` but not `Val`. One manifest line.

## 4. The converter — the connector that makes a hand traversal click into the fold

The uniqueness theorem is already the proof. `hom_eq_cata_eff` (`src/Effect4/Program/Fold.lean`) says: a
function satisfying the homomorphism equations of an algebra *is* `cata_eff` of it. A
structurally recursive `f` comes with its equation lemmas `f.eq_n : f (ctor a₀ … aₖ) = rhs`;
when every recursive occurrence in `rhs` is `f aᵢ` on an immediate child, `rhs` with `f aᵢ`
abstracted to `rᵢ` *is* the algebra field, and `f.eq_n` *is* the `EffHom` field. So the
conversion is a metaprogram with no proof search:

```
#fold_of f                       -- in a second file beside f's; nothing in f's file changes
  ⟹ def fAlg : EffAlgebra Op R :=                     -- one field per constructor:
       { eff_succeed := fun a₀ => ⟦rhs₁⟧, … }          --   rhs of f.eq_n with f aᵢ ↦ rᵢ
     def fHom : EffHom fAlg :=                         -- the seven members are f's members,
       { f_eff := f, f_stmt := f', …,                  --   the h_* fields are the equations
         h_eff_succeed := f.eq_1, … }                  --   (Fold.lean:1099)
     theorem f_eq_cata (e) : f e = cata_eff fAlg e :=  -- uniqueness (Fold.lean:1172)
       hom_eq_cata_eff fHom e
```

Three shapes, from §3, and what each needs of the converter:

1. **Pure catamorphism** (`Straight`, the list projections, `depth`/`steps`, `Ty`'s and
   `Term`'s traversals, most of `Val`'s): the scheme above, verbatim. The carrier is `f`'s
   result type at every family member (`fun _ => Bool`, `fun _ => Nat`, …), or a per-member
   type read off the mutual definitions.
2. **Accumulator threaded through children** (`effTy`, `explain`, `Provision`, the `With`
   variants of `denote`): the carrier is a function type `Acc → Res`; an arm that calls
   `f acc' child` becomes `rᵢ acc'`. Same scheme after the carrier is chosen; the converter
   reads the accumulator as the non-family explicit arguments of `f` that recursive calls vary.
3. **Paramorphism** — an arm that uses a child `aᵢ` *itself*, not only `f aᵢ` (`compileEff`'s
   `actionAt` resolving; `Sched`'s helpers): not a catamorphism. Either the child is re-folded
   with `EffAlgebra.id` paired into the carrier (`R fam := Carrier fam × Res` — the standard
   para-as-cata), or the row stays on the exemption list with the reason "paramorphic". The
   converter reports which arms are paramorphic; it does not guess.

What the converter reads: `f`'s equation lemmas (`getEqnsFor?`), the family's constructors and
which argument positions are children (`LayerView`'s `argSorts` already says this, as data),
and the algebra structure's field names (`EffAlgebra`'s `eff_succeed`, … — generated, so the
naming is `fam_ctor`). What it writes: a `def`, a `def`, a `theorem`, into a file the caller
names. The old definition is untouched until its callers move to `cata_eff fAlg` (a rename,
`f_eq_cata` rewriting any proof that unfolds `f`), and then it is deleted — the owner's "build
in parallel, slot in, delete at a good place".

For `Ty`, `Term` and `Val`, the algebra structures and folds are either generated (`TyAlgebra`,
`TermAlgebra`) or one manifest line away (`Val`); the converter is the same program at a
different family, because the generator names every algebra field the same way.

## 5. What this changes in the one list

- Row 34's "six exemptions" is 40 definitions in nine roots for `Eff` alone, plus 53 across the
  other four objects. The gate form of the census (a pinned table, `check-gen` refusing a
  moved verdict) waits until the converter has run; a gate over today's table would only
  freeze the distance.
- Row 30 (`denote`, `effTy`, `compileEff` onto the fold) is the converter's first three
  customers, in the order §4 gives: `Straight` and the projections (shape 1) to prove the
  converter, then `effTy` (shape 2), then `denote`; `compileEff` stays exempt.
- Row 35 is subsumed: a `Straight` algebra names every constructor.
- Rows 3 and 2 (new `Ty` constructors) become one algebra field each once §3.2 is folded —
  the reason to fold `Ty` first is that the boundary rows are waiting on it.
- The schema wipe of the probe note (§3 there) is unchanged in what it removes, and this census
  says what to *keep converting* rather than delete: `ofSchema` (the inverse of a fold),
  `Codec.{encodeRaw,decodeRaw}` (two `Ty` algebras), `Bridge.schema` (a `Ty` algebra).

## 6. Reading the census yourself

```
lake build Test.Audit.TraversalCensus 2>&1 | grep -v '^trace'
```

`#traversal_census T` scans every imported `Effect4.*` module; `#traversal_census T under
Effect4.Program` narrows it. Rows are `class ⟨tab⟩ module:line ⟨tab⟩ name [instance] [private]
⟨tab⟩ (family member) ⟨tab⟩ detail` (no detail column when it is empty), sorted by class, module,
line. `#traversal_class T for a b …` prints only the class of the named definitions.

## 7. The converter, landed (`fb7a5784`)

`fold_of f` is `src/Effect4/Program/FoldOf.lean` (a command elaborator, in the axiom gate's meta
list; no source is pretty-printed — the declarations are built as terms and the kernel checks
them). For a structural `f` it adds `f.alg`, `f.hom` and `g.eq_cata` for every member `g` of
`f`'s mutual block. The arms come from `f`'s unfold equation with the matcher reduced at each
constructor; the hom fields are `rfl` (structural recursion reduces on a constructor); the
connector is the generated uniqueness theorem. When an arm uses a child's value as well as its
result, the carrier pairs the value in (a paramorphism as a catamorphism) and the connector
reads `g e = (cata alg e).2`. Family members the block does not traverse carry `Unit`.

| stub file | converted | connector axioms |
| --- | --- | --- |
| `Laws/Program/Folds/Straight.lean` | `Straight` (every constructor a named field — row 35 settled) | `[propext]` |
| `Laws/Program/Folds/Looped.lean` | `Looped` | `[propext]` |
| `Laws/Program/Folds/Projections.lean` | `Stmts.toList`, `Effs.toList`, `LayerTerms.toList` (paramorphisms), `LayerTerms.length` | `[propext]` |
| `Laws/Program/Folds/Ty.lean` | `renderRaw`, `members` (para), `key`, `isNever`, `isMember`, `normalize`, `isTagTy`, `rawSupportedErrTy`, `NativeAtom.projectProduct`, `Bridge.schema`, `Codec.layout`, `Codec.isSupported` — 12 of `Ty`'s 17 | `[propext]` |
| `Laws/Program/Folds/Provision.lean` | `docsLayer` / `docsLayers` | `[propext]` |

Twenty-one hand traversals had a fold and a kernel-checked connector after the first
iteration, from six stub files that change nothing in the modules they read.

### 7.1 The accumulator shape (2026-09-18, `79349430` … `213bbb6f`)

The second iteration reads the *fixed prefix* — the leading binders every recursive call in
the block passes through unchanged — and puts every other binder, before or after the family
value, into the carrier as a function type: `findInt.alg` at `Path → Option Path`,
`Val.hasTy.alg` at `Val → List String → Bool`, `effTy`'s shape would be `R .eff := TyEnv →
Option EffTy` beside `R .layer := Option LayerTy`. A recursive call that stops short of the last
binders (`vs.mapM (encodeRaw t)`) is the curried result. Two further idioms reduce through
their case splits rather than the matcher: a match on more than the family value
(`| .unit, .unit => …`) and an overlapping pattern (`| .cons head .nil, ctx => …`, which
inspects the tail and so pairs the value in). The homomorphism equations are no longer
`rfl` against the definition: each is the unfold equation `g … node … = M` closed by `funext`
over the varying binders (and `congrArg (node, ·)` under a paramorphism), so the kernel only
ever reduces a matcher on a constructor, never the recursion's `brecOn`. Connectors are at
`[propext, Quot.sound]`.

| stub file | converted in this iteration |
| --- | --- |
| `Laws/Program/Folds/Ty.lean` | `findInt`, `Val.hasTy`, `Codec.encodeRaw`, `Codec.decodeRaw` — **`Ty` is 16 of 17** (`instReprTy.repr` remains) |
| `Laws/Program/Folds/Provision.lean` | `Provision.build` / `buildAll` |
| `Laws/Program/Folds/Denote.lean` | `denote`, `denoteB`, `denoteWith`, `denoteBWith` (**row 30's `denote` onto the fold**), `Agreement.depth`, `steps`, `depthB`, `boundB` |
| `Laws/Program/Folds/Term.lean` | `printTerm`/`printTerms`, `Terms.names?`, `noRow`, `Terms.toList`, `Term.scoped`/`Terms.scoped`, `Term.weaken`/`Terms.weaken`, `evalTerm`/`evalTerms`, `argTy` — **`Term` is 12 of 14** |

The census now marks a hand traversal that has its fold beside it: **`Eff` 18 of 40, `Ty` 16
of 17, `Term` 12 of 14**; `Representation` 0 of 5 and `Val` 0 of 17. `Val` had no fold at all;
`src/Effect4/Store/Carrier/Fold.lean` is generated now (`ValFold` in the manifest, `7bb403ed`).

### 7.2 The list-sibling shape (2026-09-18, `9cfeaf40`)

The estate writes every nested traversal of `Val` as a mutual pair — `render` beside
`renderList`, `encode` beside `encodeList`, `acceptsAt` beside `acceptsList` *and*
`acceptsFields` — exactly the generated `cata_val` / `cata_pos_list_val` pair. So a block member
over `List M` is read as a `List.foldr` over the mapped results: its `nil` and `cons` are its two
arms with `f … x …` the element's result and `s … rest …` the fold of the rest;
`s.eq_foldr : (fun acc => s fixed acc xs) = List.foldr cons nil (xs.map f)` is proved by
`List.rec` from the sibling's unfold equations; the family algebra's container field
(`val_list : List (R .val) → R .val`) gets `foldr cons nil rs`; and the sibling's own connector
`s.eq_cata` goes through the generated `cata_pos_list_val_eq`. Replacements are keyed by the
sibling called, since two siblings may read the same list. A list child the arm never mentions
(`| .list _ => Tag.list`) needs no sibling.

| stub file | converted |
| --- | --- |
| `Laws/Store/Folds/Val.lean` | `render`, `encode`, `tag`, `handles`, `beq` (its second list an accumulator), `refs`, `malformedRef`, `acceptsAt` (two siblings), `printIn` (two siblings), `Config.Val.ofStore` |
| `Laws/Machine/Folds/Val.lean` | `Val.keys`, `Val.validIn` (the stores fixed) |

**`Val` is 12 of 17**, with twelve sibling connectors beside them. Then (`13dde151`) a
position other than `List M` — `Option M`, `List (ElementOf M)`, a record wrapper — types the
field's local with the carrier in the member's place, as the generated algebra does, and
`Representation.tag` / `Check.tag` convert. The census at `13dde151`: `Eff` 18 of 40, `Ty` 16
of 17, `Term` 12 of 14, `Representation` 2 of 5, `Val` 12 of 17 — **66 of 93 hand traversals
have a fold and a kernel-checked connector**.

### 7.3 The container paramorphism (2026-09-18)

An arm that uses a child under a container or a wrapper as a value: `WF (.list xs) =
(encodeList xs).length < 2^64 ∧ WFList xs`, `payload (.ctor i args) = … ++ encodeList args`,
`withChecks?` rebuilding the node with its children, `checkId` reading `filterGroup`'s `Option`
child, `reasonsOfVal`'s case analysis on `.ctor 1 [written]`. The value is paired in as for any
paramorphism, and the generated algebra then hands the field the child's *paired results*
(`List (Val × Prop)`, `List (PropertySignatureOf (Representation × Option Representation))`).
The converter reads the value back through the position's functor map (`List.map Prod.fst`,
`Option.map`, the generated `W.map`, composed down to the member) and the field is the arm at
that reading. The equation `f_val (.list a) = alg.val_list (a.map f_val)` then needs
`(a.map (fun e => (e, f e))).map Prod.fst = a`: the composition law, the pointwise identity
under `funext` (`(e, f e).1` reduces), and the identity law, one container child at a time with
the others held at their stage. `List` and `Option` carry both laws in core; the generator had
emitted only `map_map` for its wrappers and now emits `map_id` beside it
(`tools/Effect4Gen/Fold.lean`; `ElementOf`, `PropertySignatureOf`, `IndexSignatureOf`,
`CheckRepresentationAnnotationOf` in `Schema/Fold.lean`). That is the functor's second law,
and a paired fold is its first consumer.

Two shapes the previous list kept apart fell to it: a case analysis on a container child whose
grandchild is only *read* (`reasonsOfVal`), since the arm stays as written over the read-back
value; and the positions other than `List M` under a paramorphism (`withChecks?`, `checkId`).
The sibling connectors' pointwise step is now the uniqueness theorem itself
(`hom.f_val x = cata alg x`) rather than `f.eq_cata` under `funext`, which is what makes the
paired case uniform with the plain one.

Converted: `Val.WF`/`WFList`, `Val.wf`/`wfList`, `Val.payload` (`Laws/Store/Folds/Val.lean`);
`Machine.reasonsOfVal`/`reasonsOfList` (`Laws/Machine/Folds/Stores.lean`, new);
`Schema.withChecks?`, `Bridge.checkId` (`Laws/Program/Folds/Representation.lean`). Census: `Val` 16
of 17, `Representation` 4 of 5; **66 of 93** hand traversals had a fold and a kernel-checked
connector at that point, every one at `[propext, Quot.sound]` (72 after §7.5).

### 7.4 What `fold_of` refuses today, and the shape each needs

- **A case analysis on a container child that recurses on the grandchild**
  (`Witnesses.valCode`: `| .ctor 9 [head] => 9 :: valCode head`; `Bridge.ofSchema` reading
  through `declaration`'s annotation and recursing): the recursive call is not on an immediate
  child, so the results the algebra hands over do not contain the grandchild's; the field would
  have to split on the *results* list, the generated positional folds' shape. `valCode` (1),
  `ofSchema` (1).
- **`instReprTy.repr`** (1): the implementation of `deriving Repr`, generated from the
  signature by Lean's handler; the census marks it as an instance implementation (§7.6).

The count after §7.8: 81 hand traversals, 68 with connectors, 13 named above.
- **`compileEff`** (5): exempt by ruling (row 30); `Sched`'s helpers (5) follow it.

The step after the connectors is the callers: each `f`'s callers move to `cata alg`, the
proofs that unfold `f` rewrite by `f.eq_cata`, and `f` is deleted. That is where the count in
§2 goes down.

**The named exemptions at `dceae006` (2026-10-01, by the instrument as repaired in §7.11).**
Row 40 closed this list as tracked debt — nothing is converted for uniformity's sake, a hand
definition that is not a fold is not thereby wrong — so naming each row with its shape is the
whole obligation. The exemptions named on 2026-10-01 (row 143) are `Ty.closed`,
`Ty.instantiate`, `Ty.infer`, `Ty.varsOf`, `Ty.templateAdmissible`, `Ty.sub` and the three
private traversals `Codegen.Types.ofNormalized`, `Representation.beq` and `Check.beq`. With the
thirteen of row 40 as they classify now and the statement walks the repaired instrument shows,
the 24 hand traversals without a fold beside them are:

| rows | where | shape | why no connector |
| --- | --- | --- | --- |
| `compileEff`, `compileLayer`, `localBinds`, `actionAt.entrants` | `Program/Compile.lean` | structural over the program, `Point` (fuel, addresses) threaded | exempt by ruling (row 30). `actionAt` itself does not recurse: a `one-level` row since 2026-10-01 |
| `Sched.denoteLayerZero`, `Sched.entrantPoints`, `Sched.inlineYield` | `Laws/Program/DenoteR.lean` | the reference evaluator's helpers, `compileEff`'s shape | follow `compileEff` (row 40). `denoteEffBody` and `denoteLayerBody` take their recursion as a parameter: `one-level` rows since 2026-10-01 |
| `runStmts`, `runStmts.yieldOf`, `Sched.walkR`, `Sched.walkR.yieldOf` | `Program/Compile.lean`, `Laws/Program/InterpR.lean` | `wf` on fuel: the statement walk looks up the node at a program counter and destructs it, one level per step | the recursion is on fuel and the node is looked up, not a child: no fold applies. Printed `opaque` until 2026-10-01 (the fixpoint sits in a `_mutual` helper) |
| `loopExit` | `Program/Compile.lean` | structural on a depth: walks up the enclosing blocks by path | as the statement walk. Printed `opaque` until 2026-10-01 |
| `Ty.closed`, `Ty.instantiate`, `Ty.varsOf`, `Ty.templateAdmissible` | `Program/Ty.lean`, `Laws/Program/Template.lean` | structural and pure (`instantiate` with its substitution fixed): §4's shape 1 | the row-template calculus (rows 42–43, written the evening of 2026-09-18, after the converter's run); never put through `fold_of` |
| `Ty.infer` | `Program/Ty.lean` | structural on the template, the request read in step, the substitution threaded | two values walked together; §7.1's accumulator shape with the request among the varying binders, not tried |
| `Ty.sub` | `Program/Ty.lean` | `wf` on `sizeOf a + sizeOf b`, two values walked together | not a fold of one value. Printed `opaque` until 2026-10-01 (the fixpoint sits in `Ty.sub._unary` over `WellFounded.Nat.fix`) |
| `Codegen.Types.ofNormalized` [private] | `Codegen/Types.lean` | structural and pure, every constructor named: shape 1 | private, so no census row until 2026-10-01; never put through `fold_of` |
| `Representation.beq`, `Check.beq` [private] | `Schema/Representation.lean` | `wf`, mutual: the hand `DecidableEq` of the nested mutual family (no deriving handler covers it), two values walked together | private and well-founded, so no census row until 2026-10-01; not a fold of one value |
| `Bridge.ofSchema`, `Witnesses.valCode` | `Schema/Bridge.lean`, `Laws/Machine/Witnesses.lean` | a container child's grandchild (the first bullet above) | as above |
| `instReprTy.repr` [instance] | `Program/Ty.lean` | the derived `Repr` | generated by Lean's deriving handler (§7.6) |

### 7.5 The statement sort, and typing with located refusal as one fold (2026-09-18)

`stmtsTy` split on the statement child and typed its grandchild (`| .cons (.bindYield effect)
rest => effTy sig env effect`), so statements had no carrier; `layersTy` special-cased the
singleton (`| .cons head .nil => layerTy sig head`), a split on the tail; and `explain`'s arms
called `effTy` on the children, a paramorphism as written. None of the three is a fold.
`Program/Checker.lean` (first landed as an `Option`-valued copy of `effTy`, `74f23029`; re-cut
under decision row 38, route (b)) is `check sig env p e : Except TypeRefusal EffTy` — the
located-refusal arrow of the ontology (§5, K4) as one function: its success is `effTy sig env
e` and its refusal is `explainEff sig env p e`, rule for rule, with the path `p` as an
accumulator. Three shapes differ from the hand blocks and nothing is accepted or blamed
differently:

- **a statement has a type** (`StmtTy`): a *step* with the state it contributes and the
  variables it binds (`yield*`, `const = yield*`, a branch, a loop), a *return* with its
  answer's check — carried unevaluated, since `explainStmts` blames "return not last" before
  it types the value, and evaluated by `checkStmts` once the tail is known to be empty — or
  *nothing* (`break`); "no statement after a return" is the mode flag `afterRet`, set by a
  return for its tail and carrying the return's path (where `explain` locates the refusal), as
  `inLoop` is set by a loop for its body;
- **the layers of a `mergeAll` are a list of signatures**; the nonempty merge and the
  `mergeAllEmpty` refusal are `mergeAll`'s own rule (`LayerTy.mergeNonempty`);
- **the join and the merge are total**: `EffTy.joinAnswer a b = some (Ty.join a b)` by
  definition and `GenTy.merge a b = some (GenTy.mergeT a b)`, so the fold joins with `Ty.join`
  and has no dead branch.

The connector `check_eq` (`Program/Typing/Agreement.lean`) states both projections per sort
by one structural recursion over the family, `[propext, Quot.sound]`; `explain = none ↔
effTy.isSome` (`explain_none_iff'`) is then the shape of `Except`, where `Blame.lean` proves it
by a second mutual induction of seven hundred lines. `fold_of check` converts all seven members
(`R .eff = TyEnv → List Nat → Except TypeRefusal EffTy`, `R .stmts = TyEnv → Bool → Option
(List Nat) → List Nat → Except TypeRefusal GenTy`, …), and the twelve hand rows — `effTy`'s
six and `explain`'s six — carry `eq_cata` through the agreement (`effTy.eq_cata : effTy sig
env e = (cata_eff (check.alg sig) e env p).toOption`, `explainEff.eq_cata : explainEff sig env
p e = refusal (cata_eff (check.alg sig) e env p)`). Nothing in `Typing.lean` or `Blame.lean`
changed; every property of either reaches the fold through the agreement.

Proof notes. The arms close by `cases` on each child's result and one `simp only` set: the
monad's laws stated by `rfl`, the `Option` laws of the hand blocks, the total join, path
normalisation (`p ++ [0] ++ [0] = p ++ [0, 0]`), the conditions. `split` rewrites every `if`
with the same condition on both sides at once, so no hypothesis needs carrying across. Aesop
has no target-splitting rule and these goals split on terms, not hypotheses, so it is not
used here.

Census: `Eff` 30 of the 40 hand rows, plus the seven fold-checker members, all folds (the
driver prints 47 (37)); **78 of 93** hand traversals with connectors. What remains of `Eff`
is `compileEff`'s five (exempt by ruling) and `Sched`'s five.

The first caller moved the same day: the law of the projection (DI-86). `Blame.lean`'s second
mutual block — the seven `*_none_iff` theorems by induction over both blocks, 370 lines under
`maxHeartbeats 1600000` — is deleted; the same theorems with the same statements are derived
in `Program/Typing/Agreement.lean` from `check_eq` and one lemma, `refusal_none_iff : refusal
x = none ↔ x.toOption.isSome`, by cases on `x`. The agreement moved into the core root for
that (it uses no proof search; `Api.check` is total by `explain_none_iff`, and the application
root never reaches `Effect4.Laws`). `Api.explain_none_iff` and `Test/Program/BlameContract.lean`
are untouched, at `[propext, Quot.sound]`. `Blame.lean` is 406 lines, from 777.

### 7.6 The term typer, and the derived instance (2026-09-18)

`termsTy` splits on the head's constructor to apply the literal rule and recurses on the
*rebuilt* head otherwise — the shape-inspecting arm. The fold is what `Typing.lean` already
named `argTy`, the type of a term in argument position under the enclosing atom's
const-generic flag, with the flag as the accumulator (`sig.constAtom atom` for an
application's arguments): `Typing/Terms.lean`, `Checker.argTy`/`argsTy`, two sorts, five
arms. `termTy` is the fold at `false` (`litArgTy_false`) and `termsTy` is `argsTy` rule for
rule (`Typing/Agreement.lean`, `termTy_eq`, `argsTy_eq`; `[propext, Quot.sound]`);
`fold_of Checker.argTy` converts both members and `termTy.eq_cata`/`termsTy.eq_cata` are
transported. `Term` 14 of 14 (the driver prints 16 (16) with the two fold members).

`Ty`'s last row, `instReprTy.repr`, is the implementation of `deriving Repr`: generated from
the signature by Lean's deriving handler, not a hand traversal. The census now marks a
definition nested under an instance as an instance implementation and counts those apart
(`structural 17 (of which 16 with a fold beside them, 1 instance implementations)`).

Census after this: **80 of 93** hand traversals have a fold and a kernel-checked connector.
The thirteen without: `compileEff`'s five (exempt, row 30) and `Sched`'s five, `valCode` and
`ofSchema` (the grandchild-under-a-container shape, §7.4), and the derived instance.

### 7.7 The callers of `explain` moved; the hand blame deleted (2026-09-18)

The good place for the first deletion: `explain` and `blame` had two consumers, `Api` and the
blame contract, and the fold's refusal was proved equal to the hand walk's arm for arm (§7.5).
So `explain sig env e` is now `Checker.refusal (Checker.check sig env [] e)` by definition
(`Program/Checker.lean`), `Api.checkLayer` matches the `Except` of `Checker.checkLayer` and
carries `checkLayer_eq` as its certificate (no `absurd` on a completeness law), the contract's
one direct use names `Program.explain`, and the six hand blame members (`explainEff`,
`explainLayer`, `explainLayers`, `explainStmts`, `explainEffs`, `explainAction`, 270 lines)
are deleted with the refusal half of the agreement and the six sort-level `*_none_iff`
theorems that stated it. `Typing/Blame.lean` is the vocabulary of reasons (`TypeReason`,
`TypeRefusal`, `selectRefusal`), 117 lines from 777 at the start of the day. The law of the
projection keeps its name and statement (`explain_none_iff : explain sig env e = none ↔ (effTy
sig env e).isSome`), two lines from `check_eq` and `refusal_none_iff`; `Api.explain_none_iff`
and `Test/Program/BlameContract.lean` are untouched, every battery of `Test/All.lean` builds,
and the axioms are `[propext, Quot.sound]` throughout.

This is where the count in §2 goes down for the right reason: the hand traversals are
**87** (`Eff` 34), of which **74** have a fold and a connector; the thirteen without are
unchanged. `effTy`'s block stays: its consumers are the proof files (`Typing/Sound.lean`,
`Typing/Check.lean`, `CheckedTyping.lean`, …), which unfold its equations, and moving them is
the next callers slice, not a deletion.

### 7.8 The callers of `effTy` moved; the hand checker deleted (2026-09-18)

The plan is `docs/research/2026-09-18-efftys-callers-plan.md`; this is what landed, in the
order that kept every commit green.

- **The proof graph moved first, beside the old** (`d7ea2bd9`): `Laws/Program/Typing/
  CheckInversion.lean` (one inversion per arm of `check`, every proof `aesop` over the
  checker's equations, the `Except` laws and `expect_eq_ok`) and `CheckSound.lean` (soundness
  and completeness of `check` against `HasTy` **at every path**, the same three lines per arm
  as `Sound.lean`, and `check_toOption`: the success projection is path-independent, because
  an `ok` at one path derives a judgment that completeness returns at any other). For that,
  every `Option`-answering rule of `check` now goes through `expect r o` so one lemma inverts
  them all.
- **Then the flip.** `Program/Typing.lean` split into `Typing/Rules.lean` (the type algebra,
  the term and cause typers, their weakening) and the facade `Typing.lean`, where `effTy`,
  `layerTy`, `layersTy`, `stmtsTy`, `effsTy`, `actionTy` are *definitions*: the check's success
  at the empty path. `typeOf`, `typeOfProgram`, `WellTyped` unchanged. The hand block (275
  lines) is gone. `Sound.lean` (715 → 202) is the corollaries under the old names —
  `effTy_sound`, `effTy_complete`, `effTy_eq_hasTy`, `wellTyped_iff`, `hasTy_unique`,
  `hasTy_weaken` — one line each through `toOption_eq_some`, plus the projection's equations
  at the arms other proofs unfold (`effTy_bind`, `effTy_onExit`, `effTy_succeed`,
  `effTy_scoped`). `Inversion.lean` (450 → 129) keeps the thirteen `effTy` inversions
  `MeaningSound`/`LoopSound` consume, as corollaries. `Agreement.lean` (721 → 167) lost
  `check_eq`, the 600-line structural induction: it was path independence, which is now a
  corollary. `Forms.lean` and `ScopedTyping.lean` rewrite their unfold sites with the
  equations.
- **Two things the plan had not seen.** A refusal names the term it refuses, so weakening
  is not an equation of `check` but of its success projection: `check_weaken` (facade, every
  path) is proved by pushing `Except.toOption` through the connectives (`toOption_bind`,
  `toOption_expect` — the reason is forgotten — `apply_ite`, `toOption_fold`); for that,
  `check`'s matches on bound values became `expect` helpers (`listOf?`, `exitOf?`), pair binds
  became projections, and the statement eliminator is a named `StmtTy.fold`. And the
  statement sort carries its syntax (`StmtTy.ret` holds the value's check), so `checkStmts`
  weakens by cases on the head rather than through a `checkStmt` law that cannot exist.
- **Cuts.** `Typing/Specs.lean` (1,635 generated lines, no consumer) and the `specs` group
  (`EmitSpecs`, `specs.json`, Makefile, `generate.py`, `GENERATED.md`); `Provision.lean`'s
  `build_total`/`buildAll_total` (no consumer, 175 lines); `effTy_provideService_twice` (no
  consumer); `Schema/Endpoint.lean`, `Schema/Transform.lean`, `Laws/Schema/Transform.lean`
  (the wipe list, `docs/research/2026-09-17-ontology-and-do-now-probe.md` §3; imported only by `Api` re-exports and one test section,
  both cut). `Laws/Program/Typing/Check.lean` stays: the typing-check contract consumes it.

Every battery in `Test/All.lean` and both roots build; `effTy_sound`, `hasTy_weaken`,
`effTy_weaken`, `typeOf_weaken`, `Api.explain_none_iff`, `Api.checkLayer` and the Forms laws
are at `[propext, Quot.sound]`. Census: **81 hand traversals** (`Eff` 28, down from 34: the six
of the hand checker), **68 with a fold and a connector**, the thirteen without unchanged
(`compileEff`'s five, `Sched`'s five, `valCode`, `ofSchema`, the derived instance). The
projections themselves classify as delegating to `check`, which is the fold's presentation.

### 7.9 The callers of the term typer moved; the hand term block deleted (2026-09-18)

The pattern of §7.8 at the term sort. `argTy`/`argsTy` — the fold of §7.6, until now
`Checker.argTy` in `Typing/Terms.lean` beside the hand block — is the definition in
`Typing/Rules.lean`, under the names the hand `argTy` and `termsTy` had; `termTy sig env t :=
argTy sig env false t` is its projection outside a const-generic atom, where the literal rule is
`Lit.ty` (`litArgTy_false`). Deleted: the hand `termTy`/`termsTy` mutual block, the hand `argTy`
(a case split that delegated to `termTy`), `termsTy_cons` (now `argsTy_cons`, `rfl`),
`Typing/Terms.lean`, `Folds/TermTy.lean`, and the agreement (`argTy_eq`, `argsTy_eq`,
`termTy_eq`, `termTy.eq_cata`, `termsTy.eq_cata`) — no agreement is needed when the fold is the
definition. Weakening moves onto the fold: `argTy_weaken`/`argsTy_weaken` by one arm per
constructor, where the hand `termsTy_weaken` needed three cons arms, one per head constructor,
because `termsTy` split on the head; `termTy_weaken` is the corollary at `false`, its statement
unchanged, so `Typing.lean`'s `check_weaken` simp sets are untouched.

Callers: `argTy_cases` keeps its statement and its proof — the flag reaches a literal argument
and nothing else, so `argTy … const (.var i)` and `termTy … (.var i)` are one term by
definition; `Typed.lean`'s `evalTerm_hasTy`/`evalTerms_hasTy`/`evalTerm_isSome`/
`evalTerms_isSome` read `argsTy` and `argsTy_cons` where they read `termsTy`, and the one site
that had `termTy … (.lit l) = some l.ty` by `rfl` unfolds through `argTy` and `litArgTy_false`
(the literal rule at `false` is an equation, not a definitional identity); `Forms.as_typed` adds
the same two names to its simp set. Everything else — `HasTy`'s rules, the fifty inversions,
`Sound`, `Checker.term?`, the batteries' `#guard`s — names `termTy` opaquely and compiled
untouched. `tools/conform-red` names a `termTy_reflect` that does not exist; it is not a lake
target.

Both roots and `Test.All` build; `argTy_weaken`, `termTy_weaken`, `argTy.eq_cata`,
`argsTy.eq_cata`, `evalTerm_hasTy`, `Forms.as_typed` at `[propext, Quot.sound]`;
`argTy_cases`/`argsTy_cons` at `[propext]`. Census: **78 hand traversals** (`Term` 11, down from
14: the three of the hand term block), **65 with a fold and a connector**; `Term` is 11 of 11
(the driver prints `structural 13 (of which 13 with a fold beside them)`: the two fold members
are rows too); the thirteen without unchanged. `termTy` classifies as delegating to `argTy`.
That count is the 2026-09-18 instrument's. At `dceae006` (2026-10-01), with the instrument's three
blind spots closed (§7.11), the count is **84 hand traversals, 60 with a fold and a connector,
24 without** (named in §7.4).

### 7.10 The fragments by exclusion (2026-09-18, decisions row 35)

Not a callers move: `Straight` (`Program/Fragment.lean`) and `Looped` (`Laws/Program/DenoteB.lean`)
are one hand definition each with the fold beside them, and about twenty-five proof sites unfold
them by name (`simp [Straight]`, `rw [Looped]`, `unfold Straight at h`). The fix for row 35 is at
the definition. §7's earlier line "the algebra names every constructor, row 35 settled" was
overstated: `fold_of` reads the algebra off the hand definition, so a constructor added to `Eff`
fell into `Straight`'s wildcard arm and `Looped`'s fallback to `Straight`, and the generated field
said `false` without anyone having classified it. Now both definitions name every constructor —
twelve excluded arms written `false` in `Straight`, thirteen in `Looped` less `iterate`, the five
leaves and the `perform` row-kind match repeated in `Looped` arm for arm — so a new constructor is
a missing case at each definition until it is classified. `fold_of` converts both as before
(`Straight.eq_cata`, `Looped.eq_cata`, `[propext]`).

Consumers: `Looped.of_straight`'s leaf arms are the hypothesis itself (`Looped` and `Straight` are
one term on a leaf by definition) and its excluded arms `absurd h Bool.false_ne_true`, where the
fallback arm had needed `rw [Looped]` and the wildcard's side goals discharged by hand.
`LoopSound.soundB`'s five leaf arms shared one body whose `have hs : Straight _ = true := hl`
found its term through the fallback (the only way `Looped (.succeed v)` could unify with
`Straight ?e`); they now go through one lemma, `soundB_leaf`, that takes the `Straight` witness
explicitly, one call per leaf. Everything else compiled untouched. Both roots and `Test.All`
build; the census is unchanged (the two rows were structural with folds before and after).

### 7.11 The instrument's three blind spots closed (2026-10-01)

The organization seat of the formal pass and its verifier found the census unable to measure the
distance (`docs/research/2026-10-01-formal-pass/organization/note.md` §1.4, `verify.md` ORG-04 and
§3 M1): it classed a row `wf` only when the definition's own value named `WellFounded.fix`, but
on this toolchain a well-founded definition of two or more arguments keeps its fixpoint in a
`_unary`/`_mutual` helper, and a `Nat` measure uses `WellFounded.Nat.fix`, so `wf` was 0 for every
family; it dropped private definitions with the compiler's internal names; and it saw a `match`
only through the family's own `casesOn`, so a `match` with a catch-all, compiled through a sparse
`casesOn` named after another definition, was invisible. The repair (`Laws/Auto/Traversals.lean`)
reads a definition's own code through the compiler's helpers, admits private definitions under
their written name, and gives a case analysis that does not recurse its own class, `one-level`
(§1). Its red controls are pinned in `Test/Audit/TraversalCensus.lean`: the planted shapes of
`Test/Audit/TraversalFixture.lean` (the instrument of `dceae006` misreads five of the nine and
does not see the private one), and the classes of `Ty.sub` (`wf`), `Codegen.Types.ofNormalized`
(`structural`, `[private]`), `Ty.isFactor` (`one-level`) and `Ty.closed` (`structural`).

At `dceae006`, the instrument before and after (the driver's commands; before: `lake build
Test.Audit.TraversalCensus` replaying the cached run; after: the same commands over the repaired
instrument):

| free object | takers | fold | generated | structural (fold beside) | wf | one-level (fold beside) | delegates | opaque |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `Eff` family, before | 343 | 22 | 40 | 35 (25) | 0 | — | 177 | 69 |
| `Eff` family, after | 348 (5 private) | 22 | 42 | 33 (25) | 4 | 28 (0) | 173 | 46 |
| `Ty`, before | 112 | 1 | 5 | 23 (17; 1 instance) | 0 | — | 45 | 38 |
| `Ty`, after | 115 (3 private) | 1 | 8 | 22 (15; 1 instance) | 1 | 14 (2) | 46 | 23 |
| `Term` family, before | 116 | 0 | 8 | 13 (13) | 0 | — | 19 | 76 |
| `Term` family, after | 116 | 0 | 8 | 12 (12) | 0 | 4 (1) | 18 | 74 |
| `Representation` family, before | 31 | 2 | 4 | 5 (4) | 0 | — | 6 | 14 |
| `Representation` family, after | 33 (2 private) | 2 | 4 | 1 (0) | 2 | 5 (4) | 8 | 11 |
| `Store.Val`, before | 243 | 0 | 28 | 17 (16) | 0 | — | 119 | 79 |
| `Store.Val`, after | 243 | 0 | 85 | 18 (17) | 0 | 64 (2) | 49 | 27 |

Hand traversals (structural and `wf` rows less the nine fold members), with a fold beside them,
without: before **84 / 66 / 18**; after **84 / 60 / 24** — `Eff` 30 / 18 / 12, `Ty` 23 / 15 / 8,
`Term` 10 / 10 / 0, `Representation` 3 / 0 / 3, `Val` 18 / 17 / 1. The equal totals are a
coincidence of two movements:

- **Into the distance** (rows the old instrument printed `opaque` or did not print): the statement
  walks `runStmts`, `runStmts.yieldOf`, `Sched.walkR`, `Sched.walkR.yieldOf` (`wf`) and `loopExit`
  (`structural`); `Ty.sub` (`wf`) and `Codegen.Types.ofNormalized` (private); the private
  `Representation.beq` and `Check.beq` (`wf`); and three `Val` readings in step with a `Ty`
  recursion, each with its `Ty` fold beside it — `Typed.Fits`, `Val.hasTy`, `Codec.encodeRaw`.
- **Out of it** (one-level matches the old instrument counted because they compiled through the
  family's `casesOn`): `actionAt`, `Sched.denoteEffBody`, `Sched.denoteLayerBody`; `Ty.isNever`,
  `Ty.isMember`; `noRow`; `Representation.tag`, `Check.tag`, `Bridge.checkId`,
  `Schema.withChecks?`; `Store.Val.payload`, `Store.Val.tag` — nine of these twelve with a fold
  beside them.

The `one-level` rows (115 in all; the old instrument counted 12 of them as `structural` and missed
103) and the new `generated` rows (3 `Ty`, 2 `Eff`, 57 `Val`) agree exactly with the verifier's
independent probe (`verify-CensusConsistency.lean`: its B + C and D per family). The
exhaustiveness inventory reads the same authored definitions, so it now sees private matches too:
`#exhaustive_gate Effect4.Program.Ty` reports 66 matches, 28 with no catch-all (65 / 27 before);
the new one is `ofNormalized`'s twenty-arm match, which row 119's `Ty.record` must also extend.

## 8. Scout G — the tooling that exists (`docs/research/2026-09-17-lean-tooling-scout-G.md`)

Read against the converter: **no recursion-schemes or generic-programming library exists** for
Lean 4 (Mathlib's `DeriveTraversable` refuses indices, mutual families and recursive fields;
QpfTypes is a v4.25 proof of concept) — `fold_of` is not duplicating anything. What G found
that changes the next steps, all at zero install:

1. **Batteries' linter framework** (`@[env_linter]`, `@[nolint]`, `runLinter` with
   `nolints.json`, parallel `lintCore`, `file:line:col` output) — already vendored: the census's
   `structural`/`wf` classification becomes a linter and the exemption list becomes data,
   instead of a gate written by hand.
2. **`leanchecker`** ships in the toolchain since v4.28: an independent kernel replay of every
   module's declarations — the right trust rung for `eq_cata` connectors that the elaborator
   built without source (a `check-kernel` make target, not yet written).
3. **Core `fun_induction`** proves `f = cata alg` for the accumulator shape when `rfl` will
   not (`fun_induction f <;> simp [cata, alg, *]`): the proof engine for the next iteration.
4. **import-graph at v4.33.0** (`#min_imports`, `#find_home`, `unused_transitive_imports`) turns
   the import-closure rules (core never reaches Laws; the LCNF cut) into checks.
5. **The core deriving toolkit** (`registerDerivingHandler`, `mkHeader`, `mkInstanceCmds`) for
   the generator's emitters.

Dead or blocked at 4.33: lean-egg, LeanInk, QpfTypes, loogle, CanonicalLean, Paperproof, alloy.

### 7.12 The families of `Ty` (probe U, 2026-10-01)

At `630e6c37` the census reads 122 takers of `Ty` (fold 5, generated 8, structural 22, wf 1,
one-level 14) and the gate 66 matches (43 of them in 40 hand definitions, 23 of which have
catch-alls only). Probe U places every row in one of ten families
(`docs/research/2026-10-01-type-language-probe/U/inventory.tsv`) and proves 21 of the hand
traversals equal to a generic fold over the emitted view, and `Val.hasTy` equal to the fold of
its own algebra: the spelling folds are a face table read by one interpreter per face; the
classifiers, four generic folds reading the columns of a classifier table or, for the two located
searches, a hit predicate; the union-spine folds, one fold at four atoms; the mirrors, one
reflection at five carriers. The rule for a constructor append is "no hand case analysis on `Ty`
outside the generated folds and `Laws/Program/Typed/Membership.lean`", checked by
`scripts/check-ty-rule.py` (U's `check-commit4-rule.py`, landed by seat W2) over this instrument's
output (R1–R4); its distance at `630e6c37` is 78 rows (R1 21, R2 13, R3 38, R4 6), the gate on at
the wave's commit 4. The named exemptions for `Ty` are `Fits` and `FlatFits` (the typed state's
module), the derived `Repr` and `DecidableEq` until generated, the two pass-through matchers
(`selectRefusal`, `Decision.arms`' outer match), and the `Test` fixtures and counterexample models.
