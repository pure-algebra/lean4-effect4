# The traversal census — how every definition reads each free object (2026-09-17)

Owner: "do the census; we're smarter now, we can use Lean's metaprogramming to do these
refactors fast if we know what we're shooting for. Lack of a consumer isn't the metric;
coherence of the algebra is — modelled on the universal initial algebra. Build in parallel, a
second file, then slot it in; delete once we're at a good place." Instrument:
`src/Effect4/Laws/Auto/Traversals.lean` (`#traversal_census`); driver:
`Test/Audit/TraversalCensus.lean` (`lake build Test.Audit.TraversalCensus` prints it). Tree at
`58f31703` plus the instrument.

## 1. What the instrument measures

For an inductive and everything mutual with it (the *family*), every definition of the
`Effect4.*` modules that takes a family value, classified by how it reads it:

| class | meaning |
| --- | --- |
| `fold` | through a declared fold (`cataFam`, `cata_eff`, `cata_ty`, …); the algebra is named |
| `generated` | its own recursion, but in a module `tools/Effect4Gen/manifest.json` writes from the signature (`foldMap_*`, `foldM_*`, `view_*`, the `Canonical` encoders) |
| `structural` | its own `match` or structural recursion — a hand traversal |
| `wf` | well-founded recursion with its own `match` |
| `delegates` | never looks inside: hands the value to other rows (named) |
| `opaque` | neither looks inside nor hands it on (stores or returns it) |

Helpers the compiler makes (`noConfusion`, `ctorIdx`, `brecOn.go`, a derived `decEq_n` — 77 of
the first run's 157 "structural" rows for `Eff` were these) are not rows. Nothing is asserted;
the `structural` + `wf` count is the distance from "every traversal is a fold or generated".

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
| `effTy` | `effTy`, `layerTy`, `layersTy`, `stmtsTy`, `effsTy`, `actionTy` | `Program/Typing.lean:283-488` | `Signature → TyEnv → Option EffTy` — an environment threaded through continuations (`Γ ++ [A]`) | **yes**: carrier `R .eff := TyEnv → Option EffTy`, the standard fold-returning-a-function; the continuation arm extends the environment before applying the child result |
| `explain` | `explainEff`, `explainLayer`, `explainLayers`, `explainStmts`, `explainEffs`, `explainAction` | `Program/Typing/Blame.lean:119-303` | as `effTy` plus a path | **yes**, same shape; carrier `TyEnv → List Nat → Option TypeRefusal` |
| `compileEff` | `compileEff`, `compileLayer`, `localBinds`, `actionAt`, `actionAt.entrants` | `Program/Compile.lean:547-1045` | `Point` (fuel, addresses) threaded; `actionAt` also resolves | **exempt this wave** (F-3; the 1,900-line agreement proof is stated against it); carrier `Point → NCode` is expressible |
| `Provision` | `build`, `buildAll`, `docsLayer`, `docsLayers` | `Program/Provision.lean:295-762` | over `LayerTerm(s)` only | **yes**, `R .layer`/`R .layers` carriers, the other five families trivial |
| list projections | `LayerTerms.toList`, `LayerTerms.length`, `Stmts.toList`, `Effs.toList` | `Program/Eff.lean:459-475` | pure | **yes**, and better *generated* — they are the list view of the `nil`/`cons` families the generator already knows |
| `Straight` | `Straight` | `Program/Fragment.lean:18` | `Bool`, `| _ => false` wildcard | **yes**, `R _ := Bool` with `&&`; the algebra names every constructor (row 35 settled for real) |
| `denote` | `denote`, `denoteB`, `denoteBWith`, `denoteWith`, `Looped` | `Laws/Program/{Denote:64,DenoteB:121,185,LoopSound:52,MeaningSound:43}` | meaning into the semantic domain; `With` variants take a parameter | **yes** for `denote`/`Looped` (F-3 first); the `With` variants are the same algebra at a parameter — one algebra with the parameter in the carrier, three definitions become projections |
| `Sched` | `entrantPoints`, `inlineYield`, `denoteEffBody`, `denoteLayerBody`, `denoteLayerZero` | `Laws/Program/DenoteR.lean:158-737` | the R-side evaluator's helpers | **later**: they exist for the simulation proof and follow `compileEff`'s shape |
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
All pure, all on one non-mutual inductive of 16 constructors: the cheapest family to convert
wholesale, and the one where a new constructor (`Ty.app`, row 3; `Ty.record`/`variant`, row 2)
costs 17 hand edits today and one algebra field each after.

### 3.3 `Term` — 14 hand traversals, `cata_term`/`cata_terms` unused

`printTerm`/`printTerms` (`Codegen/PrintLeaf`), `Terms.names?`/`noRow` (`Codegen/Read`),
`Terms.toList`, `Term.scoped`/`Terms.scoped`, `Term.weaken`/`Terms.weaken` (`Eff.lean`),
`evalTerm`/`evalTerms` (`Native`), `termTy`/`termsTy`/`argTy` (`Typing`). Same verdict as `Ty`.

### 3.4 `Representation` — 5 hand, 5 fold

Hand: `withChecks?` (`Authoring`), `Bridge.checkId`, `Bridge.ofSchema`, `Representation.tag`,
`Check.tag`. Fold: the printer (`Codegen/Schema.printAlgebra`), `fieldAdmissible`
(`Check.lean`), `effectfulFieldProperties` (`EffectfulField.lean`). The two `tag` projections
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

The uniqueness theorem is already the proof. `hom_eq_cata_eff` (`Fold.lean:1172`) says: a
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
Effect4.Program` narrows it. Rows are `class ⟨tab⟩ module:line ⟨tab⟩ name [instance] ⟨tab⟩
(family member) ⟨tab⟩ detail`, sorted by class, module, line.
