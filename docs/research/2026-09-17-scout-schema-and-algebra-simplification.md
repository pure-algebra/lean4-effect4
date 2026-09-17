# Scout C — the schema and the algebra: what is still hand-written, and what drifts

2026-09-17. Research only: I edited no tracked file, ran no build, ran no gate. Everything marked
**compiled** comes from a scratch file under
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/aa7ebaa0-7350-4784-b70e-322956de92e8/scratchpad/scoutC/`
type-checked with `lake env lean` against the tree while the coordinator's DI-91/DI-92 slice was
uncommitted. **Read** means I opened the file and quote a path and a declaration name. **Measured**
means a script in that scratchpad counted it over the tree. **Inferred** means a conclusion from
those, not itself checked. Nothing here is **proved** beyond the three probes.

The owner's two additions to the brief are answered in place: drift is the ranking key (§7, §8), and
proper tree types are §2.4 with a compiled probe.

One correction to an earlier draft of this note is kept visible in §5 correction 1: I first wrote
that a new atom costs a wire tag. It does not — `Term.app` carries the atom by name — and the
conclusion about atoms versus literals flips as a result.

---

## 0. Summary

1. The fold group is real and already carries a lot: `Program/Refs.lean` has no hand recursion left,
   `Eff.weaken` is generated, `scopedAt` is a generated algebra on the exponential carrier
   `Nat → Bool`. What is left hand-written is **the printer, the reader, the checker, the checker's
   refusal — and the whole schema tree**.
2. **The schema work did run ahead, and it is measurable.** `src/Effect4/Schema/**` is 9174 lines and
   631 top-level declarations, of which **108 code declarations and 173 theorems have no reference
   anywhere in the tree, tests included** (measured). `Schema/Dimension.lean` has exactly one
   reference outside itself: the import line in `src/Effect4.lean`.
3. **The same fold is hand-written three times.** `Schema/Representation.lean:1255-2111` (857 lines)
   is a hand-written `FoldAlgebra`, `fold`, per-constructor equations, `rebuild` and `fold_rebuild`
   — which is exactly what `tools/Effect4Gen/Fold.lean` emits as `Algebra`, `cata`, the `Hom`
   equations, `Algebra.id` and `cata_id`. `Store/Shape.lean` writes the same traversal six times
   (242 lines). The generator cannot take them today for one reason: `readBlock`
   (`tools/Effect4Gen/Fold.lean:43-73`) decides a child is recursive by its **head constant**, so
   `List Representation` reads as a leaf. Teaching it nested children is one generator feature worth
   about 1100 lines across three files.
4. **The largest drift hole is not volume.** It is **1060 `internal/effect.ts:NNNN`-style citations of
   the pinned rc.112** plus **456 into our own tree** that no gate checks — `check-source-citations.py`
   says so in its own first line: it checks "existence of explicit repository-relative citation paths
   (**not line ranges**)".
5. **There are two schema dialects and no theorem between them.** `Ty.schema`/`Ty.ofSchema`
   (`Schema/Bridge.lean`) and `Effect4.Store.render`/`ShapeDoc.document` (`Store/Shape.lean:425`,
   `:468`) both land in `Representation`. The composite `ofSchema ∘ Store.render : Shape → Option Ty`
   type-checks and **disagrees in five places** (probe 3, compiled): `unit` is lost, `option` is lost,
   `nat` reads back as `int`, and `bytes` and `digest` both **silently widen to `string`**. Nothing
   in the tree states or checks a relation between the two.
6. **The nominal tree type is one missing arm of a map that already exists.** `ofSchema` has **no
   arm for `Representation.reference`** — it falls to `| _ => none` (compiled). `Ty.data
   (name : String)` *is* that arm, and `Document {representation, references}` and
   `ShapeDoc {root, defs}` are the same structure. Probe compiled (§2.4).
7. The nine law and codegen files' 24 or-pattern blocks (**194 lines**, measured) are removable by one
   generated induction principle per fragment predicate. Probe compiled, use site names zero excluded
   constructors, `[propext]` only (§4).

---

## 1. Probes

- `scoutC/P1Exclusion.lean` — the fragment's induction principle, and a use site.
  **Compiled** against the pre-`5185a6cd` tree. `#print axioms refSites_nil'` → `[propext]`.
  I could not re-run it after `33990200`: `Effect4/Laws/Machine/Handles.olean` was absent while the
  coordinator's rebuild was in flight, and the brief forbids me to rebuild. It imports
  `Effect4.Laws.Program.TypedRun` and touches nothing that commit changed, so I expect it to hold,
  but **the coordinator should re-run it before acting on P4.**
- `scoutC/P2Nominal.lean` — a Lean `Tree`, its `Shape`, `acceptsAt`, the sketched typing rules, and
  three red controls. **Compiled**, every `#guard` green, **re-verified after `33990200`**.
- `scoutC/P3Reference.lean` — the two schema dialects, the missing `.reference` arm, and the
  bridge's own exact round trip as the red control. **Compiled**, every `example` green,
  **re-verified after `33990200`**.

---

## 2. Question A — the type descriptions

### 2.1 The inventory

Seven descriptions of "a type" or "a shape of data" (read):

| # | description | where | size | recursion | nominal? |
| --- | --- | --- | --- | --- | --- |
| 1 | `Effect4.Program.Ty` | `src/Effect4/Program/Ty.lean:23` | 16 constructors; the file is 722 lines with the key order, subtyping and normalization | structural only | `handle (target : String)` only |
| 2 | `Effect4.Program.CTy` | `Ty.lean:681` | `{t : Ty // Ty.Canonical t}` | — | — |
| 3 | `Effect4.Program.EffTy` | `src/Effect4/Program/Typing.lean:30` | a 3-field structure (`answer`, `error`, `requires`) | — | — |
| 4 | `Effect4.Store.Shape` / `ShapeDoc` | `src/Effect4/Store/Shape.lean:64`, `:126` | 14 constructors + `{root, defs}`; file 603 lines | **yes**, through `named` resolved in `defs` | **yes** (`struct name`, `sum name`, `named name`) |
| 5 | `Effect4.Representation` / `Document` | `src/Effect4/Schema/Representation.lean:718`, `src/Effect4/Schema/Document.lean:127` | 22 constructors + `{representation, references}`; 2111 + 441 lines | yes, through `reference` into the references table | **yes** (`declaration`, `reference`) |
| 6 | `TypeScript.TypeRef` | `.lake/packages/typescript/TypeScript/TypeRef.lean:12` | 6 constructors | yes | by qualified name |
| 7 | row type arguments | `Effect4.Program.rowTypeArgs`, used at `src/Effect4/Codegen/Read.lean:270` | `List TypeScript.TypeRef` | — | — |

Two mirrors, both generated: `ocaml/eff/eff_types.ml` (header: GENERATED by
`src/OCaml5/Tools/EffGen.lean`) and `ts/eff/eff.gen.ts` (by `tools/Tools/TsGen.lean`);
`ocaml/engine/e4_program_layout.ml` by `scripts/generate-engine-structure.py`.

**Descriptions 4 and 5 are the same idea twice.** Both are "a root plus a named table"; both are
nominal; both have a membership decision. `ShapeDoc` decides membership of a `Val`
(`acceptsAt`, `Shape.lean:161`); `Document` describes a host value. They are joined in one
direction only, by `Store.Shape.render : Shape → Representation` (`Shape.lean:425`) and
`ShapeDoc.document` (`:468`). Nothing goes back.

### 2.2 The maps

| map | where | kind | derivable? |
| --- | --- | --- | --- |
| `Ty.schema : Ty → Representation` | `src/Effect4/Schema/Bridge.lean:37` | embedding | yes — a `cata_ty` instance |
| `Ty.ofSchema : Representation → Option Ty` | `Bridge.lean:60` | partial inverse, with `ofSchema_schema : ofSchema (schema t) = some t` (`Bridge.lean:~108`) | it is a coalgebraic reader; the shape a generated reader has |
| `Effect4.Store.render : Shape → Representation` | `Store/Shape.lean:425` (the namespace is `Effect4.Store`, not `Shape`; `Shape.render` at `:92` is the *Lean-syntax* renderer, `Shape → String`) | total | yes — a `Shape`-algebra instance |
| `ShapeDoc.document : ShapeDoc → Document` | `Store/Shape.lean:468` | total | the above plus a `List.map` |
| `Canonical.shape : α → ShapeDoc`, with `toVal`, `ofVal`, `ofVal_toVal`, `fits` | generated per type, e.g. `src/Effect4/Store/Derived/Value.lean:707` | **already generated** for every type in `tools/Effect4Gen/manifest.json` | — |
| `Codegen.Types.ofTy : Ty → Option TypeRef` | `src/Effect4/Codegen/Types.lean:311` via `ofNormalized:268` | projection, **not** injective (`nat` and `int` both print `number`; the docstring says so) | yes — a `cata_ty` into `Option TypeRef` |
| `Codegen.Types.parseLegacy : String → Option TypeRef` | `Types.lean:263` | a parser, used only to open `Ty.handle`'s stored text | no; R4/R5 retire it |
| `Shape → Option Ty` | **composes today**: `Ty.ofSchema ∘ Effect4.Store.render` | partial, **and wrong in five places** | see below |

### 2.2a Two schema dialects, no theorem between them (compiled)

The last row is the finding that reframes the question. The composite
`shapeTy := Ty.ofSchema ∘ Effect4.Store.render : Shape → Option Ty` type-checks today. `P3Reference.lean`
evaluates it on every `Shape` former. It **agrees** on `bool`, `string` and `list`. It **disagrees**
on five, each by `rfl` or `decide`:

| shape | `shapeTy` answers | why | what it costs |
| --- | --- | --- | --- |
| `unit` | `none` | the store renders `unit ↦ null` (its own header's table); `Ty.ofSchema` reads only `void`, which is what `Ty.schema .unit` emits | a unit-typed value cannot cross |
| `option s` | `none` | the store renders `option s ↦ anyOf [s, null]`; `Ty.schema (.option t)` emits a `declaration "effect/schema/Option"`, and `ofSchema` reads only that | every optional field |
| `nat` | `some .int` | the store emits the `isInt` check alone; `Ty.schema .nat` emits `isInt` **and** `isGreaterThanOrEqualTo 0` | the non-negativity is dropped |
| `bytes` | `some .string` | rendered as a string with a hex pattern check that `ofSchema` ignores | **silent widening** |
| `digest` | `some .string` | the same | **silent widening**: a 32-byte digest becomes any string |

The nominal shapes (`named`, `struct`, `sum`, `anyRef`) are all `none`, **because `Ty.ofSchema` has
no arm for `Representation.reference` or for a `declaration` with a case list**. Read
`Bridge.lean:60-105`: `.declaration rep _ [] _ => some (.handle rep.id)` is the only nominal arm, and
`| .reference (ref : ReferenceKey)` falls through to `| _ => none` (compiled:
`example (k : ReferenceKey) : Bridge.ofSchema (.reference k) = none := rfl`).

The red control is that the bridge's **own** round trip is exact — `Bridge.ofSchema_schema` is proved
in the tree and the probe uses it on `unit`, `nat` and `option bool`. So every disagreement above is
on the other leg, `Effect4.Store.render`, which no theorem relates to `Ty.schema`.

> **Two dialects of one `Representation`, with no agreement lemma and no gate.** Today this costs
> nothing because nobody composes them. The moment §2.4's nominal route or R7/R8's schema printer
> does, it costs a silent widening of `digest` to `string` at a boundary. This is the sharpest answer
> I have to "are we properly utilizing the schema": we are using it twice, differently.

> **And the missing tree type is a missing case of an existing partial inverse.** That is a much
> smaller claim than "add recursive types to `Ty`", and it is why §2.4's price is what it is.

### 2.3 What a new `Ty` constructor costs today, measured

- **27** hand-written case analyses over `Ty` naming ≥ 8 constructors, outside generated files
  (measured; `Ty.lean` 8, `Schema/Codec.lean` 3, `Laws/Program/Admit.lean` 2, `Schema/Bridge.lean` 2,
  `Program/Typed.lean` 2, `tools/Conform/Effect4/LcnfMl.lean` 2, and one each in nine more).
- **39** default-arm case sites over `Ty` across **26** functions in the compiled code (measured from
  `tools/Conform/Effect4/cases-policy.json`). Each silently absorbs the new constructor at run time;
  `make check-cases` turns each into a red `lcnf.cases.default` counterexample, because the gate
  compares `sameSet absorbed cover` (`tools/Conform/Lcnf/Cases.lean:621`). **Detected**, at the price
  of 39 rows a human re-approves one at a time.
- **1** row in `tools/Effect4Gen/wire-tags.json`. Its readers enforce "the active names of a listed
  family are exactly its declared constructors" (read, the file's own comment), so forgetting it is
  **refused**.
- The OCaml and TypeScript mirrors regenerate; `ocaml/engine/e4_program.ml` (423 lines, the one
  hand-written OCaml file left on the engine path) carries a hand arm.
- **222** wildcard arms live in `src/Effect4/Laws/**`, which `check-cases` does **not** scan
  (`tools/Conform/Effect4/cases.json` roots are `Effect4` and `Test`; `Test/Audit/AxiomGate.lean:592`
  prints "Effect4 never reaches Laws"). Most are proof arms and harmless. The **definitions** among
  them — `Denote.Straight`, `Denote.Looped`, `Denote.composite`, `Denote.denote`, `Agreement.depth`,
  `Agreement.steps`, `Loop.depthB`, `Loop.boundB` — silently exclude a new form from every proved
  fragment. That silence is conservative, so it is safe; it is still a silence, because nothing tells
  you the new form has no meaning, no agreement and no soundness.

**Compare what `handle` already costs**, since it is the existing nominal former: 14 mentions in
`Ty.lean` (measured) — `renderRaw`, `members`, `key`, `isNever`, `isMember`, `isFactor`, `sub`
(falls to the `a = b` test), `normalize`, `Normal`, and one line each in `key_injective`,
`Normal.fixed`, `normal_normalize`, plus `members_atom` and `factors_singleton` by `simp_all`.

**If the arms were generated.** `cata_ty` and `TyAlgebra` already exist
(`src/Effect4/Program/Fold.lean:31`, `:49`, generated). A new constructor would then cost: the
constructor, a wire tag, and one field in each algebra instance — which the compiler demands, so
nothing is silent. About half of the 26 absorbing functions are single-argument folds and could move
(`members`, `isNever`, `isMember`, `isFactor`, `renderRaw`, `key`, `normalize`, `factors`, `isTagTy`,
`rawSupportedErrTy`, `Codegen.Types.ofNormalized`, `Schema.Bridge.schema`). `Ty.sub` and `Val.hasTy`
recurse on **two** arguments and stay hand-written (§3 (iv)).

### 2.4 Proper tree types: the nominal route (the owner's question) — compiled

**The owner's facts check out, and the route works.** From `scoutC/P2Nominal.lean`:

- A user's Lean inductive `Tree` gets a `Shape` in exactly the generator's style — a `sum` with a
  wire tag per case, recursion written `.named "Tree"` — copied from `ShapeShape`
  (`src/Effect4/Store/Derived/Value.lean:386`, generated).
- `ShapeDoc.accepts (toVal sample) = true`. A wrong field shape, an unassigned tag, and an **empty
  `defs` table** all give `false`. The empty-table control matters: it proves `named` really is
  resolved and not ignored.
- `hasDataTy defs v name := acceptsIn defs (.named name) v` is a one-line `Val.hasTy` arm. Compare
  `Val.hasTy`'s `.handle` arm (`src/Effect4/Program/Typed.lean:53-64`), a kind-byte test against a
  spelling: the nominal machinery is already there, only the resolver differs.
- **Introduction**: `fieldShapes defs name tag` answers the case's name and its fields, so a
  constructor application types against them. `caseAt` (`Shape.lean:142`) already refuses a tag no
  case carries.
- **Elimination**: `outOf defs name v` reads the value's own tag and hands back the fields. This is
  the functor's `out`, and `Decision.option` and `Decision.tag` are its two special cases — `option`
  is the two-case sum `none | some`, `tag` is the sum over string-tagged pairs. **One eliminator
  subsumes the family.**

**What it makes typed that is raw today.**

1. Scout A's authored reader layer over `TypeScript.Expr`: their finding is that the program runs but
   cannot be typed because no atom or decision can see a `Val.ctor`. `Ty.data "Expr"` against the
   generated `ShapeDoc` for `TypeScript.Expr` types it, with no new value form.
2. Folds over cons lists and trees — the loop note's `reduceT`
   (`2026-09-17-loop-sugar-and-list-elimination.md` §3) runs and does not type for this reason.
3. **Any user-declared Lean inductive as language data.** This is the one that matters for the S9a
   agent unlock: the generator already emits the `Shape`, `toVal`, `ofVal` and the `fits` proof for
   every type in the manifest, so an agent that declares an inductive gets a language type for free.

**What the printer prints.** `src/Effect4/Codegen/Schema.lean` (`documentExpr`, `representation`)
already prints a `Document` as TypeScript, and `Shape.render`'s table maps `sum ↦ variant` with a
`_tag` discriminant, `struct ↦ struct`, an all-nullary `sum ↦ anyOf` of string literals (read, the
`Shape.lean` header). So `ofTy (.data n)` is `.name [n] []` at the use site plus one emitted
`export type n = …` per named shape in the module's table — the declaration hoisting the layer block
already does. Nothing is invented.

**Where `Shape → Ty` is partial**: exactly `bytes`, `digest`, `ref kind`, `anyRef`. Everything else
maps, once `data` exists. That is a clean rule and I would write it into the module header.

**Should `option` and `list` then be derived?** No — a compiled red control says why:

```
#guard ListNatDoc.accepts (.list [.nat 1, .nat 2]) = false
#guard ({ root := .list .nat, defs := [] } : ShapeDoc).accepts (.list [.nat 1, .nat 2]) = true
```

The native `Val.list` and the tagged cons encoding are **different values**. `Val` has `list`, `pair`,
`none`, `some` as primitive frames (`src/Effect4/Store/Val.lean:150-166`) and the rows and atoms
answer those frames, not `ctor`. Retiring `Ty.list` for a nominal `ListNat` would change the value
every row answers, the bytes and the printed image.

> The nominal eliminator **sits beside** the loop note's five-atom kit; it does not subsume it.
> `uncons`/`nil`/`cons`/`none`/`some` are about `Val.list`, `Val.none`, `Val.some` — frames the host
> already speaks. `Ty.data` is about `Val.ctor` — the frame nothing in the term language can see.
> They close different gaps. The atoms are the smaller job; the nominal route is the general one.

One consequence worth the owner's attention: with `Ty.data`, `Decision.option` and `Decision.tag`
become instances of one eliminator, so the `Decision` family stops growing. That is a reason to
settle the nominal route **before** any further `Decision` constructor (§8 P10's rider).

---

## 3. Question B — hand recursions the generated fold already gives

What the fold group emits per family (read, `src/Effect4/Program/Fold.lean`, 3545 lines for four
families): `<F>Algebra`, `cata_<f>`, `<F>Hom`, `hom_eq_cata_<f>`, `<F>SelfCarrier`, `<F>Algebra.id`,
`foldMapAt_<f>` (path-indexed monoid fold), `foldMap_<f>`, `<F>MAlgebra`, `Algebra.toM`,
`MAlgebra.map`, `MAlgebra.toSeq`, `foldM_<f>`, `foldM_eq_cata_<f>`, `foldM_id_<f>`,
`foldM_natural_<f>`, plus for `Eff` the frontier family, `EffAlgebra.onRef` and `Eff.weaken` with its
fold theorem (`Fold.lean:3062-3066`).

Measured: 57 declarations outside generated files name ≥ 6 `Eff` constructors. I read the top 30 and
classify:

**(i) Already a fold instance.** All of `src/Effect4/Program/Refs.lean` (259 lines): `Eff.refSites`
and its six siblings are `foldMapAt_*` yields (`:110-122`); `expandRound` is one override of
`EffAlgebra.id` (`:131-147`); `layerPaths` is a second yield (`:164-176`). `Eff.weaken` is generated.
`Program/Scoped.lean` (302 lines, generated) is `scopedAlgebra` run by `cata_eff` on `Nat → Bool`.

**(ii) A catamorphism that could be `cata_eff`/`foldMap_eff`, with the algebra stated.**

| declaration | where | lines | carrier | algebra |
| --- | --- | --- | --- | --- |
| `Denote.Straight` | `src/Effect4/Program/Fragment.lean:20` | 20 | `Bool` | `foldMap_eff true (· && ·) e straightHead`, `straightHead` one Boolean per constructor with `.perform op _ ↦ (NativeOp.row op).kind == .sync` |
| `Denote.Looped` | `src/Effect4/Laws/Program/DenoteB.lean:123` | 13 | `Bool` | the same with `iterate ↦ true` |
| `Denote.composite` | `DenoteB.lean:175` | 7 | `Bool` | a pure head predicate; no recursion at all — it is `Eff.head ∈ compositeHeads` in disguise |
| `Agreement.depth` | `src/Effect4/Laws/Program/Agreement.lean:32` | 11 | `Nat` | `cata_eff` with `max` at branches, `+1` per node |
| `Agreement.steps` | `Agreement.lean:43` | 12 | `Nat` | `cata_eff` with `+` and per-constructor constants |
| `Loop.depthB` / `Loop.boundB` | `Agreement/Loop.lean:233`, `:276` | 11 + 12 | `Nat` | the same two with an `iterate` arm |
| `Codegen.readable` | `src/Effect4/Codegen/Read.lean:767` | 60 inside its mutual | `Nat → Bool` | **`scopedAlgebra` conjoined with one Boolean per constructor** |

That last row is worth reading twice. `scopedAlgebra.eff_catchIf` is
`fun a0 a1 a2 n => a0.scoped (n+1) && a1 n && a2 (n+1)` (`src/Effect4/Program/Scoped.lean:43`,
generated from `binders.json`); `readable`'s `.catchIf` arm is
`test.scoped (n + 1) && readable sig spell n body && readable sig spell (n + 1) handler`
(`Read.lean:779-780`). Character for character the same expression. **`readable` re-encodes the
binder table by hand**, and nothing but a reader's eye keeps the two in step (§7 D6).

Lines saved on the five `Bool`/`Nat` folds: about 60 of 86 — small. **The prize is the fusion, not
the lines.** `hom_eq_cata_eff` says any function agreeing with an algebra arm by arm *is* the fold.
That is precisely what `denoteB_straight` (70 lines), `Looped.of_straight` (35), `denoteB_mono`
(101) and `steps_le_boundB` (35) prove by hand (measured). `Looped.of_straight` says the `Straight`
algebra factors through the `Looped` one — a hand-rolled instance of fusion. With both as
`foldMap_eff` on `Bool` with head predicates ordered `hS ≤ hL`, it is one monotonicity lemma over
`foldMap_eff`, proved once for all predicates.

**(iii) Needs a scheme the generator does not emit.**

| declaration | where | lines | what is missing |
| --- | --- | --- | --- |
| `effTy` and the `Typing.lean` mutual | `src/Effect4/Program/Typing.lean:282-556` | 275 | a **monadic fold with an inherited attribute**: carrier `TyEnv → Option EffTy`. `foldM_eff` exists and `cata_eff` takes any carrier, so this is expressible today; nobody has done it |
| `explainEff` / `blame` | `src/Effect4/Program/Typing/Blame.lean:118-384` | 267 (+ 335 for its law at `:431-765`) | nothing — this is `effTy` in the `Except` monad. §8 P7 |
| `printKey` and the printer mutual | `src/Effect4/Codegen/Print.lean:320-588` | 269 | a fold with an inherited attribute (the binder level) into a `Doc`/`Expr`; R1/R2 are already the plan for the codomain |
| `compileEff` | `src/Effect4/Program/Compile.lean:549-640` | 92 | a fold into a continuation carrier (`Code → Code`) — higher-order, not a paramorphism |
| `readEff`, `read_print`, `printRow_readable` | `Read.lean:1758-2154`, `:3324-3493` | 397 + 170 | a coalgebra from `Expr`, not a fold; R5's generic reader is the home |

**(iv) Genuinely not a fold.** `Ty.sub` (`Ty.lean:373`) and `Val.hasTy`
(`src/Effect4/Program/Typed.lean:34-89`, with `hasTy_sub`'s quadratic case list at `:150-330`): both
recurse on **two** arguments, so they are folds on a product and would need a `zip` scheme that at
16 × 16 arms should not exist. Leave them.

---

## 4. Question C — the repeated case lists, and the fix (compiled)

**Measured:** 24 or-pattern blocks naming ≥ 8 `Eff` constructors, **194 lines of pure constructor
enumeration**, in nine tracked files:

```
src/Effect4/Laws/Program/Agreement/Loop.lean     6 blocks, 50 lines
src/Effect4/Laws/Program/DenoteB.lean            4 blocks, 32 lines
src/Effect4/Laws/Program/Agreement.lean          3 blocks, 29 lines
src/Effect4/Codegen/Read.lean                    2 blocks, 18 lines   (one names all 25)
src/Effect4/Laws/Program/DenoteR.lean            2 blocks, 14 lines
src/Effect4/Laws/Program/MeaningSound.lean       2 blocks, 13 lines
src/Effect4/Laws/Program/LoopSound.lean          2 blocks, 12 lines
src/Effect4/Laws/Program/Agreement/Machine.lean  1 block,  12 lines
src/Effect4/Laws/Program/TypedRun.lean           1 block,   7 lines
src/Effect4/Program/Typing.lean                  1 block,   7 lines   (names all 25)
```

The brief named five law files; the true count is nine, and two of them are outside `Laws`.

**Negative result (compiled).** A cases principle ending in a trailing variable pattern
`| e => leaf e rfl` does **not** elaborate: Lean does not split a trailing variable pattern, so
`rfl : composite e = false` has no head to reduce at. The error is
`Application type mismatch: rfl has type ?m = ?m but is expected to have type composite e = false`.
The eliminator must therefore enumerate the excluded constructors — **once**, in generated code.

**Positive result (compiled).** `scoutC/P1Exclusion.lean` defines

```lean
@[elab_as_elim]
theorem Looped.recOn {motive : NativeEff → Prop}
    (leaf : ∀ e, composite e = false → Straight e = true → motive e)
    (iterate : ∀ c i t s r b, Looped b = true → motive b → motive (.iterate c i t s r b))
    …  -- seven more composite arms, each with its children's `Looped` and its IH
    : ∀ e, Looped e = true → motive e
```

— the induction principle of the fragment `Looped`, read off `Looped`'s own definition. The 17
excluded constructors appear once (`| .succeed a, h => leaf (.succeed a) rfl h`, …).
`Looped.refSites_nil` (`src/Effect4/Laws/Program/TypedRun.lean:30-71`, 42 lines of which 7 are the
or-pattern) restates as 25 lines naming **zero** excluded constructors, at `[propext]`.

Two practical notes from the probe:

- `induction e using Looped.recOn` needs the fragment premise handled; `induction e, h using …` is
  refused ("Too many targets"); the working form is
  `refine Looped.recOn (motive := …) ?leaf ?iter … e h` with named `case`s. The generator should emit
  the recursor **and** a tactic wrapper, as `authoring_scoped` wraps the scope dispatcher.
- The `leaf` arm still does `cases e <;> first | rfl | simp_all [composite, Straight]`. That is a
  *tactic* enumeration, not a source one: it survives an alphabet change untouched.

**The head classifier** the brief suggests (`Eff.head : Eff Op → EffHead` with `heads_complete`) is
worth having for a different reason (§7 D3), but it does **not** replace the recursor: these proofs
need the children of the composite forms, which a head throws away. Build both.

---

## 5. Question D — the loop note's list evaluation, checked

Against `docs/research/2026-09-17-loop-sugar-and-list-elimination.md` §3. (Its §2, the sugar, landed
at `33990200` while I was writing — `Program/Authoring/Loops.lean`, four functions, no constructor,
no atom, no wire tag. Nothing below is affected: §3 is the open half, and that commit's own message
says so: "the list fold stays in the probe: it is untyped until the language can build and take apart
lists".)

**Holds.**

- `Ty` has `list`, `option`, `prod` (`Ty.lean:31-33`) and no recursion, so a tagged cons list has no
  type. Confirmed.
- No term builds an `Option`: `NativeAtom` (`src/Effect4/Program/NativeAtom.lean:24-37`) has `isSome`
  and `getOrElse` and nothing producing `.none`/`.some`. Scout B's S-B3 confirmed.
- Generic atoms are already the norm: `nativeAtomTy` (`NativeAtom.lean:111-119`) answers `none` — a
  scheme, not a monomorphic row — for `eq`, `pair`, `fst`, `snd`, `strings`, the four `cause*`,
  `tagIs`, `isSome`, `getOrElse`. So `none`/`nil` answering `option never`/`list never` fits.
- `Ty.sub` is covariant at `list` and `option` with `never` below everything (`Ty.lean:377-386`,
  `sub_option_of_ne`, `sub_list_of_ne`), so `forEach`'s empty accumulator under a stated cursor type
  is sound as written. Confirmed.
- I did **not** open `vendor/effect-4.0.0-rc.112/src/Effect.ts`, so `:638` `reduce` and `:1088`
  `forEach` are repeated from the note, not confirmed (§9).

**Three corrections. The first is a correction to an earlier draft of this note, not to the loop
note — I got it backwards first and the evidence is below.**

1. **An atom costs no wire tag and no compatibility exposure.** `Term.app (atom : String)`
   (`src/Effect4/Program/Eff.lean:255`) carries the atom **by name**, not by constructor tag, and
   `Effect4.Program.NativeAtom` is correctly **not** among the 21 families in
   `tools/Effect4Gen/wire-tags.json` (read). So the atom alphabet is open by name: adding one moves
   no byte and cannot fire `check-compat`. The note's price is right on that axis; what it does omit
   is `ocaml/engine/e4_program.ml` (423 lines, hand) with a translation arm per atom, and
   `harness/truth/prelude.ts` (379 lines, hand) with an export plus a `selfTestCases` row. Call it
   5 × ~75 lines, no wire conversation.
2. **Keep `nil`, `cons`, `none`, `some` as atoms, not literals** — the opposite of what I first
   wrote, and now with the evidence. Two facts settle the note's open question ("whether nullary
   atoms are allowed, or whether `none`/`nil` are literals"):
   (a) `Effect4.Program.Lit` **is** a listed wire-tag family, so a literal costs a tag plus `Lit.ty`,
   `Lit.toVal`, `printLit` and both mirrors, where an atom costs none of that;
   (b) `cons` and `some` take arguments and `Lit` holds nullary values only
   (`unit | nat | bool | str`, `Eff.lean:235`), so they could not be literals in any case.
   And nullary atoms are already reachable: `strings` has `arity = none` (`NativeAtom.lean:96`) and
   its docstring says it builds the list "including the empty list" (`:20`), so `strings()` with zero
   arguments works today. **Nullary atoms are allowed; literals would be strictly dearer.**
3. **`Decision.list` is rightly rejected, for a sharper reason.** With `Ty.data` (§2.4) the whole
   `Decision` family collapses into one nominal eliminator, so a fourth `Decision` constructor spends
   in a currency about to be retired.

**The theorem the algebra gives.** The note's claim that `reduce` is the catamorphism recovered as a
theorem is right and the machinery is in place: `Laws/Program/Iter.lean` has `iter`, `iter_succ`,
`iter_uniform`, `iter_congr`; `Laws/Program/DenoteB.lean` has `denoteB`, `meaningB`, `denoteB_mono`;
`Laws/Program/Agreement/Loop.lean` carries it to the machine. Budget `length xs + 1` is the right
statement and `iter_uniform` the right engine. I did not attempt the proof.

**A fourth route the note does not list.** `uncons` could be a `sync` **row** rather than an atom
(generated wrapper, generated OCaml carrier, one prelude export, no wire-tag appendix). But
`iterate`'s test is a *term* and a row's answer is a *program* answer, so the test
`isSome (uncons rest)` still needs the term-level atom. The note's conclusion stands.

---

## 6. Question E — the generators, and the schema tree

### 6.1 Is there one signature document?

Nearly. `tools/Effect4Gen/manifest.json` is one document with 17 groups, and
`tools/Effect4Gen/Driver.lean` needs no change to add one (read, its header). Each group names its
*types*; the generator then reads the **Lean environment** for constructors, fields and types
(`InductiveVal.ctors`: 30 uses in `tools/Effect4Gen/Main.lean`, 18 in `Authoring.lean`, measured). So
the inductive's own declaration already drives the codecs, `Shape`, `toVal`/`ofVal`/`fits`, the folds,
`Node.child`/`setChild`, the lifts, the OCaml variants and the TypeScript nodes. 14 248 lines of
committed Lean are generated from it (measured, the 17 outputs).

The partial inputs beside it:

| file | what it adds | checked against the inductive? |
| --- | --- | --- |
| `tools/Effect4Gen/binders.json` | which argument is elaborated under which binders (13 rows + a 5-key profile) | **partly**: a constructor with **no row binds nothing, silently**, and `Node.binders`, the lifts and `scopedAt` are then all consistently wrong together |
| `tools/Effect4Gen/wire-tags.json` | the wire tag per constructor (21 families) | **yes, enforced**: "the active names of a listed family are exactly its declared constructors"; "every inductive family of the program world must be listed" |
| `tools/Conform/Effect4/cases-policy.json` | which default arms may absorb what (9 families, 153 sites) | **yes, by comparison**: `sameSet absorbed cover`, `unlisted: refuse` |

### 6.2 What is still hand-listed that the declaration determines

1. **`Effect4.Program.arms` and `constructorNames`** (`src/Effect4/Program/Eff.lean:524`, `:552`).
   Two hand lists of 25, guarded only against **each other**
   (`#guard arms.map Arm.constructor = constructorNames`) and a hand-typed length
   (`#guard constructorNames.length = 25`). **Measured: neither has any consumer outside those two
   guards.** Nothing relates either to the `Eff` inductive. The cleanest silent-stale list in the tree.
2. The seven wildcard-terminated fragment definitions of §2.3, outside the scan.
3. `readable`'s binder levels (§3).

### 6.3 The one change that removes the most hand regeneration

The coordinator had to run eleven groups by hand in a fixed order, then `make gen-lcnf`, then
`python3 scripts/generate.py --only eff`. The cause is visible in `Driver.lean`: it runs every group
in one process (`for g in groups do … runLake (generateArgs …)`) and **never rebuilds between
groups**, while the `Fold` group emits `src/Effect4/Program/Fold.lean` which the `Scoped` group then
imports. After an alphabet change the first pass is always stale downstream.

> Give each group an `After` list in `manifest.json` and have the driver `lake build` between groups
> whose outputs another group imports. Then `make gen-derived` is one command and the order is data,
> not a habit. (§8 P6.)

### 6.4 The schema tree: what ran ahead, measured

`src/Effect4/Schema/**` is **9174 lines** in 13 modules and **631 top-level declarations**
(`def`/`abbrev`/`structure`/`inductive`/`theorem`, instances excluded). Measured references across
`src`, `tools`, `Test`, `harness`, `ts`, `scripts`:

| module | lines | code decls with no use outside the file | of which no use *anywhere*, tests included | theorems with no use anywhere |
| --- | --- | --- | --- | --- |
| `Annotations.lean` | 2304 | 19 / 31 | **15** | **65 / 69** |
| `Check.lean` | 1827 | 19 / 24 | **14** | 15 / 79 |
| `Representation.lean` | 2111 | 19 / 47 | **14** | 30 / 80 |
| `EffectfulField.lean` | 982 | 38 / 52 | **30** | **41 / 44** |
| `Endpoint.lean` | 395 | 17 / 36 | 7 | 3 / 7 |
| `Document.lean` | 441 | 3 / 8 | 3 | 10 / 14 |
| `Authoring.lean` | 278 | 11 / 59 | 7 | 8 / 14 |
| `Codec.lean` | 249 | 8 / 21 | 8 | — |
| `Bridge.lean` | 223 | 8 / 9 | 6 | 0 / 2 |
| `Transform.lean` | 101 | 2 / 10 | 2 | — |
| `Dimension.lean` | 102 | 1 / 3 | 1 | 1 / 1 |
| `Image.lean` | 58 | 1 / 8 | 1 | — |
| `Payload.lean` | 103 | 0 / 13 | 0 | — |
| **total** | **9174** | **146 / 321** | **108** | **173 / 310** |

Caveats I want on the record: a theorem's job is often to be *proved*, not called, so the theorem
column overstates; `simp` lemmas are used without being named; and re-exports count as use
(`src/Effect4/Api.lean:530` exports `Endpoint`, `ApiSpec`, `SchemaFn`, `SchemaTransform`). With those
allowances, **108 code declarations with no consumer anywhere** is still a hard number.

Two modules to name specifically:

- **`Schema/Dimension.lean`** (102 lines, the `effect4/codegen` annotation key) has exactly one
  reference outside itself: `import Effect4.Schema.Dimension` at `src/Effect4.lean:56`. Its key is
  read by nothing — not by `Codegen/Schema.lean`, not by `tools/Tools/TsGen.lean`, not by the OCaml
  emitters, although its own header says it is "read by the emitters".
- **`Schema/EffectfulField.lean`** (982 lines): 30 of its 52 code declarations and 41 of its 44
  theorems have no reference anywhere. Its one production consumer is
  `src/Effect4/Codegen/EffectfulField.lean`.

### 6.5 The same fold, written three times

**`Schema/Representation.lean:1255-2111` (857 lines)** is a hand-written
`Representation.FoldAlgebra` (a 24-field two-sorted algebra, `:1270`), `Representation.fold`
(`:1300`), `Check.fold` (`:1349`), nine private helper recursions, one public constructor equation
per constructor (`Representation.fold_declaration`, `fold_reference`, … `:1585-1810`),
`FoldAlgebra.rebuild` (`:1815`) and `fold_rebuild` (`:1850`).

Set that against what `tools/Effect4Gen/Fold.lean` emits for a family: `Algebra`, `cata`, `Hom` plus
`hom_eq_cata` (which *is* the constructor-equation contract), `Algebra.id` plus `cata_id` (which *is*
`rebuild` plus `fold_rebuild`), and for free `foldMap`, `foldMapAt`, `MAlgebra`, `foldM`,
`foldM_eq_cata`, `foldM_id` and `foldM_natural`. It is the same construction, one hand-written and
one generated, and the hand one is missing the monadic half.

**`Store/Shape.lean` writes the same traversal six times** (measured): `render`/`renderFields`/
`renderCases` (`:90-114`), `acceptsAt`/`acceptsList`/`acceptsFields` (`:158-191`),
`wellTagged`/`wellTaggedFields`/`wellTaggedCases` (`:207-224`), the monotonicity block (`:267-351`),
`render : Shape → Representation` with its two helpers (`:423-454`), and `printIn` (`:489-536`).
242 lines, six copies of "recurse into a `Shape`, a `List (String × Shape)` and a
`List (String × Nat × List (String × Shape))`".

**Why the generator cannot take them today.** `readBlock` (`tools/Effect4Gen/Fold.lean:43-73`)
decides a field is recursive by the **head constant** of its type:

```lean
let recFam := match head with
  | .const n _ => if members.contains n then some (famLabel n) else none
  | _ => none
```

So `List Representation` has head `List` and reads as a leaf. The `Eff` family sidesteps this by
having explicit cons-types (`Terms`, `Stmts`, `Effs`, `LayerTerms`) — the header of
`src/Effect4/Program/Eff.lean:30-33` says exactly that, and gives the reason (the nested-inductive
`DecidableEq` handler this tree refuses). The Canonical/codec generator already *does* walk
`Representation`'s nested children — `src/Effect4/Store/Derived/Schema.lean:644-681` emits
`.list (.named "ElementOf")` and the rest — so the walk exists, in a different code path.

Teaching `readBlock` a child-position language (`direct | list | option | listOf ⟨record with a ρ
field⟩`) and giving `recComb`/`foldMapOf` the matching combinators is, I estimate, ~150 lines of
generator against ~1100 lines deleted across `Representation.lean`, `Shape.lean` and
`Test/Schema/RepresentationFoldContract.lean` (334 lines). **Inferred**, not measured by doing it.

---

## 7. Where hand authoring can silently go stale today

**Silent** = no gate fails. **Detected** = a gate fails, but a human must then re-approve rows.
**Impossible** = one source, so there is nothing to keep in step.

| # | hand-maintained thing | the single source it should come from | today | the gate, if any |
| --- | --- | --- | --- | --- |
| D1 | **1060 rc.112 `X.ts:NNNN` citations** in `src/`, `ts/`, `tools/` (measured; `Machine/Stores.lean` 150, `Program/Config.lean` 111, `Program/Compile.lean` 91, `Schema/Check.lean` 48, `Machine/Fibers.lean` 46, `Program/Eff.lean` 40, …) | the pinned `vendor/effect-4.0.0-rc.112/src` tree | **silent** | `scripts/check-source-citations.py` checks "existence of explicit repository-relative citation paths (**not line ranges**)" — its own line 2 |
| D2 | **456 `src/…/X.lean:NNN` citations into our own tree** (measured) | the tree | **silent** | same |
| D2b | **the two schema dialects** (§2.2a): `Ty.schema` and `Effect4.Store.render` both land in `Representation` and disagree on `unit`, `option`, `nat`, `bytes`, `digest` | one rendering table | **silent, and already wrong** | none — no theorem, no guard, no gate relates them |
| D3 | `Eff.arms`, `Eff.constructorNames` (`Program/Eff.lean:524`, `:552`) | the `Eff` inductive | **silent** | only the two mutual `#guard`s |
| D4 | the eight fragment/measure definitions with wildcards (`Straight`, `Looped`, `composite`, `denote`, `depth`, `steps`, `depthB`, `boundB`) | the alphabet plus a stated admission list | **silent** — a new form is excluded, conservatively, with nobody told | `check-cases` does not scan `src/Effect4/Laws/**` |
| D5 | `binders.json`'s 13 rows and 5-key profile | the `Eff`/`ActionTerm`/`LayerTerm` inductives plus one decision per constructor | **silent** for a constructor with no row | none; `scopedAt`, `Node.binders` and the lifts stay consistently wrong together |
| D6 | `readable`'s binder levels (`Codegen/Read.lean:767-810`) | `binders.json`, already read by `scopedAlgebra` | **silent** (two encodings of one table) | `check-ts-reader` only compares the *two readers*, so a shared error is invisible |
| D7 | `Schema/Dimension.lean`'s claim to be "read by the emitters" | the emitters | **silent and already false** | none |
| D8 | `harness/truth/prelude.ts` (379 lines) | `NativeAtom` via `ts/eff/profile.gen.ts` | **detected, presence only** | `preludeInventoryFailures` (`harness/truth/prelude-inventory.ts`) requires a self-test case per profile atom; the behaviour check is the hand `selfTestCases` table, so a wrong implementation with a right-looking case passes. Host lane (`check-truth`), not `make check` |
| D9 | `ts/eff/read.ts` (1547 lines, "the one hand-written path of this package") | `src/Effect4/Codegen/Read.lean` | **detected on the corpus** | `check-ts-reader` runs both readers over every corpus program with `--oracle`; a construct the 400-program corpus never draws drifts silently. R6 deletes the file |
| D10 | `ocaml/engine/e4_program.ml` (423 lines) | the program alphabet, via LCNF | **detected, names only** | its own `pin ()` compares `source_ctor_names` with `engine_ctor_names` from the generated `e4_program_layout.ml`; `check-ocaml` runs it. Arms are not compared |
| D11 | `cases-policy.json` covers (153 sites, 39 on `Ty`, 12 on `Eff`) | the compiled code | **detected** | `make check-cases`, `sameSet absorbed cover`, `unlisted: refuse` |
| D12 | the 24 or-pattern blocks (194 lines) | the fragment predicate | **detected loudly** — the proofs stop compiling — at the cost of nine files edited per alphabet change | `make check` |
| D13 | `Print.heads` / `Print.reserved` | the `Head` inductive | **impossible already** | `heads_complete (h : Head) : h ∈ heads := by cases h <;> decide` (`Codegen/Read.lean:111`), plus `tools/Tools/TsGen.lean:832` cross-checking the reader's heads against `Print.lean`'s `.ident` literals |
| D14 | `NativeAtom.all` | the `NativeAtom` inductive | **impossible already** | `all_complete (atom) : atom ∈ all := by cases atom <;> simp [all]` (`NativeAtom.lean:47`) |
| D15 | `wire-tags.json` | the inductives | **impossible already** | every reader enforces "active names are exactly the declared constructors" |

D13, D14 and D15 are the estate's own three answers to this problem — a proved `_complete` lemma, a
generated table, a checked JSON file. **Every row above D13 is a place where none of the three was
applied.** That is the shape of the whole recommendation.

---

## 8. Proposals, ranked by drift removed, then lines

Twelve, as the brief asks. "Under a day" means a slice the coordinator can land in one sitting.

### Low-hanging, land now

**P1 — the alphabet's own inventory, generated and guarded.** *Drift: makes D3 impossible and turns
D4 from silent to red.* Two halves of one idea, that a hand list must answer to the inductive:
(a) emit `constructorNames` from `InductiveVal.ctors` (`tools/Effect4Gen/Authoring.lean` already
reads it), emit a flat `EffHead` enum with `Eff.head` and `heads_complete` — the D13 idiom applied to
the program alphabet — and make `arms` a total function on `EffHead`, so a missing row is a type
error rather than a `#guard` against a second hand list;
(b) for each fragment predicate write `#guard constructorNames.filter admits = [...]`, so a new
constructor makes the guard red and the author must say whether the fragment admits it.
*Deletes:* 10 hand lines. *Adds:* ~40 generated plus 8 guard lines. *Risk:* very low.
*Gate:* `make check`, `check-gen`. *Under a day:* yes — (b) is ten minutes and is the cheapest drift
fix in the note; do it first.

**P2 — check line numbers in citations.** *Drift: turns 1516 silent staleness sites (D1, D2) into a
gate.* `scripts/check-source-citations.py` already has the token regex, the inventory and a baseline
mechanism. Extend `TOKEN`/`GIT_TOKEN` to capture `:NNN(-MMM)?` and refuse a range past the file's
length; add a second regex for the rc.112 form (`internal/effect.ts:1275`, `Layer.ts:1438`) resolved
against `vendor/effect-4.0.0-rc.112/src`. Existence-of-line is cheap and catches every pin move and
every file that shrank; anchor tokens can come later.
*Adds:* ~40 lines of Python plus a baseline like `generated/citation-baseline.txt`.
*Deletes:* nothing. *Risk:* low. *Gate:* `make check-citations`. *Under a day:* half of one.

**P3 — pin the two schema dialects against each other.** *Drift: turns D2b from silent-and-already-
wrong into a `#guard`.* One test file with the thirteen rows of §2.2a as `#guard`s on
`Ty.ofSchema ∘ Effect4.Store.render`, recording what it does today, so the next edit to either
rendering table is a red row rather than a silent widening of `digest` to `string`. Whether the five
disagreements should be *repaired* is a separate question and belongs with P11.
*Adds:* ~25 lines in `Test/Schema/`. *Deletes:* nothing. *Risk:* none — it pins behaviour, it does
not change it. *Gate:* `make check`. *Under a day:* an hour.
**The cheapest thing here that touches the owner's actual question about the schema.**

**P4 — the fragment's induction principle, generated.** *Drift: 194 lines in nine files become
zero (D12).* **Compiled** (§4). Generate, per fragment predicate named in a small table, a recursor
`<P>.recOn` with one arm per admitted constructor (carrying the children's predicate and IH) and one
`leaf` arm carrying the refutation, plus a tactic wrapper, as `authoring_scoped` wraps the scope
dispatcher. *Follow-on, same slice or the next:* with the fragments reached in one place, restate
`Straight`, `Looped`, `depth`, `steps`, `depthB`, `boundB` as `foldMap_eff` instances (§3 (ii)), so
`Looped.of_straight` (35 lines) and `steps_le_boundB` (35 lines) become corollaries of one
monotonicity lemma over `foldMap_eff` on `Bool` instead of two hand-rolled fusion instances.
*Deletes:* 194 lines of enumeration and ~70 of hand fusion; each touched theorem shrinks 15–40 %
(`Looped.refSites_nil`: 42 → 25, measured on the probe). *Adds:* ~80 generated lines per fragment.
*Proof consequence:* none for the recursor — the probe's restatement is `[propext]`, as the original
is. The follow-on changes the definitional unfolding, so every `simp [Straight]` in the Laws tree
must be revisited; that is its real cost.
*Risk:* low for the recursor, medium for the follow-on. *Gate:* `make check`.
*Under a day:* the recursor yes, one file at a time; the follow-on no.

**P5 — `readable`'s scope half from `binders.json`.** *Drift: removes D6 entirely.*
`readable`'s binder arithmetic is `scopedAlgebra`'s, expression for expression (§3). Emit the scope
conjunct; `Read.lean` keeps only the per-constructor "the printer keeps this" Boolean.
*Deletes:* ~35 lines. *Risk:* low, but it belongs **inside** the R4/R5 packet, which is already
rewriting `readable`; taken separately it would collide.
*Gate:* `make check`, `check-ts-reader`. *Under a day:* yes, as part of R5.

**P6 — the driver rebuilds between groups, and the order is data.** *Drift: removes the
fixed-order-by-hand ritual (§6.3).* An `After` field per group in `manifest.json` and a `lake build`
between groups whose outputs another imports. *Adds:* ~30 driver lines plus one field per group.
*Deletes:* the eleven-command ritual. *Risk:* low; the driver already shells out to `lake`.
*Gate:* `make check-gen-full`. *Under a day:* yes.

### Bigger, still no ruling needed

**P7 — the checker in the refusal monad; `explain` becomes a projection by construction.**
*Drift: makes a whole class impossible; deletes the most lines of any proposal here.*
`effTy` (`Program/Typing.lean:282-556`, 275 lines) answers `Option EffTy`; `explainEff`
(`Program/Typing/Blame.lean:118-384`, 267 lines) walks the same tree in the same order to locate the
refusal; `explainEff_none_iff` (`:431-765`, 335 lines, at `maxHeartbeats 1600000`) proves they agree
arm by arm. **602 lines whose only job is to keep two copies of one checker in step.**
The algebra: `Except ε` and `Option` are related by the monad morphism `Except.toOption`, and
`MonadMorphism` with `foldM_natural_eff` is *already generated* (`Program/Fold.lean:20`, `:459`).
Write the checker once as `checkEff : … → Except TypeRefusal EffTy`, define
`effTy := (checkEff …).toOption` and `explain := (checkEff …).toError`; `explain_none_iff` becomes
one lemma about `Except`.
*Deletes:* **~520 lines net**, estimated, keeping `TypeReason`, `TypeRefusal` and the reason choice
per rule. *Proof consequence:* DI-86's law stops being a theorem about two definitions and becomes a
definitional identity; `Api.check`'s totality follows the same way.
*Risk:* medium — `effTy` is consumed by `decide +kernel` typing certificates and is in the LCNF
import closure, so `cases-policy.json` rows will move.
*Gate:* `make check` (certificates, `Test/Program/BlameContract.lean`), `check-cases`, `check-ocaml`.
*Under a day:* no, two.

**P8 — nested children in the Fold generator; `Representation` and `Shape` into the fold group.**
*Drift: one generated fold instead of three hand-written ones, plus the monadic half for free* (§6.5).
Teach `readBlock` (`tools/Effect4Gen/Fold.lean:43-73`) a child-position language
(`direct | list | option | listOf ⟨record with a ρ field⟩`) and give `recComb`/`foldMapOf` the
matching combinators.
*Deletes:* `Schema/Representation.lean:1255-2111` (857 lines), most of
`Test/Schema/RepresentationFoldContract.lean` (334), and lets `Store/Shape.lean`'s six mutual blocks
(242 lines) become six algebra instances (~90 lines). **~1100 net, inferred.**
*Adds:* ~150 generator lines. *Risk:* medium-high — the nested-inductive hazard named at
`src/Effect4/Program/Eff.lean:30-33` is why these families were kept out; the fold needs no
`DecidableEq`, but I have not checked that Lean's structural-recursion checker accepts the emitted
shape. **The one proposal I would probe before committing to.**
*Gate:* `make check`, `check-gen-full`, `check-schema-codec`. *Under a day:* no.

### Needs the owner's ruling

**P9 — generate the `Ty` arms.** *Drift: turns §2.3's 27 hand arms and about 20 of the 39 silent
absorbers into algebra fields the compiler demands.* `cata_ty` and `TyAlgebra` exist and are
generated; the twelve single-argument folds listed in §2.3 become `TyAlgebra` instances; `Ty.sub` and
`Val.hasTy` stay hand-written. *Deletes:* 120–180 lines, estimated.
*Risk:* medium — `normalize`'s termination and `Normal.fixed`'s proof are delicate.
*Ruling needed:* whether to pay this **before** P10, which it makes much cheaper. My recommendation:
yes, immediately before. *Gate:* `make check`, `check-cases`. *Under a day:* no, two.

**P10 — `Ty.data (name : String)`, the nominal tree type.** *Drift: closes the gap between the
store's generated `Shape` estate and the program type language, which today meet in one direction and
disagree in five places (§2.2a).* **Compiled** (§2.4). One constructor — the missing `.reference` arm
of `Ty.ofSchema` — a wire tag, `sub` at equality to start, a `ShapeDoc` carried by the `Signature`,
`Val.hasTy`'s arm as `acceptsIn`, introduction from `caseAt`'s field shapes, and one nominal
eliminator that subsumes `Decision.option` and `Decision.tag`.
*Makes typed:* scout A's reader layer, folds over trees, and any user Lean inductive.
*Cost:* the §2.3 cascade, expensive **because** those arms are hand-written; only P9 reduces it.
*Rider, and worth ruling on its own:* **no new `Decision` constructor until this is settled** — a
fourth one spends in a currency about to be retired (§5, §2.4).
*Ruling needed:* (a) does a `data` type participate in subtyping or is it invariant by name?
(b) does the `ShapeDoc` live on the `Signature` or on the module? (c) before or after R4–R6?
My recommendation: yes to the constructor; invariant by name at first; on the `Signature`; **after**
the reader line, because the printer's discriminated-union emission wants R2's positioned render.
*Gate:* `make check`, `check-cases`, `check-compat`, `check-ocaml`, `check-schema-codec`.
*Under a day:* no — a slice of its own, three or four days.

**P11 — the schema surface audit.** *Drift: 9174 lines, 108 code declarations and 173 theorems with
no consumer anywhere (§6.4), are 9174 lines that every future alphabet change must be checked
against — plus the five dialect disagreements of §2.2a, which P3 pins but does not repair.* This is
the owner's "the Effect Schema work ran ahead", quantified. The ask is not a deletion list from me —
I did not read `Annotations.lean`, `Check.lean` or `EffectfulField.lean` past their headers (§9) — it
is a **ruling on the standard**: does a declaration in `src/Effect4/Schema/**` need a production
consumer, a test, or neither? Once answered, §6.4 is the worklist; the top three by unreferenced code
declarations are `EffectfulField.lean` (30), `Annotations.lean` (15), `Check.lean` (14). **Step 0 is
free and needs no ruling:** `Schema/Dimension.lean` (102 lines) has exactly one reference outside
itself, the import at `src/Effect4.lean:56`, and its header's claim to be "read by the emitters" is
already false — either give it its consumer (`tools/Tools/TsGen.lean`'s type names and brands) or
delete it with the import.
*Ruling needed:* the standard; whether the five dialect disagreements are repaired or blessed; and
whether this runs beside M2's schema half (R7/R8) or after it.
My recommendation: **beside**, because R8 is about to ingest the whole rc.112 surface as generated
entries and should not be generated on top of an unaudited hand-written mirror.
*Gate:* `make check`, `check-schema-codec`, `check-schema-ts`. *Under a day:* step 0 yes, the rest no.

**P12 — the list and option kit** (`2026-09-17-loop-sugar-and-list-elimination.md` §3). I checked the
note's evaluation against the tree (§5) and it **holds**; my three corrections are:
(a) all five stay **atoms**, not literals — `Term.app` carries the atom by name so an atom moves no
byte and cannot fire `check-compat`, while `Lit` is a listed wire-tag family, and `cons`/`some` could
not be literals anyway since `Lit` is nullary; (b) nullary atoms are already reachable, so the note's
open question is answered — `strings` is variadic and builds the empty list today; (c) the price adds
`ocaml/engine/e4_program.ml`'s translation arm and `harness/truth/prelude.ts`'s export plus
self-test row per atom, about 5 × 75 lines.
*Gives:* `reduce` as the catamorphism recovered as a theorem at budget `length + 1` through
`iter_uniform`, fold fusion as its instance, and `forEach` answering in order.
*Ruling needed:* whether it lands before R4–R6 (the note says after; I agree), and whether `uncons`
alone is enough for a first cut (it is, for folds over lists a row returns; it leaves lists and
options unbuildable, so `forEach` cannot collect).
*Gate:* `make check`, `check-truth`, `check-ocaml`.
*Under a day:* the `uncons` atom alone, yes; the whole kit, no.


## 9. What I did not check

- **The three biggest schema modules past their headers**: `Schema/Annotations.lean` (2304 lines),
  `Schema/Check.lean` (1827) and `Schema/EffectfulField.lean` (982). §6.4's numbers for them are a
  reference count, not a reading. This is the largest hole in the note, and it is why P11 is a ruling
  request rather than a deletion list.
- I did not open `vendor/effect-4.0.0-rc.112/src` at all, so every rc.112 citation here is repeated
  from the tree, not confirmed. (That is itself evidence for P2.)
- I did not check whether the five dialect disagreements of §2.2a are *intended*. `Effect4.Store.render`
  renders for the store's spec document and `Ty.schema` for the host boundary, so some of them may be
  deliberate. What I can say is that no theorem, guard or gate records the decision either way.
- I ran no gate: no `make check`, `check-cases`, `check-ocaml`, `check-compat`, `check-truth`,
  `check-ts-reader`, `check-citations`. Every "the gate catches this" claim in §7 is read off the
  Makefile and the checker's source, not observed failing.
- P7's load-bearing step — that `Except.toOption` preserves `pure` and `bind`, so it is a
  `MonadMorphism` — is checked on paper, not compiled. It is two case splits and I expect it to go
  through, but it should be compiled before that slice starts.
- I did not check whether `foldM_eff`'s termination survives an environment-indexed carrier, which
  both P7 and "`effTy` as a fold" need.
- P8's risk is unprobed: I did not try emitting a fold for a nested family, so "~150 generator lines"
  is an estimate and the structural-recursion checker may refuse the shape.
- I did not read `tools/Conform/Effect4/specs.json`, `mirrors.json` or `rules.json`, so the LCNF
  conformance subjects are outside this note.
- I did not measure the OCaml CAS tree (`ocaml/engine/cas/**`, ~9000 hand-written lines); it is
  outside the LCNF import closure and belongs to a different question.
