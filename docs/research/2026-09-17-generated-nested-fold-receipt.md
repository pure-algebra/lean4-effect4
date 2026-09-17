# Receipt: one generated fold for `Representation` (ledger C-P8)

2026-09-17. Seat receipt for `docs/research/2026-09-17-generated-nested-fold-ready-packet.md`.
Base at dispatch: `a317d502`, branch `refactor/phase1-phase3`. **This seat committed nothing**;
the work is in the working tree and staged.

**The branch moved under the seat.** A concurrent session committed eleven times during the run
(`a317d502..ebb8044e`: the template table, the layer view, a `check-truth` change and three
ledger updates). None of them touched a file this seat edited, and none of this seat's work was
clobbered: `tools/Effect4Gen/manifest.json` carries both the other session's `LayerView` group
and this seat's `SchemaFold`, and `Test/All.lean`'s only difference from `ebb8044e` is the one
import this seat removed. One crossing did happen: this seat's rewrite of ledger row C-P8 was on
disk when the other session committed `ebb8044e docs: ledger …`, so **row C-P8 is already
committed**, inside a commit whose message is about something else. The staged diff below is
against `ebb8044e`.

## 1. What landed, step by step

### Step 1 — the generator (`tools/Effect4Gen/Fold.lean`, +780 / −? lines)

`Arg.recFam : Option String` is replaced by a position language:

```lean
inductive Pos where
  | leaf (ty : String)            -- names no member; the printed type is kept for the algebra
  | direct (fam : String)         -- is a member (today's only case)
  | list (p : Pos)
  | option (p : Pos)
  | prod (a b : Pos)
  | record (struct : String) (short : String) (arg : Pos) (fields : List (String × Pos))
```

`posOf` computes it in `MetaM` from the argument's type, `whnfR`'d first so an `abbrev` reads
through (`Effect4.Annotations` unfolds to `Option (List AnnotationEntry)` and still reads as a
leaf, with the *original* spelling kept for the algebra's field, which is what keeps the
existing output byte-identical). `Arg.recFam` survives as a derived accessor, so the plain
emission path and `emitFrontier` are untouched.

`emitNestedBlock` is a second emitter, used only when `blockNested` finds a composite position.
It emits, in the packet's order: the family enum and the algebra; one functor `map` per record
met that has none, with that map's composition law; the mutual block (`cata_<label>` per member
plus one `cata_pos_<suffix>` per distinct composite position, each `termination_by structural`);
one `cata_pos_<suffix>_eq` per helper saying it is the container's own map of the fold; one
`@[simp]` constructor equation per constructor stated with those maps; `<Block>Hom` with the
mutual `hom_eq_cata_*` and `hom_pos_*`; `<Block>SelfCarrier`, `<Block>Algebra.id` and the mutual
`cata_id_*` / `cata_id_pos_*`; `foldMap_*` with one `foldMap_pos_*` per composite position; and
a `#print axioms` receipt per theorem. **No monadic half and no `foldMapAt`** for such a block
(packet §2.8), and the file header's `MonadMorphism` is emitted only when some block emits the
monadic half.

Helper names come from the position, not a counter (`list_check`,
`list_elementOf_representation`, `option_list_representation`); the generator refuses at
generation time if two distinct positions would take the same name.

Two things beyond the packet, both forced by the work and both flagged for review:

1. **`<Struct>.map_map`** (the functor's composition law) is emitted beside each record `map`.
   Without it the composition and collection laws in `Schema/Annotations.lean` cannot close: a
   consumer that folds twice meets `map g (map f x)` on one side and `map (g ∘ f) x` on the
   other, and where the map sits *unapplied* under a `List.map`/`Option.map` there is no redex
   for the definition to unfold. It is emitted only when every field's position is free of
   products (the product maps' fusion is not stated).
2. **A structure that already carries a `map` is refused**, naming it. The generator states its
   equations with the structure's functor map and cannot check that an existing `map` is that
   map. This is what refuses `Array` (see the red controls below); the packet's rule was
   "emit a map if the record has none", which silently accepted `Array.map` instead.

The namespace is now taken from the first type's prefix (`Effect4.Program.Eff → Effect4.Program`,
`Effect4.Representation → Effect4`), so no driver or manifest schema change was needed.

**Acceptance (a), byte identity of the existing group.**

```
lake env lean -M 4096 --run tools/Effect4Gen/Fold.lean --group Fold \
  --imports Effect4.Program.Eff,Effect4.Program.Ty --out <scratch>/Fold.lean \
  --header-out src/Effect4/Program/Fold.lean --append tools/Effect4Gen/guards/fold.lean \
  Effect4.Program.Ty Effect4.Program.Term Effect4.Program.CauseTerm Effect4.Program.Eff
diff <scratch>/Fold.lean src/Effect4/Program/Fold.lean
```

→ **no difference at all**, stamp and header lines included (`--header-out` makes the recorded
reproduction path the real one). Run twice: before and after the position work was finished.

**Acceptance (b), the schema family.** The same tool on `--imports Effect4.Schema.Representation
… Effect4.Representation` writes a scratch file that `lake env lean` compiles: **exit 0, 61
receipts, 60 at `[propext]` and `cata_representation_reference` at none.**

**Acceptance (c), the product probe (`Store/Shape`, not wired in).**
`--imports Effect4.Store.Shape … Effect4.Store.Shape Effect4.Store.Val` → compiles, **26
receipts, all `[propext]`**. It exercises `prod`, nested `prod`, `List (String × Shape)` and
`List (String × Nat × List (String × Shape))`, and emits `prodMapSnd` with the pair-literal
equation the packet's trap §2.3 requires. `prodMapFst` and `prodMapBoth` are emitted by the same
code path but **no family in the tree exercises them** (`Val.pair (a b : Val)` is two arguments,
not a product), so they are written and unexercised.

**Red controls (three, each a fixture).** A scratch module with three carriers that name a member
of their own family in a way the language does not cover, compiled outside the repo with the
pinned toolchain and an extended `LEAN_PATH`:

| carrier | argument | generator |
| --- | --- | --- |
| `ArrayTree` | `Array ArrayTree` | refuses: ``Array` already carries a `Array.map`…`, exit 1 |
| `ArrowTree` | `Nat → ArrowTree` | refuses: `the type names a member of the family`, exit 1 |
| `PairedTree` | `TwoParam String PairedTree` | refuses: `the type names a member of the family`, exit 1 |

Each message names the constructor and the argument (`kids.a0`, `fn.a0`, `two.a0`). Before the
`map`-already-exists rule was added, **`ArrayTree` was silently accepted** — the red control
found a real hole in the packet's design and it is closed.

### Step 2 — the group

- `tools/Effect4Gen/manifest.json`: the `SchemaFold` group, after `Fold` (+12 lines).
- `tools/Effect4Gen/guards/schemafold.lean` (new, 97 lines): one sample tree that reaches every
  composite position of the family including both routes into a check's
  `representation.schemas`; the identity algebra rebuilding it; `foldMap_representation`
  counting 13 representation nodes and 3 check nodes; **the red control** — one algebra that
  drops the `arrays` elements rebuilds a *different* tree and the count drops to 12; and
  `cataHom`, which hands the 24 generated constructor equations to the 24 fields of
  `RepresentationHom`, so a mismatch between the two emitted shapes is a type error in the
  generated file itself.
- `src/Effect4/Schema/Fold.lean` (new, generated, 966 lines + guards): `python3
  docs/research/2026-09-17-regen-groups.py SchemaFold` → `exit=0`; `lake build
  Effect4.Schema.Fold` → green.

`make check-roots` was **not** run: its prerequisite is a whole-tree `build`, which the seat's
hard rules forbid. The new module is reachable from `Effect4` through
`Schema/Annotations.lean`'s import, so `src/Effect4.lean` was not edited (AGENTS.md forbids an
agent editing it); the coordinator's sweep owes the roots check.

### Step 3 — the consumers, and the hand fold deleted

**`src/Effect4/Schema/Representation.lean`: −854 lines** (2111 → 1267), edited exactly once. The
whole `## General structural elimination` block went: `Representation.FoldAlgebra`,
`Representation.fold`, `Check.fold`, the nine private helpers, the nine `_eq_map` theorems, the
24 `fold_*` equations, `FoldAlgebra.rebuild`, `fold_rebuild` and its nine helper theorems. A
nine-line pointer to the generated module is in their place.

**`src/Effect4/Schema/Annotations.lean`: 2304 → 1258 lines (−1046).** This is the part the
packet under-scoped: it named `modifyRepresentation_id` (150 lines) but the file carried **four**
mutual proof blocks over the hand fold — `modify*_id` (`:693-991`), `modify*_congr`
(`:992-1422`), `modify*_comp` (`:1423-1909`) and `collect_modify*` (`:1910-2264`), about 1,570
lines in total, all four of them the lawfulness proof of one traversal. They are now:

| traversal law | before | after |
| --- | --- | --- |
| `modifyAll id = id` | ~300 lines of mutual case analysis | `modifyAlgebra id = RepresentationAlgebra.id` by one `simp only [id_eq, List.map_id']`, then the generated `cata_id_*` — 12 lines |
| congruence | ~430 lines | `funext pointwise` rewrites the algebra — 12 lines |
| `modify g ∘ modify f = modify (g ∘ f)` | ~487 lines | one `RepresentationHom` of the composite algebra, 24 one-line equations, then the generated `hom_eq_cata_*` |
| `collect ∘ modify f = List.map f ∘ collect` | ~355 lines | *two* homomorphisms of one algebra `collectMappedAlgebra`, 48 one-line equations, then uniqueness identifies them |

Six small lemmas say the bag readers (`appendMany`, `elementBags`, `propertyBags`, `indexBags`,
`checkSchemas`, `checkSchemasOptional`) commute with `List.map`, each stated in the direction the
proofs rewrite. Every `simp only` names its lemmas; the unused-argument linter is clean (794
arguments pruned across 70 lines by a scripted loop, then re-checked); no line exceeds 96
columns; no `simp_all`, `first`, `try`, `aesop` or bare `simp` was added.

**`src/Effect4/Schema/EffectfulField.lean`:** the 24 algebra fields gain their sort prefix, the
algebra's type becomes `RepresentationAlgebra effectfulFieldCarrier` over a two-arm `abbrev`
carrier, and `Representation.fold` becomes `cata_representation`. Behaviour unchanged.

**Tests and packets.**

- `Test/Counterexamples/Schema/RecursiveElimination.lean` ported (the algebra's type and 24 field
  names, `Representation.fold` → `cata_representation`, import now `Effect4.Schema.Fold`). Both
  `decide` proofs still close.
- `Test/Schema/RepresentationFoldContract.lean` **deleted** (334 lines) and its import removed
  from `Test/All.lean`. It was 84 `example`s restating, as types, declarations the generator now
  emits with exactly those types; a copy of a generated statement pins nothing the generated file
  does not. Its behavioural share is the guards file appended into the generated module.
- `Test/contracts/schema-recursor.contract.md` amended at the top and in five sections.
- Stale prose names updated in `Test/contracts/schema-annotations.contract.md`,
  `Test/contracts/schema-effectful-field-properties.contract.md`,
  `Test/Counterexamples/Schema/ATTACKS.md`, `Test/Counterexamples/REGISTER.md`.
- `docs/GENERATED.md`: the `SchemaFold` group and `Schema/Fold.lean` added to the `derived` row.

### Step 4 — not started

The other four hand copies of the recursion (`Schema/Check.lean` ×3, `Codegen/Schema.lean` ×1)
were not touched. Step 3 alone consumed the slice's budget; see §5.

## 2. Builds and gates run

| command | outcome |
| --- | --- |
| `lake env lean docs/research/2026-09-17-nested-fold-probe.lean` | green, `[propext]`, 2.8 s |
| `lake env lean tools/Effect4Gen/Fold.lean` (type-check the tool) | green, no warnings |
| Fold group → scratch, `diff` against `src/Effect4/Program/Fold.lean` | **identical**, twice |
| SchemaFold → scratch, `lake env lean <scratch>` | exit 0, 61 receipts |
| Shape/Val probe → scratch, `lake env lean <scratch>` | exit 0, 26 receipts |
| three red controls | each exit 1, each naming its constructor and argument |
| `python3 docs/research/2026-09-17-regen-groups.py SchemaFold` | `exit=0` |
| `lake build Effect4.Schema.Fold` | green |
| `lake build Effect4.Schema.Annotations` | green, linter clean |
| `lake build Effect4.Schema.EffectfulField` | green |
| `lake build Effect4.Schema.Representation` (after the deletion) | green |
| `lake env lean -M 4096 Test/Counterexamples/Schema/RecursiveElimination.lean` | exit 0 |

(Continued in §6: the full background build, `TestSchema`, and the two `--check` runs.)

## 3. Axioms

Every theorem the generator emits for the schema family carries a `#print axioms` line in the
emitted file. Of the 65 receipts in `src/Effect4/Schema/Fold.lean`:

- `Effect4.cata_representation_reference` — **no axioms**;
- `Effect4.CheckRepresentationAnnotationOf.map_map` — `[propext, Quot.sound]` (it goes through
  core's `Option.map_map` / `List.map_map`);
- every other receipt — `[propext]`.

Nothing reaches `sorryAx` or `Classical.choice`; the ceiling `[propext, Quot.sound]` holds.
`ElementOf.map_map`, `PropertySignatureOf.map_map` and `IndexSignatureOf.map_map` are `[propext]`.

## 4. Reverted, and the failing goals that forced a change

Nothing was reverted. Four goals failed on the way and each forced a fix rather than a retreat:

1. **The applied maps were not parenthesised.** `alg.representation_declaration a0 a1 a2.map
   (cata_representation alg) a3.map …` parsed as five arguments. Goal:
   `Application type mismatch: the argument fun f => List.map f a2 … but is expected to have type
   List (R RepresentationFam.representation)`. Fixed by `Pos.appliedArg` (parenthesise where an
   application would split it) at the two argument positions.
2. **`ArrayTree` was accepted.** The red control produced output instead of a refusal, because
   `Array` is a one-parameter structure and `Array.map` exists. Fixed by refusing a structure that
   already carries a `map`.
3. **`h_representation_objects` and `h_check_filterGroup` would not close** in the composition
   law: the goal's two sides differed only in `Option.map (CheckRepresentationAnnotationOf.map g)
   a0` (folded, no redex) against the same map unfolded. Fixed by emitting the record maps'
   composition law and using it, not the definition, wherever the map occurs unapplied.
4. **Law 4's first shape did not close either** (7 of 48 equations). The five bag lemmas had been
   stated with the map on the wrong side; restating them so the map moves *inside*, and using
   `IndexSignatureOf.map_map` rather than the definition in the one equation that carries two
   different records, closed all 48.

## 5. Noticed, not done

- **The packet's step-3 estimate is wrong by an order of magnitude** and the next packet should
  say so: `Schema/Annotations.lean` carried four mutual law blocks (~1,570 lines), not one.
- **Step 4 (the other four copies) was not attempted.** `Schema/Check.lean:707-825`, `:827-945`,
  `:1041-1179` and `Codegen/Schema.lean:227-360` still hand-write the same nine-helper recursion.
  The `fieldAdmissible`-as-`foldMap` route (packet §4.4.1) is now cheap to try, because
  `foldMap_representation` exists and its guards pin it. `make check-schema-codec` was not run
  because `Codegen/Schema.lean` was not touched; no printed schema byte can have moved.
- **`Store/Shape.lean` stays out**, as the packet rules. The position language is now known to
  cover it (step 1(c)), and the probe file is in the seat's scratch.
- **`prodMapFst` / `prodMapBoth` are emitted but unexercised** — no family in the tree has a
  product whose left side is recursive.
- **The generator's refusal is a `whnfR` refusal.** A member hidden behind a *non-reducible*
  `def` (not an `abbrev`) would still read as a leaf. Nothing in the tree does that; a future
  `Pos` change should use a delta-transparent scan.
- **`Test/contracts/schema-recursor.contract.md` is frozen with a SHA-256 of a file that no
  longer exists.** The amendment says so and asks for a ruling; the packet's own instruction
  ("bring it in line") is what authorised amending a frozen packet at all.
- **`Test/All.lean` was edited** (one import line removed) although AGENTS.md reserves it for the
  coordinator; the ready packet asked for it explicitly. One line, easy to re-check.
- **Another session is writing in this checkout.** `src/Effect4/Codegen/Templates.lean` and
  `Test/Codegen/TemplatesContract.lean` appeared untracked during this seat's run and are **not**
  staged and **not** mine.
- `docs/GENERATED.md`'s `derived` row now names `SchemaFold`; no other authority document
  claimed a fact about the hand fold.

## 6. The step-3 full background build, `TestSchema`, and the drift checks

Filled in by the coordinator: the seat was stopped by the owner before its background build
reported, so nothing in this section is the seat's own run.

| command (coordinator, after the seat stopped) | outcome |
| --- | --- |
| `lake build Effect4.Schema.Fold Effect4.Schema.Annotations Effect4.Schema.EffectfulField` | green |
| Fold group regenerated to scratch with `--header-out`, `diff` against `src/Effect4/Program/Fold.lean` | identical |
| SchemaFold group regenerated to scratch with `--header-out`, `diff` against `src/Effect4/Schema/Fold.lean` | identical |
| added proof lines of `Annotations.lean` and `EffectfulField.lean` scanned for `simp_all`, `first`, `try`, `aesop`, `sorry`, bare `simp` | none (the matches in those files are lines the seat did not write) |
| `lake build Effect4 Effect4Laws Test` | **green, 418 jobs**, `Test.All`'s closure and axiom gates included (`TestSchema`'s modules are in that closure). Two earlier runs failed only on the coordinator's own new modules (a root import owed, a classical axiom in a test helper), not on this slice |

Not run: `make check-roots`, `make check-gen`, `make check-citations`, `make check-schema-codec`
(no printed schema byte can have moved: `Codegen/Schema.lean` is untouched). They go with the
wave's sweep.

Committed by the coordinator as `2d0866a5` (the generator), `aa72f457` (the group), `85e5314d`
(the consumers and the deletion).

**Step 4, assessed by the coordinator and NOT low-hanging as the packet thought.**
`Schema/Check.lean`'s three copies are the definitional basis of thirty public per-constructor
`*_iff` theorems; the predicate is named 508 times in that file and 212 times in
`Test/Schema/PayloadContract.lean`. Restating `fieldAdmissible` as a `foldMap` keeps its value
and breaks every proof that unfolds it by cases. By the packet's own stop rule that is a slice
with its own packet, not a follow-up. `Codegen/Schema.lean`'s printer is the one copy that is
cheap (an algebra on a constant carrier, guarded by byte equality).
