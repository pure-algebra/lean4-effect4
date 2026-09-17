# Ready packet: one generated fold for `Representation` (ledger item C-P8)

2026-09-17. Coordinator's packet for one Opus seat. Tracker:
`docs/research/2026-09-17-scout-findings-ledger.md`, row C-P8. Compiled probe:
`docs/research/2026-09-17-nested-fold-probe.lean` (green, `[propext]` only, 3 seconds, no project
imports: `lake env lean docs/research/2026-09-17-nested-fold-probe.lean`).

## 1. What and why

The owner's priority is duplicated representations and drift. The schema carrier's fold is written
by hand where the tree already has a generator that emits exactly that construction for the `Eff`
family:

| hand-written today | lines | what `tools/Effect4Gen/Fold.lean` emits for it |
| --- | --- | --- |
| `Representation.FoldAlgebra`, `Representation.fold`, `Check.fold`, nine private helpers (`src/Effect4/Schema/Representation.lean:1270-1440`) | 171 | `RepresentationAlgebra`, `cata_representation`, `cata_check` and the position helpers |
| 24 constructor equations `Representation.fold_*`, `Check.fold_*` (`:1569-1810`) | 242 | one constructor equation per constructor |
| `FoldAlgebra.rebuild`, `fold_rebuild` and its nine helper theorems (`:1815-2108`) | 294 | `RepresentationAlgebra.id`, `cata_id_*` |
| nothing | 0 | `RepresentationHom` and `hom_eq_cata_*` (uniqueness), `foldMap_*` (the monoid fold) |

The same nine-helper recursion is then written by hand **four more times** over the same family
(measured today, the scout counted only the first):

| where | what it is |
| --- | --- |
| `src/Effect4/Schema/Check.lean:707-825` | `FieldAdmissible : … → Prop`, nine helpers |
| `src/Effect4/Schema/Check.lean:827-945` | `fieldAdmissible : … → Bool`, the same nine helpers |
| `src/Effect4/Schema/Check.lean:1041-1179` | the theorem that the two agree, the same nine helpers |
| `src/Effect4/Codegen/Schema.lean:227-360` | the printer `representation : Representation → Expr`, the same helpers |

The blocker was one line: `readBlock` (`tools/Effect4Gen/Fold.lean:65-67`) decides a constructor
argument is recursive by the head constant of its type, so `List Representation` reads as a leaf.

## 2. What is already known (so the seat does not spend time on it)

1. **Lean accepts the emitted shape.** The probe is a miniature family with every position kind the
   two real families have (`List Rep`, `List Chk`, `List (ElemOf Rep)`, a record holding
   `Option (List Rep)`, `Option` of that record, `List (String × Rep)`,
   `List (String × Nat × List (String × Rep))`), written in the exact text the generator should emit.
   All of it compiles with `termination_by structural`: the fold, the helper-is-a-map lemmas, a
   public constructor equation, `Hom` + `hom_eq_cata`, `Algebra.id` + `cata_id`, `foldMap`.
   Axioms: `[propext]`.
2. **The emission rule, from the probe.** One helper per DISTINCT composite position type, all in
   the family's one mutual block, each `termination_by structural` on its own argument:
   - `List p`: `| [] => [] | x :: rest => <p> x :: <self> rest`
   - `Option p`: `| none => none | some y => some (<p> y)`
   - a one-parameter structure applied to a family member: match on the anonymous constructor
     `⟨f1, f2, …⟩`, rebuild with `⟨f1, <p> f2, …⟩`, each field by its own position
   - `a × p`: `| (a, b) => (a, <p> b)`
   Records may get their own helper (as `cata_pos_elem`) rather than being inlined in the list
   helper; both forms are accepted, the separate helper keeps the rule uniform.
3. **One proof trap, already hit and fixed in the probe.** For products, never put the product
   map's definition in a `simp only` set: unfolding it also opens an inner application on a
   variable before the induction hypothesis can rewrite it (the goal becomes
   `(a, b.fst, List.map … b.snd) = (a, helper b)` and sticks). State one equation on the pair
   literal (`prodMapSnd_mk : prodMapSnd f (a, b) = (a, f b) := rfl`) and rewrite with that.
4. **The proofs are one `simp only` per case**, of the form
   `simp only [<the def being unfolded>, <the Hom equation or nothing>, <one IH per child>]`,
   plus `rfl` after it in the `cata_id` constructor cases (as the generator already emits).
   No `first`, no `try`, no `simp_all`, no bare `simp` (AGENTS.md, the explicit-tactic rule).
5. **Consumers of the hand fold** (everything else in the tree is untouched by the rename):
   `src/Effect4/Schema/Annotations.lean` (411 mentions: two algebras `collectAlgebra` and
   `modifyAlgebra` at `:606-678`, and their laws), `src/Effect4/Schema/EffectfulField.lean:774,844`
   (one algebra), `Test/Schema/RepresentationFoldContract.lean` (334 lines, 117 mentions),
   `Test/Counterexamples/Schema/RecursiveElimination.lean` (3 mentions),
   `Test/contracts/schema-recursor.contract.md` (names both test files).
   Nothing under `tools/`, `scripts/`, `harness/`, `ocaml/`, `ts/` or the conformance policies names
   the hand fold (searched).
6. **Layering.** `Store/Shape.lean` imports `Schema/Authoring.lean`, and `Program/*` imports the
   store, so the schema tree is BELOW `Effect4.Program`. The generated schema fold cannot import
   `Effect4.Program.Fold`. That matters for `MonadMorphism` (item 8).
7. **Blast radius.** `Schema/Representation.lean` is under almost everything
   (`Annotations → Document → Check → Authoring → Store/Shape → Program`). An edit to it rebuilds
   the world. Order the work so it is edited ONCE (step 3), and do the generator work (steps 1-2)
   against scratch output first.
8. **The monadic half has no consumer on this family** (searched: no `Except`- or `Option`-valued
   structural traversal of `Representation` exists; `Ty.ofSchema` is a deep pattern match, not a
   fold). For a nested position it would need a `sequence` per position type and a new proof of
   `foldM_id` (the present one is `rfl` after one rewrite, which no longer holds under `List`).
   Not probed. Ruling for this slice: **a block with nested positions emits no monadic half and no
   `foldMapAt`**; the file header's `MonadMorphism` is emitted only when some block emits the
   monadic half. That also avoids a second `MonadMorphism` declaration.

## 3. The design

### 3.1 Positions

Replace `Arg.recFam : Option String` with a position:

```lean
inductive Pos where
  | leaf                                   -- the type names no member of the family
  | direct (fam : String)                  -- head constant is a member (today's only case)
  | list (p : Pos)
  | option (p : Pos)
  | prod (a b : Pos)                       -- at least one side is not `leaf`
  | record (struct : Name) (fields : List (String × Pos))  -- a structure with ONE type parameter,
                                           -- applied to a type that names a member
```

Computed in `MetaM` from the argument's type expression (`whnfR` it first so an `abbrev` such as
`Element := ElementOf Representation` reads through). For `record`, open the structure's
constructor telescope with the parameter instantiated to the actual argument and compute each
field's position the same way. Anything else that mentions a member (an arrow, a two-parameter
structure, `Array`) is an error naming the constructor and the argument: refuse loudly, do not read
it as a leaf. That refusal is itself the drift guard for the next constructor someone adds.

Each `Arg` also carries: `tyText` (as today), `carrierText` (the same type with every member `X`
replaced by `R .x`, for the algebra's field), and for a composite position a stable helper suffix
derived from the position, not from a counter (`list_check`, `list_elementOf_representation`,
`option_list_representation`, …), so a reordering of constructors does not rename helpers.

### 3.2 What a block with nested positions emits

In this order (the probe has each, in this order, for the miniature):

1. `<Block>Fam`, `<Block>Algebra` (fields typed by `carrierText`).
2. One `map` per record functor met, if the record has none: `ElementOf.map`,
   `PropertySignatureOf.map`, `IndexSignatureOf.map`, `CheckRepresentationAnnotationOf.map`
   (`src/Effect4/Schema/Payload.lean:75-101` defines the four records; none has a `map` today).
   The product map and its pair-literal equation, once per file, if a `prod` position occurs.
3. The mutual block: `cata_<label>` per member, `cata_pos_<suffix>` per distinct composite position.
4. `cata_pos_<suffix>_eq`: each helper equals the container's own map of the fold
   (`xs.map (cata_x alg)`, `x.map (ElementOf.map (cata_x alg))`, …). Plain `induction`/`cases`,
   outside the mutual block.
5. One `@[simp]` constructor equation per constructor, stated with the containers' maps (what the
   hand file's `fold_*` equations are, and what `Annotations.lean`'s proofs rewrite with).
6. `<Block>Hom` (equations stated with the maps) and the mutual `hom_eq_cata_*` with one
   `hom_pos_<suffix>` per composite position.
7. `<Block>SelfCarrier`, `<Block>Algebra.id`, the mutual `cata_id_*` with one
   `cata_id_pos_<suffix>` per composite position.
8. `foldMap_*` with one `foldMap_pos_<suffix>` per composite position (children left to right,
   `unit` for an empty list or `none`).
9. Receipts (`#print axioms`) for every theorem, as today.

A block with NO composite position must emit **byte for byte what it emits today**. The acceptance
test for the generator change is: regenerate the `Fold` group and `git diff --stat
src/Effect4/Program/Fold.lean` is empty.

### 3.3 Namespace and naming

The generator hard-codes `namespace Effect4.Program` (`Fold.lean:562`). Take the namespace from the
first type's prefix instead (`Effect4.Program.Eff → Effect4.Program`, `Effect4.Representation →
Effect4`); no driver or manifest schema change is needed, and the existing output is unchanged.
Labels come from `famLabel`'s default (`representation`, `check`); the block name from
`shortName` (`Representation`). So the generated names are `RepresentationFam`,
`RepresentationAlgebra` with fields `representation_declaration … check_filterGroup`,
`cata_representation`, `cata_check`, `hom_eq_cata_representation`, `cata_id_representation`,
`foldMap_representation`.

### 3.4 The new group

`tools/Effect4Gen/manifest.json`, after the `Fold` group:

```json
{ "Name": "SchemaFold", "Tool": "tools/Effect4Gen/Fold.lean",
  "Note": "The fold of the persisted schema carrier: Representation and Check, nested children included.",
  "Imports": "Effect4.Schema.Representation",
  "Out": "src\\Effect4\\Schema\\Fold.lean",
  "Guards": "tools\\Effect4Gen\\guards\\schemafold.lean", "Kinds": [],
  "Types": ["Effect4.Representation"] }
```

No Makefile change: every manifest row runs under `scripts/generate.py`'s `derived` family
(`scripts/generate.py:54-73`: for each row of `Driver.lean --commands`, build the row's imports,
run the tool, install, build the output module), in manifest order. The guards file is small:
a leaf-count algebra, `cata_id` on one concrete tree by `decide`/`#guard`, one `foldMap` count,
and one red control (a `Hom` whose equation is wrong does not type-check, or an algebra that
drops a child gives a different count). Most of `Test/Schema/RepresentationFoldContract.lean`
pins the hand equations one by one and is superseded by the generated theorems.

## 4. Steps, each with its narrow build and its acceptance

Cadence (AGENTS.md): narrow builds per step, no `make check`, no full `lake build`. One compiler at
a time: never start a build while another is running. Long builds in the background.

**Step 1 — the generator, against scratch output.**
Edit `tools/Effect4Gen/Fold.lean` only. Acceptance:
(a) `lake env lean -M 4096 --run tools/Effect4Gen/Fold.lean --group Fold --imports
Effect4.Program.Eff,Effect4.Program.Ty --out <scratch>/Fold.lean --append
tools/Effect4Gen/guards/fold.lean Effect4.Program.Ty Effect4.Program.Term
Effect4.Program.CauseTerm Effect4.Program.Eff` and `diff <scratch>/Fold.lean
src/Effect4/Program/Fold.lean` differs only in the stamp/command header lines, if at all;
(b) the same tool on `--imports Effect4.Schema.Representation … Effect4.Representation` writes a
scratch file that `lake env lean <scratch file>` compiles. Both need only modules that are already
built; nothing under `src/` has changed yet, so no rebuild is triggered.
(c) Optional but cheap, and it proves the position language on products: run it on
`Effect4.Store.Shape` to scratch and compile. Do NOT wire Shape in (§6).

**Step 2 — the group.** Add the manifest entry and the guards file; generate
`src/Effect4/Schema/Fold.lean`; `lake build Effect4.Schema.Fold`. Add the module to
`src/Effect4.lean`'s imports (`make check-roots` reads the roots; run just that target).

**Step 3 — move the consumers, delete the hand fold.** One edit to `Representation.lean`: delete
`:1255-2108` (keep the closing `end Effect4`). Then, importing `Effect4.Schema.Fold`:
- `Annotations.lean`: `Representation.FoldAlgebra ρ κ` becomes `RepresentationAlgebra R` with
  `R : RepresentationFam → Type` (for the two constant/self carriers: `fun _ => List Annotations`,
  `RepresentationSelfCarrier`); field names gain their sort prefix; `Representation.fold alg` is
  `cata_representation alg`; `Representation.fold_declaration` is the generated equation's name.
  `modifyRepresentation_id` (`:694-850`, a 150-line hand case analysis) should fall to: show
  `modifyAlgebra id = RepresentationAlgebra.id` (a `simp only` with `List.map_id'`-style lemmas
  and structure eta), then `cata_id_representation`. If it does, delete the hand proof.
- `EffectfulField.lean:774,844`: the same rename.
- Tests: port `Test/Counterexamples/Schema/RecursiveElimination.lean`; cut
  `Test/Schema/RepresentationFoldContract.lean` to what the generated theorems do not already
  state (or delete it and move the two or three behaviour guards into the generator's guards
  file); bring `Test/contracts/schema-recursor.contract.md` in line; fix `Test/All.lean`.
Narrow builds: `lake build Effect4.Schema.Annotations Effect4.Schema.EffectfulField`, then
`lake build TestSchema` (the schema test library; see `lakefile.toml`), then, in the background,
`lake build Effect4 Effect4Laws` once, because `Representation.lean` changed under everything.

**Step 4 — the other four copies (stop rule applies).** In this order, each only if the previous
is green:
1. `Schema/Check.lean:827-945`: `fieldAdmissible` as a `foldMap_representation true (· && ·)` with
   one head predicate per sort (the head predicate checks the node's own `annotations` and, for
   `arrays`/`objects`, its records' `annotations`). Keep the public name and statement.
2. `Schema/Check.lean:707-825` and `:1041-1179`: if `FieldAdmissible` can become
   `fieldAdmissible r = true` (or be derived from it) without breaking the theorems below it that
   unfold it by cases, the 140-line agreement block goes. Measure first: list the theorems that
   `unfold`/`cases` on `FieldAdmissible` and say what each would need. If more than a handful need
   real rework, STOP and report; do not push through.
3. `Codegen/Schema.lean:227-360`: the printer as an algebra on the constant carrier `Expr`
   (check carrier `Expr`). The printed text must not move: `make check-schema-codec` and the
   schema-TS pins compare it. If a byte moves, revert this sub-step and report.
**Stop rule:** any sub-step that is not green within about two hours of focused work is reverted
(edit the files back by hand; the guardrail hook refuses `git checkout --`; never use a bypass
flag) and written up in the receipt with the failing goal.

**Step 5 — receipt.** `docs/research/2026-09-17-generated-nested-fold-receipt.md`: per step what
changed, lines deleted and added (`git diff --stat`), every build command run and its result, the
axioms of the generated theorems, anything reverted and why, anything noticed and not done. Update
row C-P8 of the ledger.

## 5. Gates the seat runs (and the traps)

- `make check-roots` after adding a module.
- The generated file must be reproducible: after staging (`git add -A src tools Test`), run the
  driver's verify for the two fold groups:
  `lake env lean --run tools/Effect4Gen/Driver.lean --group Fold --check` and the same with
  `--group SchemaFold`. **`check-gen` compares the working tree with the staging area**, so stage
  before it or it reports a false drift.
- `docs/research/2026-09-17-regen-groups.py <Group> …` builds a group's imports and runs it, in
  the order given; use it rather than `make gen` (which runs groups in an order that trips on a
  stale engine layout).
- `make check-citations` if any tracked document's cited path or line range moved
  (`Test/contracts/schema-recursor.contract.md` cites the hand fold).
- Do not run `make check`, `make check-host` or a bare `lake build`. The coordinator owes one
  sweep for the wave and will run it.
- Do not commit and do not push. Leave the tree green and staged; the coordinator reviews the diff
  against this packet and commits by step.

## 6. Out of scope, with the reason

- **`Store/Shape.lean`.** Two of its six traversals (`acceptsAt`, `printIn`) recurse on a `Val` and
  a `Shape` together: folds on a product, which the scout's own note rules out for `Ty.sub`.
  The monotonicity block is an induction over `acceptsAt`. The three one-argument traversals are
  exhaustive matches Lean already checks (75 lines); turning them into algebra instances needs the
  file split in two for the generated module to sit between, for a saving under 100 lines. Probe
  it in step 1(c) so the position language is known to cover it; do not wire it in.
- **The monadic half and `foldMapAt` for nested families** (§2.8): no consumer.
- **Deleting unconsumed schema declarations at large** (ledger C-P11). Inside the files this slice
  already edits, a declaration with no reference anywhere (tests included) that would otherwise
  have to be ported may be deleted instead of ported; say so in the receipt. Nothing wider.
