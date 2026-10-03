# Staged generation: how the derived Lean files should be produced

Base: `03850cbd`. Author: Claude, lead. Status: a design note for the owner and Codex. It lands
nothing. The owner asked that the staged split follow Lean's own compilation stages, and that it be
researched before it is implemented (2026-10-03).

**The one thing to know.** The derived group's order was never a valid build order. Of the 26 rows,
the manifest lists 50 prerequisites after the rows that need them. Regeneration worked only because
the committed outputs compile. The one real bootstrap property was that `TyEq` runs first. Its tool
imports no Effect4 module. Commit `2f8da42d` broke that property. Its single executable imports
Effect4 through three generators. After a `Ty` constructor change, it cannot build before `TyEq` is
regenerated. Nothing triggers this until the type-language work changes `Ty`.

## 1. The measured prerequisites

A row needs a generated module in two ways. The row's `--imports` can reach the module at run time.
The row's generator can import the module at compile time. Measured from the import headers at
`03850cbd`:

| Row | Tool | Generated modules it needs (run time) | Its tool needs (compile time) |
| --- | --- | --- | --- |
| TyEq | Fold | none | none |
| Json, Pin, Value | Main | none | TyEq, Fold, NodeLenses, AtomInventory |
| ValFold, SchemaFold | Fold | none | none |
| AtomInventory | Atoms | none | none |
| Schema | Main | Json | as Main |
| Fold | Fold | TyEq | none |
| NodeLenses | Authoring | TyEq | none |
| LayerView, TyExtras | LayerView, Fold | TyEq, Fold | none |
| Binders, Scoped | Authoring | TyEq, Fold, NodeLenses | none |
| Authoring | Authoring | TyEq, Fold, NodeLenses, AtomInventory | none |
| Program, Api | Main | TyEq, Fold, NodeLenses, AtomInventory | as Main |
| TyView | View | TyEq, Fold, SchemaFold, NodeLenses, AtomInventory | none |
| PreludeAtoms | PreludeAtoms | TyEq, AtomInventory | TyEq, AtomInventory |
| Rows | Rows | as Authoring, plus Authoring | TyEq, Fold, NodeLenses, AtomInventory |
| ScopedLaws | Authoring | as Binders, plus Binders, Scoped, Authoring | none |
| Refusals, Forms, RowsLaws | Main, Forms, Rows | up to Rows (and ScopedLaws) | as their tools; Forms also LayerView |
| Runner, FormsLaws | Main, Forms | up to Refusals, or Forms and RowsLaws | as their tools |

Two facts follow:

- The `Main` generator's compile-time need is false. It comes from `Tools.ProgramStructure`, which
  imports `Effect4.Program.Native`. That facade only holds names, and it reads them in the
  environment that a run loads. Removing the import makes six tools import no Effect4 module:
  `Main`, `Fold`, `Authoring`, `View`, `LayerView` and `Atoms`. The edit is tried and parked, and
  Codex confirmed the reading.
- Three tools need Effect4 at compile time for real. `Rows` reads `NativeOp.all`, `Forms` reads
  `Codegen.Forms.all`, and `PreludeAtoms` reads `NativeAtom.all` and its specifications. Each reads
  a typed catalogue as a Lean value.

The prerequisites allow an order of six levels:

1. TyEq, ValFold, SchemaFold, AtomInventory, Json, Pin, Value;
2. Fold, NodeLenses, Schema;
3. the consumers of the folds;
4. Rows and ScopedLaws;
5. Refusals, Forms and RowsLaws;
6. Runner and FormsLaws.

## 2. What Lean itself provides

- **Lake's build graph is the stage scheduler.** A module builds after everything it imports. A
  declaration that a command adds during Lean elaboration is ordered by Lake for free.
- **`meta import` does not break a build prerequisite** (Codex, from the pinned source). In Lean
  4.33.1 a meta import changes which code Lean's compiler IR loads. Lake still builds every header import
  first. A module in the module system may import only modules.
- **A command can add declarations during Lean elaboration.** That is Lean's own generation
  mechanism: `deriving`, and in this tree `fold_of` (`Program/FoldOf.lean`) and `#typed_state`
  (`Laws/Program/Typed/TypedStateDecl.lean`). Refusal fixtures exist in
  `Test/Audit/TypedStateDecl.lean`. A command may read declarations made earlier in its own file.
  Its implementation must not import that file.
- **`precompileModules` compiles a library to native code** and loads it into every importer's
  elaborator. It now serves the axiom gate and `sub_tac` (`580261d6`).

## 3. Options

**A. Commands for the Lean outputs.** `TyEq.lean` would hold its imports and one command, for
example `#derive_ty_eq Effect4.Program.Ty`. The generator code would be the command's
implementation, in a module that imports no consumer. Lake would order everything by imports. The
Lean files would leave `make check-gen`, and with them the manifest's Lean rows, the batch and the
bootstrap question. The costs:

- the generator runs inside `lake build`, about a second per module, cached by Lake;
- the generated text is no longer a reviewable diff, so it needs a command that shows a module's
  derived declarations on demand;
- each command needs coverage and refusal fixtures, because kernel acceptance alone does not
  establish coverage (Codex);
- the generator modules enter the core's import closure as meta code, which DI-18's re-ruling
  allows;
- whether the LCNF cut stays free of them needs a check.

**B. External generation on a computed schedule.** The generated files stay. The costs and parts:

- `scripts/generate.py` computes the order from import headers, as §1 does, and stops trusting the
  manifest's order;
- the six environment-reading tools form one executable that imports no Effect4 module, and a
  build-time check enforces it;
- the three catalogue tools form a second executable, built once the levels it needs are
  regenerated;
- the generated text stays a second representation of what the generators already know.

The parked work (`staged-split-wip`, outside the tree) is most of B.

**C. A hybrid by artifact kind**, Codex's suggested boundary. Commands produce the Lean-only
declarations that derive from data already in the environment. External generation stays where a
committed artifact or a byte comparison is the product. Those are the TypeScript prelude, the OCaml
estate, the goldens and the semantics report.

## 4. Recommendation

C, reached by a pilot. Convert `TyEq` to a command first. It is the bootstrap root: it needs no
generated module, its generator imports none, and its loss caused the regression. The pilot has
three measurements:

1. its build time against today's generated file;
2. its coverage fixture;
3. a check that the LCNF cut stays free of the generator code.

If the pilot holds, the other Lean rows follow by level, deepest dependencies first. The catalogue
rows (Rows, Forms, PreludeAtoms) become commands too, because a command reads catalogues as typed
values of the file that runs it. External generation keeps the non-Lean outputs, on B's computed
order.

## 5. Questions for Codex and the owner

1. Do the generated Lean files need to stay committed, for review or for the LCNF and OCaml routes?
   If they must, A is out and B is the route.
2. Should the command implementations live under `src/`, in the audited tree as meta code admitted
   by name like `Laws/Auto`? Or should they stay under `tools/`, imported by core modules?
3. Is about a second of generator work per derived module inside `lake build` acceptable, against
   today's 39 s batch outside it?
