# 2026-10-08 seat MODULES, slice L1: `Modeled` in the tree

Status: landed. Decisions row 330 records the owner's ruling and this slice.

## 1. The one thing to know first

A Lean structure ties to its `Ty` by `deriving Modeled`, and its two laws come from one place.
Every value of a derived structure inhabits its type at every allocation table, and it survives
JSON under codec admission. An instance owes no proof, and a wrong instance does not compile.

## 2. Base, head and files

- Base: `93cad52d` (MODULES revision 3). Head: the commit that carries this receipt.
- New, in the core (each a `module`, decisions row 200):
  - `src/Effect4/Store/Carrier/Image/Record.lean`: `Columns`, `Image.record`, `Image.empty`;
  - `src/Effect4/Schema/Modeled.lean`: the carrier fold `Model.alg`, its carrier and image,
    the refusal fold `Model.refusalAlg`, and the class `Modeled`;
  - in the same file, the instances at `Unit`, `Bool`, `Nat`, `String`, `List`, `Option` and
    products;
  - `src/Effect4/Schema/Modeled/Derive.lean`: `deriveModeled`, the command `derive_modeled`
    and the deriving handler.
- New, in the law graph: `src/Effect4/Laws/Schema/Modeled.lean`.
- New battery: `Test/Schema/Modeled.lean`.
- Changed: the three roots (`src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`),
  `Test/Audit/AxiomGate.lean`, `tools/Tools/SemanticsRegistry.lean`, `docs/core/semantics.md`,
  `docs/core/decisions.md`, `docs/STATE.md`, and `generated/semantics.md`.

The probe's files stay in `docs/research/2026-10-08-seat-MODULES-r3/`, unchanged.

## 3. Placement of each landed theorem

| Theorem | Concept | Claim | Reach | Not established | Unlocks |
| --- | --- | --- | --- | --- | --- |
| `Model.member` | `store-typing` | `modeled-membership` (pointer) | every carrier value of every checked `Ty`, every allocation table | identity types, optional fields, refused constructors; codec admission | L2's field laws over checked records; R3 |
| `Modeled.member` | `store-typing` | a reader of `modeled-membership` at each instance | every value of a modeled type | as above | each derived type's membership |
| `Modeled.codec_roundtrip` | `exact-codecs` | `modeled-codec` (pointer) | a modeled value under `Ty.isCodecValue` at the normal form of its type | the TypeScript codec (L4); target execution | the authoring surface's JSON boundary |

Both pointers carry `@[semantics … (requirement := R3)]`. The helpers `or_none`,
`checkers_names`, `columns_names`, `names_map_refusal` and `member_fields` are steps of
`Model.member`.

## 4. The deriving step

`deriveModeled` checks the declaration before it writes anything. Each refusal is located at
the Lean syntax it is about, and the battery holds one red control for each:

| Control | Refusal |
| --- | --- |
| a hand instance with record names `z`, then `a` | `decide` shows `Model.refusal … = none` false |
| a hand instance at an identity type | `decide` shows `Model.refusal (Ty.handle …) = none` false |
| a rename of a missing field | "has no field misspelled" |
| two fields spelled `flag` | "two fields … are spelled flag" |
| one field renamed twice | "field left is renamed twice" |
| a structure with a parameter | "has parameters; the first profile is monomorphic" |
| a structure with a universe parameter | "has universe parameters; the first profile is monomorphic" |
| a field of type `Int`, through `deriving Modeled` | "field type Int has no Modeled instance" |
| a field that is a proof | "field type True is a proposition" |
| a field whose type depends on another field | "field type Fin n depends on another field" |

The two universe-parameter, proof and dependent-field controls are new since revision 3. A
field's default spelling is its name unescaped, so a field `«open»` is spelled `open`.

## 5. Commands and results

Run on 2026-10-08 from the repository root:

```sh
scratch/lean-slot.sh lake build Effect4.Schema.Modeled.Derive Effect4.Laws.Schema.Modeled
scratch/lean-slot.sh lake build Test.Schema.Modeled Tools.SemanticsRegistry
scratch/lean-slot.sh lake build Effect4 Effect4.Laws
```

Each build completed with no error and no warning (`-DwarningAsError=true`).

The semantics report was rebuilt by the commands of `make gen-semantics`, without its whole-tree
`lake build` step. `generated/semantics.md` differs from the committed copy only by the two new
claims, both proved, and by the two new nodes of R3.

**Axioms.** A scratch audit walked every declaration of the five new modules with
`Lean.collectAxioms`:

| Module | Declarations | Outside `[propext, Quot.sound]` |
| --- | --- | --- |
| `Effect4.Store.Carrier.Image.Record` | 56 | none |
| `Effect4.Schema.Modeled` | 67 | none |
| `Effect4.Laws.Schema.Modeled` | 49 | none |
| `Test.Schema.Modeled` | 195 | none |
| `Effect4.Schema.Modeled.Derive` | 17 | `Classical.choice`, through `MetaM` |

The deriving module is meta code with no theorem, like `Effect4.Program.FoldOf`. It is named in
the gate's list of audit implementation modules (`auditImplementationModules`,
`Test/Audit/AxiomGate.lean`), whose staleness check keeps the entry honest. The two compiler
helpers `fieldsRefusal._unsafe_rec` and `columnsOf._unsafe_rec` are the generated recursors the
gate admits (`isGeneratedSafeRecursor`).

A first draft of the battery held the two `decide` controls as `instance` commands. Each left
an instance whose proof is `sorryAx` in the environment, which the gate forbids. They are
`example`s now, which add no declaration.

The case-site policy (`make check-cases`) is not owed: no new code matches on a policy family.

The whole battery, the axiom gate over `Test.All` and `make check` were not run: they belong to
the owner's sweep.

## 6. Open obligations

- L2: the step language over the checked `Ty` domain, with the field laws over `Image.record`.
- L3 to L6, as the revision 3 note's section 6 orders them.
- Optional fields, and the arms `int`, `union`, `except` and `tuple`, are refused by name.
- Identity types wait for their role-specific tables (L6).
- The TypeScript face of a derived type is a finite evaluation in revision 2's probe, not a law.

## 7. Evidence kinds

The three theorems are proved for every value. The battery's `#guard` lines are finite
evaluations at one cell. Nothing here is host evidence.
