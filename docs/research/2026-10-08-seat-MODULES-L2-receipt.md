# 2026-10-08 seat MODULES, slice L2: the step language over `Ty`

Status: landed. Decisions row 330 records the ruling and this slice.

## 1. The one thing to know first

A module's step written as data inherits three laws, each proved once for the language:

- its term reads the encoding of its value;
- its term types at the step's type;
- on an update spine, a field that no overwrite names keeps its value.

Semaphore's `takeIfAvailable`, written as a step over Semaphore's own cell, has exactly
Semaphore's term, by `rfl`, and it passes the typing check. So slice L3 owes only the encoding
connector between Semaphore's model and the step's carrier.

## 2. Base, head and files

- Base: `a2d1dc7a` (slice L1). Head: the commit that carries this receipt.
- New, in the core (each a `module`):
  - `src/Effect4/Program/TyNormal.lean`: the normal-form certificate `Ty.certNormal`, a fold of
    `Ty`;
  - `src/Effect4/Schema/FieldRef.lean`: `FieldRef`, its `get` and `set` on carriers, and
    `entriesAt`;
  - `src/Effect4/Modules/Step.lean`: `Input`, `Inputs`, `Step`, `StepAlgebra`, `Step.cata` and
    the folds `term`, `eval`, `writes`, `spine`, `canonical` and `normal`.
- New, in the law graph: `src/Effect4/Laws/Program/TyNormal.lean`,
  `src/Effect4/Laws/Schema/FieldRef.lean` and `src/Effect4/Laws/Modules/Step.lean`.
- New battery: `Test/Program/StepLanguage.lean`.
- Changed:
  - `src/Effect4/Schema/Modeled.lean`: the identity context (section 4);
  - the three roots;
  - `tools/Tools/SemanticsRegistry.lean`, `docs/core/semantics.md`, `docs/core/decisions.md`,
    `docs/STATE.md` and `generated/semantics.md`.

## 3. Placement of each landed theorem

| Theorem | Concept | Claim | Reach | Not established | Unlocks |
| --- | --- | --- | --- | --- | --- |
| `Step.sound` | `translation-simulation` | `step-language-sound` (pointer) | every step that passes `canonical`, every scope, every identity context, every caller's terms that read the inputs | a fold, an optional field, a step's specification, a run | each module's `*_agrees` as a corollary; R10 |
| `Step.typed` | `store-typing` | `step-language-typed` (pointer) | every step that passes `normal`, every scope, every caller's terms typed at the inputs' types | a run; a fold | each module's `*_types` as a corollary; R4 |
| `Step.frame`, `Step.frame_read` | `translation-simulation` | `step-frame` (pointer: `Step.frame`) | every update spine; on carriers with no premise, on the frame with ascending names | a step that is no spine | a module's frame statement; R10 |
| `FieldRef.frame_laws` | `exact-codecs` | `record-field-laws` (pointer) | every record with ascending names, every identity context | an optional field | the reading law's field arms; R3 |
| `Ty.normalize_of_certNormal` | `subtyping-algebra` | a helper of `step-language-typed` | every certified type | the converse | the typing check by `rfl` |
| `Step.canonical_of_normal` | `store-typing` | a helper of both step claims | every step | — | one check gives both laws |

The lens laws on carriers (`FieldRef.get_set`, `set_get`, `set_set`, `get_set_other`,
`set_comm`) are helpers of `record-field-laws` and of `step-frame`.

## 4. What L2 changes from the revision 3 plan

Each change is a strengthening.

- **The identity context.** L1's carrier fold takes the carrier of each identity type from a
  context (`Model.Leaves`). L1's fold is the context that refuses every identity, and its laws
  are unchanged. The opaque context carries an identity as its own value, so a step reads and
  writes Semaphore's cell, which holds `Deferred` identities. Slice L6 adds a context backed by
  a table, with no change to the step laws.
- **Several inputs.** A step takes a list of inputs, so `takeIfAvailable(need, cell)` is one step.
- **The typing law.** The plan named the reading law and the field laws. The typing law is new,
  and it reuses the typing twin of the builders (`src/Effect4/Laws/Modules/Checking.lean`).
- **The normal-form certificate.** `Ty.normalize` at a product goes through the union rows,
  whose order is decided by the well-founded `Ty.sub`, so `decide` cannot close `t.normalize = t`
  there. The certificate is a fold of `Ty`, sound by one theorem, so the typing check closes by
  `rfl`.
- **A field after an optional field.** `FieldRef.there` passes a field of any kind. The carrier
  of every field is one product column (`Model.fieldCarrier`), whether the field is optional or
  not.

## 5. The battery

`Test/Program/StepLanguage.lean`:

- **Readers.** Latch's cell and its release, as steps over `Ty`. The three laws are read at the
  release, and the frame law is read on the machine's frame.
- **Finite evaluations:**
  - the release's term equals probe MODS-1's hand term, at a scope;
  - Semaphore's `takeIfAvailable`, written as a step, has `Semaphore.takeIfAvailableStep` as
    its term, by `rfl`.
- **Controls:**
  - the fault "release opens" names `open`, so the frame law's premise fails;
  - a field's read that yields a record is no update spine;
  - a record whose names are out of order fails both checks;
  - a selection at a union not in canonical order passes the reading check and fails the typing
    check.

## 6. Commands and results

Run on 2026-10-08 from the repository root:

```sh
scratch/lean-slot.sh lake build Effect4.Laws.Modules.Step Effect4.Laws.Schema.FieldRef Effect4.Laws.Program.TyNormal
scratch/lean-slot.sh lake build Test.Program.StepLanguage Test.Schema.Modeled Tools.SemanticsRegistry Effect4 Effect4.Laws
scratch/lean-slot.sh python3 scripts/check-conform.py cases
```

Each build completed with no error and no warning. The case-site audit passed:
`conform cases: PASS, exit 0`.

The semantics report was rebuilt by the commands of `make gen-semantics`, without its whole-tree
`lake build` step. `generated/semantics.md` differs only by the four new claims, all proved, and
by the new nodes of R3, R4 and R10.

**Axioms.** A scratch audit walked every declaration of the seven new modules and the changed
`Effect4.Schema.Modeled` with `Lean.collectAxioms`:

| Module | Declarations | Outside `[propext, Quot.sound]` |
| --- | --- | --- |
| `Effect4.Program.TyNormal` | 4 | none |
| `Effect4.Laws.Program.TyNormal` | 12 | none |
| `Effect4.Schema.FieldRef` | 49 | none |
| `Effect4.Laws.Schema.FieldRef` | 51 | none |
| `Effect4.Modules.Step` | 266 | none |
| `Effect4.Laws.Modules.Step` | 39 | none |
| `Test.Program.StepLanguage` | 16 | none |
| `Effect4.Schema.Modeled` | 91 | none |

The counts were taken before the combined theorem `FieldRef.frame_laws` was added. The
`_unsafe_rec` helpers are the generated recursors that the gate admits.

The whole battery, the axiom gate over `Test.All` and `make check` were not run: they belong to
the owner's sweep.

## 7. Open obligations

- **Folds in the language**: `foldWith` with its two minted binders, for the removal by identity
  and the visits. Semaphore's take, visit and withdraw need them.
- Record construction (`record`), string literals, unions and optional fields.
- **A reading footprint**: a step's value depends only on the fields it reads. With the writing
  footprint it would give commutation of independent steps.
- **A view of a step** for the authoring surface: the step is data, and no rendering of it
  exists yet.
- **L3**: the connector from Semaphore's model (`cellVal tb s`) to the step's carrier at the
  opaque context. Then `takeIfAvailableStep_agrees` and `takeIfAvailableStep_types` become
  corollaries.

## 8. Evidence kinds

The theorems are proved for every step, scope and identity context in their statements. The
battery's `#guard` lines are finite evaluations. Nothing here is host evidence.
