# Lane G — the generator of `Canonical` instances

Starts after lane S1's report (`REPORT-S1.md`, 2026-09-05 00:45): S1 is green and frozen.
General rules: `BRIEF.md`. The design: `docs/research/2026-09-04-cas-trait-plan.md` §4; the
rulings Q2 and Q5 in `docs/research/2026-09-04-cas-trait-facts.md` §5.

**Amendments after S1 (2026-09-05 00:50).**

- **You do not own a `lake`.** Lane S2 runs concurrently and owns the one `lake build Cas`.
  You verify with `lake env lean -M 4096 <file>` only (it reads the oleans S1 built and
  writes none). Your tool lives at `workshop/Cas/gen/Main.lean` (outside the `Cas` library's
  glob, so a broken file of yours can never break S2's build); your emitted files go to
  `workshop/Cas/Gen-out/<Group>.lean` with `import Cas.Canonical` (and the carriers'
  modules) at the top, checked one by one with `lake env lean -M 4096`. Never write under
  `workshop/Cas/Cas/`; the coordinator moves green output into `Cas/Derived/` afterwards.
- **Two groups already exist by hand**, written exactly as you must emit them:
  `Cas/Templates.lean` (`ExportKind`, `Entry`, `Float64`, `Json`, the mutual `Tree`/`Forest`)
  and `Cas/Program.lean` (the whole `Eff` family). They are your oracle and your first
  acceptance: regenerate `Json`, `Float64` and the `Program` group into `Gen-out/` and show
  (a) they compile under `lake env lean -M 4096` at the ceiling and (b) their `encode` agrees
  with the hand instances on the samples S1 guards (the §6 entry bytes, the eight corpus
  programs' hex from `ocaml/goldens/eff/*.hex`). Read S1's `NOTES.md` (the tactic templates,
  the `guarded` recipe for recursive families, the toolchain hazards) and `REPORT-S1.md`
  before writing a line.
- **The real deliverable is the `Schema` group**: `Effect4.Representation`, `Effect4.Check`
  and their carriers, and `Effect4.Document`, which nobody has by hand. It yields `Canonical
  Document`, the meta-schema, and unblocks lane S2's `[Content Document]` sections.
- `Digest` is `{bytes, length_eq}` now (S1's departure); a `Digest` field goes through
  `Canonical Digest` unchanged.

## What it is

A `--run` tool, `workshop/Cas/Cas/Gen/Main.lean` (module `Cas.Gen.Main`, `import Lean`;
`IO` and `Lean.Meta`; not part of any audited library), that reads inductives out of the
environment and **emits Lean text**: one file per group, `workshop/Cas/Cas/Derived/<Group>.lean`,
containing exactly what `Cas/Templates.lean` shows by hand for each type — `shapeDoc`,
`toVal`, `ofVal`, `ofVal_toVal`, `ofVal_exact`, `fits`, `instance : Canonical T` — with the
tactic scripts S1 recorded. The pattern for the environment walk is
`src/OCaml5/Tools/Describe.lean` (`getConstInfoInduct`, `forallTelescope` over each
constructor, `isStructure`, `InductiveVal.all` for a mutual block, `isNested`); the pattern for
"generated Lean text with a guard" is `src/OCaml5/Lib/Derived.lean`.

    lake env lean --run workshop\Cas\Cas\Gen\Main.lean --group Json Effect4.Json > workshop\Cas\Cas\Derived\Json.lean

The manifest of groups (type names in dependency order; a group is one emitted file whose
imports are the carriers' modules plus `Cas.Canonical`):

| group | types | notes |
| --- | --- | --- |
| `Json` | `Effect4.Json` (and `Effect4.Float64` as `nat` bits) | nested recursion through `List Json` and `List (String × Json)` |
| `Program` | the `Eff` family from `Effect4.Program.Native`: `Lit`, `Term`/`Terms`, `CauseTerm`, `Fn`, `Strategy`, `NativeOp` and the enums, `ForkOptions`/`MaskMode`/`ObserverMode` (in `Effect4.Supervision`), `Eff`/`Stmt`/`Stmts`/`Effs`/`ActionTerm` | mutual; constructor order = the Wire's; must reproduce the Wire's bytes on `Wire.Corpus` (S1's stretch instance, if it exists, is the oracle) |
| `Schema` | `Effect4.Representation`, `Effect4.Check`, the `PropertySignatureOf`/`ElementOf`/`IndexSignatureOf`/`EnumEntry`/`LiteralValue`/`Annotations`/`ReferenceKey`/`GlobalSymbolKey`/`UnionMode` carriers, `Effect4.Document` | mutual and nested; the meta-schema comes from this group |
| later, at the landing | `StdLib.Entry`, `ExportKind`, `Source`, `Pin`, the Surface carriers, the Char room's carriers | their modules import the old store, so they cannot be loaded during the spike |

## The rules the emitted code follows (they are Q2 and Q5, not choices)

- A structure is constructor 0 with its fields in declaration order; an inductive's
  constructors are numbered in declaration order; a parameter becomes an instance binder
  `[Canonical α]` and its shape is `Canonical.shape α` composed in.
- A field of type `Nat`, `Bool`, `String`, `Bytes`, `Int`, `UInt8`, `UInt64`, `Digest`,
  `List _`, `Option _`, `_ × _`, `Ref _`, `AnyRef`, or another carrier goes through that
  type's instance (`toVal`/`ofVal`/`shape`); nothing is inlined.
- The shape of a structure is `.struct "<Module.Type>" [(field, shape)…]`; of an inductive
  `.sum "<Module.Type>" [(ctor, [(arg, shape)…])…]`; a mutual block is one `ShapeDoc` whose
  `defs` bind every member by name and whose members refer to each other through `.named`.
- `ofVal` is structural on `Val` (`List.attach` or the nested-recursion support for the
  argument list); it refuses a wrong constructor index, a wrong argument count, and any
  argument its field's `ofVal` refuses.
- The proofs are the scripts of `Cas/Templates.lean`, verbatim per shape of type: a
  structure, an all-nullary sum, a sum with arguments, a nested recursion, a mutual block.
  If a script fails on a new type, fix the script for that *shape*, never patch one type by
  hand inside a generated file.

## The guard

`workshop/Cas/Cas/Gen/Check.lean`: for every type in the manifest, re-derive the constructor
and field lists from the environment and compare them with the generated `shapeDoc` (names,
order, arity); refuse on any difference. `scripts`-style regeneration is a PowerShell script
in `workshop/Cas/tools/generate-derived.ps1` that runs the tool per group and reports whether
any generated file changed (the landing turns that into `git diff --exit-code`).

## Acceptance (the plan's §4)

Every emitted declaration at `[propext]` or no axioms; the three groups above green under
`lake build Cas`; the `Program` group's bytes identical to the Wire's on the corpus; the
`Schema` group giving `Canonical Document`, after which lane S2's `[Content Document]`
sections instantiate and `metaSchema_accepts` is proved by `decide`. Report in
`workshop/Cas/NOTES.md` (dated entries) and `workshop/Cas/REPORT-G.md`.
