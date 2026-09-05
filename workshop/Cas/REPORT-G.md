# Lane G report — the generator of `Canonical` instances

Filed by the coordinator from the lane's closing message (the lane could not write this
file itself); its running notes are `NOTES-G.md` (five dated entries). Repository
`C:\Users\kokok\Dev\lean4-effect4`, branch `main`, v4.33.1. Real clock by file times:
2026-09-04 23:35 → 2026-09-05 00:35 (the lane's own timestamps, here and in its notes, run
about two and a half hours fast).

## Outcome

All four deliverables done and green.

| group | file | receipts | check |
| --- | --- | --- | --- |
| `Json` | `Gen-out\Json.lean` — `Float64`, `Json` | 9 | 2 s |
| `Program` | `Gen-out\Program.lean` — `Lit`, `FnName`, `FinalizerStrategy`, `MaskMode`, `ObserverMode`, `NativeOp`, `ForkOptions`, `Term`/`Terms`, `CauseTerm`, `Eff`/`Stmt`/`Stmts`/`Effs`/`ActionTerm` at `NativeOp` | 67 | 12 s |
| `Schema` | `Gen-out\Schema.lean` — the 13 requested carriers plus the 4 companions the block pulls in | 84 | 14 s |

160 `#print axioms` receipts: 5 with no axioms, 36 `[propext]`, 119 `[propext, Quot.sound]`,
none other. No `sorry`/`sorryAx`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern`,
`implemented_by`, no `Classical.choice`. Every `#guard` passes.

**`Canonical Document` exists** (`Effect4.Store.SchemaGen.DocumentC.instCanonical`), with
`Canonical Representation`, `Canonical Check`, `Canonical MultiDocument` and the eleven leaf
carriers; lane S2's `[Content Document]` sections are unblocked.

Discipline: PowerShell only; no `git`; no `lake build` — every compile `lake env lean -M 4096
<file>`, every run `lake env lean -M 4096 --run …`, each with a ten-minute timeout. Slowest
process 14 s, none near the memory cap, none left running. `workshop\Cas\Cas\` never touched.

## Files

- `gen\Main.lean` — the generator (`import Lean`, `--run`; outside the `Cas` glob)
- `gen\Check.lean` — the projection guard
- `gen\guards-{json,program,schema}.lean` — acceptance guards, appended verbatim by `--append`
- `tools\generate-derived.ps1` — the manifest and the regeneration/verification script
- `Gen-out\{Json,Program,Schema}.lean`, `NOTES-G.md`

## Agreement with the oracle

- Trees: `ProgramGen.EffC.toValEff p = ProgramCanonical.EffC.toValEff p` on all eight corpus
  programs, plus every constructor of `Lit`, `FnName`, `MaskMode`, `ObserverMode`,
  `FinalizerStrategy`, all twenty `NativeOp`s, `ForkOptions`, `Term`, `CauseTerm`;
  `JsonGen.JsonC.toValJson j = JsonCanonical.toVal j` on twelve `Json` samples; `Float64` on
  five bit patterns.
- Bytes: the generated hex equals `ocaml\goldens\eff\{p42,pBind,pFork,pAwait,pGen,pLoop,pCatch,
  pScope}.hex` (literals copied from the golden files, not from `Cas/Program.lean`); `p42` is 66
  bytes, digest `fa5f40…62a3`.
- Readers (spelled without the class, so the hand instance cannot answer): round trip on the
  corpus and on every `Json` sample; a byte appended refused, a byte dropped refused, a
  leading-zero constructor index refused.
- Shapes: every corpus tree fits the generated and the hand `defs`.
- `Schema` has no hand oracle, so its guards are the laws on real values: five `Document`s —
  `entryDoc.document`, the meta-schema, and a `Representation` touching an empty `$ref`, a
  bigint literal, a non-finite number literal, a nested `FilterGroup` with a `schemas` list, a
  global-symbol key, an index signature, a duplicate reference key — all round-trip, all fit,
  all refuse a corrupted frame. The meta-schema `Canonical.document Document` is a fixed
  point: the spec of `Document` is itself a stored `Document` with its own address.
  `Annotations` keeps absence and a present empty bag apart in the bytes.

## Design, as implemented

An item is a requested type with its `InductiveVal.all` block plus the applied nominal
carriers that mention a member — the fixpoint that pulls `ElementOf`/`PropertySignatureOf`/
`IndexSignatureOf`/`CheckRepresentationAnnotationOf` at `Representation` into the block. One
`defs` per item, members by `.named`, everything else through its own instance, nothing
inlined; `List`/`Option`/`×` over a member gets a companion. Two proof shapes only: recursive
→ `guarded toVal raw` (S1's recipe) with mutual `fits` via `accepts_named_of_mem`/
`acceptsAt_sum`/`acceptsFields_cons` and explicit `mem_tail`/`mem_append_of_left|right` lift
chains; non-recursive → S1's `LitC` and `Entry`/`ForkOptions` scripts verbatim. `toVal` is
identical either way, so the bytes are.

## The guard

`gen\Check.lean` is an independent second implementation: it reads the generated text, not
the generator's IR, and finds each carrier by its own `env.constants` search. It compares
struct-vs-sum, case names in order, field names in order and arity, and the constructor index
each `toVal` clause writes. It agrees on all 35 shapes. Measured refusals on corrupted
scratch copies: a renamed case, a `toVal` writing `.ctor 4` where 3 is declared, and two
swapped struct fields — each refused, naming the exact difference.

## Commands

```
pwsh -File workshop\Cas\tools\generate-derived.ps1                 # regenerate, report changes
pwsh -File workshop\Cas\tools\generate-derived.ps1 -Check          # + compile each, + guard, + axiom scan
pwsh -File workshop\Cas\tools\generate-derived.ps1 -Verify -Check  # + exit 1 if anything changed
lake env lean -M 4096 --run workshop\Cas\gen\Main.lean --group Program --imports Cas.Program --out workshop\Cas\Gen-out\Program.lean --append workshop\Cas\gen\guards-program.lean Effect4.Program.Lit … Effect4.Program.Eff@Effect4.Program.NativeOp
lake env lean -M 4096 workshop\Cas\Gen-out\Schema.lean
lake env lean -M 4096 --run workshop\Cas\gen\Check.lean workshop\Cas\Gen-out\*.lean
```

`@` reads as a space in a type argument, so an applied type is one shell word. Last full run:
`same` ×3, `green` ×3, guard agrees, exit 0 — the generator is idempotent.

## Open

- Line width: 71 lines of `Schema.lean` and 8 of `Program.lean` pass 100 columns because of
  `_root_.` qualification; a per-group `open` prelude in the emitted header is the fix.
- `Templates.Entry`/`Templates.ExportKind` are not regenerated (they live inside `Cas.Templates`,
  so a generated redeclaration would collide with the oracle); their two shapes are exercised by
  `Float64`/`ReferenceKey` and `UnionMode`/`MaskMode`.
- A bare parameterised type is refused — the `[Canonical α]` instance-binder rule is the one
  rule of BRIEF-G left unexercised (every group applies its parameters).
- `Canonical.encode = Wire.encodeProgram` is still not a theorem (the Wire imports the old
  store); the goldens are the receipt.
- Deduplicated foreign tables: where the hand file lists a repeated field type's table twice,
  the generator lists it once — both are `[]` here, and `acceptsIn` resolving a name against all
  bindings makes it harmless in general.
- Two benign warnings in emitted files, each explained where it appears: `linter.unusedSimpArgs`
  on `cases a <;> simp […]` over a sum with nullary cases, and "unused `termination_by`" on
  `Option`/`×` companions.

## Two decisions for the landing (the coordinator's, taken 2026-09-05 ~03:05)

1. The appended guards call the hand oracle by name, so a `Cas/Derived/Program.lean` beside
   `Cas/Program.lean` declares a second instance for `Eff NativeOp`. **Decision: the generated
   instances are the instances.** At the landing the hand `Program.lean` and the `Json` half of
   `Templates.lean` retire; the goldens and the reader guards stay as the receipts; `Templates`
   keeps the local `ExportKind`/`Entry`/`Tree`/`Forest` as the documented templates (a battery,
   not an instance source). In the spike both stay so the agreement guards keep running.
2. The manifest lives in `tools\generate-derived.ps1`; `-Verify` becomes `git diff --exit-code`
   once `Cas/Derived/` is tracked. **Decision: yes**, and the landing's `scripts/generate-derived.ps1`
   is this script with the paths moved.
