# 2026-10-15 seat codegen receipt: the codegen refactor, CR-0 to CR-12

Status: receipt (history, not authority). Branch `claude/codegen`, worktree
`/Users/pooks/Dev/lean4-effect4-codegen`, base `edae4e2b5`. The seat appends one section per
slice as the slice lands.

**The one thing to know before merging:** CR-0 cuts the codegen out of the program interface's
import closure, but one new module stays wide. The refusal alphabets of the printer and the
reader moved to `Effect4.Codegen.Refusal`, which `Effect4.Api` imports, because the generated
`src/Effect4/Api/RefusalsDerived.lean` reads them through `Effect4.Api`. Its imports come from
`tools/Effect4Gen/manifest.json`, which this seat may not edit. That module's edit rebuilds 454
modules; every other core codegen module rebuilds 16 to 91.

## Baseline at the base `edae4e2b5`

Each gate ran once through the shared slot before the first change. The logs are in the seat's
scratchpad (`gates/base/`).

| Gate | Result at the base | Time |
| --- | --- | ---: |
| `lake build Effect4 Effect4.Laws Tools Test` | **fails** at `Test.Program.ModuleDefinitions` only: three guards call `DefDecl.readable []`, a stale call since `582aab12d` changed its first argument to a `TypeEnv`; 329 modules built, 2 restored | 333 s |
| `make check-docs` | **fails** on one stale reference: `docs/core/decisions.md` row 362 names `tools/view/make_videos.py`, which is untracked in the main tree | 37 s |
| `make check-language` | passes | 7 s |
| `make check-ts-reader` | passes: 781 tests | 8 s |
| `make check-tsdiag` | passes: 408 programs, no program this checker types is refused | 2 s |
| `make check-ingest-smoke` | passes: 408 comparisons on each parser | 1 s |
| `make check-target` | passes: 104 rows conform; 742 pairs, 708 agree, 6 cut, 28 incomplete; rows 67 queried, 42 agree, 3 mismatch, 22 refused | 8 s |
| `make check-truth` | passes: 81 programs agree, 12 signed divergences | 75 s |
| `make check-corpus` | passes | 117 s |
| `make check-host-protocol` | passes | 95 s |
| `make check-schema-codec` | passes: 49 comparisons | 3 s |
| `make check-schema-ts` | passes | 6 s |
| `make check-gen` | passes: no drift | 100 s |

The times include the wait for the slot, so they bound a gate's own time from above.

## CR-0: the import cut

### Base and head

Base `edae4e2b5`, head `3fcd80e94`.

### What moved, and why each move serves the cut

The landing plan named three edges (`landing.md` §2.2). Reading the uses found four more, and
the first full build found a fifth.

| Edge | What the tree needed | The form landed |
| --- | --- | --- |
| `Effect4.Api` imports eight codegen modules | the face's codegen half | `src/Effect4/Api/Codegen.lean`, in the namespace `Effect4.Api`: `print`, `read`, `readAt`, `readable`, `roundTrip`, `imageCertificate`, `printDecl`, `emitModule`, `printModule`, `readModule`, `readFile`, `checkSourceBindings`, `admitModule`, `Typed.print`, `Typed.emit`, `TypedLayer.print`, `Built.print`, the Schema syntax and the exports `Target`, `Artefact` and `render`. The root `Effect4` and the entry module `Effect4.Emit` import it |
| the generated `Api/RefusalsDerived.lean` reads `PrintRefusal`, `ClassRefusal` and `ReadRefusal` through `Effect4.Api` | the three alphabets in scope of the module's fixed imports, which `tools/Effect4Gen/manifest.json` writes | `src/Effect4/Codegen/Refusal.lean`, a `module` file that imports nothing (decisions row 200); `Effect4.Api`, `PrintLeaf` and `Read` import it |
| `Laws.Program.Typed.Admission` reads `Eff.block?` from `Codegen.Print` | a program function, beside `Eff.defsOf` | `Eff.block?` in `src/Effect4/Program/Definitions.lean` |
| `Laws.Program.Typed.ListFold` imports `Laws.Codegen.ReadLeaf` | the plan read it as general lemmas; the claim `fold-typed-atomic-update` holds the leaf's printed equations in its statement (`ListFoldRules.readPrint`, `readExact`) | the codegen-free laws leave: `src/Effect4/Laws/Program/Typed/FoldEval.lean` (`evalTerm_weaken`, `foldlM_refuses`, `refModify_typed_step`) and `src/Effect4/Laws/Program/Typed/HandleIdentity.lean` (the claim `handle-identity-laws`). `ListFold` keeps its claim and its import; its consumers import the two new modules |
| `Laws.Step.Waiting` imports `Laws.Codegen.Mask` | the mask's derived form and its typing, read through the claim `mask-printed-form-profile`, whose statement holds the form's round trip | `maskForm`, `maskForm_typed`, `restore_typed` and `restore_untyped` in `src/Effect4/Laws/Program/Typed/Mask.lean`; `Waiting` reads `maskForm_typed` |
| `Laws.Step.Reading` reads `repr_inj` from `ReadLeaf` | a decimal law | `Effect4.Data.NatDecimal.repr_inj`, in `src/Effect4/Laws/Data/NatDecimal.lean` |
| the face imported `Api.Author` for `Built.print`, and `Author`'s closure makes `daemon` a keyword, which broke `Test.Program.AuthoringContract`'s structure literal | `Built.typed`, beside `Built` | `Built.typed` in `src/Effect4/Api/Built.lean`; the face imports `Api.Built` |

Two consumers now read a field's theorem in place of a claim's top node.
`step_keeps_cell` (`src/Effect4/Laws/Step/Store.lean`) reads `refModify_typed_step`, the `step`
field of `fold_typed_atomic_update`. The waiting wrapper's typing reads `maskForm_typed`, the
`typed` field of `mask_printed_form_profile`. No statement, pointer or placement changed. The
regenerated report (`generated/semantics.md`) shows the effect in R4's plan. Its graph no longer
passes through `mask_printed_form_profile`, `saved_mask_restoration` and `read_print`. They came
into it only through the mask claim's bundled statement. Every status is unchanged.

`ReadLeaf`'s copies went: the review's three (`bind_eq_ok`, `map_eq_ok`, `utf8_digitChar`) and
four decimal wrappers of the same kind (`decodeBytes_append`, `digitOfByte_digit`,
`decodeBytes_toDigitsCore`, `decodeBytes_repr`). The eight law modules that read the inversion
lemmas open `Effect4.Laws.Auto (bind_eq_ok map_eq_ok)`.

### Changed files

98 files: 94 modified and 4 new.

- The four new modules above, and the modules they left: `src/Effect4/Api.lean`,
  `src/Effect4/Api/Author.lean`, `src/Effect4/Api/Built.lean`, `src/Effect4/Codegen/Print.lean`,
  `src/Effect4/Codegen/PrintLeaf.lean`, `src/Effect4/Codegen/Read.lean`,
  `src/Effect4/Program/Definitions.lean`, `src/Effect4/Laws/Program/Typed/ListFold.lean`,
  `src/Effect4/Laws/Program/Typed/Mask.lean`, `src/Effect4/Laws/Codegen/Mask.lean`,
  `src/Effect4/Laws/Codegen/ReadLeaf.lean`, `src/Effect4/Laws/Data/NatDecimal.lean`.
- The consumers: `Laws.Step`, `Laws.Step.Store`, `Laws.Step.Reading`, `Laws.Step.Waiting`,
  `Laws.Library.Queue.Steps`, `Laws.Api.Codegen`, `Laws.Codegen.Definitions`, and the eight
  modules of the inversion lemmas.
- The root import `src/Effect4.lean`: one line appended at the end of its import block
  (`import Effect4.Api.Codegen`, with its comment). `src/Effect4/Laws.lean`, `Test/All.lean` and
  `Test/Audit/AxiomGate.lean` are unchanged.
- The importers: 47 batteries name the face (`Effect4.Api.Codegen`, or `Effect4.Emit` in the
  acceptance programs, which import entry modules); `tools/Drivers/Corpus.lean`,
  `tools/Tools/Code/Module.lean`, `tools/TestSupport/ServiceIdentity.lean`; nine harness
  scripts.
- Two stale callers of `DefDecl.readable`, failing at the base since `582aab12d`:
  `Test/Program/ModuleDefinitions.lean` (three guards, `[]` to `{}`, the empty type
  environment) and `harness/channel-transforms/Produce.lean`.
- Regenerated: `src/Effect4/Api/RefusalsDerived.lean` (its carrier line names
  `Effect4.Codegen.Refusal`) and `generated/semantics.md` (the module of
  `handle-identity-laws`, and R4's plan).
- The documents: `docs/ARCHITECTURE.md` (the face's rows; the stale hand count of module-system
  files removed), `docs/core/api-surface.md`, `docs/core/semantics.md` (the path of
  `handle_identity_laws`).

### Commands and results

Every command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. A time
includes the wait for the slot.

| Command | Result | Time |
| --- | --- | ---: |
| `lake build Effect4.Codegen.Refusal Effect4.Api Effect4.Api.Author Effect4.Api.Codegen Effect4.Emit Effect4.Api.RefusalsDerived Effect4.Program.Definitions` | passes, 183 jobs | 397 s |
| `lake build Effect4 Effect4.Laws Tools Test`, first run | fails at `Test.Program.AuthoringContract` only: `daemon` is a keyword through `Api.Author` | 1650 s |
| the same, after `Built.typed` moved | passes, 2235 jobs | 855 s |
| `python3 scripts/generate.py --only derived` | one line of `RefusalsDerived.lean` changes | 154 s |
| `#axiom_audit` over the 28 touched modules at the base, against the main tree's build | 8286 declarations within `[propext, Quot.sound]` | 149 s |
| `#axiom_audit` over the same 28 modules and the 4 new ones | 8276 declarations within `[propext, Quot.sound]` | 116 s |
| `make check-docs` | the base's one stale reference, no other | 1 s |
| `make check-language` | passes | 7 s |
| `make check-gen` | the two regenerated files differ from the base, as committed; nothing else | 96 s |
| `make check-ts-reader`, `check-tsdiag`, `check-ingest-smoke`, `check-target`, `check-truth`, `check-corpus`, `check-host-protocol`, `check-schema-codec`, `check-schema-ts` | each passes with the base's result lines; the host lane's lines differ only in a temporary folder's name | 4 s to 111 s |
| `lake env lean` on the eleven harness and application scripts | each elaborates | — |

The whole-tree gates of the second full build (`Test/All.lean`) report:

- the library-root gate: 276 API or utility modules and 622 Laws-only modules, every library
  source reachable;
- the axiom gate: 1358 modules and 126791 declarations, with its boundary of 22 modules and 49
  declarations;
- the goal gate: 25 planned goals, with 34 declarations on them.

### Axiom output

The two audits differ by 10 declarations, each named by a listing of the audited names in both
environments:

- the seven deleted copies;
- three auxiliaries of `Eff.block?` (`match_1`, `_sparseCasesOn_1` and its `else_eq`): in the
  module-system file `Program/Definitions.lean` its match is `Checker.checkModule`'s matcher;
- `repr_inj` changes its namespace to `Effect4.Data.NatDecimal`;
- the matchers of the three alphabets' `Repr` instances and four equation lemmas change their
  private names.

### The rebuild, measured

`probes/fanout.py` counts each module's importers in `src/` and `tools/`. Its walk of `Test/`
compares `root/./Test` with `root/Test`, so it counts no battery. The last column counts the
batteries too, by the same scan with that comparison repaired.

| Module | Rebuilt before | Rebuilt after | Law modules after | With the batteries, before and after |
| --- | ---: | ---: | ---: | --- |
| `Effect4.Codegen.Print` | 444 | 77 | 19 | 790, 282 |
| `Effect4.Codegen.Checked` | 417 | 48 | 5 | 756, 229 |
| `Effect4.Codegen.Types` | 458 | 91 | 24 | 810, 308 |
| `Effect4.Codegen.Read` | 439 | 72 | 18 | 783, 275 |
| `Effect4.Codegen.Schema` | 415 | 46 | 4 | 757, 230 |
| `Effect4.Codegen.Metadata` | 457 | 90 | 24 | 807, 299 |
| `Effect4.Codegen.PrintLeaf` | 450 | 83 | 20 | 798, 290 |
| `Effect4.Codegen.Templates` | 445 | 78 | 19 | 791, 283 |
| `Effect4.Codegen.Refusal` (new) | — | 454 | 366 | —, 802 |
| `Effect4.Laws.Codegen.ReadLeaf` | 64 | 15 | 14 | — |
| `Effect4.Laws.Codegen.Mask` | 15 | 2 | 1 | — |

Every core codegen module rebuilds under 100 modules except the refusal alphabet. The
alphabet holds three inductive types of plain data; CR-8 edits it once.

### Lines removed and added

819 lines removed and 1015 added, the four new modules' 737 lines among them. The moves are
neutral in lines; the added lines are the new modules' notes and the face's docstrings.

### Evidence

- Proved: the whole tree within `[propext, Quot.sound]` and its boundary (the axiom gate of
  `Test/All.lean`), and the touched modules (`#axiom_audit`).
- Tested: the nine behaviour gates above, against the base's result lines.
- The counts of rebuilt modules are a scan of import lines, not a build.

### Landed theorems and their placement

No new theorem. Each moved declaration keeps its name, statement and placement. The exception
is `repr_inj`, whose namespace is now `Effect4.Data.NatDecimal`. It is an untagged helper of the
binder law `Var.name_inj` and of `mint_depth_inj`.

### Open obligations

- `README.md`, the owner's, says that `Effect4.Api` holds `print`, `printDecl` and the Schema
  syntax. They are `Effect4.Api.Codegen`'s now, which the root `Effect4` imports.

### Proposed decisions rows (proposals only)

- **P-CR0-1.** After the lowering branch merges, the Refusals group of
  `tools/Effect4Gen/manifest.json` imports `Effect4.Api.Codegen` in place of `Effect4.Api`.
  `Effect4.Api` then drops `Effect4.Codegen.Refusal`, and the alphabet rebuilds what the codegen
  face rebuilds, not 454 modules.
