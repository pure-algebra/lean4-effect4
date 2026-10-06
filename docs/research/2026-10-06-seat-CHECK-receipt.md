# 2026-10-06 seat CHECK receipt: the checker tests the references' formation only, and the facade loses its dead arm

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-check-brief.md`, with the dispatch message
and the coordinator's one message during the slice. Design note:
`docs/research/2026-10-06-seat-CHECK-design.md`, with two addenda.

**The one thing to know before merging:** one statement is new, in a file outside the brief's
list. It is the facade's equation `Api.explain_eq_if_refsWF`, in
`src/Effect4/Laws/Api/Codegen.lean`. The brief asks for no new statement. The coordinator asked
for this one during the slice, and the file is the seat's choice (item 10, choice C2).

Seven more facts stand beside it.

- **The two definitions changed in one commit, `5627ef4a`, and no statement changed.** The
  environment of 758 modules holds one changed type: the generated equation
  `typeOfProgram.eq_1`.
- **No program's answer changes**, and no program had a refusal from the dead arm (item 8).
- **The runtime root imports no law.** `Api.explain_none_iff` needs the structural law only.
- **Three files changed that the brief does not name.** `Laws/Api/Codegen.lean` holds the new
  statement. The coordinator asked for the comment in `ReferenceExpansion.lean`. The baseline
  lost two lines by hand. Two more files changed because a proof broke: `Typed/Assembly.lean`
  and `Typed/Commands/Finish.lean`.
- **Two proofs broke that the design note said would hold** (item 10, finding F1).
- **`generated/semantics.md` is not regenerated.** Its two rows of R5's placed nodes stay
  (measured). Other rows are not measured (item 10, finding F6).
- **The merge rebuilds the cone of `Program/Typing.lean`.** Here the builds after the change
  took about 13 minutes at two threads, by the logs' times.

The sections below carry item numbers. Item 1 is the bold line above.

## 2. Base, head and commits

| Item | Value |
| --- | --- |
| Branch | `seat/check`, in the worktree `/Users/pooks/Dev/lean4-effect4-qsteps` |
| Base | `8fcab517` |
| Main-line heads taken in | none |
| Head | the commit that holds this receipt; its parent is `5627ef4a` |

Nothing is pushed.

| Commit | Step | Content |
| --- | --- | --- |
| `649ebab3` | 0 | the design note: the measure, and each proof over the new forms in scratch |
| `a467ce77` | 1 | the facade's equation, proved against the definitions of the base; the note's first addendum |
| `5627ef4a` | 2 | the two definitions, each proof that broke, the comment of `ReferenceExpansion.lean`, the battery, the baseline's two lines; the note's second addendum |
| the head | 3 | this receipt |

## 3. Changed files

`git diff --stat 8fcab517..5627ef4a` lists 12 files. This receipt is the thirteenth.

| Group | File | What changed |
| --- | --- | --- |
| The runtime root | `src/Effect4/Program/Typing.lean` | `typeOfProgram` tests the references' formation only; its comment |
| The runtime root | `src/Effect4/Api.lean` | `Api.explain` without the arm for a kept site; the proof of `Api.explain_none_iff`; two comments. No import changed |
| The laws | `src/Effect4/Laws/Program/ReferenceTyping.lean` | `typeOfProgram_eq_if_refsWF` is `rfl`; two comments |
| The laws | `src/Effect4/Laws/Program/CheckedTyping.lean` | three proofs: `TypedProgram.layerRefsWF`, `TypedProgram.expanded_refSites`, `TypedProgram.hasTy`; four comments |
| The laws | `src/Effect4/Laws/Program/TypedRun.lean` | the proof of `typeOfProgram_looped`, and its comment |
| The laws | `src/Effect4/Laws/Program/Typed/Assembly.lean` | two proofs: `layerRefsWF_of_typeOf`, `load_typed_of_denotesTyped`; one comment, which loses a line citation |
| The laws | `src/Effect4/Laws/Program/Typed/Commands/Finish.lean` | the proof of `load_typed_of_denotesTyped_typed` |
| The laws | `src/Effect4/Laws/Api/Codegen.lean` | new: `Api.explain_eq_if_refsWF` |
| The laws | `src/Effect4/Laws/Program/ReferenceExpansion.lean` | the header's line of consumers; a comment only |
| The batteries | `Test/Program/ReferenceExpansion.lean` | one import; a tenth program; 15 guards and 6 examples more; two pinned axiom outputs more; the pinned plan status, at six statements |
| The fixture | `Test/fixtures/proof-style/baseline.tsv` | two lines removed, by a script that names each |
| The notes | `docs/research/2026-10-06-seat-CHECK-design.md`, and this receipt | new |

Not edited, though the brief gives them: `src/Effect4/Laws/Program/Signature.lean`, whose proof
holds, and `Test/Program/LayerRefs.lean`, whose facts are kernel evaluations of the same answers.

I edited none of the coordinator's files: `docs/core/decisions.md`, `docs/STATE.md`,
`lakefile.toml`, `generated/semantics.md`, `docs/core/semantics.md` and
`tools/Tools/SemanticsRegistry.lean`. I removed no constructor.

## 4. Commands and results

Each Lean, Lake or `make` command ran through
`/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`, named `SLOT` below. Each `make` took the
flags `-o build -o ts/eff/node_modules -o harness/truth/node_modules`, named `FLAGS`. A scratch
file ran as `SLOT lake env lean -M6144 -DwarningAsError=true FILE`, named `LEAN FILE`. The
scratch folder is
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/acf2315e-02ac-4acd-9ef9-b0734bd686a7/scratchpad/check/`,
named `SCRATCH`. It holds each log and each probe.

| Command | Result | Evidence |
| --- | --- | --- |
| `SLOT lake build`, on the base | `Build completed successfully (1008 jobs)`; Lake restored each output | tested |
| `LEAN Test/All.lean` and `LEAN Test/Audit/ProofStyle.lean`, on the base | the base's row of the gates' table below | tested |
| `LEAN SCRATCH/probe-api.lean`, `probe-laws.lean`, `probe-axioms.lean`, `answers.lean`, `answers2.lean`, on the base | exit 0, each | tested: the design note's probes |
| `SLOT lake build Effect4.Laws.Api.Codegen`, then `SLOT lake build`, on the tree of `a467ce77` | `Build completed successfully (342 jobs)`; then 1008 jobs, with the gates | proved: step 1 |
| `LEAN SCRATCH/battery-before.lean`, against the build of `a467ce77` | exit 0: each new check of the battery states an answer of the tree before the change | tested |
| `SLOT lake build M`, for seven modules after the change | each `Build completed successfully`: `Effect4.Program.Typing`, `Effect4.Laws.Program.ReferenceTyping`, `Effect4.Laws.Program.CheckedTyping`, `Effect4.Api`, `Effect4.Laws.Api.Codegen`, `Effect4.Laws.Program.Signature`, `Effect4.Laws.Program.TypedRun` | proved |
| `SLOT lake build Test.Program.ReferenceExpansion` | `Build completed successfully (345 jobs)` | tested |
| `SLOT lake build`, the first run after the change | exit 1, one error: `src/Effect4/Laws/Program/Typed/Assembly.lean`, in `load_typed_of_denotesTyped` (finding F1) | reproduced: `SCRATCH/probe-split.lean` |
| `SLOT lake build Effect4.Laws.Program.Typed.Commands.Finish`, after the repair | `Build completed successfully (444 jobs)` | proved |
| `SLOT lake build`, the second run | `Build completed successfully (1008 jobs)`, with the gates | proved, and tested |
| `SLOT lake build`, on the tree of `5627ef4a` | `Build completed successfully (1008 jobs)`; Lake built no module | tested |
| `LEAN SCRATCH/checks.lean`, before and after; `cmp` of the two outputs | identical: the types of 27 declarations, and 14 axiom lines (item 5) | tested |
| `LEAN SCRATCH/envdump.lean`, on the base, on `a467ce77` and after; `python3 SCRATCH/envdiff.py` | item 6 | tested |
| `LEAN SCRATCH/plan.lean`, before and after | item 7 | tested |
| `SLOT SCRATCH/red-one/run.sh SCRATCH`: 24 copies of the battery, one falsified check in each | each copy exits 1; 23 give one error, and one gives two | tested: the red controls |
| `LEAN SCRATCH/battery-green.lean`, a copy equal to the battery by `cmp` | exit 0, and no message | tested |
| `SLOT make FLAGS gen-fixtures` | `PASS generate: requested producers ran in dependency order`; exit 0 | reproduced |
| `SLOT make FLAGS corpus` | `kept 408 (readable 385) refused 0 (dir .lake/corpus, depth 4, generated 400, wire corpus 8)`; exit 0 | reproduced |
| `git status --short -- generated ocaml ts harness`, after both | no line: no generated file moves | reproduced |
| `opam exec --switch=effect4 -- dune build`, in `ocaml/` | exit 0 | tested |
| `opam exec --switch=effect4 -- dune test --force engine`, in `ocaml/`, with `E4_LEAN_CORPUS` at the worktree's `.lake/corpus` | exit 0; `ALL PASS` 28 times, and no `FAIL` line; the Lean lane prints `0 divergences` | tested |
| `SLOT make FLAGS check-cases` | `conform cases: PASS, exit 0; .lake/conform/cases.json`; the report says 231 rows, 231 pass, 0 refused | tested |
| `SLOT make FLAGS check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` | tested |
| `python3 scripts/check-language.py --strict` on the design note and on this receipt | `PASS check-language: no finding`, for each | tested |

The engine's test read one corpus folder, and it prints the folder:
`/Users/pooks/Dev/lean4-effect4-qsteps/.lake/corpus: 408 files, 408 decoded`. `make corpus` wrote
that folder in this slice, after the change. The test's cross face reports `agree=9 differ=2`.
Earlier receipts record the same line, and the test does not gate on it.

The default builds, with the gate lines that `Test/All.lean` prints:

| Tree | Jobs | API and Laws-only modules | Modules, declarations | Planned goals, declarations on goals | Proof style: uses, unread, entries |
| --- | --- | --- | --- | --- | --- |
| the base `8fcab517` | 1008 | 175, 310 | 758, 88976 | 24, 11 | 1914, 52, 1163 |
| `a467ce77` | 1008 | 175, 310 | 758, 88977 | 24, 11 | 1914, 52, 1163 |
| `5627ef4a` | 1008 | 175, 310 | 758, 88975 | 24, 11 | 1911, 52, 1161 |

On each run the library-root gate reports that every library source is reachable, and that
`Effect4` never reaches Laws. The axiom gate reports the semantic and test axioms at
`[propext, Quot.sound]`. The goal gate reports that no other declaration reaches `sorryAx`. The
proof-style gate refuses nothing.

### The acceptance, item by item

| Item of the brief | Result |
| --- | --- |
| 1. The default build passes with the gate lines; no kept statement changed | yes: the table above, and item 5 |
| 2. `make gen-fixtures` and `make corpus` move no generated file; `dune build` and `dune test --force engine` pass | yes; the test read the worktree's `.lake/corpus` |
| 3. `make check-cases` and `make check-docs` | both pass |
| 4. The commands that the coordinator runs | not run: the list below |

### Not run

- `make check-gen`, `make check-slow`, `make check-corpus`, `make check-target`,
  `make check-truth`, the conservativity script and `make gen-semantics`.
- `make record-proof-style`: I removed the two lines by a script that names each.
- `make gen-lcnf`: no LCNF root reaches either definition (the design note, section 3).
- `make check`, `make check-full` and `make status`, as targets.
- Every TypeScript lane and every host run. No package was installed.

### Red or stale for a reason outside the slice

Nothing that I ran is red for such a reason. One run was red inside the slice: the first
default build after the change (finding F1).

## 5. Each kept statement's `#check`

`SCRATCH/checks.lean` prints the statements below with full names. The output before is of the
build of `a467ce77`, and the output after is of `5627ef4a`. `cmp` finds the two outputs equal,
so the block stands for both. The base holds the same types: its dump differs from the dump of
`a467ce77` by one added declaration, the facade's equation, and by no type.

```text
Effect4.Api.explain_none_iff : ∀ (program : Effect4.Api.Program) (table : Effect4.Program.RowTable),
  Effect4.Api.explain program table = Option.none ↔ Effect4.Api.wellTyped program table = Bool.true
Effect4.Api.blame_none_iff : ∀ (program : Effect4.Api.Program) (table : Effect4.Program.RowTable),
  Effect4.Api.blame program table = Option.none ↔ Effect4.Api.wellTyped program table = Bool.true
@Effect4.Api.explain : Effect4.Api.Program → optParam Effect4.Program.RowTable [] → Option Effect4.Program.TypeRefusal
@Effect4.Api.blame : Effect4.Api.Program → optParam Effect4.Program.RowTable [] → Option (List Nat)
@Effect4.Api.check : Effect4.Api.Program →
  (table : optParam Effect4.Program.RowTable []) → Except Effect4.Program.TypeRefusal (Effect4.Api.Typed table)
@Effect4.Program.typeOfProgram : {Op : Type} →
  Effect4.Program.Signature Op → Effect4.Program.Eff Op → Option Effect4.Program.EffTy
@Effect4.Program.typeOfProgram_eq_if_refsWF : ∀ {Op : Type} (sig : Effect4.Program.Signature Op)
  (p : Effect4.Program.Eff Op),
  Effect4.Program.typeOfProgram sig p =
    if p.layerRefsWF = Bool.true then Effect4.Program.typeOf sig p.expandRefs else Option.none
Effect4.Api.explain_eq_if_refsWF : ∀ (program : Effect4.Api.Program) (table : Effect4.Program.RowTable),
  Effect4.Api.explain program table =
    if Effect4.Program.Eff.layerRefsWF program = Bool.true then
      Effect4.Program.explain (Effect4.Program.nativeSignature table) [] (Effect4.Program.Eff.expandRefs program)
    else Option.some { path := [], reason := Effect4.Program.TypeReason.referencesIllFormed }
@Effect4.Program.typeOfProgram_expandRefs : ∀ {Op : Type} (sig : Effect4.Program.Signature Op)
  (p : Effect4.Program.Eff Op),
  p.layerRefsWF = Bool.true → Effect4.Program.typeOfProgram sig p.expandRefs = Effect4.Program.typeOfProgram sig p
@Effect4.Program.checkTypedProgram_type : ∀ {Op : Type} (sig : Effect4.Program.Signature Op)
  (program : Effect4.Program.Eff Op),
  Option.map Effect4.Program.TypedProgram.ty (Effect4.Program.checkTypedProgram sig program) =
    Effect4.Program.typeOfProgram sig program
@Effect4.Program.checkTypedProgram_sound : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op} {checked : Effect4.Program.TypedProgram sig program},
  Effect4.Program.checkTypedProgram sig program = Option.some checked →
    Effect4.Program.typeOfProgram sig program = Option.some checked.ty
@Effect4.Program.TypedProgram.type_unique : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op} (left right : Effect4.Program.TypedProgram sig program), left.ty = right.ty
@Effect4.Program.TypedProgram.unique : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op} (left right : Effect4.Program.TypedProgram sig program), left = right
@Effect4.Program.checkTypedProgram_eq_some : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op} (checked : Effect4.Program.TypedProgram sig program),
  Effect4.Program.checkTypedProgram sig program = Option.some checked
@Effect4.Program.checkTypedProgram_complete : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op} {ty : Effect4.Program.EffTy},
  Effect4.Program.typeOfProgram sig program = Option.some ty →
    ∃ checked, Effect4.Program.checkTypedProgram sig program = Option.some checked ∧ checked.ty = ty
@Effect4.Program.checkTypedProgram_refusal_iff : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op},
  Effect4.Program.checkTypedProgram sig program = Option.none ↔ Effect4.Program.typeOfProgram sig program = Option.none
@Effect4.Program.TypedProgram.layerRefsWF : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op} (checked : Effect4.Program.TypedProgram sig program),
  program.layerRefsWF = Bool.true
@Effect4.Program.TypedProgram.expanded_refSites : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op} (checked : Effect4.Program.TypedProgram sig program),
  Effect4.Program.Eff.refSites [] program.expandRefs = []
@Effect4.Program.TypedProgram.hasTy : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op} (checked : Effect4.Program.TypedProgram sig program),
  Conform.Effect4.Typing.HasTy sig [] program.expandRefs checked.ty
@Effect4.Program.checkTypedProgram_of_hasTy : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op} {ty : Effect4.Program.EffTy},
  program.layerRefsWF = Bool.true →
    Conform.Effect4.Typing.HasTy sig [] program.expandRefs ty →
      ∃ checked, Effect4.Program.checkTypedProgram sig program = Option.some checked ∧ checked.ty = ty
@Effect4.Program.admitProgram_eq_ok : ∀ {program : Effect4.Program.NativeEff} {app : Effect4.Program.SigApp}
  (admitted : Effect4.Program.AdmittedProgram program app),
  Effect4.Program.admitProgram program app = Except.ok admitted
@Effect4.Program.typeOfProgram_ext : ∀ {Op : Type} {s s' : Effect4.Program.Signature Op},
  Effect4.Program.SigExtends s s' →
    ∀ {e : Effect4.Program.Eff Op} {t : Effect4.Program.EffTy},
      Effect4.Program.typeOfProgram s e = Option.some t → Effect4.Program.typeOfProgram s' e = Option.some t
Effect4.Program.Denote.typeOfProgram_looped : ∀ (sig : Effect4.Program.Signature Effect4.Program.NativeOp)
  (e : Effect4.Program.NativeEff),
  Effect4.Program.Denote.Looped e = Bool.true → Effect4.Program.typeOfProgram sig e = Effect4.Program.effTy sig [] e
@Effect4.Program.Typed.layerRefsWF_of_typeOf : ∀ {Op : Type} {sig : Effect4.Program.Signature Op}
  {program : Effect4.Program.Eff Op} {ty : Effect4.Program.EffTy},
  Effect4.Program.typeOfProgram sig program = Option.some ty → program.layerRefsWF = Bool.true
Effect4.Program.Typed.load_typed_of_denotesTyped : ∀ (root : Effect4.Program.Typed.ProgramSource)
  (rootTy : Effect4.Program.EffTy) (fuel compileFuel : Nat),
  Effect4.Program.Typed.DenotesTyped root →
    Effect4.Program.Typed.raceRegistrationR
          (Effect4.Program.Sched.denoteR root.program root.program (Effect4.Program.rootPoint compileFuel)) =
        Option.none →
      Effect4.Program.typeOfProgram root.signature root.program = Option.some rootTy →
        ∃ w,
          Effect4.Program.Typed.MachineTyped root rootTy w (Effect4.Program.Sched.loadR root.program fuel compileFuel)
Effect4.Program.Typed.load_typed_of_denotesTyped_typed : ∀ (root : Effect4.Program.Typed.ProgramSource)
  (rootTy : Effect4.Program.EffTy) (fuel compileFuel : Nat),
  Effect4.Program.Typed.DenotesTyped root →
    Effect4.Program.typeOfProgram root.signature root.program = Option.some rootTy →
      ∃ w, Effect4.Program.Typed.MachineTyped root rootTy w (Effect4.Program.Sched.loadR root.program fuel compileFuel)
@Effect4.Program.expanded_refs_nil_of_wf : ∀ {Op : Type} (root : Effect4.Program.Eff Op),
  root.layerRefsWF = Bool.true → Effect4.Program.Eff.refSites [] root.expandRefs = []
```

## 6. Each proof that moved or changed

No proof moved to another file. The dumps of `SCRATCH/envdump.lean` compare the base with
`5627ef4a`, by declaration name, over every `Effect4.*` and `Test.*` module.

| Measure | Count | Which |
| --- | --- | --- |
| declarations | 88976, then 88975 | 758 modules, the counts of the axiom gate |
| a changed type | 1 | `typeOfProgram.eq_1`, the definition's generated equation. Its type hash is now that of `typeOfProgram_eq_if_refsWF` |
| added | 4 | `Api.explain_eq_if_refsWF`; two matchers of the new proof of `Api.explain_none_iff`; the battery's `refusedBody` |
| removed | 5 | the matcher `Api.explain.match_1` with its two equations and its splitter; one `simp` helper of the old proof of `Api.explain_none_iff` |
| a changed value under a kept type | 18 | the 2 definitions, 10 theorems and 6 battery proofs, below |

The ten theorems, and the eleventh declaration, which is new:

| Declaration | File | The proof now |
| --- | --- | --- |
| `Api.explain_none_iff` | `src/Effect4/Api.lean` | cases on the one test; the structural `Program.explain_none_iff` at the expansion; `nofun` twice where the test fails |
| `typeOfProgram_eq_if_refsWF` | `src/Effect4/Laws/Program/ReferenceTyping.lean` | `rfl` |
| `TypedProgram.layerRefsWF` | `src/Effect4/Laws/Program/CheckedTyping.lean` | the hypothesis of the `split` is the fact |
| `TypedProgram.expanded_refSites` | the same file | `expanded_refs_nil_of_wf` at `TypedProgram.layerRefsWF` |
| `TypedProgram.hasTy` | the same file | a rewrite by the equation and `if_pos`; no `simpa` |
| `typeOfProgram_looped` | `src/Effect4/Laws/Program/TypedRun.lean` | a rewrite by the equation, `if_pos` and the fixed expansion; no `simp` |
| `layerRefsWF_of_typeOf` | `src/Effect4/Laws/Program/Typed/Assembly.lean` | the hypothesis of the `split` is the fact |
| `load_typed_of_denotesTyped` | the same file | a rewrite by the equation and `if_pos`; no `split` |
| `load_typed_of_denotesTyped_typed` | `src/Effect4/Laws/Program/Typed/Commands/Finish.lean` | the same rewrite |
| `typeOfProgram_ext` | `src/Effect4/Laws/Program/Signature.lean` | the script is unchanged; its term unfolds the new definition |
| `Api.explain_eq_if_refsWF` | `src/Effect4/Laws/Api/Codegen.lean` | new at `a467ce77`, from `expanded_refs_nil_of_wf`; `rfl` at `5627ef4a` |

The six battery proofs are the field `typed` of a certificate, proved by `cbv`, in
`Test/Api/HostSessionContract.lean`, `Test/Api/KeyedHostContract.lean` and
`Test/Run/RunContract.lean`. `cbv` evaluates through the definition's equation, so each term is
new. Each answer is the same, and each proof passes with its text unchanged.

`typeOfProgram_expandRefs`, `checkTypedProgram_of_hasTy` and `Api.blame_none_iff` keep their
proof terms: the dump finds no change in them.

## 7. What the proof-style baseline loses, and the pinned plan status

`Test/fixtures/proof-style/baseline.tsv` loses two lines.

```text
src/Effect4/Api.lean	explain_none_iff	simp_all	2
src/Effect4/Laws/Program/TypedRun.lean	typeOfProgram_looped	simp-without-only	1
```

The gate's count of uses falls by 3 and its count of entries by 2 (item 4's table). The
coordinator confirms with `make record-proof-style` at the merge.

The plan status of the six statements that the battery pins, after the change:

```text
Effect4.Program.expanded_refs_nil_of_wf: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Program.typeOfProgram_eq_if_refsWF: proved; nearest []; 0 lemmas, 0 definitions
Effect4.Program.typeOfProgram_expandRefs: proved; nearest [Effect4.Program.typeOfProgram_eq_if_refsWF, Effect4.Program.expanded_refs_nil_of_wf]; 0 lemmas, 0 definitions
Effect4.Program.checkTypedProgram_of_hasTy: proved; nearest [Effect4.Program.typeOfProgram_eq_if_refsWF]; 0 lemmas, 0 definitions
Effect4.Program.TypedProgram.expanded_refSites: proved; nearest [Effect4.Program.expanded_refs_nil_of_wf]; 0 lemmas, 0 definitions
Effect4.Api.explain_eq_if_refsWF: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
```

Against the build of `a467ce77`, three lines differ. Two edges left, and one arrived.

- **Left:** `typeOfProgram_eq_if_refsWF` to `expanded_refs_nil_of_wf`. The equation is the
  definition's own.
- **Left:** `Api.explain_eq_if_refsWF` to `expanded_refs_nil_of_wf`. That edge was in the tree
  at `a467ce77` only.
- **Arrived:** `TypedProgram.expanded_refSites` to `expanded_refs_nil_of_wf`. Before, the
  certificate read the checker's second test, and it rested on no node.

No pinned `#print axioms` output moved. Each of the six prints `[propext, Quot.sound]`.

## 8. Evidence: what is proved, and what is only tested

| Claim | Evidence |
| --- | --- |
| The checker answers the structural type of the expansion exactly where the references are well formed | proved: `typeOfProgram_eq_if_refsWF`, by definition |
| The old `typeOfProgram` gave the same answer at every typing signature and program | proved in the tree of the base: the same statement, from `expanded_refs_nil_of_wf` |
| The old `Api.explain` gave the same refusal at every program and row table | proved in the tree of `a467ce77`: `Api.explain_eq_if_refsWF`, from `expanded_refs_nil_of_wf` |
| No program has a refusal that came from the dead arm | proved: `expanded_refs_nil_of_wf` (`src/Effect4/Laws/Program/ReferenceExpansion.lean`); an `example` of the battery states it at the lost arm's condition. The battery pins no such program, because none exists |
| The facade's refusal is `none` exactly where the program is well typed | proved: `Api.explain_none_iff`, with the imports of the runtime root |
| A certificate's expansion has no reference site | proved: `TypedProgram.expanded_refSites`, from `expanded_refs_nil_of_wf` |
| No statement of the tree changed, except the definition's generated equation | tested: the dumps, by a 32-bit hash of each type; and the `#check` of 27 declarations, by text |
| The nine programs type or refuse as before, and the facade gives each the same refusal | tested: the battery's guards, which pass against the build before the change too |
| The facade answers the structural refusal of the expansion, past a reference site | tested at one program: `refusedBody` |
| `TypeReason.layerReference` keeps a producer | tested at one program: the structural refusal of `refusedBody` as written |
| The corpus keeps each answer | reproduced: `generated/corpus-index.tsv` holds `Api.wellTyped` and the refusal of 408 programs, and it did not move |
| The engine's fixtures keep their bytes | reproduced: `make gen-fixtures` installs the writers' output, and no fixture moved |

No evidence of the slice is host-only, and no host ran. Each guard of the battery is bounded:
one program each. The corpus is bounded: 408 programs. The theorems hold at every program.
`typeOfProgram_eq_if_refsWF` and `TypedProgram.expanded_refSites` hold at every operation alphabet
and typing signature. The facade's two hold at the native signature, with every row table.

## 9. The landed theorem's placement

**`Api.explain_eq_if_refsWF`** (`src/Effect4/Laws/Api/Codegen.lean`), untagged, as its twin
`typeOfProgram_eq_if_refsWF` is:

- Concept: `initial-algebras-folds`; property: the reference expansion leaves no reference,
  read at the facade's refusal.
- Question: a step under the claim `reference-expansion-complete`, whose pointer stays
  `expanded_refs_nil_of_wf`. Consumer: no proof in the tree. The coordinator asked for it as the
  record that the facade may lose its arm.
- Reach: the native typing signature at every row table, and every program. It has no premise.
- Does not establish: that a refusal is right, any typing success, or any fact about a run. At
  `5627ef4a` it is the definition's own equation, and it states no fact about the old form.
- Unlocks: nothing on the M5 to M7 spine. It serves R5.

No other statement is new. The ten theorems of item 6 keep their statements and their
placements. No claim's status moves, and no requirement closes.

## 10. Choices, findings and proposals

### Choices

- **C1. The facade's equation landed before the definitions changed.** Its right side is the
  new form, so the tree never holds a copy of the old definition. Seat REFS took the same route
  for the checker's equation.
- **C2. Its file is `src/Effect4/Laws/Api/Codegen.lean`.** The coordinator's message says
  "beside the equation". The equation's file holds laws at every operation alphabet, and it
  does not import the facade. An import there puts `Effect4.Api` under that file and under 5
  law modules that do not reach it today (`SCRATCH/closure.py`). `Laws/Api/Codegen.lean` imports
  the facade and reaches the expansion theorem already. Moving the theorem is a small edit, if
  the coordinator wants the other file.
- **C3. The battery imports `Effect4.Laws.Api.Codegen`.** It needs the facade for the controls
  that the brief asks, and the law module for the equation's pin.
- **C4. No copy of an old definition is in the tree.** The battery states that no program is
  at the lost arm, as an `example` from the expansion theorem. It holds no old form.
- **C5. The red controls are guards beside the checks, and falsified copies in scratch.** Four
  guards state that a different value is not the answer. Each of 24 falsified copies fails.
- **C6. `Test/Program/LayerRefs.lean` is not edited.** Its comment cites `typeOfProgram` by a
  line range that is wrong at the base too (proposal P3).

### Findings

- **F1. `split` reads an `if`'s condition from the context.** The two load theorems first take
  the formation fact from the checker's answer. After the change the checker's `if` tests that
  fact and no other. `split` then rewrites the `if` to its `then` branch in both cases, and the
  second case holds no refuted equation. The design note's probe stated the inner step without
  that context, so it passed. `SCRATCH/probe-split.lean` reproduces the mechanism in three
  examples. Both proofs now rewrite by the equation.
- **F2. The measure found three proofs beyond the list of seat REFS's proposal P4**:
  `layerRefsWF_of_typeOf` and the two load theorems. Ten declarations unfold `typeOfProgram`,
  and one of the ten unfolds `Api.explain` too.
- **F3. A `cbv` proof's term changes with a definition that it evaluates.** Six battery proofs
  changed so, and each passes (item 6). A `decide +kernel` proof's term does not change.
- **F4. The definition's generated equation now has the type of `typeOfProgram_eq_if_refsWF`**,
  by the dump's hash. The kept statement is the definition's own equation in that exact sense.
- **F5. An instance at a closed program reads one branch.** The battery applies the facade's
  equation at `refusedBody`. A falsified `else` branch there passes, because the kernel
  evaluates the test. The statement's pin by type holds both branches, and its falsified copy
  fails.
- **F6. `generated/semantics.md` may be stale, in rows that I did not measure.** The plan
  gives R5's two placed nodes the report's own counts after the change: 19 lemmas and 106
  definitions, and 57 and 322 (`SCRATCH/plan-effect4.lean`). Four proofs now use
  `typeOfProgram_eq_if_refsWF` that did not before: `TypedProgram.hasTy`, `typeOfProgram_looped`
  and the two load theorems. So a node above one of them may count one lemma more.
- **F7. On two refused programs the structural refusal is the lost arm's answer.** The
  expansions of `insideTarget` and `missing` keep a site. The structural checker refuses each
  at that site with `layerReference` (tested, a finite probe). The formation test refuses both
  programs first, so the facade never answers so.
- **F8. Two comments cite `typeOfProgram` by a line range that is wrong at the base**, in
  `src/Effect4/Laws/Program/DenoteR.lean` and in `Test/Program/LayerRefs.lean`. The third such
  comment was in `Typed/Assembly.lean`, at a proof that I changed, and it now cites the name.

### Proposals (not rulings)

- **P1. The sentence of `docs/core/semantics.md`**, in the required property
  `reference-expansion-complete`. One sentence there says that the checker's second test
  follows from its first. Replace that sentence, with its citation, by the text below.

  ```text
  So the whole-program checker tests the references' formation only (`typeOfProgram`,
  `src/Effect4/Program/Typing.lean`), and the facade's refusal has no arm for a kept reference
  site (`Api.explain`, `src/Effect4/Api.lean`). Each equation is its definition's own
  (`typeOfProgram_eq_if_refsWF`, `src/Effect4/Laws/Program/ReferenceTyping.lean`;
  `Api.explain_eq_if_refsWF`, `src/Effect4/Laws/Api/Codegen.lean`).
  ```
- **P2. Run `make gen-semantics` at the merge**, and read its diff (finding F6).
- **P3. Cite `typeOfProgram` by name in the two comments of finding F8.** A comment edit of
  `DenoteR.lean` rebuilds the typed state's graph, so it fits a slice that rebuilds it already.
- **P4. `docs/STATE.md`**: seat CHECK's line moves from the open seats to the merged ones.

## 11. Open obligations

None of the brief's assignment. No planned goal is new, and none of the 24 moved.

## 12. Proposed decisions rows (proposals only)

No new row. One status, for row 273:

| Topic | Proposal |
| --- | --- |
| Row 273, point 2 | landed with seat CHECK's merge (`5627ef4a`): `typeOfProgram` tests the references' formation only, and `Api.explain` has no arm for a kept reference site. Ten declarations unfold the checker, three more than proposal P4 listed: nine proofs changed, and `typeOfProgram_ext` kept its script. Both equations are their definitions' own. The facade's equation `Api.explain_eq_if_refsWF` is new, and its proof at `a467ce77` records that no refusal changed |
