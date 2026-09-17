# Scout E — cleanup, proof organization, low-hanging fruit around the recent changes

Date 2026-09-17. Branch `refactor/phase1-phase3`. Read at `5185a6cd` (the DI-91/DI-92 slice,
which the coordinator committed while this scout was running; every line number below is against
that commit). Research only: no tracked file was edited, no build, no generator, no git write.

Evidence words used exactly: **read** (I opened the source), **compiled** (I built a scratch file
under the scoutE scratchpad with `lake env lean` and quote its output), **measured** (a script over
the tree, quoted), **inferred** (a conclusion from the two, marked as such). Nothing here is
*proved* or *tested* in this repo's sense: I ran no gate.

Ranking inside each group is by (lines removed × how often a future alphabet change touches the
place) ÷ risk.

---

## 0. Where the brief is wrong against the tree

Four corrections, each measured.

1. **`tools/Conform/Effect4/cases-policy.json` is clean.** The stale file is its twin,
   `tools/Conform/Effect4/cases-policy-complete.json`, which names all four retired constructors
   in 18 `cover` lists. Detail in §D-1.
2. **`Prim.yieldableError` and `CodeMeans.yieldError` are not leftovers of the `yieldError`
   retirement.** `Prim` is the *machine* alphabet, not `Eff`. It models the rc.112 `YieldableError`
   primitive and it is a green census row (`Test/Audit/RuntimeCoverage.lean:100-104`,
   `op.YieldableError`, witnesses `FrameFiber.step_yieldableError` and
   `Prim.yieldableError_host_class_refused`). Deleting it would cost that row and 21 sites in
   `src/Effect4/Machine/Frames.lean`. **Keep.** What is true, and worth recording, is in §D-6.
3. **`Head.whileLoop` is correctly named.** `Head` is the table of *printed TypeScript heads*
   (`src/Effect4/Codegen/Print.lean:53-71`); `iterate` prints `Effect.whileLoop` mapped by
   `Effect.map`. The list is guarded: `heads_complete` (`Codegen/Read.lean:111`) is
   `cases h <;> decide`, so an omitted head fails the build. This is the *good* precedent the
   `Eff.arms` table lacks (§D-2).
4. **`ts/eff/read.ts`, `ts/eff/ingest/{ck,oxc}.ts` and `fixtures/refusals/e-loop.ts` have no
   leftovers.** Every `Effect.whileLoop` / `Effect.callback` there is the *Effect TypeScript*
   export, not the retired `Eff` constructor: `read.ts:1207` refuses a bare `Effect.whileLoop`
   head (which is what R5 owes), `ck.ts:940` / `oxc.ts:708` reject `E-LOOP`, `oxc.ts:707` /
   `ck.ts:939` reject `Effect.callback` as a closure argument. `ts/eff/read.ts:592` and `:1022`
   already record the retirements in the past tense. Nothing to do on the TypeScript face.

A fifth item the brief asked me to check and I could not find: **the explicit-tactic rule is not
written in any tracked file.** I grepped `AGENTS.md`, `docs/*.md` (`ARCHITECTURE`, `DESIGN-BASIS`,
`DESIGN-MAP`, `DESIGN-ISSUES`, `STATE`, `GENERATED`, `RUNTIME-COVERAGE`, `SCHEMA-ANNOTATIONS`) and
the `Intro/*` and `Handles/*` module headers for `simp_all`, `first`, `try`, "explicit tactic".
No hit. The rule lives only in the session's memory. **Measured** state of the two trees:

| tactic | `Laws/Program/Intro/*` + `Laws/Program/Handles/*` | all of `src/Effect4/Laws` |
| --- | --- | --- |
| `simp_all` | 0 | 231 |
| `first \| …` | 0 | 88 |
| `try …` | 0 | 255 |
| bare `simp [...]` (no `only`) | **13** | 790 |

So the rule as remembered ("no `first`, `try`, `simp_all`") is held exactly; the stronger reading
("`simp only` everywhere") is not. The 13 bare `simp`s are listed in §A-9. Recommendation in §C-5:
write the rule down, at the strength the owner wants, in `AGENTS.md` under **Working**.

---

## A. Safe today — one commit, no proof changes

Every item here I verified by grep or by a compiled probe. Total: **≈ 36 lines removed, 13 comment
or docstring lines corrected, 2 lines added, and one known-red gate fixture turned green.**

### A-1. `Test/fixtures/trust-gate/expr-equality.lean.txt` — the one-line repair (compiled)

The known red that stops `make check-tools` (STATE.md, "Known red, older than S1").
**Compiled** the fixture as-is: three `Application type mismatch` errors, `String` supplied where
the pinned package wants `TypeScript.TypeRef` (`.lake/packages/typescript/TypeScript/Syntax.lean:58`
`arrow (returnType : Option TypeRef)` and `:61` `generic (fn : Expr) (typeArgs : List TypeRef)`).

Edit — insert one line after `namespace ExprEqualityTrustRegression`:

```lean
/-- A bare name as a target type: the fixture writes type arguments as names. -/
private instance : Coe String TypeScript.TypeRef := ⟨fun s => .name [s] []⟩
```

**Compiled** with that line and nothing else changed:

```
PASS finite Expr equality probes: all constructors, nested values, field order, and float bits
PASS Expr module declarations have total safe definitions or compiler companions of them
```

Lines: +2. Risk: none to the library (the fixture is a `.txt` run by
`scripts/test-trust-gate.sh:377`). Gate: `make check-tools`. Caveat: I checked only that *this*
fixture now compiles; whether `check-tools` is green end to end after it I did not run.

### A-2. `src/Effect4/Api.lean:152-153` and `:378-383` — two false statements about `callback`

`readable`'s `perform` arm is now unconditional (`src/Effect4/Codegen/Read.lean:774`,
`| .perform op request => sig.dom op && requestReadable (sig.rowOf op) n request`): the row's
kind is not consulted, and `callback` does not exist. **Compiled** against `Effect4.Api`:

```
#eval Api.readable Effect4.Program.Wire.Corpus.pAwait                     -- true
#eval (Api.roundTrip Wire.Corpus.pAwait).toOption == some Wire.Corpus.pAwait  -- true
#eval (Api.check Wire.Corpus.pAwait).toOption.isSome                      -- true
```

So both sentences are wrong:

- `Api.lean:152-153` — old: `` what it loses is documented on `Effect4.Program.readable` (a
  `perform` on an async row reads back as `callback`) ``.
  New, from `readable`'s own arms (**read**, `Codegen/Read.lean:767-808`): `` what it loses is
  documented on `Effect4.Program.readable` (a loop and the two non-Boolean decisions, until R5
  reads them; the internal fiber actions; a `daemon` on a scoped fork) ``.
- `src/Effect4/Codegen/Read.lean:768-770`, the docstring of `readable` itself, carries the same
  staleness one level down: `` rows performed on the kind their row declares ``. **Read**:
  `requestReadable` (`:747-761`) switches on `row.shape`, and the `perform` arm (`:774`) does not
  mention `kind` at all — the kind test left with `callback`. Edit: drop that clause and add
  `` no loop and no `optionCase`/`caseTag` decision (R5) ``, which is what the arms at `:788-796`
  now say.
- `Api.lean:378-383` — the paragraph justifying why `readable` is **not** a field of
  `AdmittedProgram` rests entirely on `` the historical wire program `Wire.Corpus.pAwait` is typed
  and runs, and is not readable (it spells `perform` on an async row, which the reader
  canonicalises to `callback`) ``. `pAwait` *is* readable now, and round-trips to itself. The
  parenthetical is false and the example no longer supports the conclusion.

The wording fix is (A); whether the *decision* still stands needs a fresh witness or the owner —
see §C-1. Lines: 5 changed. Risk: none (docstrings only). Gate: `make check`.

### A-3. `Test/Program/InvocationContract.lean` — 18 duplicated guards and two `x = x` theorems

`callback` retired into `perform`, and the two fixtures that were the two spellings became the
same definition, character for character:

```
:89  def performSleep    : Api.Program := .perform .sleep (.lit (.nat 1))
:90  def callbackSleep   : Api.Program := .perform .sleep (.lit (.nat 1))
:125 def performExternal : Api.Program := .perform (.external 0) (.lit (.nat 7))
:126 def callbackExternal: Api.Program := .perform (.external 0) (.lit (.nat 7))
```

**Measured** (a script that collapses the two spellings and looks for equal statements): 18 pairs
of `#guard`s now check the same fact.

```
:94/:95   :96/:102  :97/:105  :99/:106  :103/:104   (sleep)
:130/:131 :132/:137 :138/:139 :140/:141 :142/:143 :144/:169
:225/:227 :232/:233 :247/:248 :269/:271 :273/:274 :275/:278 :276/:279
```

`:99` and `:106` are the *same literal guard written twice*, independent of the retirement.

Two theorems are now `x = x`:

- `:101` `theorem sleep_print_same : Api.print performSleep = Api.print callbackSleep := rfl`
- `:148-152` `theorem replay_perform_external_eq_callback : Api.replay performExternal … =
  Api.replay callbackExternal … := by rfl` — and this one is **DI-61's named API receipt**
  (`docs/DESIGN-ISSUES.md:135`, "at the API, … the same equality of `Api.replay` on the admission
  fixture"). It proves nothing now.

Edit: delete `callbackSleep`, `callbackExternal`, the 18 duplicated guards and the two theorems;
rename the remaining fixtures' comments ("Both spellings …" → "The one invocation form …"); add
one sentence recording that DI-61's two-spelling receipts retired with the constructor, exactly as
`src/Effect4/Laws/Program/Invocation.lean:11-14` already records for the compile-side twin.
Lines removed: ~25. Risk: none (deletes only guards that duplicate a surviving one; I checked each
pair has a surviving member). Gate: `lake build Test.Program.InvocationContract`, `make check`.

### A-4. `src/Effect4/Codegen/Read.lean:3130` — one dead private helper

```lean
private theorem names_spell_weaken {sig : Signature Op} … : 11 lines
```

**Measured**: the short name `names_spell_weaken` appears exactly once in `src`, `Test`, `tools`,
`harness` and `workshop` — its own declaration. It carries no `@[simp]`, and `private` bars any
outside use. Delete: −11 lines. Risk: needs a build (`lake build Effect4.Codegen.Read`).

For honesty: the same scan found five other unused `private` theorems
(`Codegen/Schema.lean:221`, `Program/Typing/Blame.lean:405,409,414,418`) — **all five carry
`@[simp]`**, so they are reached by `simp`/`simp_all` without being named. They are **not**
deletion candidates. I corrected my own first pass here.

### A-5. Stale line-range citations of the printer

`Codegen/Print.lean:158-168` is `Var.name` and `printLit` — **read**. The `iterate`/`reduce` print
arm is `Codegen/Print.lean:398-415`. Two comments point at the wrong lines:

- `src/Effect4/Program/Compile.lean:40` — `` (`src/Effect4/Codegen/Print.lean:158-168`) ``
- `src/Effect4/Program/Compile.lean:1260` — `` (`Codegen/Print.lean:158-168`) ``

Both were correct when they were written about `whileLoop`; the `iterate` landing moved the arm and
left the numbers. Edit: drop the range, cite the arm by name —
`` (`src/Effect4/Codegen/Print.lean`, `print`'s `.iterate` arm) ``. Why not just renumber: the
internal-citation gate (`scripts/check-internal-citations.sh`) protects only five authored
documents, so a line range into a Lean module is unguarded and will go stale again (§D-3).
Lines: 2 changed. Risk: none.

### A-6. Four dangling module citations

**Measured**: of 518 shorthand `` `Foo/Bar.lean` `` citations under `src`, `Test` and `tools`, 68
resolve to no file in the tree. Most of the 68 are legitimate — Lean core (`Init/Prelude.lean`,
`LCNF/Basic.lean`), or a retired module named together with its revision (`Machine/Layer.lean`
(`4aae12f`), `git:4aae12f`), or self-documented ("has since been split", "used to forward to").
Four are simply wrong:

| site | cites | fact |
| --- | --- | --- |
| `src/Effect4/Api.lean:111` | `Laws/Api/Blame.lean` | never existed; `src/Effect4/Laws/Api/` holds Codegen, Frontier, Fuel, Guard, HostSession, Runner, RunnerBytes. The law is `Api.explain_none_iff`, twelve lines below at `:125` |
| `src/Effect4/Program/Scoped.lean:262` | `Laws/Program/Authoring/Scoped.lean` | no such file; **generated**, so fix the source: `tools/Effect4Gen/guards/scoped.lean:6` |
| `tools/Effect4Gen/guards/scoped.lean:6` | `Laws/Program/Authoring/Scoped.lean` | the generator's copy of the same sentence |
| `src/Effect4/Laws/Program/Means.lean:28` | `Simulation.lean` | the module is the directory `Laws/Program/Simulation/` (8 files); no `Simulation.lean` |

Edits: `Api.lean:111` → `` (`Api.explain_none_iff`, below) ``; the two `Scoped` sites →
`` `src/Effect4/Laws/Program/Authoring/Lifts.lean` `` (where the 48 scope lemmas live);
`Means.lean:28` → `` `Laws/Program/Simulation/*` ``. Note the `Scoped.lean` one must be edited in
the guard file and regenerated, not in the output. Lines: 4 changed. Risk: none for three; the
generated one needs `make gen-derived` + `make check-gen`.

### A-7. `src/OCaml5/Eff/Goldens.lean:295-296` — a docstring the DI-91 slice left behind

```
/-- Kept under its name (DI-60: no fixture is renamed). `whileLoop` retired into `iterate`:
the same loop written with `iterate .nat` and answering `.lit .unit`. -/
def pWhile : P := .iterate none (n 0) …
```

`5185a6cd` changed the body to `iterate none` and left `iterate .nat` in the prose. Edit:
"written with `iterate` at no cursor annotation (DI-91) and answering `.lit .unit`".
The sibling docstrings at `:302`, `:324`, `:391`, `:397`, `:402` are all still accurate — **read**.
Lines: 1 changed. Risk: none.

### A-8. `Test/Program/CompileContract.lean:558` — a section header naming a retired constructor

`` /-! ## `whileLoop` `` heads a block whose fixture is `.iterate none …` (`:565-572`). The
fixture keeps its name under DI-60, which is fine; the *heading* reads as if the constructor were
live. Edit: `` /-! ## The loop (`iterate`; the fixture keeps its `whileLoop` name, DI-60) ``.
Lines: 1 changed. Risk: none.

### A-9. The thirteen bare `simp`s in `Intro/*` and `Handles/*`

If the owner's rule is "`simp only` in the law modules" (it is not written down — §0), these are
the only violations, and all thirteen are one-lemma unfoldings that `simp only` covers:

```
src/Effect4/Laws/Program/Intro/Fibers.lean:26   simp [actionAt, h]
src/Effect4/Laws/Program/Intro/Fibers.lean:38   simp [actionAt, h]
src/Effect4/Laws/Program/Intro/Fibers.lean:87   … := by simp [actionAt, h]
src/Effect4/Laws/Program/Intro/Fibers.lean:104  simp [forkScopedAt, h]
src/Effect4/Laws/Program/Intro/Fibers.lean:141  simp [racePoints, h]
src/Effect4/Laws/Program/Intro/Merge.lean:142   simp [layerBuildR, h]
src/Effect4/Laws/Program/Intro/Weight.lean:32   simp [denoteAt, h]
src/Effect4/Laws/Program/Intro/Weight.lean:80   simp [suspendBodyAt, hf]
src/Effect4/Laws/Program/Intro/Weight.lean:85   simp [suspendBodyAt, hf, h]
src/Effect4/Laws/Program/Intro/Weight.lean:94   simp [suspendBodyAt, hf, h]; rfl
src/Effect4/Laws/Program/Intro/Weight.lean:119  … by simp [actionAt.entrants, entrantPoints] at hx
src/Effect4/Laws/Program/Handles/Hooks.lean:544 (fun _ h => h), by simp⟩
src/Effect4/Laws/Program/Handles/Hooks.lean:547 · simp [Val.keys_eq_handles, Store.Val.handles, …]
```

I did **not** compile `simp only` replacements — each needs the `Option`/`Bool` closers that `simp`
supplies, and guessing them from the source would be a claim I cannot back. Risk: touches a proof;
do it one file at a time with `lake build` between. This is (A) only if the owner rules the rule in
(§C-5); otherwise it is noise.

### A-10. `harness/truth/truth-check-*` — six abandoned run directories

`scripts/check-truth.py:40` uses `tempfile.TemporaryDirectory(prefix='truth-check-', dir=truth)`,
so a clean run leaves nothing. Six directories survive from interrupted or hand-made runs
(**measured**, `du -sh`):

```
232K  truth-check-cszuo26w        Sep 12 16:52
192K  truth-check-s2-host         Sep  9 23:21
396K  truth-check-s3              Sep 10 05:38
396K  truth-check-s3-fixed        Sep 10 06:02
 20K  truth-check-s6b1-recording  Sep  9 23:28
4.0K  truth-check-structural      Sep 16 09:39
```

All six are ignored (`.gitignore:36` `/harness/truth/truth-check-*/`), so they are invisible to the
gates and to `git status` — 1.2 MB of stale receipts that read as current if anyone opens them
(`truth-check-s6b1-recording/receipt.json` holds absolute paths into itself). They are *not* junk
to delete blind: `s2-host`, `s3`, `s3-fixed`, `s6b1-recording` are named after slices, so they may
be receipts someone kept. Recommendation: `make clean-check` gains
`rm -rf harness/truth/truth-check-*` **after** the coordinator confirms none is a kept receipt; if
one is, it belongs under a name that is not the temp prefix. Risk: none to the build.

---

## B. Mechanical moves — one commit each, biggest win first

### B-1. The `Guard` race-ownership block is written twice (−≈470 lines net)

The coordinator noticed `raceSites_loopFinishAt` in two files. **Measured**: it is one of **59
declarations** that `src/Effect4/Laws/Program/Guard/Core.lean` and
`src/Effect4/Laws/Program/Guard/FrameOwned.lean` both declare. I compared the two copies
declaration by declaration after stripping comments and whitespace: **57 are identical in statement
and proof; the other 2 differ only by a trailing docstring my span extractor swept in — they are
identical too.** Both files were added in the same commit, `e94be3c6`.

The block in `Core.lean` (namespace `Effect4.Program.Guard`): **498 lines** at `:22`, `:984-1349`,
`:1374-1428`, `:1435-1461`, `:1470-1473`, `:2118-2162`. It covers `raceSites`, `stepRaceSites`,
`actionRaceSites`, `optionActionRaceSites`, `HooksNoRace`, `RaceCodeOwned`, `RaceIdsBelow`,
`FrameCodeOwned`, `RaceHostsPreserved`, `NRace`, `NFiber`, `StoredCodeNoRace`, `DeferredCodes`, and
46 lemmas: the whole `raceSites_*` family (`ofExit`, `asyncRoute`, `compileEff`, `resolve`,
`compileLayer`, `resolveLayer`, `embed_ofExit`, `finProgram`, `progOf`, `store_contA`,
`store_contE`, `completion`, `cancelProgram`, `cancelProgramOf`, `innerLayerAt`, `regionCode`,
`contEOf`, `contAOf`, `suspendBodyAt`, `runStmts_yieldOf`, `runStmts`, `closeDone`,
`closeSeqStep`, `store_iterNext`, `loopFinishAt`, `loopNextAt`, `loopResumeAt`, `actionEntrants`,
`actionAt`, `forkScopedAt`, `actionOf`, `withFiberOf`), `hooksNoRace_interpOf`/`_interpAt`,
`raceCodeOwned_of_no_sites`/`_transport`/`_beginRace`, `raceHostsPreserved_append`/`_updateRace`,
`race_id_of_lookup`, `race_lookup_updateRace`/`_fresh`, `deferredCodes_cellAt`/`_make`/`_setCell`/
`_register`. The matching block in `FrameOwned.lean` (namespace
`Effect4.Program.Guard.FrameOwned`) is **448 lines**.

The duplication already costs a third thing. `src/Effect4/Laws/Program/Guard/Settle.lean:134-159`
holds **26 lines of bridge lemmas whose only job is to say the two copies are the same**:

```lean
theorem frameDraft_sites_eq (code : NCode) :
    Effect4.Program.Guard.FrameOwned.raceSites code = raceSites code := by
  induction code <;> try (first
    | rfl
    | simp_all [Effect4.Program.Guard.FrameOwned.raceSites, raceSites])
  …
theorem frameDraft_owned_iff (m : NativeMachine) (f : NFiber) :
    Effect4.Program.Guard.FrameOwned.FrameCodeOwned m f ↔ FrameCodeOwned m f := …
theorem frameDraft_deferred {m : NativeMachine} (state : GuardState m) : … := …
```

That proof is also the only `try (first | …)` search in this part of the tree, and it exists purely
to transport across a copy-paste.

**Move plan.** New module `src/Effect4/Laws/Program/Guard/RaceSites.lean`, `import Effect4.Api`
only (that is `FrameOwned.lean`'s first import and `Core.lean`'s only one), namespace
`Effect4.Program.Guard`, holding the 59 declarations once. Then:

- `Core.lean` — delete the 498 lines, `import Effect4.Laws.Program.Guard.RaceSites`. Every use
  inside stays as written: the names are in `Effect4.Program.Guard`, the namespace the file is
  already in.
- `FrameOwned.lean` — delete the 448 lines, add the same import. Its own namespace is
  `Effect4.Program.Guard.FrameOwned`, which puts every prefix in scope, so unqualified `raceSites`,
  `FrameCodeOwned`, `DeferredCodes` resolve to the shared ones.
- `Settle.lean` — delete `frameDraft_sites_eq`, `frameDraft_owned_iff` and `frameDraft_deferred`
  (`:134-159`) and their 11 `Effect4.Program.Guard.FrameOwned.`-qualified uses: after the move the
  two sides are one term, so the rewrites become nothing. `Settle.lean` is the only file that
  qualifies with `FrameOwned.` (**measured**: 11 occurrences; `NativeState.lean` and
  `ReturnFields.lean` have 0).
- `src/Effect4/Laws.lean` — no change; `Guard.lean` reaches the new module through `Core`.

Net: −498 −448 −26 +≈500 ≈ **−470 lines**, and 59 proofs elaborate once instead of twice — on the
two slowest proof modules in the tree (`Guard/FrameOwned` 84s, `Guard/Core` 67s, STATE.md §16).
Risk: needs a build; no statement changes. Gate: `lake build Effect4.Laws.Program.Guard`, then
`make check`.

*Which copy to keep:* neither — extract. Making `Core` import `FrameOwned` would drag
`Effect4.Laws.Machine.Handles` (5,500 lines) into the import closure of `Core`'s ten dependents for
no reason; making `FrameOwned` import `Core` would drag 3,800 lines of guard-state induction into a
file whose header says "no global GuardState induction is copied".

### B-2. `src/Effect4/Codegen/Read.lean` — 2,571 lines of proof inside an implementation module

**Measured**: the file is 3,507 lines and holds 101 theorems. Definitions run to `:926`; the
declarations after that are `LawfulTable` (`:2909`) and `nativeSpell` (`:2914`) and **nothing else**
— the rest is proof: the binder-injectivity block, the term and cause round trips, `read_print`
(`:1759`), `read_print_layer`/`_layers`/`_stmts`/`_effs`/`_action`, `read_exact_all` (`:2304-2892`,
a 589-line induction), `read_exact` (`:2892`), the native-profile lemmas, `roundTrip_eq` (`:3042`)
and the positional-weakening block (`:3054-3507`).

**Measured, and this is the point:** *no core (non-`Laws`) module uses any of those 101 theorems by
name.* I extracted every theorem name from the file and grepped `Api.lean`, `Codegen/Forms.lean`,
`Codegen/Admit.lean`, `Codegen/Checked.lean`, `Codegen/SourceBindings.lean` and `Effect4.lean`. The
only hits are three docstring mentions in `Api.lean` (`:146`, `:147`, `:158`,
naming `read_print`, `read_exact`, `roundTrip_eq` as prose). The real consumers are:

| consumer | uses |
| --- | --- |
| `src/Effect4/Laws/Codegen/Module.lean` | `read_print`, `read_print_layer`, `bind_eq_ok` (12×), `ok_bind` (3×) |
| `src/Effect4/Laws/Codegen/HoistingReadable.lean` | `readable_select_iff` (4×) |
| `src/Effect4/Laws/Codegen/Checked.lean` | `lawfulTable_member`, `nativeLawful` |
| `Test/Codegen/ReadContract.lean` | `read_print`, `read_exact`, `roundTrip_eq`, `roundTrip_weaken`, `readKey_exact`, `readKey_printKey`, `read_print_layer`, `Var.name_ne`, `name_notin` |
| `Test/Program/WeakenContract.lean` | `roundTrip_weaken`, `nativeLawful` |

**Move plan.** New `src/Effect4/Laws/Codegen/Read.lean`, `import Effect4.Codegen.Read`, same
namespace `Effect4.Program`, taking `:927-2901` and `:2919-3505` — 90 theorems, 2,571 lines.
`Codegen/Read.lean` keeps `:1-926` (every `def`, the five `heads` lemmas, `savedVar?_some`,
`readable_select_iff`, the four `Except` receipts) plus `LawfulTable` and `nativeSpell`.
Importers to change: `Laws/Codegen/Module.lean`, `Laws/Codegen/HoistingReadable.lean`,
`Laws/Codegen/Checked.lean`, `Test/Codegen/ReadContract.lean`, `Test/Program/WeakenContract.lean`
(each adds `import Effect4.Laws.Codegen.Read`), and `src/Effect4/Laws.lean` if the new module is not
otherwise reached. `src/Effect4.lean` and `tools/Tools/TsGen.lean` unchanged.

One risk to name: `ok_bind` and `map_ok` (`:913`, `:916`) are `@[simp]`, so a bare `simp` in a
downstream *core* module could be leaning on them silently. Keep the whole
"Receipts: what the reader needs of `Except`" section (`:911-926`) in the core half — that is what
the boundary above does — and the simp set the core sees does not move. Risk: needs a build, no
statement changes. Gate: `lake build Effect4 Effect4.Laws`, then `make check`.

### B-3. `Laws/Program/Invocation.lean` — a third statement of one equation

After `callback`, `Invocation.lean` (80 lines) holds three theorems, **none used anywhere in
`src`** (**measured**; `Test/Program/InvocationContract.lean` imports the module and
`Test/Counterexamples/Archive/REGISTER.md` names `checkTable_none_externalRow`). One of the three
duplicates a stronger lemma that already exists:

```
Invocation.lean:39   compileEff_perform_eq_asyncRoute (hf : p.fuel = k+1)
                       (h : (∃ i, op = .external i) ∨ op.row.kind = .async)
Intro/Equations.lean:22  compileEff_perform_nonsync (hf : p.fuel = k+1)
                       (hkind : (NativeOp.row op).kind ≠ .sync)
```

Same conclusion; the second subsumes the first (an external row is `.async` by `checkTable`'s own
`notAsync` rule), and it has two corollaries at `:33` and `:39` already. `Invocation.lean` cannot
import `Intro/Equations.lean` cheaply (it imports only `Effect4.Program.Compile`), so the move goes
the other way: state DI-61's theorem in `Intro/Equations.lean` as a three-line corollary of
`compileEff_perform_nonsync`, delete `Invocation.lean`'s 9-line proof, and leave `compile_zero_fuel`
and `checkTable_none_externalRow` where they are. −9 lines and one independent proof.
Risk: touches a proof. Gate: `lake build Effect4.Laws.Program.Intro`, `make check`.

### B-4. `src/Effect4/Program/Typing/Blame.lean:431-765` — 51 copies of one tactic line

**Measured**: the line

```lean
simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy,
  explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
```

appears **51 times** in the 334-line mutual block that proves `explainEff_none_iff`, each followed
by `(repeat' split) <;> simp_all [EffTy.joinAnswer]`. Most of the thirteen names are irrelevant to
any one arm, which is what the `linter.unusedSimpArgs` warnings the brief names come from.

This one does **not** move out of the implementation module, and the brief's premise is wrong here:
`Api.check` (`src/Effect4/Api.lean:437-444`) uses `explain_none_iff` **inside a `def`**
(`:444`, `absurd ((explain_none_iff program table).mp h) …`) to be total, and the library root never
reaches `Effect4.Laws`. The law has to live beside the definition, exactly as STATE.md §17 records.

What can be cut is the repetition. Two options, both needing a build:
(a) name the list once — `local macro "blame_arm" : tactic => …` or a `simp` set — and write
`blame_arm` 51 times; (b) restate the mutual induction over `Node` and its binder table so the arms
that share a shape share a proof. (a) is the cheap one: −49 × 2 lines ≈ **−100 lines**, and an
alphabet change then edits one list instead of 51. (b) is a design question (§C-4). Risk: touches a
proof, and the file already sets `maxHeartbeats 1600000`, so measure the elaboration time before
and after. Gate: `lake build Effect4.Program.Typing.Blame`, `make check`.

### B-5. The loop-fragment leaf lists — one eliminator for sixteen sites

**Measured** across `src`, `Test` and `tools`: **24 or-pattern arms that name six or more `Eff`
constructors**, of which **16 are in the loop-fragment law files landed at `c885f04a`**:

```
src/Effect4/Laws/Program/Agreement/Loop.lean   :266-270, :317-321, :382-389, :798-811   (17 alts each)
src/Effect4/Laws/Program/DenoteB.lean          :176-177 (8), :257-261, :327-333, :454-463 (17 each)
src/Effect4/Laws/Program/LoopSound.lean        :154-158 (17), :514-520 (12)
src/Effect4/Laws/Program/MeaningSound.lean     :136-139 (13), :639-646 (13)
src/Effect4/Laws/Program/TypedRun.lean         :67-71 (12)
src/Effect4/Laws/Program/DenoteR.lean          :1288-1291 (17), :1360-1362, :1364-1370, :1540-1546
src/Effect4/Laws/Program/Agreement.lean        :1454-1461 (12), :1914-1925 (12)
src/Effect4/Laws/Program/Agreement/Machine.lean :201-212 (12)
src/Effect4/Program/Typing.lean                :685-691 (25)
src/Effect4/Codegen/Read.lean                  :3265-3271 (24)
src/Effect4/Codegen/Print.lean                 :54-64 (53, the Head list — guarded, see §0.3)
```

Every 17-alternative list is the same thing: the complement of `composite`
(`Laws/Program/DenoteB.lean:175-179`), i.e. the arms where `Looped e = Straight e` holds by the
catch-all. The classifier already exists, and so does one collapsing lemma for the function:

```lean
theorem denoteB_leaf (k : Nat) (e : NativeEff) (env : List Val) (h : composite e = false) :
    denoteB k e env = leafB e env
```

What is missing is the *eliminator*. Every one of those sixteen sites is a structural recursion on
`NativeEff` that needs constructor patterns for termination, so `denoteB_leaf` cannot reach them.
One declaration would:

```lean
/-- Structural induction on the loop-bearing fragment: nine composite arms and one leaf. -/
theorem Looped.rec' {motive : NativeEff → Prop}
    (leaf : ∀ e, composite e = false → Straight e = true → motive e)
    (iterate : ∀ c i t s r b, motive b → motive (.iterate c i t s r b))
    (suspend bind select exit catchCause matchCause onExit : …) :
    ∀ e, Looped e = true → motive e
```

Each call site then names nine arms instead of nine plus a seventeen-alternative list. Saving:
≈ 60 lines and, more to the point, an added or retired constructor edits **one** declaration
instead of sixteen. `Looped` already has the eight per-arm projections (`Looped.bind`,
`Looped.select`, `Looped.catchCause`, `Looped.matchCause`, `Looped.onExit`, `Looped.suspend`,
`Looped.exit`, `Looped.iterate`, `DenoteB.lean:136-166`) that the eliminator's proof needs, so the
eliminator is a ~30-line assembly of things that exist.

I did **not** compile this; the statement above is a sketch of the shape, not a checked one. Risk:
touches every loop-fragment proof. Gate: `lake build Effect4.Laws.Program.TypedRun`, `make check`.
This is the single highest-value organization change for future alphabet work, and it is the one I
would put second after B-1.

### B-6. `src/Effect4/Codegen/Read.lean:215` — `rowAnswer`'s dead parameter

```lean
def rowAnswer (_row : Row) (op : Op) (request : Term) : Eff Op := .perform op request
```

The row is ignored; the docstring says why ("the row stays a parameter so that the readers of the
four row shapes keep one signature"), which is a real reason and reads honestly. **Measured**: 36
mentions of `rowAnswer` in the file, of which **16** pass the argument as `(sig.rowOf op)`; the rest
are `simp only [rowAnswer]`, `rw [print_rowAnswer]` and the like, which do not name it.

Is the deletion mechanical? **Yes for the call sites, no for the statements.** Dropping `_row`
removes `(sig.rowOf op)` from 16 places, of which five are inside *theorem statements*
(`:1438`, `:1450`, `:1521`, `:1564`, `:1619`, `:1653`, `:1659-1660`, `:2210`, `:2260-2263`,
`:1692`) — so it is a statement change, not a rename, and it must land with B-2 or after it. My
recommendation: **leave it**. It is 1 line, the docstring is accurate, and the "one signature for
four shapes" reason survives the retirement. If it is touched at all, do it in the same commit as
B-2 while the statements are already moving.

---

## C. Needs the owner's word

### C-1. `AdmittedProgram` and `imageCertificate`: the justification lost its witness

DI-61(c) (`docs/DESIGN-ISSUES.md:135`) says `readable` is not a field of `AdmittedProgram`
"because `readable` is exact reconstruction after printing, not executable validity, **and the
historical wire program `pAwait` is typed, admitted and not image-certified**".
`Api.lean:378-384` repeats it. **Compiled**: `pAwait` is now readable, admitted and
image-certifiable. The *reason* may still be the right one — the separation is between two kinds of
claim, not between two programs — but the register's evidence is gone. Options:

- (a) keep the separation, replace the example with a program that is typed and not readable today
  (the 45 loop programs are the obvious candidates until R5 lands, which makes the example
  temporary);
- (b) keep the separation and state it without an example, as a claim about what a certificate
  means;
- (c) revisit whether `readable` belongs in `AdmittedProgram` now that the invocation forms are one.

**Recommended: (b).** The distinction is about what is certified, not about which programs happen
to fail; an example that R5 will delete is a third place to keep in step. Whoever takes it should
also amend DI-61's row, which is the authority.

### C-2. `tools/Conform/Effect4/audit.json` and `audit-complete.json` are run by nothing

**Measured**: `scripts/check-conform.py` has three profiles — `compiler`, `native`, `cases` — and
`cases` runs `tools/Conform/Cli/Audit.lean --config tools/Conform/Effect4/cases.json`, which names
`cases-policy.json`. Grepping the whole tree for `audit-complete` finds exactly one hit: its own
`"tool"` field. `audit.json` has no caller either. So `cases-policy-complete.json` (1,383 lines) is
a pin nothing checks — and it is stale by four retired constructors (§D-1), which is the proof that
nothing checks it. Options: (a) delete `audit-complete.json` and `cases-policy-complete.json`
(−1,393 lines); (b) wire the complete walk into `check-full` and re-seed the policy;
(c) keep as a by-hand tool and mark it in the file's note as unchecked.
**Recommended: (b) if the mono-extension walk still earns its 351 rules, else (a).** Its own note
says the cost is "a toolchain bump will need a re-seed and a diff" — a pin with that cost and no
gate is the worst of both. This is the owner's call because the file records a measurement
(351 case sites vs 122) somebody paid for.

### C-3. Generated modules carry their laws; the generator already knows how to split

`src/Effect4/Program/Scoped.lean` (69 theorems, 302 lines) and `src/Effect4/Program/Fold.lean`
(60 theorems, 3,545 lines) are generated law-bearing modules under the **core** root, while the
same generator emits `Program/Authoring/Lifts.lean` **and** `Laws/Program/Authoring/Lifts.lean` as
a pair. The inconsistency is the generator's, not the tree's. Splitting `Fold.lean` would move
~60 fold theorems out of the core root; splitting `Scoped.lean` likewise. Whether that is worth a
generator change depends on whether any core `def` needs those theorems — I did not check that
(§What I did not check), and it is the deciding fact. **Recommended: ask the coordinator to
measure it during the next `Fold.lean` regeneration rather than as its own slice.**

### C-4. `Blame.lean`'s 51 arms: macro or restructure

B-4(a) is a tactic abbreviation, safe and mechanical. B-4(b) — restating the refusal projection as a
fold over `Node` and the binder table, the way `scopedAlgebra` is stated — would make the whole
block a handful of arms and put `explain` on the same footing as `scopedAt`. That is a design
decision (it changes what `explain` *is*, and the owner's standing rule is to go one level higher
toward the algebra). **Recommended: take (a) now as part of this cleanup, and put (b) on the
generation-medium lane where the equation-lemma emitter already wants `explain`** — STATE.md's
"Next" item 0 names `explain` as one of the first three emitters (`Straight`, `effTy`, `explain`),
so (b) is already planned and should not be done twice.

### C-5. Write the tactic rule down

It is not in any tracked file (§0). Proposed sentence for `AGENTS.md` under **Working**:

> In `src/Effect4/Laws/**`, a proof closes with named tactics. `simp` names its lemmas as
> `simp only [...]`; `simp_all`, `first | …`, `try` and `aesop` are not used. Outside `Laws/`
> the rule is advisory.

If the owner wants only the weaker form (no `simp_all`/`first`/`try`), say so — the tree is already
at the weaker form in `Intro/*` and `Handles/*`, and 790 `simp` calls away from the stronger one
everywhere else.

### C-6. `docs/STATE.md` — four sentences that are now false

The file is the entry point; these are the ones a reader would act on wrongly.

| line | text | what is true |
| --- | --- | --- |
| 44 | "`check-citations` fails on an untracked owner doc (`docs/CAS-IFIED-APIS-AND-SCHEMAS.md:335` cites `src/Effect4/Codegen/Casify.lean`, which does not exist)" | **Not true at HEAD.** I ran `python3 scripts/check-source-citations.py`: `PASS source-citations: 3602 citation tokens examined; 0 baselined missing targets`. The allowance was added in `37ff9b21` (`scripts/source-citations-allowed.txt:3`). Replacement: delete the sentence, or "`check-citations` is green; the `Casify.lean` citation of the untracked owner doc is allowed at `scripts/source-citations-allowed.txt:3`." |
| 45 | "decision D1, how `iterate`'s annotation is read, owed by the owner" | Superseded: DI-91 landed at `5185a6cd` as (d′). Replacement: "D1 is answered by DI-91 (d′) and landed at `5185a6cd`: `cursorTy : Option Ty`, `none` synthesized and readable, `some t` printed and not readable." |
| 43 | "`iterate` is landed the same way (2026-09-17: the constructor with its cursor annotation, typing by subsumption at the annotation …)" | The annotation is now optional and typing reads `cursorTy.getD c0`. Add ", made optional the same day by DI-91". |
| 9 | heading "## True at the DI-86 landing (2026-09-16, night)" | The section under it is two days old while items 5, 6 and 10 of "Next" describe 2026-09-17 landings, so a reader takes the stale half as current. Re-stamp the heading, or move the 2026-09-17 facts up into it. |

One more, not false but arithmetically loose and worth one minute from whoever edits the file:
line 44 says "the printed corpus directory holds none (363 programs written, 45 counted as
refused …)" and "the reader's refusals on the 400 are exactly the loops", while line 60 says "45 of
the 410 corpus programs". 363 + 45 = 408. `.lake/corpus/index.tsv` has 363 rows and
`Test/Codegen/ReadContract.lean:648` guards `(Test.Program.Gen.corpus 400 4).length = 400`, so the
three numbers are counting three different sets (generated 400, generated + wire, written). Say
which each is.

DI-91's register row still reads **recommended**; it is landed. DI-92's reads **open**; the
`intFreeProgram` field and `admitProgram_program_int` landed in the same commit. Both rows want the
ruling written in, since "a ruling is made only when written into a tracked file" (`AGENTS.md`).

---

## Silent drift found

The coordinator's addition: every place where today's alphabet changes (four retirements, and
`iterate`'s optional annotation) needed a **hand** edit that a generator or a guard should have
produced or caught, ranked by how badly a miss would read. "Silent" means the build and every gate
stay green while the tree says something false; "loud" means something refuses.

### D-1. The complete case-site policy went stale and nothing noticed — **silent**

`tools/Conform/Effect4/cases-policy-complete.json` names the four retired constructors in the
`cover` lists of **18** function entries (**measured**):

```
Node.setChild, Eff.expandRound, Eff.layerPaths, Node.child, Eff.refSites,
evaluateNative, provideLayerWithK, syncValueAt, forkScopedAt, loopAt, actionAt,
suspendBodyAt, compileEff, Provision.docsSem, Provision.docsBody,
Provision.Deploy.deploySem, Provision.Deploy.deployBody, addReceiver
```

The checker would refuse them — `tools/Conform/Lcnf/Cases.lean:419-421`: "a constructor listed but
not absorbed is a refusal too (the policy is stale)". But **nothing runs this policy** (§C-2), so
the rows sat through four retirements. A reader who opens the file learns that `whileLoop` and
`callback` are live.

Cheapest guard to make it loud: give the file a caller. One line in `scripts/check-conform.py`'s
`PROFILES` (a fourth profile `cases-complete` pointing at `audit-complete.json`) plus one
prerequisite in the Makefile's `check-full`. If the walk is not worth running, delete the pair —
either way the tree stops holding an unchecked claim.

### D-2. `Eff.arms` and `Eff.constructorNames` are hand lists with a self-satisfied guard — **silent**

`src/Effect4/Program/Eff.lean:524-559` holds two hand-written tables and this guard:

```lean
#guard arms.map Arm.constructor = constructorNames
#guard constructorNames.length = 25
```

The guard compares the two hand lists **with each other**. Both are edited by the same hand in the
same commit, so they always agree; neither is compared with the declaration. A constructor added
and forgotten, or a retired one left in, passes. The four retirements needed a hand edit here
(three removed rows, two added) and a hand edit to the `25`.

**Compiled** a probe (`run_cmd` reading `Effect4.Program.Eff`'s `ctors` from the environment):

```
env ctors (25): [succeed, fail, failCause, sync, suspend, perform, bind, gen, catchCause,
  matchCause, onExit, exit, uninterruptible, interruptible, yieldNow, awaitFiber, withFiber,
  scoped, acquireRelease, provideLayer, service, provideService, catchIf, select, iterate]
equal: true
```

So they agree **today**. The guard that would keep them agreeing: five lines in
`tools/Effect4Gen/Authoring.lean`, which already reads `Effect4.Program.Eff` from the environment —
compare `info.ctors` against `Effect4.Program.constructorNames` and fail the generator. Then
`make gen-derived` / `make check-gen` is the alarm, no metaprogramming enters `src/`, and the `25`
can go. Contrast `heads_complete` (`Codegen/Read.lean:111`, `cases h <;> decide`), which is the same
guarantee for `Head` and costs one line.

### D-3. Line-number citations into this repo's own Lean modules are unguarded — **silent**

`scripts/check-internal-citations.sh` refuses a line-numbered citation only into five *authored
documents* (`docs/research/SCHEMA-CUTOVER.md`, `PLAN.md`, `AGENTS.md`, `docs/ARCHITECTURE.md`, the
former routing doc), and `scripts/check-source-citations.py` explicitly checks paths "not line
ranges" and only recognises paths that begin at a scanned root. **Measured**: **240** line-ranged
`.lean` citations and **518** shorthand ones (`` `Stores.lean:1209-1240` ``) live in `src`, `Test`
and `tools`, none of them scanned.

The `iterate` landing moved the printer's loop arm from `Print.lean:158-168` to `:398-415`, and the
two citations in `src/Effect4/Program/Compile.lean` (`:40`, `:1260`) now point at `Var.name` and
`printLit` while asserting a claim about the printed loop (§A-5). Four more shorthand citations name
files that do not exist (§A-6).

Cheapest guard: extend `TOKEN` in `check-source-citations.py` to accept a bare
`Dir/File.lean` shorthand and resolve it as a path suffix against the inventory. That alone makes
§A-6's four dangling names loud. Line *ranges* into mutable Lean modules cannot be checked cheaply
— the honest fix is the house rule the internal gate already states for documents: cite the
declaration by name, not the line. 240 sites is too many for one commit; the rule plus a widened
scanner stops new ones.

### D-4. Two contract fixtures collapsed into one and their theorems became `x = x` — **silent**

§A-3. `performSleep`/`callbackSleep` and `performExternal`/`callbackExternal` are now the same
definition; `sleep_print_same` and `replay_perform_external_eq_callback` are `rfl` on identical
terms; 18 `#guard` pairs check one fact twice. `replay_perform_external_eq_callback` is DI-61's
named API receipt, so the register points at a theorem that proves nothing, and the build is green.

Cheapest guard: where a contract compares two spellings, pin that they *are* two —
`#guard performSleep != callbackSleep` beside the theorem. One line per pair, and it fires the day
a retirement makes them equal. (The compile-side twin was handled correctly:
`Laws/Program/Invocation.lean:11-14` deleted `compile_perform_eq_callback` and wrote down why. The
API side was not.)

### D-5. A docstring the DI-91 slice contradicted in the same hunk — **silent**

`src/OCaml5/Eff/Goldens.lean:295-296` still says "written with `iterate .nat`" two lines above
`def pWhile : P := .iterate none …`, changed by the same commit (§A-7). Nothing reads a docstring.

Cheapest guard: none that is cheap. This is what review is for; the mitigation is that the fixture
block is small and the coordinator's own diff showed both lines. Worth noting that the same slice
got the *hard* parts right without a guard's help: `Test/Program/Gen.lean:257-263`'s comment was
updated with the draw, and `ocaml/engine/e4_program.ml:239-240` already reads
`Option.map of_ty c`.

### D-6. `Prim.yieldableError` is unreachable from any program, and the census does not say so — **silent, low**

**Measured**: nothing constructs `Prim.yieldableError`. `compileEff` never emits it; the only
mention outside `Frames.lean` and its proofs is `Program/Compile.lean:364`, a pass-through arm of
`embed`, and the stores never build one either (`Machine/Stores.lean` has no occurrence). Since
`Eff.yieldError` retired, the census row `op.YieldableError`
(`Test/Audit/RuntimeCoverage.lean:100-104`, coverage `green`, disposition `foreignBoundary`) is
witnessed by two frame-machine theorems about a primitive **no source program can reach**.

That is not wrong — the row is about the rc.112 runtime's primitive, and the machine models it
faithfully — but "green" now means something weaker than it did on 2026-09-16, and the census says
nothing about the change. Cheapest fix: one sentence in the row's docstring in
`Test/Audit/RuntimeCoverage.lean` recording that no `Eff` constructor compiles to it since
`19a1fd8b`. **Do not delete the primitive** (§0.2).

### D-7. Where the retirements were *loud*, for the record

Worth writing down, because it is where the design already works and it is the pattern the items
above should copy.

- **`tools/Effect4Gen/wire-tags.json`** enforces "the active names of a listed family are exactly
  its declared constructors" and "every inductive family of the program world must be listed". A
  retired constructor left in `active` refuses at generation. Loud.
- **`ocaml/engine/e4_program_layout.ml`** is generated from Lean and carries the ordered constructor
  names per family; `E4_program.check_manifest` compares the manifest, `Eff_types` and the engine,
  and `ocaml/engine/test/test_engine.ml` additionally mutates the manifest (transposing two
  same-arity `eff` arms) and requires the pin to refuse it. Loud, and adversarial.
- **`Head` / `heads` / `reserved`** in the printer: `heads_complete` is `cases h <;> decide`. Loud.
- **`ctor_index_eff`** in `ocaml/engine/e4_program.ml:369-394` is a hand list, but OCaml's
  exhaustiveness plus the generated `Eff_types` make an add or a retire a compile error. Loud.

The three silent cases (D-1, D-2, D-3) are exactly the three artefacts that are **hand-written text
compared against other hand-written text**, or against nothing. That is the shape to look for.

---

## Module organization — the smallest regrouping worth doing

`src/Effect4/Laws/Program/` has seven groups (`Agreement/`, `Authoring/`, `Guard/`, `Handles/`,
`Intro/`, `Simulation/`, `Typing/`) and **38 top-level files**. I am proposing exactly one move,
because it has a reason a reader feels rather than a tidiness reason.

Six files landed together at `c885f04a` and are one development — the budgeted meaning over
`Looped` and what it proves:

```
DenoteB.lean      488   the fragment, denoteB, meaningB, the monotonicity
Iter.lean          56   iter, iter_succ, iter_uniform, iter_congr
LoopAgreement.lean 51   the agreement's statement
MeaningSound.lean 728   the meaning is never wrong
LoopSound.lean    549   loops are type-sound at every budget
TypedRun.lean     121   read off the certificate
                 2073 lines
```

They currently sit between `Denote.lean` and `DenoteR.lean`, which are a different thing (the
compositional meaning and the reference runtime). A reader opening `Laws/Program/` cannot tell the
loop development from the straight one.

**Proposal:** `src/Effect4/Laws/Program/Budget/` holding those six files under their **existing
names** (`Budget/DenoteB.lean`, `Budget/Iter.lean`, `Budget/LoopAgreement.lean`,
`Budget/MeaningSound.lean`, `Budget/LoopSound.lean`, `Budget/TypedRun.lean`). No renames — the names
are already good and a rename storm is exactly what the owner's rule warns against. Import edits:
the six headers, `src/Effect4/Laws.lean` (six lines), `Laws/Program/Agreement/Loop.lean`, and the
Test contracts that import them (`Test/Program/DenoteBContract.lean`,
`Test/Program/LoopSoundContract.lean`, and whichever others name them). Roughly 20 import lines.

I am *not* proposing to group `CheckedTyping`, `Decision`, `Invocation`, `ErrorQueries`,
`ValueModel`, `LinkedRows`, `Hoisting`, `HoistingTotal`, `ReferenceTyping`, `ScopedTyping`: each is
small and named for what it is, and moving them buys a shorter directory listing and nothing else.
`Invocation.lean` is the one whose home is genuinely in question, and B-3 answers it by emptying
most of it instead.

---

## What I did not check

- **I ran no gate.** No `lake build`, no `make`, no `bun`, no generator. Every "it compiles" claim
  is a scratch file under
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/aa7ebaa0-7350-4784-b70e-322956de92e8/scratchpad/scoutE/`
  run with `lake env lean`, quoted verbatim. The two exceptions are read-only scripts:
  `scripts/check-source-citations.py` (which writes nothing — `generated/citation-baseline.txt` does
  not exist, and `git status` was unchanged after) and my own Python scans.
- **The `linter.unusedSimpArgs` warning list.** The brief names four sites; I could not obtain the
  warning text without building the modules, so §A-9 and §B-4 are read off the source, not off the
  linter. I did not produce corrected `simp only` lines for `Machine/Timer.lean:133-134`,
  `Laws/Program/Handles/Hooks.lean` or `Test/Program/RuntimeRContract.lean`: guessing the closing
  lemma set from the source would be a claim I cannot back. `Machine/Timer.lean:133-135` is
  an eight-lemma `simp only [...]` immediately followed by a bare `simp`, which is the shape that
  produces the warning; the repair is to fold the second into the first, and that needs a build to
  find.
- **Whether any core `def` needs a theorem from the generated `Program/Fold.lean` or
  `Program/Scoped.lean`** (§C-3). That is the fact that decides whether they can be split, and it
  needs a name-by-name scan I did not run.
- **Elaboration time.** I claim B-1 removes 59 duplicate elaborations from two modules STATE.md
  records at 84s and 67s; I did not measure the saving.
- **The `Looped.rec'` statement in B-5 does not typecheck as written** — it is a sketch of the arms,
  not a compiled declaration. Whoever takes it should expect to adjust the motive's arguments.
- **Whether `make check-tools` is green after A-1.** I compiled only the one fixture.
- **`Test/` beyond the files the retirements touched**, `Test/contracts/*.contract.md` (which name
  retired theorems in several places — e.g. `faces.contract.md:46-50`, `:60`,
  `frames.contract.md:153`, `:320`, `program-denotation.contract.md:110-118` — all of which I read
  as frozen packets whose job is to record history, so I did not list them as leftovers), and the
  whole of `Test/Counterexamples/`.
- **The 341 law theorems in `src/Effect4/Laws` that nothing else mentions.** I measured the number
  and then deliberately did *not* turn it into a deletion list: a law module's job is to state laws,
  and the sample I inspected (`Witnesses.lean`'s census witnesses, `Guard/Core.lean`'s `Reachable`
  API, `HostBoundary.lean`'s refusals, `Iter.lean`'s `iter_congr`, `MeaningSound.lean`'s
  `meaning_stores`, `Laws/Api/RunnerBytes.lean`'s three row lemmas) are all top-level statements
  named in STATE.md or in a contract. Deciding which of the 341 are dead needs the obligations
  ledger, not a grep.
- **`ocaml/eff/` and the rest of `ocaml/engine/`** beyond `e4_program.ml`, `e4_program_layout.ml`
  and `test_engine.ml`; and `mirrors.json` / `rules.json` under `tools/Conform/Effect4/`, whose
  callers I did not trace.
