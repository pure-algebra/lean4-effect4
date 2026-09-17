# Scout F: a coverage sniff test, and the close-out list for the language foundations

Read-only scout, 2026-09-17 13:00 CDT, on `refactor/phase1-phase3` at `6545d862` with 86
uncommitted paths in the checkout (the coordinator's `iterate`/`admitProgram` slice and three
other scouts reading). No tracked file changed. No gate ran. Everything marked **counted** or
**compiled** came from a scratch file under
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/aa7ebaa0-7350-4784-b70e-322956de92e8/scratchpad/scoutF/`
run with `lake env lean -M6144`, or from parsing a committed file. Everything marked **read**
is a claim about a file in the tree, cited by path. Everything marked **inferred** is an
argument from those, not an executed fact. Nothing here is **proved** by me.

## 0. The short answer

Coverage against rc.112 is thin and it is thin in a shape nobody chose. Two lanes run a program
on the real runtime: 36 hand programs (`make check-truth`) and 127 of 400 generated programs
(`make check-corpus`). Counted across both:

- **Every one of the 25 `Eff` constructors reaches rc.112 in at least one program.** That is the
  good news and it is better than I expected. But six of them (`sync`, `suspend`, `matchCause`,
  `onExit`, `uninterruptible`, `interruptible`) reach it *only* through the generated corpus,
  where nobody wrote the program and nothing about it was chosen; and four (`awaitFiber`,
  `acquireRelease`, `catchIf`, `iterate`) reach it *only* through the 36 hand programs, because
  they never survive a random draw well-typed. The remaining fifteen are in both halves, though
  the generated side of four of them is one typed program (`catchCause`, `select`, `perform`)
  or two (`provideLayer`).
- **Six of the eleven printable fiber actions are never compared** (`forkIn`, `runIn`,
  `interrupt`, `interruptAll` in both forms, `awaitAll`); five more cannot print at all, by a
  guarded design choice.
- **Ten of the 20 atoms, 48 of the 55 built-in native row positions (15 of the 23 row families),
  and two of the three decisions are never compared with rc.112 at all.**
- **`select … .option`, `select … .tag`, `iterate` with a `some` annotation, `iterate` with a
  non-`unit` result, `sleep` and `clockNow` occur in no program of either corpus.**

The absences are not random: they are the constructors whose typing needs a subterm of a
particular type, which a random draw almost never supplies, plus the constructors the 36 hand
programs happened not to use. The generated half was measured on 2026-09-16
(`docs/research/2026-09-16-testing-corpus-coverage.md`) and its numbers still hold exactly;
the hand half had not been measured until now.

The internal side is in better shape but its statements are narrower than the word "never
wrong" suggests: the compositional meaning and its machine agreement are stated on `Looped`,
which is 13 of the 25 constructors, and on `perform` only for `sync` rows (read,
`src/Effect4/Program/Fragment.lean:20`, `src/Effect4/Laws/Program/DenoteB.lean:123`). The
whole-alphabet theorem is `run_eq_ref`, and it relates two of our own artefacts at the empty
table with no oracle answers (read, `src/Effect4/Laws/Program/RuntimeR.lean:197-211`).

Ten of the checker's 24 refusal reasons, and one of the printer's four, have no red control
anywhere (counted). One control file that exists (`harness/truth/select-controls.ts`, the three
`caseTag` narrowing controls and one `optionCase` control) is compiled by no lane, because the
only `tsc` invocation that names it rewrites the config into a work directory the file was
never copied to (read). Three `.test.ts` files under `harness/truth/` are run by nothing.

## 1. The alphabet, counted

From the declarations, not from the brief.

| Family | Count | Owner |
| --- | --- | --- |
| `Eff` | 25 | `src/Effect4/Program/Eff.lean:304`; `#guard constructorNames.length = 25` at `:559` |
| `Stmt` | 6 | `src/Effect4/Program/Eff.lean:376` |
| `ActionTerm` | 16 | `src/Effect4/Program/Eff.lean:395` |
| `LayerTerm` | 10 | `src/Effect4/Program/Eff.lean:421` |
| `CauseTerm` | 4 (`interrupt` two-valued) | `src/Effect4/Program/Eff.lean:271` |
| `Decision` | 3 | `src/Effect4/Program/Decision.lean:36` |
| `Term` / `Lit` | 3 / 4 | `src/Effect4/Program/Eff.lean:254`, `:235` |
| `NativeAtom` | 20 | `src/Effect4/Program/NativeAtom.lean:24`; `NativeAtom.all.length = 20` |
| `NativeOp` built-ins | 55 positions (23 declared constructors, eight of them per `FnName`) | `src/Effect4/Program/Native.lean:101`; `NativeOp.all.length = 55` |
| `Ty` | 16 | `src/Effect4/Program/Ty.lean` |
| `TypeReason` | 24 | `src/Effect4/Program/Typing/Blame.lean:28` |
| `PrintRefusal` | 4 | `src/Effect4/Codegen/Print.lean:41` |
| `ReadRefusal` | 8 | `src/Effect4/Codegen/Read.lean:44` |
| `AdmitRefusal` | 6 (+ `TableRefusal` 2) | `src/Effect4/Program/Admission.lean:69`, `src/Effect4/Program/Native.lean:349` |

Family sizes 25 / 6 / 16 / 10 were **compiled** off the derived shapes (`EffShape`, `StmtShape`,
`ActionTermShape`, `LayerTermShape`), not counted by eye; `(20, 55, 25)` likewise.

**The brief is right** that `Decision` is `bool | option | tag` and that `NativeOp` holds Ref,
Deferred, Scope, `sleep`, `clockNow` and `external`. **The brief undercounts** nothing I found.

## 2. The lanes, and what each one actually compares

| Lane | Target | Programs | Compares |
| --- | --- | --- | --- |
| `check-truth` | rc.112 | 36 hand programs (`harness/truth/Truth.lean:364`), all well typed | exit, reduced schedule, `runSyncExit`, plus `tsc --noEmit` over the printed modules |
| `check-corpus` | rc.112 | 400 generated (`Test/Program/Gen.lean`), **127 typed**, of which 121 agree and 6 differ | run outcome, schedule, sync exit, inferred type per column |
| `check-tsdiag` | tsgo 7.0.0-dev.20260629.1 | 363 printed programs | the checker's located refusal against TypeScript's diagnostics — types only, nothing runs |
| `check-target` | tsgo | the same 36 names, hand-listed again in `Test/fixtures/target/selection.json` | answer/error/requirement columns of the printed modules |
| `check-schema-codec` | rc.112 `Schema.toCodecJson` | the contract's `Ty` cases | codec JSON |
| `check-ts-reader` | our own Lean reader | corpus `.ts` + the 36 truth modules | the TypeScript reader's JSON byte-identical to Lean's oracle |
| `check-ocaml` | our own Lean bytes | the eff goldens, the engine's own tests, the three-engine differential over the printed corpus | wire bytes, engine behaviour |
| `check-compat` | a promoted baseline | the reflected families and retained byte vectors | constructor shapes by wire tag |
| `check-census` | rc.112 source bytes | 139 census rows | the census↔`RuntimeCoverage.lean` join |
| `make check` (`Test/**`) | ourselves | 106 `.lean` contract modules | `#guard`s and the axiom gate |
| `src/Effect4/Laws/**` | ourselves | 144 `.lean` modules | the theorems |

Two facts about that table matter and are easy to miss.

- **`check-compat` is in `CHECKS` but in no aggregate.** `check`, `check-host` and `check-full`
  do not list it (read, `Makefile:241-243` against `:236-237`). It is green (stamped,
  `docs/STATE.md` item 6) and it runs only when someone types its name.
- **Only two lanes run a *program* on rc.112.** `check-tsdiag` and `check-target` are
  type-level; `check-schema-codec` does execute rc.112 (`Schema.toCodecJson`, with a
  `effectPackage.version === "4.0.0-rc.112"` assert at `harness/truth/schema-codec/check.ts:6`)
  but on `Ty` codec values, not on `Eff` programs; `check-ts-reader`, `check-ocaml`,
  `check-compat` and `make check` compare us with ourselves.

## 3. The matrix

Cells: **T** = in the truth corpus (compared with rc.112, run and typed); **C**`n` = typed in
`n` of the 400 generated programs (compared with rc.112); **c**`n` = present but only in
*untyped* generated programs (printed and type-checked by tsgo, never run against rc.112);
**—** = absent from both. All counts **compiled** by a census over the two corpora
(`scoutF/census.lean`, `scoutF/truthcensus.lean`), one row per program, presence not occurrence.

### 3.1 `Eff` (25)

| Constructor | rc.112 truth | rc.112 corpus | `Straight` | `Looped` |
| --- | --- | --- | --- | --- |
| `succeed` | T (27) | C22 | yes | yes |
| `fail` | T (10) | C23 | yes | yes |
| `failCause` | T (4) | C17 | yes | yes |
| `sync` | **—** | C19 | yes | yes |
| `suspend` | **—** | C10 | yes | yes |
| `perform` | T (17) | C1 (`deferredAwait` only) | sync rows only | sync rows only |
| `bind` | T (25) | C6 | yes | yes |
| `gen` | T (1) | C7 | no | no |
| `catchCause` | T (3) | C1 | yes | yes |
| `matchCause` | **—** | C2 | yes | yes |
| `onExit` | **—** | C1 | yes | yes |
| `exit` | T (4) | C8 | yes | yes |
| `uninterruptible` | **—** | C4 | no | no |
| `interruptible` | **—** | C8 | no | no |
| `yieldNow` | T (2) | C22 | no | no |
| `awaitFiber` | T (3, `.awaitValue` only) | c53 | no | no |
| `withFiber` | T (4) | C38 | no | no |
| `scoped` | T (9) | C9 | no | no |
| `acquireRelease` | T (9) | c35 | no | no |
| `provideLayer` | T (7, `isLocal = false` only) | C2 (`isLocal = true` only) | no | no |
| `service` | T (7) | C17 | no | no |
| `provideService` | T (4) | C5 | no | no |
| `catchIf` | T (7) | c38 | no | no |
| `select` | T (4, `.bool` only) | C1 (`.bool` only) | yes | yes |
| `iterate` | T (1, `none` annotation, `unit` result) | c44 | no | yes |

Six constructors have **no** rc.112 truth-corpus program: `sync`, `suspend`, `matchCause`,
`onExit`, `uninterruptible`, `interruptible`. All six are carried only by the generated corpus,
where each has between 1 and 19 typed programs — thin for `onExit` (1), `catchCause` (1),
`matchCause` (2), `select` (1), `provideLayer` (2).

Four are compared with rc.112 nowhere: `awaitFiber`, `acquireRelease`, `catchIf`, `iterate` are
each **either** in the truth corpus **or** typed in the generated corpus, never both — and
`awaitFiber` in the generated corpus and `iterate`/`catchIf`/`acquireRelease` there are all
untyped, so those four rest entirely on the truth corpus's 3, 9, 7 and 1 programs.

### 3.2 `ActionTerm` (16)

| Action | rc.112 truth | rc.112 corpus | Note |
| --- | --- | --- | --- |
| `fork` | T (3) | C20 | |
| `forkIn` | — | c36 | never typed |
| `forkScoped` | — | C10 | |
| `runIn` | — | c3 | never typed |
| `interrupt` | — | c13 | never typed |
| `interruptScoped` | — | — | printer refuses (`internalAction`), by design |
| `interruptAll` (no interruptor) | — | c8 | never typed |
| `interruptAll` (with interruptor) | — | c10 | never typed |
| `awaitAll` | — | c5 | never typed |
| `awaitAllFailFast` | — | — | printer refuses, by design |
| `snapshotChildren` | — | — | printer refuses, by design |
| `awaitNewChildren` | — | — | printer refuses, by design |
| `raceAll` | — | C1 | one typed program |
| `setContext` | — | — | printer refuses, by design |
| `getContext` | — | C7 | |
| `getId` | — | C7 | six of these are the DI-73 disagreements |
| `closeScope` | T (1) | c9 | one truth program; never typed in the corpus |

Five actions cannot be compared because the printer refuses them (that is a design choice with a
guard, `Test/Program/Gen.lean` `refusedDrawn`/`refusedUnknown`). Of the eleven printable actions,
**five are never typed anywhere** (`forkIn`, `runIn`, `interrupt`, `interruptAll` in both forms,
`awaitAll`) and one (`closeScope`) rests on a single truth program.

### 3.3 `LayerTerm` (10), `Stmt` (6), `CauseTerm`, `Decision`, `Lit`

| Item | rc.112 truth | rc.112 corpus |
| --- | --- | --- |
| `layer.succeed` | — | C2 |
| `layer.effect` | T (7) | c7 |
| `layer.effectDiscard` | — | c10 |
| `layer.provide` | — | C1 |
| `layer.provideMerge` | — | C1 |
| `layer.merge` | T (2) | C1 |
| `layer.fresh` | — | C1 |
| `layer.orDie` | T (2) | C1 |
| `layer.ref` | T (1, `pDiamond`) | c4 |
| `layer.mergeAll` | T (1) | C1 |
| `stmt.bindYield` | T (1) | C1 |
| `stmt.yieldDiscard` | — | C3 |
| `stmt.ret` | T (1) | C6 |
| `stmt.ifElse` | T (1) | c7 |
| `stmt.whileTrue` | — | c6 |
| `stmt.breakLoop` | — | c13 |
| `cause.fail` / `.die` / `.interrupt none` / `.both` | T (4 / 2 / 1 / 4) | C7 / C4 / C5 / C1 |
| `cause.interrupt (some who)` | **—** | C1 |
| `decision.bool` | T (4) | C1 |
| `decision.option` | **—** | **—** |
| `decision.tag` | **—** | **—** |
| `lit.unit` / `.nat` / `.bool` / `.str` | T all four | C all four |

Six layer forms are absent from the truth corpus and carried by exactly one typed generated
program each. Three statement forms (`ifElse`, `whileTrue`, `breakLoop`) are never typed in the
generated corpus; `ifElse` has one truth program, the other two have none.

**`select … .option` and `select … .tag` occur in no program of either corpus.** The four truth
programs named `pOptionSome`, `pOptionNone`, `pTagHit`, `pTagMiss` use `select … .bool` over the
atoms `isSome`/`getOrElse`/`tagIs`, not the option or tag decision (compiled: the census finds
`decision.bool` in four truth programs and no `decision.option` or `decision.tag` anywhere; read:
`harness/truth/corpus.json` holds no `optionCase(` or `caseTag(` in any `expr`, `decl` or
`declInferred`, and four programs hold a ternary).

### 3.4 Native rows (55 built-ins plus `external`)

| Row | rc.112 truth | rc.112 corpus |
| --- | --- | --- |
| `refMake`, `refGet`, `refSet`, `refUpdate` | T (8, 7, 3, 5) | never typed |
| `refGetAndSet`, `refSetAndGet`, `refGetAndUpdate`, `refUpdateAndGet`, `refUpdateSome`, `refGetAndUpdateSome`, `refUpdateSomeAndGet`, `refModify`, `refModifySome` (× 5 `FnName`s where applicable) | **—** | never typed |
| `deferredMake`, `deferredAwait` | T (1, 1) | `deferredAwait` C1 |
| `deferredIsDone`, `deferredPoll`, `deferredSucceed`, `deferredFail` | **—** | never typed |
| `scopeMake .parallel` | T (1) | never typed |
| `scopeMake .sequential` | **—** | never typed |
| `sleep` | **—** | **never drawn at all** |
| `clockNow` | **—** | **never drawn at all** |
| `external` | T (7, with tapes) | not drawn (the generated corpus runs at the empty table) |

Eight of the 23 declared row families reach rc.112, all through the truth corpus; the generated
corpus contributes exactly one typed row use in 400 programs (`deferredAwait`). At *position*
granularity it is seven of `NativeOp.all`'s 55: `refUpdate` occurs only at `FnName.incr` (read,
`src/Effect4/Program/Wire.lean:93`, `harness/truth/Truth.lean:143`, `:157` — the only three
`refUpdate` sites in either corpus), and `scopeMake` only at `.parallel`. The other four
`FnName`s (`double`, `zeroWhenPositive`, `noChange`, `takeAndBump`) are carried by no row that
runs. **The timer rows are drawn by no corpus.** `sleep` and `clockNow` appear only in Lean-side contracts
(`Test/Api/TestClockContract.lean`, `Test/Api/FrontierContract.lean`,
`Test/Program/CompileContract.lean`, `Test/Program/InvocationContract.lean`,
`Test/Machine/Runtime/SchedulerCoreContract.lean`, `Test/Codegen/ReadContract.lean`,
`Test/Api/ExternalContract.lean`) and in the OCaml engine's own tests
(`ocaml/engine/test/test_timers.ml`, `bench_timers.ml`, `test_host.ml`). Every "sleep" in
`harness/truth/run-truth.ts` is a JavaScript `setTimeout`, not `Effect.sleep` (read, `:490`,
`:565`, `:587`, `:605`).

### 3.5 Atoms (20)

Compared with rc.112 (present in a program that runs there): `succ`, `add`, `isZero`, `eq`,
`pair`, `strings`, `causeError`, `getOrElse`, `isSome`, `tagIs` — **10 of 20**.

Never compared with rc.112: `pred`, `not`, `lt`, `fst`, `snd`, `causeIsFail`, `causeIsDie`,
`causeIsInterrupt`, `or`, `and` — **10 of 20**. Of those, six (`pred`, `not`, `lt`, `fst`, `snd`
and `eq`'s ill-typed forms) are drawn by the generator but survive into no typed program;
`causeIsFail`, `causeIsDie`, `causeIsInterrupt`, `or`, `and` are not in the generator's
`atoms` list at all (read, `Test/Program/Gen.lean:84`: ten names, not twenty).

### 3.6 `Ty` (16), in the answer and error columns of typed programs

Compiled over both corpora: `never`, `unit`, `nat`, `bool`, `string`, `handle`, `prod`,
`exitOf`, `fiberOf`, `union`, `lit` occur. **`int`, `option`, `list`, `except`, `causeOf` occur
in no typed program's answer or error column** in either lane. `int` is banned by admission
(`AdmitRefusal.uninhabited`, DI-67, DI-92); `causeOf` is only ever a binder type (read,
`src/Effect4/Program/Typing.lean:313`, `:338`); `option` and `list` arise from `causeError`
and `strings` inside terms, not as columns; `except` is produced only by a derived form
(`src/Effect4/Program/Derived.lean:1135`) and `Ty.result`.

## 4. Finding 1 — alphabet items with no rc.112 comparison, ranked by whether we claim to match

The project's claim is stated per constructor: `arms` in `src/Effect4/Program/Eff.lean:524-549`
gives every `Eff` constructor its rc.112 combinator and its `internal/effect.ts` line, and
`NativeOp.row` gives every native row its `vendor/effect-4.0.0-rc.112/src/...` citation. So for
every item below the tree asserts an rc.112 counterpart by file and line. That is the gap that
matters; there is no item in the `Eff`, native or action alphabet that is "ours alone".

The ranking mixes two grades. Items whose *only* evidence is a generated program are listed
because nobody chose that program: it types by accident and exercises the constructor's
interesting behaviour only by accident too. Items with no program at all are listed first.

**Rank 1 — cited to rc.112, and either never run against it or run only by accident.**

1. **The timer rows, `sleep` and `clockNow`.** Cited to `internal/effect.ts:6114-6116` and
   `:6118`, transcribing `ClockImpl.sleepMillis`. Drawn by no corpus, in no truth program. The
   logical clock, the deadline ordering and the `0`-millis-is-`yieldNow` rule
   (`src/Effect4/Program/Native.lean:122-128`) are asserted about rc.112 and tested only against
   ourselves. Highest risk: a timer is the one row whose semantics is a schedule, and schedules
   are exactly what `check-truth` compares.
2. **`select … .option` and `select … .tag`.** Cited to the prelude's `optionCase`/`caseTag`
   (`src/Effect4/Codegen/Print.lean` `Head.optionCase`, `.caseTag`). In no program of either
   corpus. The one artefact that would test the narrowing, `harness/truth/select-controls.ts`,
   is compiled by no lane (§7). `Decision.decide_typed` is proved
   (`src/Effect4/Laws/Program/Decision.lean`) — that is our semantics, not TypeScript's
   narrowing of `readonly ["A", number] | readonly ["B", string]`.
3. **`awaitFiber .joinEffect`.** `Fiber.join` versus `Fiber.await` is cited to
   `internal/effect.ts:5291, :5304` as two different rc.112 primitives. Only `.awaitValue`
   appears in the truth corpus; `.joinEffect` types in no generated program. The generator has a
   hand guard that *both* modes are drawn (`Test/Program/Gen.lean`, `coversEff`), and both are —
   in untyped programs, which never run.
4. **`acquireRelease` with a failing release.** The three truth programs (`pAcquire`,
   `pAcquireClosed`, `pAcquireHandle`) release through `refSet`, whose error column is `never`
   (read, `src/Effect4/Program/Native.lean:177`). rc.112's `acquireRelease` is
   `uninterruptible + onExit over the scope`; what a failing finalizer does to the exit is not
   tested on either face.
5. **`iterate` with a non-`unit` result, and with a `some` annotation.** `pLoop`'s result term is
   `.lit .unit` (read, `src/Effect4/Program/Wire.lean:90-93`); the generator's four loop draws
   answer `unit` (stamped, `docs/STATE.md` item 6). The census finds `iterate.ann.none` and never
   `iterate.ann.some` in either corpus. The printed shape is `Effect.map(Effect.whileLoop(…), …)`
   — the `map` is exactly what a non-`unit` result exercises, and it is exercised by one program
   whose result is `unit`.
6. **`matchCause`, `onExit`, `uninterruptible`, `interruptible`.** Cited to
   `internal/effect.ts:2645`, `:4006`, `:4302-4310`, `:4331-4352`. Absent from the truth corpus;
   carried by 2, 1, 4 and 8 typed generated programs. `uninterruptible`/`interruptible` are mask
   regions, and a mask's whole content is *when an interrupt is noticed* — the generated corpus
   compares a run and a schedule, so it does touch this, but with no program written to make the
   mask matter.
7. **`sync` and `suspend`.** 19 and 10 typed generated programs, no truth program. Low semantic
   risk (both are in `Straight`, both proved against the meaning), but they are the two most
   common constructors in real Effect code and no hand program uses them.
8. **`forkIn`, `runIn`, `interrupt`, `interruptAll` (both forms), `awaitAll`.** Cited as
   `WithFiberAction`s. Never typed anywhere, never in the truth corpus. `interruptAll` with and
   without an interruptor is guarded as *drawn* by `coversAction` — again, only in untyped
   programs.
9. **Thirteen `Ref`/`Deferred` row families with no program, plus `scopeMake .sequential` and
   four of the five `FnName`s.** Nine read-modify-write rows (`refGetAndSet`, `refSetAndGet`,
   `refGetAndUpdate`, `refUpdateAndGet`, `refUpdateSome`, `refGetAndUpdateSome`,
   `refUpdateSomeAndGet`, `refModify`, `refModifySome`) and four `Deferred` rows
   (`deferredIsDone`, `deferredPoll`, `deferredSucceed`, `deferredFail`). Each cites a `Ref.ts`
   or `Deferred.ts` line range. The store semantics they claim (`refModifySome`'s partial
   function, `refUpdateSomeAndGet`'s answer, `deferredSucceed`'s "did it win" boolean) is tested
   only by our own `Test/Machine/Runtime/StoresLawsContract.lean`.
10. **Ten atoms.** `pred`, `not`, `lt`, `fst`, `snd`, `causeIsFail`, `causeIsDie`,
    `causeIsInterrupt`, `or`, `and`. These are *prelude* functions we ship
    (`harness/truth/prelude.ts`), so "matching Effect" means matching our own prelude — lower
    risk than 1-9, but `causeIsFail`/`causeIsDie`/`causeIsInterrupt` read an rc.112 `Cause`, and
    that reading is a claim about rc.112's cause representation.

### 4.1 Explicitly, on the eleven items the brief named

Four of them are covered and the brief should stop worrying about them.

| Item | Verdict |
| --- | --- |
| `iterate` with a non-`unit` result | **not compared.** The one truth loop (`pLoop`) results in `.lit .unit`; the generator's four loop draws answer `unit`. |
| `iterate` with a `some` annotation | **not compared, and not drawn at all.** Counted: `iterate.ann.some` occurs in zero programs of either corpus. It landed yesterday with DI-91. |
| `select … .option` | **not compared, and not drawn at all.** The `optionCase` head is emitted by no corpus program. |
| `select … .tag` | **not compared, and not drawn at all.** The `caseTag` head is emitted by no corpus program; the four `pTag*`/`pOption*` truth programs use `select … .bool` over the `tagIs`/`isSome`/`getOrElse` atoms. |
| `catchIf` with a tag test | **covered.** Seven truth programs (`pCatchIfHit`, `pCatchIfMiss`, `pCatchIfRetained`, `pTagHit`, `pTagMiss`, `pTagTwoFail`, and `pCatchError`), three of them with `tagIs` in the test, and their retained-column types are pinned in `harness/truth/Truth.lean:786-800`. Thin but chosen, and it is the DI-39/DI-82 residual rule's evidence. |
| `acquireRelease` with a failing release | **not compared.** Three truth programs; every release is `refSet`, whose error column is `never`. |
| `provideLayer` local versus shared | **both compared, by disjoint lanes.** `isLocal = false` only in the truth corpus (five programs); `isLocal = true` only in the generated corpus (two typed programs). Neither form has a chosen program that exercises the memo map's sharing, except `pDiamond`, which tests `layer.ref` sharing under `isLocal = false`. |
| `awaitFiber` both modes | **half.** `.awaitValue` in three truth programs; `.joinEffect` in no typed program anywhere. |
| `withFiber` actions (`forkIn`, `forkScoped`, `runIn`, `interruptAll` ±, `raceAll`) | **`forkScoped` covered** (ten typed generated programs) and **`raceAll` by one**; `forkIn`, `runIn`, `interruptAll` in both forms, `interrupt` and `awaitAll` **never typed anywhere**. |
| `yieldNow` priorities | **covered.** All three priorities the generator draws (0, 1, 2) are typed: 4, 10 and 8 generated programs; the truth corpus has priority 0 twice. |
| the timer rows | **not compared.** §3.4. |
| the external rows | **covered.** Seven truth programs with committed tapes (`harness/truth/tapes/*.jsonl`: `pSqlite`, `pKv`, `pSqlFail`, `pSqlCatch`, `pSqlExit`, `pSqlOrDie`, and `pAcquireHandle` through `Host.acquire`/`close`/`read`). Note that `run_eq_ref` explicitly does **not** cover a run with external rows (DI-57), so these rows have host evidence and no internal agreement theorem. |
| every atom on an ill-typed argument | **five of twenty have a red control**; §5. |

**Rank 2 — ours alone, where an internal law or contract is the right test.** `Ty.int` (banned,
`AdmitRefusal.uninhabited`); `layer.ref` as an identity mechanism (DB-12 says rc.112 keys its
memo map on the object, so the *reference* is our encoding of rc.112's sharing — `pDiamond`
tests the sharing, which is the right thing); `Decision` itself as a carrier; the wire tags; the
blame projection. For all of these `#guard`s and theorems are the right instrument and they
exist.

## 5. Finding 2 — refusals with no red control

Counted by grepping the constructor name across `Test/**` and by reading the `reason` column of
`generated/corpus-index.tsv` (363 rows) and `generated/tsdiag-agreement.tsv`.

**`TypeReason` (24). Produced somewhere: 14.**

- By the generated corpus (`generated/corpus-index.tsv` `reason` column): `notFiber` (45),
  `term` (43), `requestNotSubtype` (39), `predicateNotBool` (27), `cause` (20),
  `errorNotAdmitted` (17), `listOfFibersExpected` (11), `valueNotSubtype` (8), `scopeExpected`
  (8), `breakOutsideLoop` (7), `exitExpected` (4).
- By `Test/Program/BlameContract.lean` and nothing else: `returnNotLast` (`:45`), `mergeAllEmpty`
  (`:48`), `referencesIllFormed` (`:51`).

**No red control anywhere — 10 of 24:** `outsideDomain`, `notSelectable`, `stepNotCursor`,
`initialNotCursor`, `natExpected`, `contextExpected`, `snapshotExpected`, `serviceUnknown`,
`layerReference`, `literalOutsideAlphabet`.

Three of those ten are new or newly load-bearing and are the ones I would not leave:
`notSelectable` is `select`'s own refusal (a non-option under `.option`, an untagged column under
`.tag`) and the corpus draws neither decision; `stepNotCursor` and `initialNotCursor` are
`iterate`'s two typing rules, and `initialNotCursor` is the rule DI-91's optional annotation just
created. `outsideDomain` is DI-54's `Signature.dom`, reachable only through a supplied table.
`layerReference` is distinct from `referencesIllFormed` (the latter is the pre-typing
well-formedness refusal, pinned at `BlameContract.lean:51`; the former is the structural refusal
of a bare `.ref` during typing) and only the latter has a control.

**`PrintRefusal` (4). No control: `layerRef`.** `internalAction` is pinned at
`Test/Api/ApiContract.lean:104`, `unsafeName` at `Test/Codegen/PrintContract.lean` (counterexample
`E4-TARGET-NAME-CE-001`), `typeSpelling` at `Test/Codegen/PrintContract.lean:72`. `layerRef` is
produced at `src/Effect4/Codegen/Print.lean:686`, `:694` and
`src/Effect4/Laws/Codegen/Module.lean:97`, and named by no test.

**`ReadRefusal` (8): all eight have controls** in `Test/Codegen/ReadContract.lean` and siblings
(counted: `unknownHead` 5, `unknownIdent` 4, `arity` 13, `binder` 1, `shape` 19, `negative` 3,
`unsupportedStmt` 2, `annotation` 13 mentions across `Test/**`).

**`AdmitRefusal` (6) + `TableRefusal` (2): all eight have controls** (`illTyped` 4,
`duplicateKey` 1, `builtinCollision` 1, `valueRowTrailing` 1, `uninhabited` 8, `notExternal` 5,
`notAsync` 4).

**Per-atom ill-typed controls: 5 of 20.** `Test/Program/NativeAtomContract.lean` has 65 guards,
and `nativeAtomTy "<name>" [...] = none` appears for `succ` (1), `eq` (1), `tagIs` (2), `isSome`
(3), `getOrElse` (5). The other fifteen atoms have no ill-typed-argument control. The generated
corpus produces 43 `term` refusals, which covers the *path* generically but names no atom.

## 6. Finding 3 — what the laws exclude

Three per-constructor families exist and their domains differ. All counted by grepping the
theorem names.

| Family | Covers | What it says |
| --- | --- | --- |
| `denoteR_*` (`src/Effect4/Laws/Program/DenoteR.lean`) | **all 25** constructors (plus `denoteR_straight`, `denoteR_zero`) | the term reference's equation per constructor |
| `intro_*` (`src/Effect4/Laws/Program/Intro/*.lean`) | **all 25** | the compile agrees with the reference at that constructor |
| `meaning_*` (`src/Effect4/Laws/Program/Denote.lean`) | **12**: `succeed`, `fail`, `failCause`, `sync`, `suspend`, `perform`, `bind`, `select`, `exit`, `catchCause`, `matchCause`, `onExit` | the compositional meaning's equation |

So the charter's rule 3 ("no construct without an equation") holds in the `denoteR` sense for the
whole alphabet, and in the *compositional meaning* sense for 12.

**The fragments.** `Straight` (read, `src/Effect4/Program/Fragment.lean:20`) is those 12, with
`perform` admitted only when the row's `kind` is `.sync`. `Looped` (read,
`src/Effect4/Laws/Program/DenoteB.lean:123`) is `Straight` plus `iterate` — **13 of 25**.

**The 12 constructors with no proved agreement between machine and compositional meaning:**
`gen`, `uninterruptible`, `interruptible`, `yieldNow`, `awaitFiber`, `withFiber` (and with it all
16 fiber actions), `scoped`, `acquireRelease`, `provideLayer`, `service`, `provideService`,
`catchIf`. Plus `perform` on every `.async` row — which is `deferredAwait`, `sleep`, and every
supplied external row.

**What "never wrong" covers today.** `meaning_never_wrong` and `meaning_typed`
(`src/Effect4/Laws/Program/MeaningSound.lean`) and `meaningB_never_wrong`/`meaningB_typed`
(`LoopSound.lean`) are stated on `Straight`/`Looped` **at the empty table**;
`TypedProgram.run_soundB` carries them to the machine through `Agreement.loopAgreement`
(stamped, `docs/research/2026-09-16-strict-proof-obligations.md` O9, O12). The whole-alphabet
statement is `run_eq_ref` (read, `src/Effect4/Laws/Program/RuntimeR.lean:197-211`) and its own
docstring says what it is not: *"At the empty table, with no oracle answers (DI-57) … it does not
extend to a run with external rows"*, and it relates the frame machine to our term reference, not
to rc.112. So for the 12 constructors above, "never wrong" today means "the two Lean evaluators
agree", not "the run is type-safe".

**The reader's domain excludes three forms by construction.** `readable` is `false` for
`select … .option`, `select … .tag` (read, `src/Effect4/Codegen/Read.lean:1879-1880`) and for
every `iterate` (read, the `readable` clause). `Test/Codegen/ReadContract.lean:661-672` pins that
the corpus's round-trip refusals are *exactly* the loop-bearing programs. That is a deliberate,
guarded hole that R5 closes — but while it is open, the three forms are outside the reader lane,
the diagnostics lane, the OCaml differential and the printed corpus directory (45 of 410
programs, stamped in `docs/STATE.md` item 6).

## 7. Finding 4 — hand-listed where a table exists (drift)

The generator's *constructor* coverage is exemplary and should be the model: `Test/Program/Gen.lean`
`expected` is built from the derived shapes (`EffShape`, `StmtShape`, `ActionTermShape`,
`LayerTermShape`), so `#guard missing = []` demands every printer-accepted constructor with no
name written in the file, and the two hand exception lists (`refusedActions`, `pendingEffs`) are
themselves guarded against renaming (`refusedUnknown`, `pendingEffsUnknown`). Seven places do
not follow it.

1. **`Test/Program/Gen.lean:84`, `atoms`: ten names of twenty.** `tagIs`, `isSome`, `getOrElse`,
   `strings`, `or`, `and` and the four cause queries are not drawn. The mechanism to make this
   impossible already exists and is proved: `NativeAtom.covers` with `covers_iff`
   (`src/Effect4/Program/NativeAtom.lean:80-90`). It is used only in
   `Test/Program/NativeAtomContract.lean:36-39`, to test itself. One line —
   `#guard NativeAtom.covers (atoms.map Prod.fst)` — would have failed the day `tagIs` landed.
   **This is the single clearest instance of the owner's concern in the tree.**
2. **`Test/Program/Gen.lean:89`, `fns`: a verbatim copy of `Effect4.Program.fnNames`**
   (`src/Effect4/Program/Native.lean:309`). Same five names, two owners, no guard.
3. **No guard demands that the corpus draw every native row.** `NativeOp.all` is the table and
   `NativeOp.all_complete` is proved (`src/Effect4/Codegen/Read.lean:2925`), but nothing states
   "every row occurs in `sample`". Compiled: `sleep`, `clockNow` and `external` occur in no
   generated program, and no check notices.
4. **No guard demands that the corpus draw every `Decision`.** `expected` ranges over node
   families only, and `Decision` is a field, not a node. The two enumerated fields that *are*
   guarded — `awaitFiber`'s mode and `interruptAll`'s interruptor — are guarded by two
   hand-written `coversEff`/`coversAction` calls (`Test/Program/Gen.lean`, the last four
   `#guard`s). When `select` landed with three decisions and `iterate` with an optional
   annotation, no one added the matching pair of lines. Compiled: `.option`, `.tag` and
   `iterate.ann.some` are drawn zero times, silently.
5. **`harness/truth/Truth.lean:364`, `corpus`: 36 hand-listed programs with an identity pin and
   no coverage guard.** `:779-785` pins that the names are unique and that the list is exactly
   those 36 — which is DI-60's shape and catches an accidental edit — but nothing states that
   the list *covers* anything. The generated corpus has `missing = []`; the truth corpus, which
   is the lane that actually runs programs on rc.112, has no analogue. Six `Eff` constructors,
   ten fiber actions, five layer forms, two decisions and 47 native rows are absent from it and
   no check says so. The fix is the same shape as `missing`: a `#guard` over `heads` of the
   truth corpus against the derived shapes, with a named, guarded exception list.
6. **`Test/fixtures/target/selection.json`: the same 36 names again, by hand.** With the
   identity pin at `Truth.lean:780` that is a third and fourth written copy of the truth
   corpus's membership; the JSON one is consumed by `check-target` and `check-corpus` and is
   joined to the Lean list by nothing.
7. **`harness/truth/tsconfig.json:26` includes `select-controls.ts`; no lane compiles it.**
   `scripts/check-truth.py:57-62` reads that config, overrides `files` with absolute paths to
   `run-truth.ts` and `session/*.ts`, writes it into a temporary work directory, and runs `tsc`
   there. The work directory receives `prelude.ts`, `session/` and the freshly generated
   modules — not `select-controls.ts`. A TypeScript `include` glob that matches nothing is
   silently ignored, so the four narrowing controls of `caseTag`/`optionCase` compile nowhere.
   Counted: the string `select-controls` occurs twice in the repository, in that `include` and in
   the file's own header comment.
   The same paragraph covers three test files run by nothing: `harness/truth/catch-if.test.ts`,
   `harness/truth/native-queries.test.ts`, `harness/truth/prelude-inventory.test.ts`. The only
   `bun test` invocations are `cd ts/eff && bun test` (`Makefile:308`), `bun test tools/target`
   (`:341`) and `cd ts/eff && … bun test` in `scripts/check-ingest.sh:35`. None reaches
   `harness/truth`.

Two things that look like drift and are not: `ocaml/eff/test/test_lean_wire.ml`'s
`same_program` list is read from a generated file (`:88-90`), not hard-coded, which answers
DI-52's worry; and `refusedActions` in `Gen.lean` is a hand list with a guard that every name is
a real constructor.

## 8. Finding 5 — known reds, held baselines, and the six differing runs

- **`check-corpus`'s baseline is held, on purpose.** `harness/truth/corpus-results.tsv` is the
  committed expected file; `check-corpus` reports 18 changed rows against it, every one an
  untyped raw program whose loop test is not a Boolean, whose recorded Lean exit moved from a
  silent `success` to the wrong-shape defect (stamped, `docs/STATE.md` item 5). The promotion
  happens once, at the end of the `Eff` series. **The `Eff` series is now closed** — the four
  DI-79 retirements are done and the owner ruled `gen` stays (stamped, `docs/STATE.md` item 6) —
  so this promotion is *due*, and it is the only thing between the corpus lane and a clean run.
- **`make check-tools` is red**, older than S1: `scripts/test-trust-gate.sh` stops on
  `Test/fixtures/trust-gate/expr-equality.lean.txt`, a `String` where the pinned `typescript`
  package wants a `TypeRef` (stamped, `docs/STATE.md` item 6). Pre-existing; also recorded in
  memory as the `typescript` v0.5.0 repin's known red.
- **`check-citations` fails** on an untracked owner document:
  `docs/CAS-IFIED-APIS-AND-SCHEMAS.md:335` cites `src/Effect4/Codegen/Casify.lean`, which does
  not exist (stamped, `docs/STATE.md` item 5). That document is one of the eight untracked
  `docs/*.md` files in `git status`.
- **The six typed corpus runs that differ** (read, `harness/truth/corpus-results.tsv`; registered
  in `harness/truth/corpus-known-differences.md`): `g81`, `g102`, `g144`, `g250`, `g289`, `g313`,
  each listed twice — once under `run differ` and once under `sync differs`. The recorded reason
  for both dimensions is **DI-73**: a fiber id answered as a value (`getId`, or a fiber handle
  from a layer build) is the machine's allocation index on one face and the runtime's counter on
  the other, so `eq(getId, 0)` is `true` here and `false` there and renumbering cannot repair it.
  DI-73 is **open**, its recommendation withdrawn on 2026-09-13 on the corpus audit's
  counterexample. The register also holds three other registered disagreement classes that are
  not run differences: `g38 g183 g276 g352 g123 g390` (`tsc errors`, DI-76(c),
  `Effect.context()`'s inferred requirement), `g50 g89 g290` (`types mismatch-R`, DI-24, printed
  `Context.Service` keys have no nominal identity), `g16 g49 g55 g160 g308 g363`
  (`types mismatch-A`, DI-77, `unit` renders as `void` and the value as `undefined`).
- **The corpus's totals**, read from the committed file: 400 rows, 127 well typed, `run` =
  121 agree / 6 differ / 273 untyped; `types` = 110 agree / 8 refused / 6 mismatch-A /
  3 mismatch-R / 273 untyped; `tsc` = 146 clean / 254 errors; `straight` = 75 of 400.
- **The checker is stricter than tsgo on 28 programs.** `generated/tsdiag-agreement.tsv`:
  `refused-agree` 158, `typed-clean` 134, `refused-unmapped` 42, `refused-silent` 22,
  `refused-gap` 6, `refused-other` 1. The 22 silent and 6 gap rows are programs Lean refuses and
  the host does not complain about; the lane is designed to fail only in the other direction (a
  program Lean types and TypeScript refuses), so these 28 are recorded, not gated.
- **`check-compat` is green and runs in no aggregate target** (§2).

## 9. The ranked gap list

Ranked by the brief's rule: a gap where we *claim* to match Effect and do not test it ranks
first, then a red control that is missing for a rule that is new or load-bearing, then coverage
that is thin rather than absent.

1. **The timer rows (`sleep`, `clockNow`) reach no corpus.** Cited to two rc.112 line ranges,
   claimed to transcribe `ClockImpl.sleepMillis`, and compared with rc.112 nowhere.
2. **`select … .option` and `select … .tag` reach no corpus, and their one control file is dead.**
   Two of three decisions; `caseTag`'s narrowing is the reason the prelude exists.
3. **`iterate` has one rc.112 program, with a `unit` result and no annotation.** The constructor
   landed today; the printed `Effect.map` head landed with it; the annotation landed with DI-91.
4. **The six never-typed printable fiber actions** (`forkIn`, `runIn`, `interrupt`,
   `interruptAll` with and without an interruptor, `awaitAll`) and `closeScope`'s single truth
   program.
5. **`awaitFiber .joinEffect`, `acquireRelease` with a failing release, `provideLayer` local vs
   shared.** Each is a documented behavioural difference in rc.112 and each has one side tested:
   `.awaitValue` but not `.joinEffect`; a `never`-erroring release but not a failing one;
   `isLocal = false` only in the truth corpus and `isLocal = true` only in two generated
   programs, so neither form has a chosen program that shows what the memo map does.
6. **The six constructors whose only rc.112 evidence is a generated program** (`sync`,
   `suspend`, `matchCause`, `onExit`, `uninterruptible`, `interruptible`). They are covered, but
   by programs nobody wrote: `uninterruptible`/`interruptible` are mask regions whose whole
   content is *when an interrupt is noticed*, and no program in the tree was written to make a
   mask matter.
7. **Ten of 24 `TypeReason`s have no red control**, three of them (`notSelectable`,
   `stepNotCursor`, `initialNotCursor`) belonging to the two constructors that just landed.
8. **Fifteen of the 23 native row families and ten of the 20 atoms never reach rc.112.**
9. **`PrintRefusal.layerRef` has no control**; fifteen atoms have no ill-typed-argument control.
10. **The truth corpus has no coverage guard**, so gaps 1 to 6 will re-open silently after any
    alphabet change.
11. **The drift list of §7**, of which item 1 (`atoms`) and item 4 (enumerated fields) are the
    two that are already wrong today.

---

# Part 2 — the close-out list for the language foundations

## 10. What "foundations closed" means, from the record

Five lines. Each rests on one sentence of the record, quoted.

1. **The alphabet is closed: no `Eff`, `Stmt`, `ActionTerm` or `LayerTerm` constructor is added
   or retired again without a wire-tag migration.**
   *"The four retirements of DI-79 are done, and the owner ruled on 2026-09-17 that `gen` stays
   (with `Stmt` and `Stmts`), so the alphabet is settled: the series closes with the one corpus
   baseline promotion"* — `docs/STATE.md`, "Next, in order" item 6.

2. **Both directions of the boundary cover that alphabet off one table: the printer emits every
   constructor and `readable` accepts every image it emits.**
   *"`readable` keeps its name and its domain, guarded by a Boolean equality against today's
   definition; `Read.lean` comes down to `readable` and the table; `Forms.all` becomes rows of
   the same table and its nineteen guards become generated `rfl`s"* — `docs/STATE.md` item 7.

3. **One typing certificate is the input of every face.**
   *"`Api.check` answers the certificate or the located refusal and is total by
   `Api.explain_none_iff`; `Typed` carries a program with its certificate into `run`, `replay`,
   `runSync`, `print`, `emit` and `bytes`"* — `docs/STATE.md`, the DI-86 landing paragraph.

4. **Safety is a per-constructor invariant, not a per-fragment theorem, so a new constructor
   adds lemmas and re-proves nothing.**
   *"The strict form of 'prove safety for the fragment' is therefore not a fragment theorem but
   the constructor lemmas of `typedState_step` (D5) … state the invariant first, then never
   prove safety per fragment again."* —
   `docs/research/2026-09-16-strict-proof-obligations.md` §4.

5. **The evidence is honest about its own domain: nothing claimed about rc.112 rests on a lane
   that does not run it, and no baseline is held.**
   *"Finite checks are evidence, never proofs. A `#guard`, a lane run or a host differential may
   accompany a theorem or mark what is not yet proved; it never stands where a statement about
   all programs is claimed."* — `docs/research/2026-09-16-core-goals-and-end-state.md` §10,
   rule 1; with *"The baseline is not promoted: it moves once, at the series' end"* —
   `docs/STATE.md` item 5.

Lines 1 and 3 are true today. Line 2 is false for three forms (`select … .option`, `.tag`,
every `iterate`). Line 4 is false: D5 is a definition to freeze, not a definition in the tree
(O9 is proved fragment-wise and the note says so). Line 5 is false on both halves — §4 and §8
of this note.

## 11. What remains, in order

Sizes are my estimate against the file sizes and the packets' own step lists, marked
**inferred**. "Blocks" and "blocked by" are read off `docs/STATE.md` and the packets.

| # | Item | Size | Blocks | Blocked by | Ruling owed |
| --- | --- | --- | --- | --- | --- |
| 1 | **Promote the corpus baseline** (`make gen-corpus-results`) | minutes plus one corpus lane run | a clean `check-host`; every later change's ability to see a real corpus regression | nothing — the `Eff` series closed today | none; STATE item 6 already commits to it |
| 2 | **R4.1–R4.3**: `Template.lean`, `Templates.lean`, `printT = print` then `print := printT` | days (728 lines replaced; one engine lemma "owed and not yet probed") | R5, R6 | nothing | none (DI-91 ruled) |
| 3 | **R5.1–R5.3**: `readT`, the two laws, `iterate` read | days (3,504 lines replaced) | 45 corpus programs returning to four lanes; `holdsLoop` returning to a plain guard; `select … .option`/`.tag` becoming readable; the reader-as-`Eff` demonstration; R6 | R4 | none |
| 4 | **R6**: the table exported, `ts/eff/read.ts` replaced by one matcher | a day to days | ends the three-reader drift; cancels DI-88's LCNF-to-TypeScript reader backend | R5 | none |
| 5 | **D5 stated** (the typed-state invariant) and its first constructor lemmas | a day to state; days to prove out | O9 past the fragment, O11, S8b, and line 4 of §10 | nothing — *"the invariant can be written against today's machine; its first two constructor lemmas are `Progress.lean`'s"* | none |
| 6 | **The truth-corpus coverage guard**, in the shape of `Gen.lean`'s `missing` | hours | line 5 of §10; makes gaps 1, 2, 4, 5 of §9 impossible to re-open silently | nothing | none |
| 7 | **The four missing rc.112 programs**: a timer program, a `select … .option` and a `select … .tag` program, an `awaitFiber .joinEffect` program, an `acquireRelease` with a failing release, an `iterate` with a non-`unit` result | a day (each needs its schedule or tape expectation) | §9 ranks 1, 2, 3, 5, 6 | the *round-trip* half of `.option`/`.tag` waits on R5; the *run* half does not — the printer already emits `optionCase`/`caseTag` | none |
| 8 | **The typed-idiom generator family** (`docs/research/2026-09-16-testing-corpus-coverage.md` §4) | a day (~150 Lean lines, one new index family) | the 47 never-typed native rows, five fiber actions, three statement forms and ten atoms reaching rc.112 | nothing | none; DI-60's count-pin rule already governs it |
| 9 | **The missing red controls**: ten `TypeReason`s, `PrintRefusal.layerRef`, fifteen per-atom ill-typed guards | hours | §9 ranks 7 and 9 | `outsideDomain` needs a supplied table refused by `Signature.dom`; the rest are one `#guard` each | none |
| 10 | **The drift repairs of §7**: the atom guard, `fns` as one owner, a row-coverage guard, the enumerated-field guards, `select-controls.ts` copied into the work directory, the three orphan `.test.ts` files wired or deleted | hours | line 5 of §10 | nothing | one: delete or wire the three orphan test files |
| 11 | **DI-73** — is a fiber id a value? | a ruling, then hours | the six corpus rows that differ; the only recorded run disagreement with rc.112 | **owner ruling**; the recommendation was withdrawn 2026-09-13 on the corpus audit's counterexample | **yes** |
| 12 | **`check-compat` into an aggregate** | one line | nothing; it closes the Makefile's own stated condition, which S1 satisfied | nothing | none |
| 13 | **`make check-tools`'s red fixture** (`Test/fixtures/trust-gate/expr-equality.lean.txt`: a `String` where the pinned `typescript` package wants a `TypeRef`) | hours | `check-full` | nothing | none |
| 14 | **`check-citations`'s dangling citation** (`docs/CAS-IFIED-APIS-AND-SCHEMAS.md:335` → `src/Effect4/Codegen/Casify.lean`, absent) | minutes | `check-host` | nothing | one: is that untracked owner document staying? |
| 15 | **M2's first slice**: R8 (the Effect module surface read from the pinned package) then R7 (the schema printer) | days+ | DI-89's generated package rows; the rest of M2 | STATE's order puts it after R4–R6 | the generation medium's seven questions are answered "as recommended", and the layout note §6 lists what changes on the ground — worth a confirmation before R8 starts |

Items 1, 6, 9, 10, 12, 13, 14 are all of a day's work together and none is blocked. Items 2–4
are the only long line, and 5 can run beside them in a separate worktree (it touches `Laws` and
`Machine`, not `Codegen`).

## 12. What can be cut or deferred, and which claim it does not weaken

The two claims to protect: **"any Effect code the profile covers reads into `Eff`; coverage
grows by data"** (`docs/STATE.md`, "What this is") and **"a well-typed program's run never
reaches a wrong-shape arm"** (O9).

**Safe to defer.**

- **R1–R3 (`Doc`, `Tree`, spans, blame-to-code).** These position a diagnostic; neither claim is
  about position. The record already makes them a parallel lane (`docs/STATE.md`: "the redesign
  lives on the surface obligations and touches none of the semantic ones"). The one thing they
  block is R3, "the missing third of the S9a agent unlock" — that is an unlock, not a
  foundation.
- **The five printer-refused fiber actions.** They cannot print, so they cannot be compared, and
  the refusal is guarded by name (`refusedDrawn`, `refusedUnknown`). No rc.112 evidence is owed.
- **`Ty.option`, `.list`, `.except`, `.causeOf` as program columns.** `causeOf` is only ever a
  binder type; `except` only a derived form's answer. No corpus program is owed.
- **The foreign-style product's 11,520 files** (`check-ingest`, nightly). The 2026-09-16 note
  measured that a pairwise covering array keeps the detection power. Cutting it changes a
  nightly's size, not either claim.
- **`e4_program.ml`, the OCaml hand translation.** The owner's rule is that it goes when the
  program alphabet is declared once by the codegen API. Keeping it weakens "one machine, three
  faces", not the two claims above.
- **The schema lanes and DI-08.** Outside the language foundations.
- **R11, the two-dimensional layout algebras, the `eff { … }` macro.** Already deferred with a
  reason in `docs/STATE.md`.

**Not safe to cut.**

- **R5.** While it is open the reader refuses every loop, so "any Effect code the profile covers
  reads into `Eff`" is false for the construct the language made primitive today. This is the
  one item where deferring costs the first claim outright.
- **The corpus baseline promotion (item 1).** A held baseline means `check-corpus` reports 18
  known changed rows and cannot show a new one; "coverage grows by data" rests on that lane
  being able to say no.
- **The `select … .option`/`.tag` evidence (item 7).** `Decision` exists so that the narrowing
  is the host's; nothing tests the host's narrowing today.
- **D5 (item 5).** Without it, O9 is re-proved per fragment, and the 12 constructors of §6 stay
  outside the second claim indefinitely.

## 13. The three cheapest tests that would most raise confidence now

Each fails today. Each is small. Each closes a whole class rather than one case.

1. **One line in `Test/Program/Gen.lean`:**
   `#guard NativeAtom.covers (atoms.map Prod.fst)`.
   The predicate and its characterisation (`NativeAtom.covers_iff`) are already proved
   (`src/Effect4/Program/NativeAtom.lean:80-90`) and already used to test themselves
   (`Test/Program/NativeAtomContract.lean:36-39`). The guard fails today and names the ten
   missing atoms. Widening `atoms` to all twenty with their arities is about ten more lines, and
   it puts `tagIs`, `isSome`, `getOrElse`, `strings`, `or`, `and` and the four cause queries into
   the printed corpus, the reader lane, the diagnostics lane and the OCaml differential at once.
   *Cost: about a dozen lines. Closes: §9 rank 8 (the atom half) and §7 item 1 permanently.*

2. **A coverage guard for the truth corpus**, in the exact shape of `Gen.lean`'s
   `missing = []`: `heads` over `OCaml5.Truth.corpus`, `casesOf` over the four derived shapes, a
   named exception list guarded against renaming, one `#guard`. A `#guard` in
   `harness/truth/Truth.lean` is elaborated by `lake env lean --run`, which is what both
   `make gen-truth` and `scripts/check-truth.py` invoke, so the guard runs in `check-truth`
   without a new lane, beside the 77 `#guard`s already there. It fails today naming six `Eff`
   constructors, ten fiber actions, five layer forms, two decisions and the loop annotation.
   *Cost: about twenty lines, all of them copied from `Gen.lean`'s `Coverage` section. Closes:
   §7 item 5, and it is what makes line 5 of §10 checkable rather than asserted.*

3. **Ten `#guard`s in `Test/Program/BlameContract.lean`**, two lines each, for the ten
   `TypeReason`s with no red control: `outsideDomain`, `notSelectable`, `stepNotCursor`,
   `initialNotCursor`, `natExpected`, `contextExpected`, `snapshotExpected`, `serviceUnknown`,
   `layerReference`, `literalOutsideAlphabet`. Three of them (`notSelectable`, `stepNotCursor`,
   `initialNotCursor`) are the rules `select` and `iterate` brought in this week, and
   `initialNotCursor` is the rule DI-91's optional annotation created yesterday. The file's
   existing guards are the template
   (`#guard Api.explain (.select (.lit (.nat 1)) .bool …) = some ⟨[], .predicateNotBool .nat⟩`).
   *Cost: about twenty lines. Closes: §9 rank 7.*

Fourth, if a fourth is wanted, and cheaper than all three: one `shutil.copyfile` in
`scripts/check-truth.py` beside the existing `prelude.ts` copy, so that
`harness/truth/select-controls.ts` lands in the work directory and the `include` in
`harness/truth/tsconfig.json` stops matching nothing. That is the `caseTag`/`optionCase`
narrowing evidence, already written, currently compiled nowhere.

## 14. Where this brief is wrong against the tree

- **"the runtime coverage census … 97 behaviour rows with witnesses".** Counted:
  `Test/Audit/RuntimeCoverage.lean` holds **137** rows — 135 in the denominator (two
  `targetOnly` excluded), of which 133 `green`, 2 `partial` (`op.Failure`,
  `layer.launch-holds-scope`), 0 `absent`; `generated/effect-runtime-census.tsv` holds **139**
  data rows. 97 is the figure in the memory note, not the tree.
- **"`generated/corpus-index.tsv` … 400 programs".** It holds **363** rows: the 45 loop-bearing
  programs are out of the printed corpus until R5, and the 8 wire-corpus programs are in.
  `generated/tsdiag-agreement.tsv` likewise holds 363.
- **"`Test/Program/Gen.lean`, 400 programs"** is right, and **"127 of 400 typed"** is still
  exactly right today (compiled), after `branch`, `whileLoop`, `callback` and `yieldError`
  retired and `select` and `iterate` landed.
- **"the session/keyed/timer harnesses (`harness/truth/session/*`)".** `harness/truth/session/`
  holds `Keyed.lean`, `Session.lean` and four `.ts` files; it is the keyed-protocol lane
  (`check-host-protocol`, in `check-full` only) and the session sources type-checked by
  `check-truth`. There is no timer harness under `harness/truth`; the timer tests are
  `ocaml/engine/test/test_timers.ml` and the Lean contracts named in §3.4.
- **"`make check-corpus` … 400 programs from `Test/Program/Gen.lean`"** is right for
  `harness/truth/corpus-results.tsv` (400 rows), but only 127 of them reach rc.112 at all.
- Everything else in the brief that I checked holds: the truth corpus is 36 programs; the six
  differing typed runs are `g81 g102 g144 g250 g289 g313` under DI-73; `check-tools` is red on
  `Test/fixtures/trust-gate/expr-equality.lean.txt` (stamped, not re-run by me); the four DI-79
  retirements are done; `gen` stays; DI-91 is ruled; `loopAgreement` and the two soundness
  theorems are merged; R4/R5/R6 has nothing implemented; M2 is not started.

## 15. What I did not check

- **I ran no gate.** Not `make check`, not `check-truth`, not `check-corpus`, not `check-ocaml`,
  not `check-tools`, not `bun`, not `tsc`, not `dune`. Every lane verdict in this note is
  **stamped** from `docs/STATE.md` or read from a committed results file, never observed.
- **I did not re-run the corpus against rc.112.** The 121/6/273 split, the six DI-73 rows and
  the tsdiag verdicts are read from `harness/truth/corpus-results.tsv` and
  `generated/tsdiag-agreement.tsv` as committed; if the coordinator's uncommitted slice changes
  them, my numbers are the committed ones.
- **My truth-corpus census types against the empty signature.** Eight of the 36 programs
  (`pDiamond`, `pAcquireHandle`, `pSqlite`, `pKv`, `pSqlFail`, `pSqlCatch`, `pSqlExit`,
  `pSqlOrDie`) need the host row table, so their constructors are counted as present but their
  *types* are missing from §3.6's census. `harness/truth/corpus.json` records all 36 as
  `wellTyped`, so presence is right and the `Ty` column is a lower bound.
- **Presence, not weight.** Every corpus count is "programs containing the constructor", not
  occurrences, and says nothing about whether a program *exercises* the constructor's
  interesting behaviour. A program can contain `uninterruptible` and never be interrupted.
- **I did not read the OCaml engine's tests** beyond their file names and the seam gate's
  header, nor `ts/eff/test/*`, nor `tools/target/*.test.ts`, nor `Test/Counterexamples/**`
  beyond grepping them for refusal constructors. The claim "all eight `ReadRefusal`s have
  controls" is a grep count of the constructor name across `Test/**`, not a reading of each
  guard.
- **I did not verify the `select-controls.ts` finding by running `tsc`.** It is read from
  `harness/truth/tsconfig.json:26` and `scripts/check-truth.py:44-60`, plus the fact that the
  string occurs nowhere else in the repository. TypeScript's silent treatment of a non-matching
  `include` glob is **assumed**, not tested.
- **I did not price items 2–4 of §11 against the code.** The "days" estimates are inferred from
  the packet's seven steps and the two files' line counts, not from a trial.
- **I did not check the Conform lane (`check-cases`, `check-native`)** beyond the Makefile
  recipe, nor what `tools/Conform/**` covers of the alphabet.
- **I did not open the review log's B1–B21 register**, only the notes the brief named.
