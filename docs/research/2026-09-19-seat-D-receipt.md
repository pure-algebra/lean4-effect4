# Seat D — one compiler, and the typing checked against it

Branch `seat/D-one-compiler` from `bf179374`. Five commits, all green on
`make check-target` (six steps) with `make check-truth` and `python3 scripts/check-corpus.py`
run to completion. Evidence words: **measured** = a number read off a run; **tested** = a
finite checker run; **proved** = a theorem (this seat proved none); **assumed** = stated, not
checked.

## 0. The one thing the coordinator must know

**`make check` has been red since wave 1, and not because of anything in this slice.**
`harness/truth/prelude.ts` re-exports `prelude-atoms.gen.ts` since `50aa8422`;
`scripts/check-corpus.py` never copied that file into its work directory, so every emitted
module of the generated corpus lost every atom — five programs failed to load at run time and
all 400 rows recorded a compiler error, against a `harness/truth/corpus-results.tsv` last
promoted at `abe220ef`, before the atom block. `check-corpus` is a member of `make check`.
One copy line fixes it (`54ee444a`), and with it the committed table is reproduced **byte for
byte under tsgo**: 400 programs, run {untyped 273, agree 121, differ 6}, tsc {errors 254,
clean 146}, types {untyped 273, agree 110, mismatch-A 6, mismatch-R 3, refused 8}, 27
registered disagreements. The retired compiler hid it: it reported one unattributed module
error against the prelude, which the lane's per-program regex never saw, where tsgo reports
TS2305 per program.

Second thing, smaller: **`typescript@5.9.2` is still in `ts/eff/package.json`, as a parser.**
The brief's receipt line asked for no `typescript` 5.x in any tracked lockfile; that is not
reachable in this slice and should not be forced. Six modules import it, and after this seat's
work none of them constructs a checker — `ts/eff/ingest/ck.ts` (1101 lines, the recognizer
twin's ck leg), `ts/eff/check-styles.ts`, `ts/eff/ingest/fidelity/source.ts`,
`ts/eff/ingest/census/corpus.ts`, `census/decls-ck.ts` and `census/legs.ts` call
`createSourceFile`, the `is*` guards and `parseConfigFileTextToJson`. tsgo publishes **no
standalone parser** (a source file exists only inside a project), so porting the ck leg alone
would make the twin parse every file twice with two different engines, which is the one thing
a twin must not do. Row 57's own words carve this out ("`typescript@5.9.2` leaves the pins once
no reader needs its parser"), and its substance — one compiler decides *assignable* — is
delivered and is now a control: `tools/target/oracle.test.ts` greps the tracked tree for
`createProgram|getTypeChecker|transpileModule|…` and fails if any file constructs a second
checker (verified red by adding one, then removed).

## 1. Commits

| commit | what |
| --- | --- |
| `ad446a60` | **one compiler** (row 57, plan 0.11/Q8): `tools/target/oracle.ts` off `typescript@5.9.2`; the new `tools/target/checker.ts` drives tsgo's sync API under node; `check-truth`, `check-corpus`, the schema-codec line and `ts/eff`'s `typecheck` run tsgo; the compiler is pinned in `ts/eff/package.json` and installed by the one `bun install`; two hand AST rewrites retired; the no-second-checker control |
| `54ee444a` | **the corpus lane's work directory** was missing `prelude-atoms.gen.ts` (§0) |
| `27f93018` | **1.10a**: `renderTy`/`rowArguments` deleted; the row lane's expected columns come from `generated/row-types.tsv` (`tools/Tools/RowTypes.lean`, `Ty.renderRaw`); `tsgo --noEmit -p tools/target` joins `check-target` |
| `2f0a7b46` | **1.10**: the assignability differential, `tools/Tools/TyVectors.lean` + `tools/target/assignability.ts` → `generated/assignability.tsv`, with its red control |
| `beb8259b` | **1.11(b)**: every row of `NativeOp.row` and every atom against the export it transcribes → `generated/row-citations.tsv`; the `callable` query kind |

## 2. Measured

**The lane.** `make check-target` now runs six steps: the row-signature table in `--check`
mode, `tsgo --noEmit -p tools/target/tsconfig.json`, `bun test tools/target` (24 tests,
5 files, 195 assertions), the conformance report (47/47 agree, 0 mismatching, 0 refused), the
assignability differential and the rows report. The oracle's own run went from 2.5 s (tsc
5.9.2, one process) to ~6 s wall (two node children, each spawning the compiler); one
compiler instance over the 47-query project is 475 ms for the snapshot, 26 ms for the
diagnostics and 36 ms for the type queries — the tsc 5.9.2 path was ~2.4 s for the same work.
`ts/eff`'s whole-package typecheck is 1.7 s under tsgo.

**The assignability differential** (`generated/assignability.tsv`), 600 ordered pairs:

| verdict | count |
| --- | --- |
| agree | 594 |
| cut | 6 |
| incomplete | 0 |
| defect | 0 |
| refused | 0 |

All six cuts are one thing: `Ty.renderRaw` is not injective. `nat` and `int` both print
`number` (2 rows), and `refOf nat` prints `Ref.Ref<number>`, the same text a
`.handle "Ref.Ref<number>"` prints verbatim (4 rows). The order tells them apart and the target
cannot. The two readings of each direction — the checker's own `isTypeAssignableTo` and one
ordinary assignment statement — **never disagreed** on any of the 600 pairs, in either
direction.

**The three known gaps** (type-algebra note §5.2) are the first rows and two of them *agree
with the target*:

* `gap/option-union`: `Option.Option<number | string>` and
  `Option.Option<number> | Option.Option<string>` — `sub` false one way, true the other, and
  tsgo says exactly the same. The target does not distribute `Option` over a union either.
* `gap/prod-never`: `readonly [never, number]` against `never` — again identical verdicts. The
  target also keeps an uninhabited tuple apart from `never`.
* the third (no function types, so no contravariant position anywhere) has no pair to witness
  it: there is no arrow to write on either side.

So those two gaps are incompleteness against **value containment**, not against the target's
order — which is a sharper statement than the note makes, and it is now a committed row.

**The red control's sensitivity.** Each pair carries `Ty.sub` under one swapped arm — `refOf`
read covariantly instead of invariantly (decisions row 55). 10 pair-directions move and
**all 10 are caught** by the differential. The control has its own control: neutralising the
mutation makes the lane fail with "the red control is not caught by any pair; the differential
measures nothing" (run, seen, restored).

**The rows and atoms** (`generated/row-citations.tsv`), 42 queries — 22 rows, 20 atoms:
10 agree, 2 mismatch, 30 reported. Four findings:

1. `Scope.make` answers `Scope.Scope.Closeable`, not `Scope.Scope`, and takes an optional
   strategy argument where the row's request is `[]`. A row disagreement beyond DI-97/DI-98.
2. `Effect.sleep` takes `Duration.Input`; the row's `[number]` is a restriction of it, not its
   type (mismatch on the request, exact on the answer).
3. `Effect.currentTimeMillis`, the `clockNow` row's spelling, **is not an export of
   `effect/Effect`**: rc.112 publishes it as `Clock.currentTimeMillis` (`Clock.ts:265`) and the
   cited `internal/effect.ts:6118` is `@internal`. No printed program has ever exercised it, or
   the corpus would not compile.
4. Nine atoms agree exactly on request and answer with the prelude's declarations (`succ`,
   `pred`, `isZero`, `not`, `add`, `lt`, `strings`, `or`, `and`). `tagIs` agrees on its answer,
   and its request `[string, unknown]` is textually what the prelude declares — C7's claim,
   checked.

**The atoms' verdicts at `never` and at `option t` (finding C6).** The prelude declares
`isSome` as `<A>(value: Option.Option<A>) => boolean` and `getOrElse` as
`<A>(value: Option.Option<A>, fallback: NoInfer<A>) => A`. The target therefore accepts *every*
`option t` at that parameter, and it accepts `never`: `generated/assignability.tsv` row
`core/0-7` has `never` below `Option.Option<number>` with `subLR`, `assignableLR` and
`statementLR` all true, and the `option` family has `Option.Option<never>` below every other
`Option.Option<_>`. So **the head rule is stricter than the target**: `optionPresence` refuses
an argument whose head is not `.option` (so `never`), where TypeScript accepts it, and
`mono [.option .unknown] .bool` with subsumption at the parameter is exactly what the target
does. Same for `getOrElse`'s first parameter. The custom rules that remain genuinely their own
are `fst`/`snd`'s column projection and the four cause queries, whose input the target spells
`Cause.Cause<unknown> | Exit.Exit<unknown, unknown>` — one union, not a head rule.

**The corpus lane's text did not move.** 400/400 rows byte-identical to the committed
`harness/truth/corpus-results.tsv` under tsgo, so nothing was promoted. The expected columns of
the row queries *did* change spelling — a handle now reads `SqlClient.SqlClient`, bound by the
query's own declarations, where the retired hand printer wrote `Adapter.SqlHandle` — without
changing one verdict.

**Lockfiles checked** for `typescript` 5.x: `ts/eff/bun.lock` (holds `typescript@5.9.2` as a
devDependency, the parser of §0, plus the new `@typescript/native-preview@7.0.0-dev.20260629.1`
and its seven platform packages, so a Linux or Windows clone installs the same compiler) and
`harness/schema-host/package-lock.json` (`typescript@7.0.2` + `@effect/tsgo`, untouched: that
harness was already on TypeScript 7). No other lockfile is tracked
(`git ls-files | grep -E 'package-lock|bun.lock|yarn.lock|pnpm-lock'`).

## 3. What the compiler migration actually changed

* `tools/target/oracle.ts` keeps its face (`Query`, `Report`, `query`, the
  assignment-statement method, the `limitations` register, which now names the compiler and its
  version) and became text-only: it spawns `tools/target/checker.ts` under node with a request
  file and reads the report back. The sync client reads a node-internal pipe handle
  (`stdout._handle.fd`), which bun does not have — measured, not assumed.
* The query modules are never written to disk: tsgo's API takes virtual filesystem callbacks
  (`readFile`/`fileExists`/`directoryExists`/`getAccessibleEntries`/`realpath`), which is the
  same shape as the retired compiler host's `readFile` override.
* Two hand AST rewrites were retired rather than ported, because tsgo has no standalone parser
  or printer. A handle binding (`Host.Resource` → `Adapter.HostResource`) is now a
  *declaration* in the query source (`declare namespace Host { export type Resource = … }`), so
  the expected column is the string Lean rendered and the compiler does the binding by name
  resolution; two names on one target are refused at the binding (DI-24/DI-76, which the old
  per-column dedup only caught when the two shapes were textually equal). A method's receiver
  is the object type the compiler parsed out of `X["m"]`, in a no-lib no-resolve project of its
  own (23 ms).
* One caution for whoever touches `checker.ts`: `checker.getTypeArguments` on a type that is
  not a reference **panics the compiler's Go server** (seen). Every call is guarded by
  `type.isTypeReference()`, as the retired code guarded on `ObjectFlags.Reference`.
* `harness/tsdiag/run-tsdiag.mjs` now resolves the compiler from `ts/eff/node_modules` instead
  of `/opt/homebrew`, with `TSGO_HOME` still overriding: one install, one pin, and a fresh
  clone needs no global package.

## 4. Not done, and why

* **1.11(a), the span pinning of every `Row.cite`.** Not started. The design is settled and
  small: a driver `tools/Tools/Cites.lean` writing `generated/cite-spans.tsv` with, per cite of
  the `vendor/…:<a>[-<b>]` form, the path, the line span, the span's first non-blank line as a
  literal anchor that must occur exactly once in the file, and a SHA-256 of the span's bytes —
  the `scripts/generate-effect-runtime-census.sh:1-18` idiom — with a `--check` mode in
  `check-target` beside the row-signature check. It is a self-contained hour. I ran out of
  room and preferred a clearly-scoped gap to an untested driver.
* **The `clockNow` spelling, the `Scope.make` answer and the `Effect.sleep` request** are
  reported, not fixed: rewriting a row is language-ledger work and the brief says report.
* **The corpus lane's 5.9.2-era `tsc` column** was measured under a broken prelude since wave 1
  (§0). The numbers in the committed table are, as it turns out, the same ones a correct run
  produces — but that is luck about *which* programs err, not a property anyone had checked.

## 5. Files outside the brief's list that I touched, and why

* `scripts/check-corpus.py` — the only other reader of the retired `tsc` binary (its step 4),
  and the missing-atom-block defect of §0. Leaving it would have kept the second compiler in
  the lockfile and left `make check` red.
* `Makefile` line 364 (`check-schema-codec`) — the last invocation of
  `node …/typescript/bin/tsc` in the tree. One word.
* `scripts/lib/truth_host.py` — the shared host selection, which now also refuses a missing
  compiler and a missing `node`, and exports the one command that runs it.
* `tools/target/checker.ts`, `tools/target/assignability.ts`, `tools/target/rows.ts`,
  `tools/target/assignability.test.ts` are new files under `tools/target/*`, which the brief
  gives me.

No file under `src/`, `ocaml/`, `Test/` (except reading `Test/Api/AcquireHandleContract.lean`),
`docs/core/` or another seat's tree was edited. No Test module was added, so `Test/All.lean` is
untouched. `README.md` and the owner's untracked `docs/*.md` are untouched.

## 6. Proposed decisions rows

**Row 32, amendment (tsgo for scanning *and* typing).** Row 32 says "scanner = tsgo in
`harness/schema-host` (the oxc recognizer has no checker)". After this slice that is no longer a
statement about one harness: tsgo is the repository's only type checker, pinned in
`ts/eff/package.json` and installed by the one `bun install`, and every typing lane —
the target oracle, the truth typecheck, the corpus typecheck, `ts/eff`'s own typecheck, the
schema codec, the diagnostics lane and the two new lanes — asks it. Proposed text: *"scanner and
type oracle = tsgo (`@typescript/native-preview`, the version `ts/eff/package.json` pins);
`typescript@5.9.2` remains only as a syntax-only parser for the ingest recognizer twin and the
two syntax readers, and no file of the tree constructs a second checker (controlled in
`tools/target/oracle.test.ts`)."*

**A new row: a typing rule is checked against the target's compiler.** Proposed text: *"Every
rule of the type language that claims something about the target is checked against the
target's compiler, and the check is a committed table, not a run: `Ty.sub` against the
compiler's order over a named pair set (`generated/assignability.tsv`, both readings of both
directions, each disagreement classified `cut`/`incomplete`/`defect`, a `defect` failing the
lane, and a swapped-arm control that must be caught); every row of `NativeOp.row` and every
atom of the alphabet against the export it transcribes (`generated/row-citations.tsv`, a report
where rc.112's export is generic, a signed exception with its content where the row disagrees
on purpose). A rule with no row in either table is a claim nobody checked."*

**A third, smaller one, if the coordinator wants it ruled rather than left as a finding:**
`optionPresence` and `optionDefault` become `mono [.option .unknown] .bool` and a subsumption
rule at the first parameter (C6), on the evidence of §2: the target accepts `never` and every
`option t` there, and the head rule refuses `never`. That is a change to
`src/Effect4/Program/NativeAtom.lean`, seat V's file, not mine.
