The registry seat's claims hold (all seven probes rerun with exit 0 and output identical to its logs), and the two layer gaps are wider than it reports: the live admission and host session accept them, they can make a checked program die with the bad-shape defect that M6's typed state admits at every type, and for gap 2 the printed TypeScript fails the pinned compiler.

# Registry seat: adversarial verification

Verifier for seat `registry`. Base `be15b062` (HEAD is `48cd1de1`, but no file under `src/`,
`Test/`, `ocaml/`, `ts/`, `generated/` or `lakefile.toml` changed since the base). I did not
edit the seat's files. Their SHA-256 hashes still match the seat's note §12. I wrote this
note and four probes in this folder: `verify-Gaps.lean`, `verify-Origins.lean`,
`verify-Registry.lean`, `verify-LaneReach.lean`. Scratch files stayed in the session
scratchpad.

Evidence words. **Proved**: a kernel theorem, axioms printed. **Tested**: a finite check
(`#guard`, a counted run, or a TypeScript run). **Reproduced**: I reran the seat's probe and got
the same output. **Reading**: I read the code and did not check it by machine. **Assumed**: not
checked at all.

## 1. Verdicts, claim by claim

1. **M6's capstone is false with no host answer (errLeak).** Confirmed. I read
   `typedState_reachable` (`Laws/Program/Typed/Assembly.lean:225-227`). The seat's statement
   is that obligation's proposition, instantiated at `errLeak` (coerced with the empty table),
   `errLeakTy`, fuel 200 and `bad`. The proof uses the typed state's own fields: the `exit`
   clause of `preds` (`Assembly.lean:54`) and `WorldValid.root` (`Validity.lean:34`). The run is
   on the reference machine itself (`bad_has_bad_exit` decides `replayR` directly). The tape is
   `[evaluate, flush]`. `RunDecision` has exactly one answer constructor, `answerAsync`
   (`Machine/Fibers.lean:452-476`), so any `isAnswer` predicate passes this tape.
   Reproduced, `[propext, Quot.sound]`. Stronger than claimed: the live admission
   `admitProgram` also accepts `errLeak` and `valueLeak` (`errLeak_admitted`,
   `valueLeak_admitted`, proved in `verify-Gaps.lean`). So a capstone premised on admission
   instead of `Api.typeOf` is refuted too.
2. **Refuted again by gap 2 (valueLeak).** Confirmed. Reproduced, `[propext, Quot.sound]`.
3. **Gap 1: a layer body is checked at `[]` but built in the enclosing environment.**
   Confirmed by reading and reproduced. `checkLayer` checks an `effect` body at `[]`
   (`Program/Checker.lean:231-232`). The runtime builds the layer at `p.child 0`
   (`Program/Compile.lean:774`, `:777`) and the body at `q.child 0` (`:745`), and
   `Point.child` keeps `env` (`:79-80`). The design text says layer bodies are closed
   (`Program/Eff.lean:375-378`), so the runtime is the side out of step. Wider than claimed:
   - `Layer.effectDiscard` has the same gap (`discardLeak_native_exit`, proved);
   - the live host session reaches the bad exit (`liveExit errLeak`, tested);
   - a body that takes `succ` of the shifted level dies with `badName` (`crash1_*`, proved).
4. **Gap 2: a layer leaf's value is never compared with its key's service type.** Confirmed.
   `succeed` checks only that the literal is in the alphabet (`Checker.lean:228-230`).
   `effect` keeps only the body's error (`:231-233`). `service key` answers
   `sig.serviceTy key` (`:215-217`). `provideService`, by contrast, refuses with
   `valueNotSubtype` (`:224`). Reproduced. Wider than claimed:
   - the live session answers `"x"` and `true` (tested);
   - `crash2` dies with `badName` (proved).
   The seat's "TypeScript's own checker would reject" was assumed. It is now **tested**: the
   pinned `tsgo` (7.0.0-dev.20260629.1) refuses the printed `valueLeak` (TS2379, `string` is not
   `number`) and `succeedLeak` (TS2345, `boolean` is not `number`). It accepts the printed
   `errLeak` and `valueControl`. So `Api.printDecl` emits, for an admitted Lean program,
   TypeScript that the pinned compiler refuses. Run without type checking, those two programs
   answer `"x"` and `true` under Effect rc.112, like the Lean runtime.
5. **The printed TypeScript for errLeak agrees with the checker.** Confirmed, and upgraded from
   a reading to **tested**. I ran the printed text, verbatim from `LayerGap.lean:285-289`,
   under Effect 4.0.0-rc.112 (`harness/truth/node_modules/effect`, bun 1.4.2). It fails with
   `"x"`; so does the control. The Lean runtime fails with `9`. The seat's parenthetical that
   the OCaml engine agrees with the Lean runtime is **unverified**. It is likely, because
   `ocaml/gen` is the LCNF translation of the same `Compile`/`Fibers` code, but I did not run
   it.
6. **`staticEnvAt` is sound (proved).** Confirmed. I read every case of `stepEnv_checks`; the
   53 cases follow `Node.child` (52 clauses and the no-child case). Each case takes the
   checker's own child environment from the destructured success. Nothing is vacuous: the
   hypothesis is the root's check, and the conclusions are existentials over definitions that
   compute. `declared_finalizer` is `rfl` by definition, as it should be. 18 theorems, axioms
   as logged. The seat says plainly that exactness (the fold *is* the checker's environment)
   is tested, not proved; that is accurate.
7. **`staticEnvAt` equals the checker's environment (tested).** Confirmed. Reproduced:
   6662 paths with 0 disagreements, 10728 sites with 0 failures, 3959 handle observations, and
   11 of 11 wrong folds caught. I checked the oracle's soundness by reading:
   - the probe `closeScope (var i) (var i)` always refuses and names the exact type
     (`Checker.lean:377-381`);
   - every checker arm checks a child before any sibling whose environment depends on it.
   One limit: the oracle covers program nodes only. Action nodes, race list cells and
   statement nodes are covered through their program children.
8. **Every lane fiber is declared and fits (tested).** Confirmed. Reproduced byte for byte:
   34336 runs, 70080 fibers, 0 violations. Two limits the seat does not state:
   - 6826 of the fibers (2626 layer builds and 4200 finalizers) are declared with answer
     `unknown`, so their answer check accepts any value;
   - the deep check counts handles in success values only (`Declared.lean:96`). `fitsB` falls
     back to `Val.hasTy` for failed exits and causes (`Core.lean:255-258`, `:272`), so fiber
     handles inside typed failures are never checked against the registry.
9. **The checks are not vacuous (tested).** Confirmed. Reproduced: 13193, 348, 4200 and 2626
   violations for the four wrong registries; 2107, 2095 and 0 for the deep controls.
10. **The fixtures fail exactly four runs, all gap 1 (tested).** Confirmed. Reproduced; the
    guard at `Declared.lean:239-243` passes. Note that the fixtures hold no race. I added one:
    a race two binders deep whose entrants read both levels, with the levels also swapped. Every
    entrant is declared at its own type, and every exit fits under all four lane tapes (tested,
    `verify-Registry.lean`).
11. **`spawn` is the only creator of forked fibers, with three callers (reading).** Confirmed by
    my own reading:
    - `spawn` is called at `Fibers.lean:958`, `:969`, `:1217`, `:1226`, `:1234`, `:1431`,
      `:1441` and `:1454`, which are the three caller groups the seat names;
    - roots are made at `Api.lean:258`, `Fibers.lean:2187` and `:2197`;
    - the stores alphabet's forks (`Stores.lean:2089-2093`) and races (`:2104`, site `none`)
      are reachable only through `ProgName` programs. The native compile enters stores
      programs only through finalizer, close-walk, completion, cancel, race-settle, interrupt
      and ambient-scope entries (`Compile.lean:1083-1505`). None of these reaches a stores
      `fork`, `forkIn`, `forkScoped` or `raceAll` action; the one that forks is the parallel
      close walk, through `forkFinalizers` with site `[]` (`Stores.lean:1769-1795`,
      `:1870-1873`, `:2115`).
    The seat leaves out `loadR` (`Laws/Program/RuntimeR.lean:41-44`), the reference machine's
    root; that is harmless. On its open question about the reference evaluator's sites: they
    are the same as the native machine's. `origin_eq_ref` (proved, `verify-Origins.lean`) shows
    every fiber id has the same origin on `Api.replay` and `replayR`, on every tape, at the
    empty table.
12. **Layer builds are missing from `Api.supervision`; merges fork empty-site daemons; a running
    build reads as an unpinned daemon (tested).** Confirmed. Reproduced (`sites.log`). The last
    point is broader than the seat says. A running race entrant also reads as an unpinned
    daemon (tested: `unpinnedDaemonsAlive = [1, 2]` while two entrants sleep). By reading of
    `statusOf` (`Api/Supervision.lean:215-226`), so does a running parallel-close finalizer
    daemon. All three internal daemon kinds are owned and awaited, by the merge's await, the
    race and `closeParAwait`, yet `daemonsQuiet` reports them as invisible daemons.
13. **A layer build answers an encoded spine, so it is declared with answer `unknown`; a
    finalizer daemon is declared `⟨unknown, never⟩` (tested).** Confirmed as tested, and by
    reading of `finProgram`. The seat's "scratch run" for `Ty.context` is not in its files, but
    the `layerAsContext` control (2626 violations) reproduces the point. Like every declaration
    the checker gives, these rest on gap 1 being fixed: a release, or a layer build, whose
    program sits in a layer body under a binder runs on shifted levels (reading; not
    constructed).
14. **Cells and deferreds carry no creation site; memo entries are keyed by layer path; the
    template rows (tested).** Confirmed. Reproduced (`cells.log`). I also checked that literal
    terms have base types (`termTy` of `"x"` is `string`, of `1` is `nat`), so `Ref.make` of a
    literal gets `refOf string` and not a singleton literal type (tested in scratch).
15. **With `staticEnvAt`, the boundary refuses the forged handle and admits the honest one under
    a binder (tested).** Confirmed. Reproduced (`Declared.lean:290-299`).

Count slips in the note, not in substance:
- `LayerGap.lean` has 30 theorems with printed axioms (the note and the probe summary say 28);
- `proofs.log` has 18 lines (the note §12 says 19).

## 2. Reruns

Commands from the repository root, all through the lock. `S` is the session scratchpad and `D`
is `docs/research/2026-09-30-pass/registry`. `Core.lean` was compiled into a fresh directory,
`$S/registry-verify-olean`, not the seat's.

| Probe | Command | Exit | Result |
| --- | --- | --- | --- |
| `Core.lean` | `bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true -R docs/research/2026-09-30-pass -o $S/registry-verify-olean/registry/Core.olean $D/Core.lean` | 0 | no output, as `core.log` |
| `Sites.lean` | `LEAN_PATH=$S/registry-verify-olean bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true $D/Sites.lean` (all rows below use this form) | 0 | "all guards passed", as `sites.log` |
| `Cells.lean` | same form | 0 | as `cells.log` |
| `LayerGap.lean` | same form | 0 | identical to `layergap.log`: 30 axiom lines, `errLeakTy_closed` none, `tape_answers_nothing` `[propext]`, the rest `[propext, Quot.sound]` |
| `Proofs.lean` | same form | 0 | identical to `proofs.log`: 18 lines; four use none, `term_ok` `[propext]`, the rest `[propext, Quot.sound]` |
| `StaticEnv.lean` | same form | 0 | identical to `staticenv.log` |
| `Declared.lean` | same form | 0 | identical to `declared.log` (107 s) |

## 3. The verifier's probes

All exit 0, through the same lock and the same form of command.

- **`verify-Gaps.lean`.** 14 theorems, each `[propext, Quot.sound]`:
  - `errLeak_admitted` and `valueLeak_admitted`: `admitProgram` accepts both;
  - `crash1_checked` and `crash2_checked`: both checked at `(nat, never)`;
  - `discardLeak_checked` and `discardLeak_native_exit`: gap 1 in `effectDiscard`;
  - `crash1_native_dies`, `crash2_native_dies`, `crash1_reference_dies` and
    `crash2_reference_dies`: every reason of the root's exit is `die badName`, on both
    machines;
  - `strongExit_of_dies`: an exit whose reasons are all defects is a `StrongExit` at every
    type, in every world;
  - `allDie_of_diesBadShape`, `crash1_exit_clause_blind` and `crash2_exit_clause_blind`: the
    typed state's exit clause accepts both crashes at every type.

  Guards (tested): `admitProgram` accepts all six gap programs, and the live session
  (`start`, `evaluate`, `flush`) ends errLeak with `9`, valueLeak with `"x"`, succeedLeak with
  `true`, and both crashes with `badName`. The lane's `badDefect` rule flags both crashes.
- **`verify-Origins.lean`.** `origin_eq_ref`, `[propext, Quot.sound]`: the same origin for every
  fiber id on the native and reference replays. It is built from `replay_rel`,
  `BMeans.fiber?_cases` and `FMeans.origin`.
- **`verify-Registry.lean`** (imports the seat's `Core`). The race under two binders, in both
  level orders, is declared and fits under four tapes. Live race entrants read as unpinned
  daemons.
- **`verify-LaneReach.lean`** (imports the seat's `Core`). Among the 8584 typed lane programs,
  1343 hold a layer, and none is a gap-1 or gap-2 candidate. The detector finds the seat's
  three programs, which serve as positive controls. This confirms the note's "the lane cannot
  reach them" (tested). The note's stated reason fits the typed corpus. The random corpus's
  layer arm (`Test/Program/Gen.lean:193-203`) can draw effect bodies of any type, but none of
  its typed samples does.
- **TypeScript** (scratch, not in the tree). The files import `{ Context, Effect, Exit, Layer }`
  from `harness/truth/node_modules/effect/dist/index.js` by absolute path. Their bodies are the
  seat's print guard text and `Api.printDecl` rendered by `TypeScript.Render.constDecl`. Two
  runs:
  - `bun run errleak.ts` ran the printed errLeak and its control under
    `harness/truth/node_modules/effect` (4.0.0-rc.112). Exit 0; both fail with `"x"`.
  - `harness/truth/node_modules/.bin/tsgo -p tsconfig.json` checked the four printed
    declarations from `Api.printDecl`, with `strict`, `exactOptionalPropertyTypes` and
    `moduleResolution: bundler`. Exit 1, two errors: TS2379 at `valueLeak` and TS2345 at
    `succeedLeak`.

## 4. What the seat missed

1. **The gaps break "never goes wrong", and M6's typed state cannot see it.** A gap can make a
   checked, admitted program die with the bad-shape defect, through `succ` of a value of the
   wrong type. The exit-type lane forbids that defect for checked programs
   (`Test/Program/ExitTypeLane.lean:34`). But `StrongExit` admits every `die` at every type
   (`ErrorImage.lean:31-36`, `Typed/Admission.lean:65-75`); this is proved in
   `strongExit_of_dies` and `crash*_exit_clause_blind`. So even a repaired capstone would not
   exclude these crashes. The only "never wrong" statement is `meaning_never_wrong`
   (`Laws/Program/MeaningSound.lean:746`), and it covers the straight fragment only. The other
   typed-state clauses were not checked on these runs.
2. **The live API is affected, not only the proof statement.** `admitProgram` and
   `HostSession.start` accept the gap programs, and the live session reaches the bad exits.
3. **For gap 2, the printed TypeScript does not compile.** So the faces disagree at compile
   time as well as at run time.
4. **Gap 1 is not specific to `Layer.effect`.** Every layer build starts from the one entry at
   `Compile.lean:774`/`:777`. That includes `effectDiscard`, `ref` redirects (`:693-700`;
   `Point.redirect`, `:115-116`, keeps the referring point's `env`), merge sibling builds
   (`:1453-1455`) and `provide` chains.
   By the same reading, the seat's proposed runtime repair at that entry covers them all.
5. **The reference machine records the same sites** (`origin_eq_ref`, proved). This answers the
   seat's open question about `EvaluateR.lean` for the registry's purpose.
6. **The daemon view misreads all three internal daemon kinds**, not only layer builds: race
   entrants (tested) and parallel-close finalizer daemons (reading) too.
7. **Six silent `site := []` defaults.** They are at `WithFiberAction.fork`, `forkIn` and
   `forkScoped` (`Fibers.lean:304-310`), `spawn` (`:926`), `launchEntrant` (`:957`) and the
   `FiberAction` twins (`:1428`, `:1440`, `:1451`). A new caller that forgets a site records
   `[]` without complaint. The required `kind` the seat proposes makes this visible as an
   undeclared fiber. Dropping the defaults would make it a compile error.

## 5. On the proposals

- **1 (`ForkKind`, `kind` required in `spawn`).** Sound. An alternative with less new state:
  put `kind` in `Origin.forked`. The fiber list is append-only (only `++` and `map` touch
  `m.fibers`), and `FMeans.origin` already carries origins to the reference machine. The
  separate ledger has its own reason, though (the origin plan's route B).
- **4 (boundary `fitsB`).** "Cells and deferreds compare exactly" should be "both ways". Their
  invariance is mutual subtyping (`Ty.lean:453-454`). Syntactic equality would refuse
  equivalent types, such as a union written in the other order. `fitsB` also needs arms for
  failed exits and causes before it can stand in for `Val.hasTy` on host answers that carry
  typed failures.
- **5 (`FiberRegistryAgrees`).** It is stated over `NativeMachine`, but M6's typed state is
  over `RState`. State it on the reference machine, or generically. `origin_eq_ref` transports
  it.
- **6 (make the checker call `stepEnv`).** As written this re-checks siblings. `stepEnv`'s
  `bind` step calls `Checker.check` on the first child, so a checker arm that called it would
  check that child twice, and a left-nested chain of binds would double at each level. Share
  the environment rule given the sibling types the checker already has, not `stepEnv` itself.
- **7 (runtime repair of gap 1).** Sufficient by my reading (see §4, item 4). The `run_eq_ref`
  relation will need the same change in the reference denotation.
- **8 (checker repair of gap 2).** Agreed. It should also refuse a leaf whose key has no
  service type, as `service` does. On the lane it would refuse no program (0 candidates,
  tested).
- **Add to M6:** a never-wrong clause (no `badName` or `notImplemented` defect in a checked
  run), or an explicit statement that M6 does not claim it.

## 6. Not verified

- That the OCaml engine reproduces the Lean runtime on the gap programs (likely; not run).
- The other clauses of the typed state on the crash runs (only the exit clause is examined).
- The seat's §7 generic-cell design beyond its template-row guards (design text, not a claim
  with evidence).
