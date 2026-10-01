M6's capstone, M5's `typedState_load` and M6's `step_loop` are each proved false on checked programs that use no host. The causes are two layer typing gaps, live in the API today, and the old value judgment's store-length liveness. So the answer-free restriction (decision 5, Codex item B) is necessary but repairs none of them. The design that survives: two layer repairs; the `Fits` judgment with liveness read from the world's tables; the guard's token bound in M6's typed state; then the capstone derived by the generic lifts, which are proved.

# Design-and-probing pass of 2026-09-30: synthesis

Base `be15b062` on `refactor/phase1-phase3`. HEAD is `48cd1de1`, and no file under `src/`, `Test/` or `ocaml/` has changed since the base. Research only. This is the only file this seat wrote in the tree. One scratch probe ran in the session scratchpad (Appendix A).

Short paths: `Program/…`, `Machine/…` and `Laws/…` are under `src/Effect4/`. Seat files are named relative to this folder, for example `registry/LayerGap.lean`.

**Sources:**
- the five seat notes and the five adversarial verifications in this folder (`registry`, `membership`, `lift`, `fiberslice`, `numbers`). Each verifier reran its seat's probes and got identical output, so every seat count below is reproduced unless marked;
- the external runtime contract, the host-answers note, the origin-ledger plan, and the authority-promotion plan §3;
- the Codex brief for slice 6 (`2026-09-30-codex-brief-slice6-and-fixes.md`), because Codex is carrying out its items A–C now;
- the owner's route, as commit `6f7f6601` states it. Now: slice 6 and three bounded fixes (rows 95 and 96, and row 97's interim rule), then M5–M7. Parked: the full host-services contract, storage replacements, stage proofs and FloatLib.

**Evidence words:**
- **Proved**: a kernel theorem within `[propext, Quot.sound]`, with its axioms printed.
- **Tested**: a finite check (a `#guard`, a counted run, or a differential with a red control).
- **Reproduced**: rerun, or run on a real engine, with the same output.
- **Reading**: read in the code, not run.
- **Assumed**: not checked.

Each seat claim also carries its verifier's verdict: confirmed, partly, refuted or unverified.

## 1. For the owner

Five seats probed the design and five verifiers tried to break their work; every probe reran with the same output. Three building blocks hold. A fiber's declared type can be computed from where it was made and from the checker, with no type stored in any value: this is proved at every fork and race site and tested on 70,080 fibers. One membership judgment, `Fits`, checks a value's shape and its handles together over the real value layout: its laws are proved, and the whole slice-5 walk re-proves over it with 8 small proof edits. One generic lift carries a fact through the command loop, a decision and a whole run: it is proved, and it re-derives the guard's own contract without the guard's four hand inductions. But the typed guarantee as written today is false, even with no host. Two layer typing gaps let a checked program finish with a value outside its type, on both machines and through the live API: a layer's body runs in the wrong environment, and a layer's value is never compared with its key's type. The old value judgment makes the one-line program `Ref.make(5)` untypable. And M6's queue fact accepts a resume for a token that does not exist yet. Counting only runs with no host answer, which Codex is doing now, is still needed, but it fixes none of these. So the design the pass points to is this: fix the two layer gaps; adopt `Fits` with liveness read from the world's tables; give M6's typed state the bound the guard already carries; then derive M6 from the proved lifts. The fiber boundary work belongs to the parked host-services contract, and it works once the layer gap is fixed. On numbers, floating point does not fix exact naturals, because a double is exact only up to 2^53. Today one checked program gives three different answers on Lean, OCaml and TypeScript, and none of them refuses. The fix is the one DI-56 already ruled: each face equals the exact Lean reference inside its range and refuses outside it. The open choice is whether that refusal is written once in Lean, so that OCaml and the coming WASM target inherit it, or whether the native face becomes exact. FloatLib is a model to learn from, not a dependency: every compiler substitution should carry a proved equation, and a fast path should carry its proof inside the value.

## 2. The design, as one story

### 2.1 Every fiber gets a declared type from how it was made

**Who makes fibers.** Reading, confirmed by the registry verifier's own reading:
- **Roots.** Three functions make root fibers: `Api.load` (`Api.lean:255-260`), `runFork` and `runCallback` (`Machine/Fibers.lean:2183-2200`).
- **Forks.** Only `spawn` (`Fibers.lean:924-939`) makes a forked fiber, and it has three kinds of caller:
  - the `fork`, `forkIn` and `forkScoped` arms, and their `FiberAction` twins, pass the action's path;
  - `launchEntrant` passes the race's list cell;
  - `forkFinalizers`, in a parallel scope close, passes `[]`.
- **Layer builds.** A `merge`/`mergeAll` layer build goes through the `fork` arm with the layer's own path (`Program/Compile.lean:1453-1455`). This is a third internal kind of fork that the ledger plan does not name.

**Checks behind the census:**
- `registry/Sites.lean` pins one run per construct.
- `registry/Declared.lean` met no unrecognized site among 70,080 fibers.
- The reference machine records the same origin for every fiber, on every tape, at the empty table (`origin_eq_ref`, proved, `registry/verify-Origins.lean`).

**The record.** The fork ledger (Codex item C) keeps four things per forked fiber: child, parent, daemon flag and site. That is enough for native programs today, with one inference: an empty site means a finalizer daemon. The inference holds only by a census of the code. A three-valued `kind` would remove it (§4, K4).

**The declared type is computed, never stored:**

| Fiber | Declared answer and error |
| --- | --- |
| root | the admitted program's type (`Api.typeOf`) |
| source fork (`fork`, `forkIn`, `forkScoped`) | the checker's type of the forked body, checked in the static environment at its site |
| race entrant | the entrant's type at its list cell, found the same way |
| layer build | answer `unknown`; error the layer's error. Its answer is an encoded service spine that no `Ty` names. |
| finalizer daemon | `⟨unknown, never⟩` |

**The static environment** is a fold along the path. At each node it applies the checker's rule for the child it takes.
- **Proved sound.** If the root checks, the fold is defined along every path, and the node it reaches checks in the fold's environment.
  - `stepEnv_checks` has one case per clause of `Node.child`. With `staticEnv_checks` it is in `registry/Proofs.lean`; independently, `envAt_checks` is in `fiberslice/Sites.lean`.
  - At a fork, the declaration is exactly the `fiberOf` the checker gave the handle. Registry seat: `fork_handle`, `api_fork_handle`. Fiberslice seat: `siteDecl_fork`, `siteDecl_forkIn`, `siteDecl_forkScoped`, `siteDecl_race`.
- **Tested exact** against an oracle that shares no code with the fold (`registry/StaticEnv.lean`):
  - 0 disagreements on 6,662 program paths;
  - 0 failures on 10,728 fork sites;
  - 11 of 11 deliberately broken folds caught.
- **Tested on the lane.** Over 34,336 runs, every one of 70,080 fibers is declared, and every exited fiber fits its declaration. Four wrong registries fail as they should.

**The one condition.** A declaration is only as right as the agreement between the checker and the runtime. Layer gap 1 (§2.4) breaks that agreement. Inside a layer body under an outer binder, a fork is declared at one type and returns another:
- proved: `forkLeak_*`;
- tested, through the fiber-slice prototype: a `nat` program ends with `"s"` (`fiberslice/verify-LayerEnv.lean`).

So the registry stands on the gap-1 repair.

**Cells and deferreds** have no creation record today. The Ref heap holds values only, and the compile drops the `perform`'s point (`registry/Cells.lean`, tested). The same pattern would need two things:
- a cell ledger, with the site carried into the store step;
- for a generic `Deferred.make`, its answer and error written at the site, because a template instantiates them to `never never`.

That work belongs to generic cells (rows 42–44), inside the parked host-services contract.

### 2.2 One membership judgment reads the declarations

**What `Fits` is.** `Fits w v ty` is defined in `membership/note.md` §2. It is one recursion over the value shapes `Val.hasTy` already reads:
- a product is the two-cell list;
- a Result and an exit are constructors;
- a snapshot is decoded through the same view as a list;
- a union takes one whole branch, for shape and handles together.

At each handle it reads the world's table where the handle sits:
- a fiber's declaration must lie below the expected type (covariant);
- a cell's or deferred's declaration must be equivalent to it, meaning subtyping both ways, as `Ty.sub` reads invariance;
- the native spellings `Ref.Ref<number>` and `Deferred<number, number>` mean a cell or deferred declared at `nat`;
- a context's statically typed services must fit;
- `unknown` asks only that every handle be declared.

An exit is a value, so `FitsExit` is `Fits` at `exitOf`.

**Proved** in `membership/Fits.lean`:
- it implies the runtime shape check (`fits_hasTy`), and the converse is false (`converse_false`);
- it is closed under `Ty.sub` (`fits_sub`); the old judgment is not (`strongValue_not_closed_under_sub`);
- it is monotone under the host order, for values and for exits (`fits_mono`, `fitsExit_mono`);
- it implies declared liveness, which equals `HandlesLive` on valid worlds (`fits_live`, `live_iff_handlesLive`);
- it is a fold (connector `FitsInv.eq_cata`).

Six value gaps of the old judgment are each a set of three theorems (`g1`–`g6`, `Gaps.lean`): the old judgment accepts the value, `Fits` refuses it, and the honest value fits.

**Why it is needed now, not only for hosts.** The old judgment reads liveness from store lengths. A world that declares a fresh cell without growing the heap is a legal later world. So a program that allocates a cell and then returns it or binds it has no typed derivation.
- The kernel refutes M5's `typedState_load` at the checked program `Ref.make(5)`: `typedState_load_false` in `Gaps.lean`, and the ledger's own proposition as `typedState_load_refuted` (`membership/verify-load.lean`).
- It also refutes it at `Ref.make(5).flatMap(Ref.get)` and at `Deferred.make()`.
- With liveness read from the tables, the same M5 instance holds for both Ref programs (`typedStateF_load_ref`, `typedStateF_load_get`, `membership/verify-fits.lean`).
- The slice-5 walk re-proves over `Fits`: 58 of 882 copied lines become 20, in 8 declarations, and every statement changes by a rename only (`walk.diff`, reproduced byte for byte).

**The runtime twin.** A host check cannot decide a `Prop` over a world. The fiber-slice prototype's `fitsAt decl allocated path v ty` is the decidable version. It is the same recursion, reading a declaration function, and it answers with a located refusal (a value path and a reason). Proved in `fiberslice/Research/Pass/FiberSlice/Proofs.lean`:
- it implies `Val.hasTy`;
- on values with no fiber handle it gives exactly today's verdict;
- its verdict carries over to any table at most as wide as the registry.

The theorems are `fitsAt_hasTy`, `fitsAt_none_of_hasTy`, `admitD_eq_of_fiberFree` and `fits_narrower`. What is missing is the bridge from the runtime verdict to `Fits` in the world (§4, K6).

### 2.3 One lift carries a fact through the machine

Three generic theorems are proved in `lift/Lift.lean` (71 theorems, none reaching `Classical.choice`):
- **The command loop.** A fact that every command keeps, on a machine that has not halted, holds after `driveState` at every fuel, at a later world (`driveState_lift`).
- **One decision.** The decision lift (`stepDecisionState_lift`) takes three kinds of premise:
  - the command fact;
  - a snapshot fact, for the tasks a `fire` holds outside both the machine and the queue;
  - one premise per edit the decision makes outside the loop.

  The bundle has 13 fields (`DecisionLift`), and the split over decisions is exhaustive.
- **A whole run.** By induction over the tape or the history (`replayEval_lift`, `reachable_lift`, `foldl_lift`).

A frame law sits under all three (`driveStep_append`). Running a command on `rest ++ s` is running it on `rest` with `s` kept, except when the machine halts.

**The reuse is real, and checked:**
- The guard's four hand inductions on fuel (`Laws/Program/Guard/Driver.lean:18-99`) are one lift at four invariants (`driverContract_of_lift`).
- The guard's decision and run results follow without the hand proofs (`guard_decisionLift`, `guardState_steppedBy_of_lift`). The verifier's dependency walk confirms that none of these reaches the hand proofs (tested).
- The trace agreement is an instance at every level: `reachable_agrees_of` gives `M1Trace.reachable_agrees`.
- With today's `origin` field, four edits that rewrite a fiber through `update` need distinct fiber ids (`AgreesUpdates`; finite control C3). The fork ledger removes that need.

**For M6** the lift gives exact implications: `m6_capstone`, `m6_capstone_of_steps` and `m6_capstone_admitted`. But their premises cannot all hold today:
- M6's queue fact and typed state count a queued resume for a token not yet allocated as typed, because they require nothing of it. The next park makes that token live.
- At `perform sleep 1`, M5's `typedState_load` contradicts five of the 18 step obligations (`load_and_five_inconsistent`). It also contradicts `decision_preserves` at `fire` (`load_and_fire_inconsistent`). Both are in `lift/verify-*.lean`.
- Both results are conditional on M5 at that program, which is open.

The guard already carries the missing bound: `GuardState.keysBelow` and `ReservedKeys.below` (`Laws/Program/Guard/Core.lean:1066`, `:1082`).

### 2.4 How the boundary check, the typed state and M6 fit together

**Two layers**, as the host-answers note says. The runtime check decides what a host may send. The typed condition is what the preservation proof needs. They meet in three facts:
- the world's fiber table agrees with the registry (`FiberRegistryAgrees`);
- the runtime verdict reflects into `Fits`;
- preparation moves the value into the extended world.

**M6's statement, repaired, has six parts.** Each answers a proved counterexample.

| Part | Counterexample it answers | Where it lands |
| --- | --- | --- |
| 1. Count only tapes with no host answer | a `sleep` answered with `42` (`current_capstone_false`) | Codex item B |
| 2. A layer's body is built in a closed environment | `errLeak`, `forkLeak`, `discardLeak`, `crash1` (registry seat and its verifier) | new slice 1 |
| 3. A layer's value must fit its key's service type | `valueLeak`, `succeedLeak`, `crash2` | new slice 2 |
| 4. `Fits`, with liveness read from the tables | `Ref.make(5)`, which refutes every tape-restricted capstone (`restricted_capstone_refuted`); `step_loop` at `fork(Ref.make(5))` (`step_loop_refuted`) | row 96, with D3 |
| 5. The guard's token-freshness bound | the sleeper's early resume (`load_and_fire_inconsistent`) | new slice 4 |
| 6. A never-wrong exit clause, or a disclaimer | `crash1` and `crash2` die with `badName`, and the typed state's exit clause admits that at every type (`strongExit_of_dies`) | new slice 4 |

With all six in place, the generic lifts turn three premises into the capstone, as `m6_capstone_of_steps` already does for today's statement:
- `typedState_load`;
- the 18 per-command obligations, restated with the bound;
- `decision_preserves`, or its six edit facts.

The implication is proved; the premises remain to prove (slice 6). Each of the six parts is a bounded repair in the owner's sense; none is a large contract.

**The boundary, now.** Path A (Codex item A) refuses internal handle kinds in host rows, and any internal handle in a reply. It closes what the pass reproduced (`fiberslice/LivePath.lean`, `fiberslice/Holes.lean`):
- three live typing holes: a forged fiber, a forged context, and a layer's memo deferred read as a number;
- one wrong certificate: the `refOf` mislabel.

**The boundary, later**, with the parked host-services contract: lift path A one handle kind at a time, as declarations land.

For fibers the route is shown to work. The derived declaration plus `fitsAt` refuses the forged reply and applies the honest one on the live keyed session. Nothing changes for answers that hold no fiber (96,556 journals compared). Before it can land, it needs:
- the gap-1 repair;
- a rule for template rows: refuse open type variables at table admission, as the contract's `var` row says;
- declarations for internal fibers, with refusal of the ones no program ever held;
- the OCaml name-coupling check (§4, K14).

Contexts need an owner ruling on untyped keys such as the memo map (§4, K8). Cells and deferreds need creation records.

### 2.5 Numbers across the three faces, and FloatLib

**Where the faces stand:**
- The Lean reference is exact (`Nat`).
- The OCaml face lowers `Nat.add` to a raw `+`, which wraps at 2^62. It lowers `Nat.mul` to a product that saturates (`OCaml5/Lcnf/Translate.lean:162`, `:163-169`).
- The TypeScript face computes with doubles, which are exact only to 2^53.

**The evidence.** One checked, closed program with small literals gives three answers, and no face refuses. All three runs were reproduced, and the verifier reran them.

| Face | Answer |
| --- | --- |
| Lean | 2 / false / 2305843009213693954 / 5 / 416 |
| OCaml | 2 / true / -2305843009213693949 / 5 / 903 |
| rc.112 | 1 / false / 2305843009213693952 / 0 / 904 |

DI-56 ruled the fix on 2026-09-09: a bounded profile, with refusal, intermediate results included. Neither face implements it.

**Floats do not help**, because a double holds every natural only up to 2^53. The evidence supports this policy:

1. **A star around the reference.** The Lean reference stays exact. Each face is related to it by a simulation on one observation: inside the face's profile, equal values; outside it, a refusal. The faces are not compared with each other.
2. **The judgment that predicts the refusal point is proved.** `evalChecked`, with `evalChecked_ok_iff` and `evalChecked_refusal_outside`, is in `numbers/Checked.lean`. Its path is the right path (`evalChecked_refusal_located`, proved by the verifier).
3. **The models prove where the check belongs on each target:**
   - On TypeScript, a check after the operation is exact (`jsAdd_checked`, `jsMul_checked`).
   - On OCaml, a plain check after `+` is blind, because the wrapped sum is negative. A check before the operation is exact (`mlAdd_under_check`), and so is one with a sign test (`mlAdd_signcheck_exact`, verifier).
   - Inside its bound, each target model computes the machine's own value (`ocaml_matches_machine`). The TypeScript lemma `typescript_agrees` now holds without its one assumption (`hdiv`, `numbers/verify-div.lean`).
   - The models match the real engines on 50,000 sampled operations (tested). One edge differs, `min_int / -1`, and it cannot occur inside the profile.
4. **Three ways to get there on the native face:**
   - checked rows written per target (DI-56 as written);
   - the refusal defined once in Lean, with the bound as data (L1), so that every target made from OCaml inherits it;
   - exact native naturals (Zarith), measured at 1.07 ns per addition. A checked addition also measured 1.07 ns, on the same one machine.

   L1 gives two faces the same refusal point when they run the same profile. The only other way the verifier found is a new engine-wide global that would also govern every counter. L1 is also the option that carries to the WASM route the owner named, because it does not lean on the native 63-bit `int`. That js_of_ocaml's `int` is 32 bits and wasm_of_ocaml's is narrower than native is assumed here, not checked; DI-56's framing repair for js_of_ocaml points the same way.

**FloatLib** (arXiv 2609.19352; read, not run, and the verifier re-read the sources) is a verified floating-point library. Its methods transfer. The library itself does not: it needs Lean v4.34.0, Mathlib and an axiom audit, and the owner has parked it. Seven methods transfer:
1. **Every compile-time substitution carries a proved equation on a stated domain.** `Translate.builtin?` has none today. `numbers/Models.lean` writes the first ones, for the `Nat` rows.
2. **A fast backend is a value that carries its proof** (`run_eq_spec`), so choosing it cannot change an answer. Today the engine's `Fast` and `Ref` carriers are tied only by a differential.
3. **Propose, then check cheaply.** FloatLib accepts a division result only after a cheap proved check. This repository already does the same in `Schema.encode`, and would do it in the host check. The pre-check `a ≤ bound − b` is another instance.
4. **Decide whole small domains** instead of sampling them.
5. **Test the specification against an outside oracle, under a named relation,** and tie the fast versions to it by proof.
6. **State the trust boundary.**
7. **Natural numbers as several machine words, proved equal to `Nat`,** if the native face should ever be exact and still made from LCNF.

Binary64 arithmetic is needed only if the language models rc.112's `Duration`, `Schedule` or `Random` arithmetic. Then `Math.pow` must stay a host answer, because the standard does not fix its rounding.

## 3. What is proved, what is tested, what is read

### 3.1 Registry seat

| Claim | Evidence | Kind | Verdict |
| --- | --- | --- | --- |
| Gap 1. A layer's effect body is checked at `[]` but built in the enclosing runtime environment. `errLeak`, checked at `(nat, string)`, fails with `9` on both machines; the control fails with `"x"`. | `registry/LayerGap.lean`: `errLeak_checked`, `errLeak_native_exit`, `errLeak_violates`, `errLeak_reference_exit`, `errLeakControl_fits` | proved | confirmed, and wider. `effectDiscard` has the same gap (`discardLeak_native_exit`). `crash1` dies with `badName` on both machines. `admitProgram` accepts the program (`errLeak_admitted`). All three are proved in `registry/verify-Gaps.lean`. The live session reaches the bad exit (tested). |
| Gap 2. A layer leaf's value is never compared with its key's service type. | `valueLeak_*`, `succeedLeak_*`, `key_service_nat`, `valueControl_fits` | proved | confirmed. The pinned `tsgo` refuses the printed TypeScript of both programs (TS2379, TS2345; tested), so the printer emits code that does not compile for an admitted program. `crash2` dies with `badName` (proved). |
| M6's capstone is false on a tape with no host answer. | `m6_capstone_false_without_hosts`, `m6_capstone_false_valueLeak`, `tape_answers_nothing` | proved | confirmed |
| The printed TypeScript of `errLeak` follows the checker, not the Lean runtime. | a print guard | tested | confirmed, and upgraded: run under rc.112, it fails with `"x"` (reproduced) |
| `staticEnvAt` is sound, and at a fork the declaration is the handle's `fiberOf`. | `registry/Proofs.lean`: `stepEnv_checks` (53 cases), `envAlong_checks`, `staticEnv_checks`, `fork_handle`, `api_fork_handle`, `declared_*` | proved | confirmed (18 axiom lines, not 19) |
| `staticEnvAt` is the checker's own environment. | `registry/StaticEnv.lean`: 6,662 paths with 0 disagreements; 10,728 sites with 0 failures; 11 of 11 broken folds caught | tested | confirmed, for program nodes |
| Every lane fiber is declared and fits its declaration. | `registry/Declared.lean`: 34,336 runs, 70,080 fibers, 0 violations; four wrong registries fail | tested | confirmed. Limits: the 6,826 internal fibers are declared with answer `unknown`, and the deep check reads success values only. |
| `spawn` is the only creator of forks, with three callers; layer builds are a third internal kind. | reading; `registry/Sites.lean` | reading, tested | confirmed; the reference machine records the same origins (`origin_eq_ref`, proved) |
| A running internal daemon reads as an unpinned daemon. | `registry/Sites.lean` | tested | confirmed, and wider: race entrants too (tested); parallel-close finalizers by reading |
| Cells and deferreds carry no creation site. | `registry/Cells.lean` | tested | confirmed |
| The note's counts. | `LayerGap.lean` has 30 theorems; `proofs.log` has 18 lines | — | partly (count slips only) |
| Proposal: the checker calls `stepEnv`. | — | — | partly: it re-checks siblings, and a left-nested chain of binds doubles the work at each level |
| Proposal: cells compare exactly at the boundary. | — | — | partly: compare both ways, as `Ty.lean:453-454` does |

### 3.2 Membership seat

| Claim | Evidence | Kind | Verdict |
| --- | --- | --- | --- |
| `Fits` implies `Val.hasTy`, under every invariance reading and at every `Ty`. The converse is false. | `Fits.lean:247` `fits_hasTy`; `Gaps.lean:287` `converse_false` | proved | confirmed |
| Six value gaps G1–G6: product, Result, successful exit, union, snapshot, native cell spelling. | `Gaps.lean:299-362`, 18 theorems | proved | confirmed |
| `Fits` is closed under `Ty.sub`; the old judgment and the equality reading are not. | `fits_sub`, `strongValue_not_closed_under_sub`, `fitsEq_not_closed_under_sub` | proved | confirmed; the other direction of the mutual subtyping is `sub_ref_backward` (verifier) |
| M5's `typedState_load` is false at `Ref.make(5)`. | `typedState_load_false` | proved | confirmed, and understated. The verifier refutes, each matched to the ledger's own statement: the obligation itself (`typedState_load_refuted`); the M6 capstone (`typedState_reachable_refuted`); every tape-restricted capstone (`restricted_capstone_refuted`); and `M6Ledger.step_loop` (`step_loop_refuted`). The bind program and `Deferred.make()` refute it too. All proved in `membership/verify-{load,step}.lean`. |
| Under `Fits`, the loaded code of `Ref.make(5)` is typed. | `Walk.lean:1246` `refProg_typedF` | proved | confirmed, and stronger: the M5 instance itself holds under `Fits` for `Ref.make(5)` and for the bind program (`typedStateF_load_ref`, `typedStateF_load_get`) |
| G6's cost: checker admission does not imply program typing under the old judgment. | `admitted_but_untypable` (verifier) | proved | new (from the verifier) |
| The pair program needs `Fits`. | `strongValue_no_fst`; `fits_pair`, `fits_fst`, `await_fits`; three guards | proved, tested | partly: "the steps M6 needs" is a reading |
| Monotonicity. The old monotonicity laws were unproved, not false. | `fits_mono`, `fitsExit_mono`; `OldMono.lean` | proved | confirmed; the verifier matched both proofs to the ledger |
| Liveness, the list arm, the fold. | `fits_live`, `live_iff_handlesLive`, `fits_list_iff`, `FitsInv.eq_cata` | proved | confirmed; `fold_of` is at `Fits.lean:226`, not `:186` |
| The slice-5 walk re-proves: 58 of 882 lines become 20, in 8 declarations. | `Walk.lean`, `walk.diff` | proved, measured | partly: the seven obligation namespaces only elaborate, so the claimed ceiling change is not measured |
| Inventory: 150 declarations to migrate (90 in `src`, 60 in tests). | `Inventory.lean` | reading | confirmed |
| Estimate (two or three slices) and placement. | — | reading | unverified; two placement faults (K13) |

### 3.3 Lift seat

| Claim | Evidence | Kind | Verdict |
| --- | --- | --- | --- |
| The command-loop lift holds generically. | `Lift.lean:68` `driveState_lift`; `:95`; `:117` | proved | confirmed |
| The guard's four hand inductions are one lift. | `driverContract_of_lift` | proved | confirmed (the dependency walk is tested) |
| The frame law, with a halt as the one exception. | `driveStep_append`; control C2 | proved, tested | confirmed; a native halt drops the queued tail (tested) |
| The decision lift: 13 fields, exhaustive, with a snapshot fact for `fire`. | `stepDecisionState_lift`, `Guarded` | proved | confirmed |
| The answer premise must hold after the answer's `resume`. | `guardQueue_refuses_live_answer` | proved | confirmed |
| Inert answers go around the queue. | `inert_resume`, `answer_of_split` | proved, reading | confirmed; the seat missed the dual case, a token declared only later |
| The trace agreement is an instance at every level. | `reachable_agrees_of`, `ledger_*` | proved | confirmed |
| The guard's decision and run results are instances of the lift. | `guard_decisionLift`, `guardState_steppedBy_of_lift` | proved | confirmed |
| `decision_preserves` follows from the 18 obligations and six edits. | `m6_decision_preserves` | proved (an implication) | partly: its premises contradict M5 at `perform sleep 1` |
| The M6 repair holds, and the plan's §10 withdrawal is reversed. | `m6_capstone`, `m6_capstone_of_steps`, `m6_capstone_admitted` | proved (implications) | refuted as a repair by `load_and_fire_inconsistent`, `load_and_five_inconsistent` and `load_and_steps_inconsistent` (proved, conditional on M5 at `perform sleep 1`). Also, under the old judgment the repaired statement is itself false at `Ref.make(5)`, unconditionally (`restricted_capstone_refuted`, membership verifier). |
| Today's capstone is false. | `current_capstone_false` | proved | confirmed; the verifier matched it to the ledger |
| The book's lockstep lift is not an instance. | `Laws/Machine/Book.lean:694-735` | reading | confirmed |

### 3.4 Fiber-slice seat

| Claim | Evidence | Kind | Verdict |
| --- | --- | --- | --- |
| On the live keyed session and on the tape route, the forged fiber reply is refused and the honest one applied. | `LivePath.lean:72-126` | tested | confirmed for closed rows. It fails at a template row (`verify-Template.lean`) and for a fork in a layer body (`verify-LayerEnv.lean`); both tested. |
| Every nesting gap is refused at its value path. | `LivePath.lean` §2; `verify-Nesting.lean` | tested | confirmed |
| `envAt` is the checker's environment, and `siteDecl` is the checker's type at every fork and race site. | `Sites.lean` (17 theorems) | proved | confirmed; these are facts about the checker, not the runtime |
| The declaration needs the site's environment. | `LivePath.lean` §3, with a red control | tested | confirmed |
| Nothing else changes. | `admitD_eq_of_fiberFree`, `acceptReply_of_acceptReplyD`, `fitsAt_hasTy`, `fitsAt_none_of_hasTy` | proved | confirmed, for answers with no fiber handle |
| 96,556 journals agree with production. | `Replays.lean` | tested | confirmed; 57,340 of them never reach the new clause |
| The declaration lane: 28,918 source forks, 0 violations. | `DeclLane.lean` | tested | partly. The arity check runs one tape of four. The `never` control does not run the violation branch. The invariant is false outside the corpus. |
| Contexts and memo deferreds are live holes today. | `Holes.lean` | tested | confirmed; the proposed context clause refuses honest contexts read under a layer (`verify-Context.lean`) |
| The engine has no answer admission, so nothing generated changes. | reading | reading | partly: the engine calls a specialization of `replayCheckedFrom` by name, so the `lcnf` byte check is owed |
| The runtime check carries over to narrower tables, and an admitted value is strong (the fiber part). | `fits_narrower`, `envelopeD_fits_table`, `admitted_value_strong` | proved | partly: `admitted_value_strong` restates two of its own hypotheses, and the chain from the admission to the world is open |
| P0: path A breaks no in-tree row. | the path probe's 15 rows | — | refuted: `Test/Api/ExternalContract.lean:15` answers `Ref<number>` (`verify-PathA.lean`, tested) |

### 3.5 Numbers seat

| Claim | Evidence | Kind | Verdict |
| --- | --- | --- | --- |
| One checked program gives three answers, and no face refuses. | `Faces.lean`, `ocaml/faces.log`, `ts/faces-run.log` | reproduced | confirmed |
| DI-56 is ruled and implemented on neither face. | reading | reading | confirmed |
| `evalChecked` is a located refusal, complete against `InProfile`. | `Checked.lean`: `evalChecked_ok_iff`, `evalChecked_refusal_outside` | proved | confirmed; the path is right (`evalChecked_refusal_located`, verifier) |
| Where the check goes on each target. | `Models.lean`: `jsAdd_checked`, `mlAdd_under_check`, `mlMul_under_check`, `evalIn_ok_iff` | proved | partly. On OCaml, a check after the operation is exact with a sign test (`mlAdd_signcheck_exact`). The saturating product's post-check is exact below `max_int` (`mlMul_postcheck_exact`). `evalIn` needs its inputs inside the bound. |
| Each model equals the machine inside its bound. | `Face.sim`, `ocaml_matches_machine`, `typescriptExactDiv_matches_machine` | proved | confirmed; the division lemma is now proved (`hdiv`), so `typescript_agrees` holds with no assumption |
| The models match the engines. | 20,000 TypeScript and 30,000 OCaml operations, 0 differences | tested | partly: sampled, and `min_int / -1` differs; the verifier widened the red controls |
| The project's own translator lowers the checks as the models say. | `Lower.lean`, `ocaml/lower.log` | reproduced | confirmed |
| A literal above 2^53 means three different numbers; a literal at 2^62 is refused with no location. | `Faces.lean`; the engine's decoder | tested, reproduced | confirmed |
| The engine already catches `Profile_refusal`. | reading | reading | partly: only on the `step` path; `api_run` would let it escape |
| Stale documentation: `e4_nat.mli`, `NOTES.md` §5, `Json.ofNat`. | reading | reading | confirmed |
| The FloatLib reading. | WebFetch | reading | confirmed, with two small corrections |
| The cost of one addition. | `ocaml/bench_add.log` | measured, one machine | confirmed within 2% |
| L0 + T1 + N1 gives the same refusal point on every face. | note §7 | — | refuted by the verifier: T1 refuses at 2^53−1 and N1 at 2^62−1 |

### 3.6 This seat's own check

**Codex item A, step 2, flips one in-tree guard.** Tested in `ItemA.lean` (Appendix A), against a copy of `externalValue` and `admitAnswer`'s success arm with the brief's one change.
- The fixture `Test/Api/ExternalContract.lean:55-57` pins `deadHandle` for a dead cell answered at the row `"cell"`.
- Under the brief's rule, the same reply is refused earlier, as `answerType`.
- A live cell at that row is accepted today and refused under the rule.
- Green run: exit 0, five guards pass. Red control, expecting the old refusal under the rule: exit 1, two guards fail.

By reading, the rule makes `deadHandle` unreachable for success values. No other in-tree host row answers an internal kind; I grepped every `registration := .external` row under `Test/`.

### 3.7 Claims to drop or flag

1. **"The lift covers M6" and "the plan's §10 withdrawal is reversed".** Refuted. The withdrawal stands.
2. **"Path A breaks no in-tree row".** Refuted, and step 2 changes one guard (§3.6).
3. **"The answer-free restriction is M6's current-scope repair"** (host-answers note §4, plan decision 5). It is true that the restriction is necessary. It is false that it suffices.
4. **"L0 + T1 + N1 gives one refusal point on every face".** Refuted.
5. **"The fiber slice regenerates nothing".** Unshown, until the `lcnf` byte check is run.
6. **"The OCaml engine agrees with the Lean runtime on the gap programs".** Unverified; nobody ran it.
7. **The membership estimate and its placement.** Unverified, with two faults (K13).
8. **"Silently"** in the fiber-slice note's F13. Wrong: the build reports the break.

## 4. Conflicts, and what to do about each

**K1. Does the lift cover M6?**
- The lift seat says it does, and that the plan's §10 withdrawal should be reversed.
- The lift verifier refutes this. So do the membership verifier (the capstone is false at `Ref.make(5)` under every tape restriction) and the registry seat (the layer gaps).
- Recommendation: keep the withdrawal. Land the generic family now. Land the `m6_*` instance only after slices 1–4.

**K2. Is the answer-free restriction a repair?**
- Codex item B and plan decision 5 call the answer-free restriction the repair. The pass refutes the restricted capstone on host-free programs, three ways.
- Recommendation: keep item B, because it is necessary. Register `E4-SCHED-CE-015` as repaired for host answers only.
- Mark the capstone's docstring as still refuted, citing the new counterexamples. Register those counterexamples as open (ids for the coordinator): the layer environment, the layer value, `Ref.make(5)`, and the sleeper's early resume.

**K3. Does path A break anything in the tree?**
- Codex item A, the host-answers note B1 and the path probe all say it breaks nothing.
- In fact, step 1 refuses the in-tree fixture row `ExternalContract` `"cell"` (`Ref<number>`), though no test admits that table. Step 2 flips one guard (§3.6). The brief's stop rule ("a test or in-tree row legitimately needs an internal handle") will fire.
- Recommendation: tell Codex before it gets there. Keep the rule. Turn the row into a refused-profile fixture: `admitProgram` refuses the table at the row's path. Change the dead-cell guard to the new reason. Record that host-returned internal cells wait for the parked registry; this is the authority question of row 7.
- Small (reading): the brief's new failure-arm check changes no behaviour. `Err` payloads are already handle-free (`valOfErr_keys`, `causeImage_handleFree`, as the fiber-slice verifier notes). State it as a theorem rather than as new runtime code.

**K4. Should the fork ledger carry a `kind`?**
- The registry seat wants a three-valued `kind` now. The fiber-slice seat says its slice does not need it. The Codex brief says not now.
- The census inference ("empty site = finalizer") holds natively today. Its risk is a new caller that forgets its site.
- Recommendation: follow the brief and add no `kind`, since the registry is parked. In item C, drop the six silent `site := []` defaults (`Fibers.lean:304-310`, `:926`, `:957`, `:1428`, `:1440`, `:1451`), so that a missing site is a compile error. Add a `merge`/`mergeAll` layer-build fixture to the comparison runner; its fixture list names only two internal kinds. Add `kind` when the registry unparks.

**K5. Two static-environment folds.**
- The registry's `stepEnv`/`envAlong`/`staticEnvAt` carries the loop flag. The fiber-slice seat's `envStep`/`envAt`/`siteDecl` does not.
- The registry seat proposed that the checker call the fold. The verifier showed that re-checks siblings.
- Recommendation: one fold, keeping the loop flag, in `Program/Sites.lean`. Make exactness hold through one shared rule per node: the checker and the fold both read it, given the sibling types. Do not make the checker call the fold. Two ways to meet the house rule on traversals: generate the fold's shape from `binders.json`, which already gives the number of binders each child adds, with the types from the checker's rule; or list it in the traversal census with its connectors, the oracle battery and arity agreement with `Node.childLevel`. Parked, with the registry.

**K6. Three membership checks.**
- The registry's `fitsB` is Boolean and checks success values only. The fiber slice's `fitsAt` gives located refusals and reads fiber declarations only. The membership seat's `Fits` is a `Prop` covering every constructor and every handle kind.
- Recommendation: one judgment, two carriers. `Fits` is the world's. `fitsAt` is the runtime's located-refusal checker. Write both as folds over `Ty`, joined by algebra agreement ("two folds agree when their algebras do").
- Then prove one reflection lemma: if the world's tables agree with the registry, `fitsAt` accepting implies `Fits`, after preparation, in the extended world.
- Variance follows D1 and D2: fibers covariant; cells and deferreds compared both ways. Failure causes need no handle check today, because `Err` is a closed alphabet (`valOfErr_keys`).

**K7. Undeclared internal fibers.**
- The fiber slice admits them "at the top", at `fiberOf unknown unknown`. The registry declares them, and refuses at the boundary the ones no program held.
- The contract (§3) says "including internal forks". `WorldValid.fibers` and `HandlesLive` need a `Γ` entry for every fiber.
- Recommendation: the registry's rule. Parked.

**K8. Context clauses.**
- The fiber slice's `servicesFit` refuses keys with no static type, so it refuses an honest context read under a layer, which carries the memo-map key `(3,3)`. The membership seat's `ServicesFit` checks typed keys and asks only liveness of the others.
- Recommendation: the internal judgment uses the membership seat's clause. At the boundary, contexts stay refused (path A) until the owner rules whether a host may hand the program a context holding a memo map. That is an authority question.

**K9. "Exact" invariance versus `Equiv`.**
- The contract's matrix (§4) says "exact invariant declared type" for `refOf`/`deferredOf`. The membership seat reads it as `Equiv`, subtyping both ways.
- Recommendation: `Equiv`. The equality reading loses values when a type is spelled differently (`fitsEq_not_closed_under_sub`, proved). Read the contract's "exact" as `Ty.sub`'s invariance.

**K10. Template rows.**
- The contract's `var` row says to instantiate templates or refuse open variables. The fiber-slice prototype does neither: it refuses honest replies at template fiber rows.
- Recommendation: refuse open variables in host rows' answer and error columns at table admission. For fiber templates, path A already does this. Instantiate from the call's static type later.

**K11. One refusal point across the number faces.**
- The numbers seat promised one refusal point under L0 + T1 + N1. Its verifier found:
  - the bounds differ;
  - T1's throw carries no location, and surfaces in two forms;
  - `api_run` does not catch the refusal;
  - L1 covers terms only.
- Recommendation: relate each face to the reference under its own profile (§2.5, point 1). The same point across faces is promised only for faces running the same profile, which needs L1. A printer refusal of big literals is a static admission check. Give it a Lean twin (every literal within the profile) beside the dynamic `evalChecked`, so that both sides judge the same program.
- A check before or after the operation: both are exact for hand-written OCaml rows (with a sign test after). Under L1 the check is written on `Nat`, so it must come first.

**K12. The scalar policy's scope.**
- The contract's scalar policy covers counters, ids, tokens and fuel. The numbers seat covers program arithmetic.
- Recommendation: state two policies. Program values follow the profile. Machine counters rest on `NOTES.md`'s length argument on 63-bit targets; reopen that argument for 32- and 31-bit targets before WASM.

**K13. Where `Fits` lives.**
- The membership seat would put `fold_of` in `Laws/Program/Folds/Ty.lean`, and the bridge laws in the new module. The verifier found an import cycle, and names used before they are defined.
- Recommendation: put `fold_of` in the new `Laws/Program/Typed/Membership.lean`. Put the bridge laws (`live_iff_handlesLive`, `fitsEq_strongValue`) in `Typed/Admission.lean` or later. Add an argument-order adapter where the ledger needs one.

**K14. Small conflicts:**
- The lift seat's Q2 would replace `decision_preserves` by the six edits. Keep `decision_preserves` until the bound lands, because replacing it moves the defect into the 18 obligations.
- The fiber slice says no generated group changes. Run `python3 scripts/generate.py --only lcnf`, byte-identical, and `dune build` whenever `replayCheckedFrom` changes: the engine calls `step_decision_state_at_program_replay_checked_from_spec_1` by name.
- The origin plan's §3 names two internal fork kinds. Amend it to three.

## 5. Decisions for the owner

The authority-promotion plan's thirteen decisions appear below with their numbers there. The plan's status line says they became rows 91–103. The Codex brief's citations (rows 91–97) and commit `6f7f6601` (row 100) fit plan #n = row 90+n. That mapping is read from those two sources, not from `docs/core/decisions.md`.

### 5.1 Changed

1. **Plan #1 (row 91), the ledger's construct kind.**
   - The pass makes it concrete: `inductive ForkKind | action | raceEntrant | finalizer`. It also finds a third internal kind, layer builds through the `fork` arm.
   - Recommendation: no `kind` now, because the registry is parked; add it when the registry unparks. In item C, drop the six silent `site := []` defaults and add a layer-build fixture.
2. **Plan #5 (row 95), M6 counts runs with no host answer.**
   - Still recommended, and necessary, but not a repair. The capstone stays false on host-free programs: through the layer gaps; at `Ref.make(5)` under every tape restriction; and, conditionally, through the token gap.
   - Recommendation: scope `E4-SCHED-CE-015` to host answers, and register the host-free counterexamples as open. The repair is completed by new decisions 1–4 below and by plan #6.
3. **Plan #6 (row 96), the constructor-complete membership judgment.** Adopt `Fits` (membership note §2), with four sub-decisions:
   - **D1.** Invariance at cells and deferreds is subtyping both ways. Recommended.
   - **D2.** The native spellings mean cells or deferreds declared at `nat`. Recommended; otherwise M6 cannot type a native Ref operation reached through a variable.
   - **D3.** Liveness is read from the world's tables. Required: under store lengths M5 is false (proved), while with the tables the M5 instance holds for two allocation programs (proved).
   - **D4.** `unknown` keeps its internal meaning; the external boundary refuses unregistered handles. Recommended.
4. **Plan #7 (row 97), the interim refusal of internal handles, with the registry as the route.**
   - Two changes to the facts. First, the rule refuses one in-tree fixture row, and step 2 flips one guard (§3.6). Recommendation: accept that loss; host-returned internal cells wait for the parked registry.
   - Second, the fiber registry is now shown feasible: a sound fold, and tested lanes. Before it can lift path A for fibers, it needs: the gap-1 fix (new decision 1); refusal of open type variables in host rows; declarations for internal fibers, with refusal of never-held ones; and an owner ruling on contexts that carry untyped keys such as the memo map.
   - Unchanged: whether a host may return any existing fiber of the right type, or only a handle it was given ("echo-only"). Types cannot settle that; it is an authority question (row 7).

### 5.2 New

1. **Layer gap 1: repair it in the runtime.** Build a layer at a closed point, in `provideLayerWithK` and in the reference denotation. Recommended over making the checker read the enclosing environment, for two reasons: it matches the design text (`Program/Eff.lean:375-378`), the printed TypeScript and memo identity by path (DB-12); and one entry covers every layer build.
2. **Layer gap 2: repair it in the checker and in `LayerHasTy`.** A `succeed` or `effect` leaf must fit its key's service type, and a key with no service type is refused. This amends a frozen judgment: `LayerHasTy.succeed` today says "the value's type plays no part". Recommended, because TypeScript, with Effect's own types, already refuses these programs (the pinned `tsgo`: TS2379, TS2345).
3. **M6's typed state carries the guard's token-freshness bound.** Every internal key and every queued resume key lies below `nextToken` (shapes in `lift/verify.md` §3). The other option states the obligations on reachable machines only. Recommended: the bound, because the guard already proves it for the same code.
4. **"Never goes wrong" in M6.** Either an exit clause that refuses the lane's bad defects (`badName`, `notImplemented`, `missingService` with an empty requirement row; `Test/Program/ExitTypeLane.lean:34-37`), or an explicit statement that M6 does not claim it. Recommended: the clause. At the least, write the disclaimer now.
5. **The number policy.** Recommended:
   - now: L0 (the proved judgment) and T1 (TypeScript checked atoms, the harness classifying both forms a refusal takes, a located refusal of big literals);
   - on OCaml-made targets: L1, the refusal defined once in Lean with the bound as data, checked also on host answers and the clock;
   - exact native naturals (Zarith) only when a native use needs values above 2^62;
   - each face related to the reference under its own profile.

   This keeps DI-56's ruling and changes its implementation plan. Choosing exact native naturals would amend DI-56 for the native face.
6. **FloatLib: learn its methods, adopt nothing.** It is already parked. Binary64 is modelled only with `Duration`, `Schedule` or `Random` arithmetic, and then `Math.pow` stays a host answer. Recommended.
7. **The generic lift family lands now.** Re-derive the guard's `DriverContract` and delete its four hand inductions. No M6 instance until new decisions 1–4 and plan #6 have landed. Recommended.

### 5.3 Unchanged

| Plan # | Decision | What the pass adds |
| --- | --- | --- |
| #2 (row 92) | the reader switch rests on bounded evidence | `origin_eq_ref` (proved): the reference machine records the same origins, which supports moving the `FMeans` readers |
| #3 (row 93) | the trace agreement stays an obligation; `forkedOf` moves to `Test/` | `reachable_agrees_of` derives `M1Trace.reachable_agrees`; the ledger removes the distinct-id premise (finite control C3) |
| #4 (row 94) | automation after three hand proofs | the lifts are the general theorems; automation was not tried |
| #8 (row 98) | one public typed host replay route over the keyed journal | the raw certified routes still finish the forged program, by design (`fiberslice/verify-Raw.lean`); keep that as a control for the migration |
| #9 (row 99) | external completion before the public guarantee | reinforced: even the internal guarantee is false today |
| #10 (row 100) | stable host resource identity, preparation, cleanup | not probed |
| #11 (row 101) | compose only through named connections | the number policy is one such connection, and FloatLib's equation-per-substitution is the method for the translation table |
| #12, #13 (rows 102, 103) | homes of the system map and the host boundary | executed |

## 6. Next slices, in order

**Step 0. Amendments to Codex's work in flight.** Codex is on items A–C now; the pass supports these amendments.
- **A.** Pre-rule the `ExternalContract` fixture before the stop rule fires (K3). `deadHandle` stays as a constructor, for the parked registry.
- **B.** `E4-SCHED-CE-015` is repaired for host answers only. The capstone's docstring cites the open counterexamples (K2).
- **C.** Drop the six silent site defaults. Add a `merge`/`mergeAll` layer-build fixture to `Test/Api/ForkLedgerRunner.lean`. Add no `kind` (K4).
- **Addendum D:** slice 5 below.
- **Addendum E:** slice 3 below.

**Slice 1. The layer body's environment (runtime and reference).**
- Files:
  - `Program/Compile.lean`: `provideLayerWithK` (`:767-781`) builds at a closed point at `:774` and `:777`. Every layer build starts from this one entry, by the verifier's reading: `effect`, `effectDiscard`, `ref` redirects, `merge`/`mergeAll` siblings and `provide` chains.
  - `Laws/Program/DenoteR.lean`: `provideLayerR` (`:525`) and the `provideLayer` arm (`:671-672`), changed in step, so `run_eq_ref` keeps its shape.
  - the laws that unfold them;
  - a counterexample file under `Test/Counterexamples/`.
- Statement: a closed point, for example `{ p.child 0 with env := [] }` (name proposed), and a lemma that every layer build starts at a point with an empty environment. That lemma is the runtime side of `LayerHasTy.effect`'s premise `HasTy sig [] body t`.
- First probe: `registry/LayerGap.lean` and `registry/verify-Gaps.lean`, restated with the repaired expectations:
  - `errLeak` fails with `"x"` on both machines, matching the printed TypeScript under rc.112;
  - `forkLeak`'s child and `discardLeak` follow the checker;
  - `crash1` no longer dies with `badName`;
  - `fiberslice/verify-LayerEnv.lean`'s fork returns its declared `nat`.
- Gates:
  - `provideLayerWithK` and `constructionAt` are in `ocaml/gen/closure-api_engine.tsv` (grep), so regenerate in the fixed order, then `dune build` and `make check-ocaml`;
  - run `errLeak` on the OCaml engine, which nobody has done yet;
  - register `E4-PROV-CE-005` (proposed id).
- Order: after item C's regeneration, so that one regeneration does not race another.

**Slice 2. A layer's value against its key's type (checker and judgment).**
- Files:
  - `Program/Checker.lean`: `checkLayer` (`:226-236`);
  - `Laws/Program/Typing/HasTy.lean`: `LayerHasTy.succeed` and `.effect` (`:414-426`);
  - `Laws/Program/Typing/CheckSound.lean`: `checkLayer_sound` (`:287`) and `checkLayer_complete` (`:544`);
  - `Laws/Program/Typing/Sound.lean` (`:88-92`, `:151`);
  - the refusal alphabet: a constructor like `valueNotSubtype`. Check whether a derived manifest lists that alphabet.
- Statement (shape; `litTy` is a proposed name):
  - `succeed` gains `sig.serviceTy key = some ty` and `Ty.sub (litTy value).normalize ty.normalize = true`;
  - `effect` gains `sig.serviceTy key = some ty` and `Ty.sub t.answer.normalize ty.normalize = true`;
  - a key with no service type is refused, as `service` refuses it.
- First probe:
  - `valueLeak`, `succeedLeak` and `crash2` are refused by `Api.typeOf` at a path;
  - `valueControl` still checks;
  - `registry/verify-LaneReach.lean` shows that no lane program changes (0 candidates).
- Gates: `checkLayer` is not in the engine closure (grep: 0 rows), so no LCNF regeneration. Build the typing laws narrowly. Register `E4-PROV-CE-006` (proposed id).

**Slice 3. The membership judgment (row 96; Codex addendum E).**
- Files:
  - new `Laws/Program/Typed/Membership.lean`: the definitions of `membership/note.md` §2 with `inv := Equiv`, `fold_of` in this module, and the laws that do not mention old names;
  - bridge laws in `Typed/Admission.lean`;
  - the cut-over of `Typed/{Admission,Residual,Stack,Assembly}.lean`, following `membership/walk.diff`;
  - the 60 test declarations;
  - the proofs lean on the existing `Effect4.TypedState` aesop bank, which already closes the heap-extension goal (its red control is in `membership/Fits.lean`).
- Statements: `membership/note.md` §6: `fits_hasTy`, `fits_live`, `fits_sub`, `fits_mono`, `fitsExit_mono`, `fitsExit_success_iff`, `fitsExit_failure_iff`, `fitsExit_of_clean`, `fitsExit_failure_of_error`, `fits_list_iff`, `fits_fst`, `await_fits`.
- First probe:
  - green tests: `membership/verify-fits.lean` (`typedStateF_load_ref`, `typedStateF_load_get`);
  - negative tests: `Gaps.lean`'s `g1`–`g6` and `typedState_load_false`, kept against a local copy of the old judgment, as item B keeps `ReviewedRReachable`.
- Gates: narrow builds; laws only, so no regeneration. Register G1–G6, G7 and G8/G10 under the next `E4-TYPED-CE` ids.

**Slice 4. The rest of M6's statement.**
- Files:
  - `Laws/Program/Typed/Assembly.lean`: `TypedState`, `QueueOk`, `StepPreserves`, the snapshot fact;
  - `Typed/Contracts.lean`: `ResumeOk`;
  - `Typed/Validity.lean`, if the bound goes into `WorldValid`;
  - the guard's key lists (`Laws/Program/Guard/Core.lean:124-138`), generalized over the code type.
- Statements:
  - `InternalKeysBelowR`, `QueueFresh`, `StepPreserves'` and `m6O'` (lift verifier §3; not compiled);
  - an exit clause `NoShapeDefect ty ex` (name proposed): the lane's `badDefect`, lifted into the typed state.
- First probe:
  - `lift/verify-steppreserves.lean` and `lift/verify-decision.lean`: the early queue must fail `QueueFresh`, because token 0 is not below `nextToken = 0`;
  - a proof of `typedState_load` at `perform sleep 1`: a green control, and it makes the old-statement refutations unconditional;
  - `crash1` and `crash2` fail the new exit clause.
- Gates: narrow builds. Register the sleeper's early resume.

**Slice 5. The lifts and users 1–3 (rows 93–94; Codex addendum D).** It can run beside slices 1–4 once item C has landed.
- Files:
  - new `Laws/Machine/Lift.lean`, with the signatures of `lift/note.md` P1;
  - `foldl_lift` and `reachable_lift` beside `Guard.Reachable`;
  - optionally, `Laws/Program/Guard/Driver.lean` re-derived from `driverContract_of_lift`, with its four hand inductions deleted;
  - users 1–3 against the ledger.
- Statements:
  - `StepKeeps`, `driveState_lift`;
  - `driveStep_append`, restated arm by arm: the probe's proof uses `first | …`, which `src/` forbids;
  - `Guarded`, `DecisionLift`, `stepDecisionState_lift`, `answer_of_split`, `AdmittedReplay`, `replayEval_lift`;
  - `reachable_agrees_of`, taking `M1Trace` from 2 to 0.
  - The `m6_*` instance waits for slices 1–4.
- First probe:
  - `lift/Lift.lean` against the tree;
  - the verifier's dependency walk, as the check that the re-derived results do not reach the hand proofs;
  - keep the `parkedAt_em` pattern, because `by_cases` on an existential reaches `Classical.choice`.

**Slice 6. M5–M7, on the owner's route.**
- `typedState_load`: the general form of `typedStateF_load`;
- the 18 obligations, restated;
- `decision_preserves`;
- then the capstone by `m6_capstone_of_steps`.
- Open inside it: `step_loop` under `Fits` (not attempted), `M3bWorld.typedProg_mono`, and whether pending tokens need the bound too.

**Slice 7. Numbers.** A bounded fix; the owner places it.
- **7a, L0.**
  - Files: `evalChecked`, `InProfile` and a static twin (every literal within the profile) in `src/Effect4/Program/`; their laws in the Laws graph.
  - Rule: split every `↔` before `omega`, because a bare `omega` on an iff reaches `Classical.choice` (`numbers/verify-omega.lean`).
  - First probe: `numbers/Checked.lean`.
- **7b, T1.**
  - `NativeAtom.row` prelude strings for `add`, `succ` and `mul`: check with `Number.isSafeInteger` and throw `ProfileRefusal`; regenerate the prelude group.
  - The harness classifies both forms a refusal takes: thrown while the program value is built, or a defect later.
  - The printer and reader refuse a natural literal above `rc112.natBound` at its path.
  - The comparator gets the class "outside the profile".
  - First probe: the faces program (`evalChecked (2^53-1)` refuses at `[]` with 2^53+1, and rc.112 must refuse there too), `bigLiteral`, and the DI-56 pair.
- **7c, native,** per new decision 5.
  - L1: `Option NumberProfile` through the 31 `evalTerm` call sites of `Program/Compile.lean`, plus a theorem that `none` is today's `evalTerm`. `evalTerm` is in the engine closure, so regenerate.
  - The fallback rows: sign- or pre-checked; the refusal caught on `api_run` as well; `pow` and `shiftLeft` left saturating, for `Val.wf`.
  - First probe: the faces program on OCaml returns `Outside_profile`.
- **7d, documentation.** Repair the `Json.ofNat` docstring, `ocaml/engine/e4_nat.mli` (notes N2 and D3, and its dead citations), and `ocaml/gen/NOTES.md` §5.

**Parked with the host-services contract.** Each item is written down, with what it needs first.
- **The static environment and the fiber registry:** one fold (K5), `fiberDecl`, `FiberRegistryAgrees`, and `kind` if wanted. Needs slice 1.
- **The fiber boundary slice:** `fitsAt`, `admitDeclared`, `EnvelopeDeclared` and `acceptReplyDeclared`, wired at `Api/HostSession.lean:171` and `Program/Admit.lean:118`.
  - It also needs: the admission's reason carried in the session phase, which regenerates the derived `Runner` group; the template rule (K10); the internal-fiber rule (K7); and the reflection lemma (K6).
  - Needs slices 1 and 3, and the `lcnf` byte check.
- **Contexts:** the owner's authority ruling (K8).
- **Cells and deferreds:** creation records, with generic cells (rows 42–44).

## 7. Open questions (not decisions)

- **M5 and M6 under `Fits`:**
  - `typedState_load` under `Fits` for every program: only two instances are proved;
  - `step_loop` under `Fits`: not attempted;
  - `M3bWorld.typedProg_mono`: not attempted.
- **Pending tokens.** Do the tokens in `f.pending` need the freshness bound (`preds.PendingOk`, `Typed/Assembly.lean:53`)? The guard's key list does not cover them.
- **The OCaml engine on the gap programs.** Nobody has run it.
- **The daemon view.** Supervision's daemon view reports owned internal daemons as unpinned: race entrants, layer builds and parallel-close finalizers. The daemon-quiet observation should classify them by origin.
- **Thin corpus coverage.** Two environment rules have few hits in the red controls: statement bindings (2) and generators (8). The typed corpus could gain generator programs that fork.
- **The OCaml engine and the registry.** When a table-aware OCaml entry exists, should the engine carry the checker and the static environment, compiled through LCNF, or receive a per-site table computed at admission?
- **Several roots.** A machine with more than one root needs `Point.root` in the recorded site.
- **The book.** Should it get a relational (lockstep) form of the decision and replay lifts?
- **Delayed reads.** The contract's `ofRefGet` case was not probed by this pass.

## 8. Commands this seat ran

Reads only (`cat`, `sed`, `grep`, `git log`, `git show --stat`), plus one scratch probe through the one-compiler lock. `S` is the session scratchpad.

```
bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true $S/synthesis/ItemA.lean
  exit 0; no output (five #guards pass)
bash $S/serial.sh lake env lean -M6144 -DwarningAsError=true $S/synthesis/ItemARed.lean
  exit 1; two guards "did not evaluate to `true`" (the red control: the old refusal expected
  under item A's rule)
```

`ItemA.lean` is outside the tree. Its SHA-256 is `96055f136895c0145e7574c174f525f2c2f942a98f7376cde710807423c0159c`, and its text is in Appendix A. `ItemARed.lean` is the same file with the two expected refusals under item A's rule changed back to `.deadHandle Api.root 0`. The probe defines no theorem, so it prints no axioms.

I ran no git write, no `make`, no `lake build` and no generator, and spawned no agent.

## Appendix A. `ItemA.lean` (the scratch probe of §3.6)

```lean
import Effect4.Api
import Test.Api.ExternalContract

/-! Synthesis scratch probe (not in the tree). Codex brief item A, step 2, says the reply check's
non-allocation arm refuses any handle in a success value. This copies `externalValue` and
`admitAnswer`'s success arm with that one change and runs both on the in-tree fixture
`Test/Api/ExternalContract.lean:55-57` (row "cell", answer `NativeOp.refTy`, a dead cell). -/

namespace Research.Pass.Synthesis
open Effect4 Effect4.Program Effect4.Machine
open Test.Api.ExternalContract (program table)

/-- `externalValue` (`Program/Compile.lean:1354-1365`) with item A's rule: no handle at all. -/
def externalValueA (ty : Ty) (allocated : List String) (value : Val) :
    Option (List String × Val) :=
  match ty, value with
  | .handle target, .nat index =>
    if externalHandleTarget target && index == allocated.length then
      some (allocated ++ [target], Value.external index)
    else none
  | _, _ =>
    if Val.hasTy value ty allocated && (Store.Val.handles value).isEmpty then
      some (allocated, value)
    else none

/-- `admitAnswer`'s success arm (`Program/Admit.lean:59-66`) over `externalValueA`. -/
def admitSuccessA (row : Row) (m : NativeMachine) (fiber : FiberId) (token : Nat) (v : Val) :
    Option Refusal :=
  if (externalValueA row.answer m.state.externals.allocated v).isNone then
    some (.answerType fiber token row.answer)
  else if !mintedIn m v then some (.deadHandle fiber token)
  else none

/-- The machine parked on the "cell" row, as the fixture's `refusal` reaches it. -/
def parked : NativeMachine := (Api.replay (program 1) 1000 [Api.evaluate] [] table).machine

def deadCell : Completion Val Err Defect FiberId Ann := .ofExit (.success (Val.cell ⟨0⟩))

-- Today: the fixture's expected refusal.
#guard ((externalRow table 1).map fun row => admitAnswer row parked Api.root 0 deadCell) =
  some (some (.deadHandle Api.root 0))
-- Under item A step 2: the same reply is refused earlier, with a different reason.
#guard ((externalRow table 1).map fun row => admitSuccessA row parked Api.root 0 (Val.cell ⟨0⟩)) =
  some (some (.answerType Api.root 0 NativeOp.refTy))
-- Red control: the fixture's own route still reports deadHandle at the base.
#guard Test.Api.ExternalContract.refusal (program 1)
  [Api.evaluate, .answerAsync Api.root 0 deadCell] = some (.deadHandle Api.root 0)
-- Under item A step 2 no success value with an internal handle reaches `mintedIn`:
-- a live cell at the same row is refused too (today it passes the shape check and is live).
def liveCellProgram : NativeEff := .bind (.perform .refMake (.lit (.nat 7))) (program 1)
def parkedLive : NativeMachine := (Api.replay liveCellProgram 1000 [Api.evaluate] [] table).machine
#guard ((externalRow table 1).map fun row => admitAnswer row parkedLive Api.root 0 deadCell) =
  some none
#guard ((externalRow table 1).map fun row => admitSuccessA row parkedLive Api.root 0 (Val.cell ⟨0⟩)) =
  some (some (.answerType Api.root 0 NativeOp.refTy))

end Research.Pass.Synthesis
```
