# P2b frontier and layers receipt — 2026-09-11

P2b resumed on 2026-09-12 from `db17914` under the owner's accepted amendments.
The owner also approved the two evaluate-entry helper amendments below. Commit 1
is complete and all its required gates have passed under the unchanged declared-red policy.
The historical statement check below is retained as evidence; its stop is no
longer the current lane status. Commits 2–4 remain in scope.

The observation laws now name host-await priority and the separate runnable and
fiber-exit predicates. The driver repair in commit 1 makes `Cmd.evaluate` a no-op
on a parked fiber and removes its old park-clearing assignment. Legitimate
resumes unpark before evaluation: `Cmd.resume` for yields, deferreds and timers,
and `interruptRecord` for interrupts. The rc.112 entry has no bare evaluation of
a suspended fiber (`internal/effect.ts:599–628`, `:1118–1132`).

`Interrupted f` is the existing aggregate `interruptPending f` or an exit. The
guard-persistence law quantifies over every non-answer decision, as ruled; it
is not restricted to protocol-admitted decisions. Production ruling and contract
changes were already recorded in `db17914` before this resumption.

## Commit 1 statement dependency — explicit unparked premise required

The authorized evaluator repair is implemented, and the focused 93-job regression
build passes. The bare-evaluate battery retains the original request and token;
the keyed session accepts and applies the later reply for that original key.
The compile-fuel split and both exhaustion sites also pass their new battery.

Two existing laws in `src/Effect4/Laws/Machine/Clauses.lean` still assert that an
evaluate enters the loop whenever the fiber has not exited and is not running:

- `Effect4.Machine.drive_evaluate_enters` (line 65).
- `Effect4.Machine.driveState_evaluate_enters` (line 1833).

Their premises are `m.stuck = none`, `m.fiber? id = some f`, `f.exit = none`, and
`f.running = false`. They omit whether the fiber is parked. Their conclusions
clear its park, mark it running, emit `RunEvent.started id`, and enter the loop.
Under the owner's repair a guarded fiber instead remains unchanged.

The checked witness has one guarded fiber, no exit, no running flag, an empty
trace, a one-command `[Cmd.evaluate 0]` queue and command fuel 1. It satisfies all
four original premises. Actual execution has no started event; the claimed
right-hand side contains one. The contradiction holds for any interpreter.

**Owner-approved statement amendment (2026-09-12):** add
`(hpark : f.parked = Parked.notParked)` to both entry lemmas and the corresponding
`#check` in `Test/Audit/RuntimeCoverage.lean:2136`. Their existing conclusions can
remain unchanged because the redundant park assignment is equal under `hpark`.
Add separate no-op clauses for parked fibers when repairing their proof clients.
This is the exact proof dependency of the already-authorized machine repair.
The owner explicitly approved both premises and the audit check after reviewing
the checked counterexamples. Implementation resumed with this amendment recorded
in the frozen foundation contract.

Coordinator verification, exit 0:

```sh
LEAN_NUM_THREADS=2 lake env lean -M4096 docs/research/2026-09-11-p2b-frontier-and-layers-evidence/agent/C1EvaluateClauseProbe.lean > docs/research/2026-09-11-p2b-frontier-and-layers-evidence/c1-evaluate-clause-parent-check.log 2>&1
```

```text
'P2b.C1EvaluateClauseProbe.original_premises' does not depend on any axioms
'P2b.C1EvaluateClauseProbe.drive_evaluate_enters_false' depends on axioms: [propext, Quot.sound]
'P2b.C1EvaluateClauseProbe.driveState_evaluate_enters_false' depends on axioms: [propext, Quot.sound]
```

The commit 1 implementation has passed every required gate. The full build
passes (312 jobs), including the proof graph, module closure and axiom audit.
The initial focused build collided with a parallel generator build while both
wrote `Profile.olean`; after the shared dependency build finished, the retry
passed. Both logs are kept as `c1-regression-build.log` and
`c1-regression-retry.log` in the evidence directory. This was an output collision,
not a reason to restore the superseded restriction on parallel Lean checks.

## New statement dependency — guard-key ownership (2026-09-12)

The repaired evaluator does not establish `guard_persists` for every arbitrary
machine value. The statement currently supplies only an outstanding request and
a non-answer decision; it has no reachability or guard-key ownership premise.

Checked witness: load and evaluate the single callback `.callback (.external 0)
(.lit (.nat 7))` against one external async row. It has one fiber, with the request
`some (.external 0, .nat 7)` at `(fiber 0, token 0)`. Retain that fiber, and replace
the timer store with `parked.state.timers.sleep Api.root 0 0`. This deliberately
gives a timer the same key as the external guard. This machine is **not claimed
reachable** from `Api.load`; the unqualified theorem nonetheless quantifies over it.

At command fuel 1, decision `.advance 0` resumes that key through the timer's
existing resume path. Afterwards `requestOf` at the original key is `none`, while
the fiber's aggregate `interruptPending` and `exit.isSome` are both false. The
decision is neither an answer for the key nor a cancellation. The parked-evaluate
repair works as approved; this witness does not use bare evaluation.

`C3GuardOwnershipProbe.lean` in the evidence directory proves the exact negation
of the requested disjunction for this machine and decision. Its four `#guard`s
also pass. Fresh command (exit 0):

```sh
LEAN_NUM_THREADS=2 lake env lean -M1024 docs/research/2026-09-11-p2b-frontier-and-layers-evidence/C3GuardOwnershipProbe.lean > docs/research/2026-09-11-p2b-frontier-and-layers-evidence/c3-guard-ownership-theorems.log 2>&1
```

```text
'P2b.C3GuardOwnershipProbe.before_request' depends on axioms: [propext, Quot.sound]
'P2b.C3GuardOwnershipProbe.after_request' depends on axioms: [propext, Quot.sound]
'P2b.C3GuardOwnershipProbe.after_no_interruption' depends on axioms: [propext, Quot.sound]
'P2b.C3GuardOwnershipProbe.guard_persists_counterexample' depends on axioms: [propext, Quot.sound]
```

**Owner-approved amendment (2026-09-12):** state `guard_persists` and its
single-fiber corollary for a starting machine reachable from `Api.load` by the
same program/table interpreter over an explicit prefix of decisions. Keep the
quantification over every nonmatching-answer decision, including decisions the
host protocol does not admit. Prove the ownership invariant needed to exclude
timer/deferred/dispatcher resumes at an outstanding external guard. Reachability
excludes this manually injected state; sufficiency for the revised universal law
still requires the proof and is not asserted by this probe.

The owner explicitly approved this amendment after reviewing the checked
counterexample. The temporary statement stop is resolved and the four-commit
lane continues. The later observation, fuel and type-expansion drafts remain
scratch work and are not counted as delivered commits. The tracked contract
amendment will accompany the guard-law commit.

## New statement dependency — the scope of fresh isolation (2026-09-12)

The new fresh map has no parent, as dispatched. The stronger clause about **every
memo operation during the fresh subtree** is false when a `Layer.effect` body
contains a non-local `provideLayer`. That program operation reads the ambient
`CurrentMemoMap` service; `freshThen` does not replace that service when it passes
the fresh map to `resolveLayer`.

`C4FreshContextProbe.lean` is a finite, executable witness using the unchanged
compiler. An outer counted layer is provided once. Its body provides a fresh
effect layer, whose build program provides a reference to the outer counted layer
and waits at an external callback. The program passes `layerRefsWF` and
`Api.wellTyped`. At compile fuel 64, the native replay reports:

```text
memo maps (id, parent, [(layer path, observers)]):
[(1, none, [([1, 0, 0], 2)]),
 (7, some 1, []),
 (8, none, [([1, 0, 1, 0, 0], 1)]),
 (14, some 7, [])]
external await key: (fiber 0, token 1)
command fuel 160: fresh map 8 exists; outer entry observers = 1
command fuel 200: fresh map 8 exists; outer entry observers = 2
```

Map 8 is the fresh map and really has no parent. The nested program's map 14
looks through 7 to enclosing map 1; its lookup of `[1, 0, 0]` returns owner 1.
The counted Ref remains 1, so the nested reference reused the enclosing build.
This is an ordinary loaded-program execution, not the injected machine from the
guard-key probe. Both observer counts, the fresh map's absent parent, the lookup's
enclosing owner and the final memo-map projection have passing `#guard`s.

Fresh command (exit 0):

```sh
LEAN_NUM_THREADS=1 timeout 30s lake env lean -M1024 docs/research/2026-09-11-p2b-frontier-and-layers-evidence/C4FreshContextProbe.lean > docs/research/2026-09-11-p2b-frontier-and-layers-evidence/c4-fresh-context-probe.log 2>&1
```

This evidence is a finite probe, not a kernel theorem of general runtime
execution. Earlier attempts in this scratch file used the wrong expected guard
token and a nonexistent display field; those failed elaborations are not evidence.
The final script exits 0 with the projections above.

**Owner-approved amendment (2026-09-12):** scope `fresh_never_shares` to lookups
and memo operations routed through the fresh map (and its isolated descendants).
Prove that their lookups stay in that parent chain and their writes leave enclosing
maps unchanged. Exclude independently invoked nested program-level `provideLayer`
operations that select an ambient memo map. Keep `freshThen`, the compiler and
rc.112 behavior unchanged. The parentless-map lookup and memo-hit helper drafts
already check at `[propext, Quot.sound]`; they do not prove the broader false clause.

The owner explicitly approved this map-scoped law after reviewing the witness.
The statement stop is resolved; all four commits remain in scope. The tracked
contract amendment will accompany the layer-law commit.

## Commit 1 proof dependencies

The repaired `driveStep` arm has two paths: a parked fiber retains its machine
state; an unparked fiber enters evaluation under the two amended clauses.
`Program.Sched.drive_evaluate` uses the existing relation's equality of park
states to take the same branch on the compiled and reference machines. This
feeds `stepAgrees` and the existing book simulation.

The driver's empty-tape and incomplete-command exits supply `.tape` and `.fuel`
respectively. `ReplayRel` now requires equality of those tags together with
`BookMeans` at a frontier. `book_replayEval` transports both, so `replay_rel` and
`replayRel_classify_obs` retain the original classification/observation conclusion
under the stronger relation. `run_eq_ref` is textually unchanged.

`Api.load` receives compile fuel; `Api.replay` uses its command fuel for the
driver and its trailing compile-fuel parameter for loading. Defaults retain the
original budget choice. The reference entries mirror that split. The fuel and
guard batteries exercise the separate budgets and the accepted old-key reply.
The OCaml suite and rc.112 gates are finite execution checks, separate from the
Lean simulation and its axioms.

## Commit 1 implementation and checks

Base: `db17914`. The exhaustion tag is part of `ReplayResult`, and the two driver
sites distinguish tape exhaustion from command exhaustion. `ReplayRel` requires
equal tags. The API and reference runners take a trailing compile budget with
the original command budget as its default. `Outcome` and the statement of
`run_eq_ref` are textually unchanged. The five handwritten OCaml callers pass the
original budget explicitly to retain that default through the generated function.

The parked-evaluate negative tests check both the raw tape and the keyed session:
the extra evaluate retains the request and token, the original reply is accepted
and applied, and the next external call receives the next token. No truth tape or
generated file was edited by hand. The source types, Eff, LayerId, compiler, values,
wire, ordinals and declared-red policy are unchanged.

Fresh checks completed before the final sweep:

| Check | Result | Evidence file |
| --- | --- | --- |
| `LEAN_NUM_THREADS=3 lake build` | Exit 0; 312 jobs | `c1-lake-build-retry.log` |
| Library roots | 92 API/utility modules, 53 Laws-only modules; no Laws reachability from Effect4 | same build log |
| Module and axiom audit | 279 modules, 44,230 declarations; semantic/test ceiling `[propext, Quot.sound]` | same build log |
| Direct `#print axioms` | Exit 0; the exact reports below | `c1-axioms.log`, `agent/c1-proof-axioms.log` |
| `bash scripts/check-truth.sh` | Exit 0; 31 programs, exits and schedules agree with rc.112; fresh modules type-check | `c1-truth-retry.log` |
| `bash scripts/check-host-protocol.sh` | Exit 0; 57 runs, 52 programs, 29 controls; exact exits and keyed applications | `c1-host-protocol-retry.log` |
| `opam exec --switch=effect4 -- dune test engine` in `ocaml/` | Exit 0; differential reports 559 programs, 3,472 tapes, 76,682 positions, 153,364 projection comparisons, zero divergences, 23 checks | `c1-dune-engine-retry.log` |

The existing exact-name implementation allowance for `Classical.choice` remains
seven modules and 36 declarations; it was not expanded. The OCaml suite also
prints its pre-existing, non-gated cross-face differences for `pAcquire` and
`pProvide`, which are present in the P2a evidence as well. Its success is not a
claim that those historical cross-face differences have been repaired.

Failed attempts are retained, not counted as accepted gates. The first full build
found two old frontier constructor applications in `BehaviourContract`; both now
carry the tape tag. The first truth and host checks agreed on execution but refused
stale generated provenance; their owning producers were rerun. The first OCaml
check found a handwritten caller missing the new trailing budget; all five callers
were updated. The first sweep stopped at generated-stale after `Tools.ProgramStructure`
was rebuilt later than the derived generator; the affected producers were
rerun successfully with that dependency current. The initial logs have their unsuffixed names;
retries are separately named. No failed run was restamped as a pass.

The final sweep completed with exit 0. Its exact summary is below. The [generated inventory](2026-09-11-p2b-frontier-and-layers-evidence/c1-generated-inventory.md)
lists all 343 generated paths with their producer, revision, toolchain, input
stamp and SHA-256. Only `ocaml/gen/api_gen.ml` and
`ocaml/engine/api_engine.ml` changed payload; the other 341 paths carry updated
provenance. Truth result and tape payloads, printed TypeScript and `.ty` goldens
are unchanged. Every product was regenerated by its existing producer.

`git diff --check` reports one pre-existing generator-formatting defect in newly
emitted output: a whitespace-only line at `ocaml/engine/api_engine.ml:10320`.
The generator emits it; it was not edited by hand. The remaining diff passes the
whitespace check. This is not one of the declared gates and is recorded separately.

Final gate command: `LEAN_NUM_THREADS=3 bash scripts/sweep.sh`, exit 0.
All 18 gates ran with fresh input stamps; none used a previous successful result.
The unchanged declared-red entry is the two historical flat LCNF projections
`ocaml/gen/fibers_gen.ml` and `ocaml/gen/machine_gen.ml`; the owner-deferred
`generated/schema-structural-assurance.tsv` remains deferred. Their policy was
not edited. The current API mirror, engine checks and generation comparison pass.

```text
sweep: every gate, one process at a time
generated-stale          DECLARED    1s  miss
library-roots            PASS   27s  miss
source-citations         PASS    1s  miss
internal-citations       PASS  127s  miss
effect-runtime-census    PASS   15s  miss
ts-eff                   PASS   46s  miss
conform                  PASS   37s  miss
generated                PASS    2s  miss
schema-typescript        PASS   57s  miss
schema-codec             PASS    2s  miss
ts-eff-corpus            PASS   18s  miss
ingest                   PASS  734s  miss
host-protocol            PASS  122s  miss
truth                    PASS   77s  miss
streams                  PASS    7s  miss
gen-check                PASS   22s  miss
dune-tests               PASS    4s  miss
engine-tests             PASS    4s  miss
sweep: 18 gates, 0 hit, 18 miss, 1303s total; table in .lake/sweep-summary.tsv
PASS every gate under the declared-red policy; declared failures are listed above
```

The sweep repeated the 31-program rc.112 truth comparison and the 57-run keyed
host comparison successfully. Its OCaml checks passed; the library suite reported
760 checks and zero failures. No commit 1 obligation remains open. The later
reason, persistence and layer proof drafts are not part of this commit.

Direct coordinator `#print axioms` output, exit 0:

```text
'Effect4.Machine.drive_evaluate_enters' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.driveState_evaluate_enters' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.ReplayRel.machine' depends on axioms: [propext]
'Effect4.Machine.book_replayEval' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.replay_rel' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.replayRel_classify_obs' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.run_eq_ref' depends on axioms: [propext, Quot.sound]
'Test.Api.FrontierContract.command_exhaustion' depends on axioms: [propext, Quot.sound]
'Test.Api.FrontierContract.tape_exhaustion' depends on axioms: [propext, Quot.sound]
'Test.Api.HostSessionContract.evaluate_retains_guard' depends on axioms: [propext, Quot.sound]
'Test.Api.HostSessionContract.evaluate_retains_token' depends on axioms: [propext, Quot.sound]
```

The separately checked dependency reports (`agent/c1-proof-axioms.log`, exit 0):

```text
'Effect4.Machine.ReplayResult.machine' does not depend on any axioms
'Effect4.Machine.ReplayResult.le' does not depend on any axioms
'Effect4.Machine.ReplayResult.terminal' does not depend on any axioms
'Effect4.Machine.ReplayResult.le_refl' depends on axioms: [propext]
'Effect4.Machine.ReplayResult.le_trans' depends on axioms: [propext]
'Effect4.Machine.ReplayResult.le_antisymm_terminal' does not depend on any axioms
'Effect4.Machine.ReplayResult.frontier_le' does not depend on any axioms
'Effect4.Machine.replay_frontier_mono_single' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.obs_mono_of_le_terminal' does not depend on any axioms
'Effect4.Machine.ReplayRel' depends on axioms: [propext]
'Effect4.Machine.replayEval_nil' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.replayEval_cons' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.book_suffices' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.Witnesses.replay' depends on axioms: [propext, Quot.sound]
'Effect4.Machine.Witnesses.replayArm' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.loadR' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.replayR' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.classify' does not depend on any axioms
'Effect4.Program.Sched.drive_evaluate' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.stepAgrees' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.suffices_eq_ref' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.run_eq_ref_exit' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.straight_ref' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.straight_sufficient' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Sched.straight_beh' depends on axioms: [propext, Quot.sound]
'Effect4.Program.handles_minted' depends on axioms: [propext, Quot.sound]
```

## Historical statement check

Everything from this heading onward describes the earlier stopped preflight at
`1774ecc`, not the current resumed implementation. The owner accepted its three
findings in `db17914`; the exact approved helper amendment is recorded above.

P2b initially stopped before commit 1 on 2026-09-12. Lean checked two counterexamples to
`observe_of_reasons` and a third to `guard_persists` that also defeats the proposed
single-fiber corollary. No implementation, generated output, contract amendment
or commit was made. The proposed changes below are awaiting an owner ruling.

The dispatch supplies the stop rule: “If a theorem needs a statement change to be
true, stop and write the counterexample into the receipt instead of weakening the
law silently.” This stop follows that instruction.

## Checkout and finishing criteria

- Main checkout: `/Users/pooks/Dev/lean4-effect4`; no new worktree or branch.
- Branch: `refactor/phase1-phase3`.
- Base and final HEAD: `1774ecc7932477302bb68bf343800d1cf4a0692e`.
- The tracked working tree was clean at entry. The existing P2a commits remain
  in place. No P2b files were staged, committed or pushed.
- Authored artifacts are this receipt and the scratch evidence under
  `docs/research/2026-09-11-p2b-frontier-and-layers-evidence/`.
  `COORDINATION.md` records the claim and release. These paths are ignored by Git.

Completion requires four sequential commits with the requested laws, batteries,
generated carriers and mirror, truth fixtures, and all specified gates accepted
before each commit under the unchanged declared-red policy. Statement checking
stopped that sequence before implementation.

| Requested commit | Status | Generated files and stamps | Commit gates |
| --- | --- | --- | --- |
| 1 — exhaustion tag and fuel split | Not started | No changes; generator not run | Not run |
| 2 — reason alphabet and observations | Blocked by the counterexamples below | No changes; carrier generator not attempted | Not run |
| 3 — fuel stability and guard persistence | Blocked by the guard counterexample below | No changes | Not run |
| 4 — layer sharing laws and truth fixtures | Not started | No changes | Not run |

## 1. `idle` does not imply `awaitDecision`

The requested reason rule is:

```lean
awaitDecision is present ↔ why = .tape ∧ some fiber is runnable
```

The requested observation law additionally requires:

```lean
HostProtocol.observe m = .idle ↔ awaitDecision is present
```

Take the program `succeed (lit (nat 42))`, compile fuel 32, the one-decision tape
`[Api.evaluate]`, and command fuel 0. The current driver returns its initial
machine with an unfinished command receipt. This is exactly the frontier site
that commit 1 must tag `.fuel` (`Machine/Fibers.lean:2141`).

The machine has a runnable root and no external await. Therefore
`HostProtocol.observe` returns `.idle` (`Api/HostProtocol.lean:97`). The required
reason rule makes `awaitDecision` absent because the tag is `.fuel`.

`P2bStatementCheck.idle_iff_decision_refuted` proves the negation of the required
equivalence for this witness. `P2bStatementCheck.observation_law_incompatible`
also proves that any Boolean membership projection satisfying the prescribed
reason rule conflicts with the unrestricted observation equivalence. Changing
the representation of the reason list cannot repair this conflict.

The scratch file defines its own two-constructor `Exhaustion` and the exact
requested decision-membership formula. These are a statement probe, not landed
production carriers. The machine and its step are the unchanged production
driver. No new implementation is assumed in the counterexample.

As a control, an empty tape on the same initial machine has a runnable fiber
and would receive the `.tape` tag, so the prescribed `awaitDecision` is present.
The observer cannot distinguish these two exhaustion causes from the machine
alone.

## 2. `terminated` does not imply a finished replay

Read the dispatch's “terminated iff finished” as comparing
`HostProtocol.State.terminated` with `Run.outcome = .finished`, consistent with
the frozen `Outcome` alphabet. The same program, compile fuel 32 and tape
`[Api.evaluate]`, at command fuel 3, gives:

```text
replay outcome: frontier
HostProtocol.observe: terminated
stepDecisionState completion receipt: false
```

All fibers have exited, but the driver has not finished the command queue.
`replayEval` takes the unfinished-command frontier branch before checking the
empty-tape completion condition. Merely adding `.fuel` at that branch preserves
this witness.

`P2bStatementCheck.terminated_iff_finished_refuted` proves the negation of the
claimed equivalence. The finished outcome appears at command fuel 5, which is
also checked as a positive control. If “finished” instead means the machine's
fiber-exit predicate, the observation law must name that predicate explicitly;
it cannot be presented as equivalence with the run outcome.

The finite probe prints these exact observations:

| Command fuel | Replay outcome | Host observation |
| --- | --- | --- |
| 0, 1, 2 | `frontier` | `idle` |
| 3, 4 | `frontier` | `terminated` |
| 5, 6, 7 | `finished` | `terminated` |

The two refutation theorems, rather than this finite table alone, establish the
failures of the proposed statements.

## 3. A non-answer decision can replace an outstanding guard

An independent check produced this witness using the current public runner:

```lean
program := .callback (.external 0) (.lit (.nat 7))
parked := (Api.replay program 40 [Api.evaluate] [] [] table).machine
afterFull := steppedBy program 40 table parked Api.evaluate
```

`table` contains one external asynchronous operation, with `nat` request, answer
and error types. `steppedBy` is the existing wrapper for `stepDecisionState`'s
machine projection (`Program/Admit.lean:248`), the same projection as
`stepDecision`.

The named receipts establish:

| Observation | Before the second `evaluate` | After the second `evaluate` |
| --- | --- | --- |
| Request at root fiber 0, token 0 | `some (.external 0, .nat 7)` | `none` |
| Request at root fiber 0, token 1 | Not needed for the refutation | `some (.external 0, .nat 7)` |
| Interrupt pending, deferred interrupt, interrupted cause, exit, finalization | Not needed for the refutation | All absent |

The initial machine has exactly one fiber. The decision is `evaluate`, so it is
neither an answer nor a cancellation. `driveStep`'s `Cmd.evaluate` branch clears
the park before entering the loop (`Machine/Fibers.lean:1804`). With command
fuel 1 the old request is already gone; with fuel 40 the callback has parked
again on a new token.

`P2b.GuardPersistsProbe.guard_persists_counterexample` proves that the old request
exists, the decision is not any answer for its key, and the proposed disjunction
fails when interruption means an interrupt request or any exit. The companion
`full_budget_no_interrupt_or_exit` receipt additionally excludes the existing
deferred-interrupt and interrupted-cause flags and finalization. There is no
declaration named `Interrupted` in the current `src/Effect4` tree; the packet's
schematic name therefore cannot be instantiated to a checked existing declaration
without identifying which fields define it.

The starting state is reachable through `Api.replay`, so a reachability premise
alone does not exclude this example. Its single fiber and cancellation-free
decisions also satisfy the proposed single-fiber description. No change to compile
fuel or exhaustion tags repairs the guard replacement.

**Required decision:** either restrict the persistence laws to an explicitly
defined class of decisions that excludes restarting a waiting fiber, or authorize
a machine behavior change that prevents that restart from clearing the guard.
The former needs a precise admissibility predicate and further proof; adding
only a reachability premise is insufficient. The latter changes current replay
behavior and requires regression checks. Neither alternative has been applied
or claimed sufficient for the full universal theorem.

## Proposed observation amendment — not applied

Keep the required exhaustion tags, reason membership rules and existing
`HostProtocol.observe` behavior. State its agreement with the machine predicates
that it actually inspects:

- `awaitingAsync` iff an `awaitHost` reason is present.
- `terminated` iff no `awaitHost` reason is present and every fiber has exited.
- `idle` iff no `awaitHost` reason is present and some fiber is runnable.
- Separately, `awaitDecision` is present iff the tag is `.tape` and some fiber is
  runnable, exactly as dispatched. Consequently, under the `.tape` tag and
  absence of an `awaitHost` reason, `idle` iff `awaitDecision` is present.

The absence of host awaits is material: `observe` prioritizes an external await
over a runnable fiber. This proposal states that existing priority explicitly.
It does not change the reason alphabet or the driver. These replacement universal
laws have not been proved in this stopped preflight.

Do not identify fiber termination with `.finished` for an arbitrary replay;
any additional relation between them needs an explicit driver-completion premise.
No replacement for `run_eq_ref` or `finished_mono_fuel` is proposed.

## Fresh verification

The checked source is
`docs/research/2026-09-11-p2b-frontier-and-layers-evidence/StatementProbe.lean`.
Run from the main checkout:

```sh
LEAN_NUM_THREADS=2 lake env lean -M4096 docs/research/2026-09-11-p2b-frontier-and-layers-evidence/StatementProbe.lean > docs/research/2026-09-11-p2b-frontier-and-layers-evidence/statement-probe.log 2>&1
```

Exit status: **0**. Both refutations elaborate without a proof escape. The exact
`#print axioms` output is:

```text
'P2bStatementCheck.zero_command_step' depends on axioms: [propext, Quot.sound]
'P2bStatementCheck.zero_command_observe' depends on axioms: [propext, Quot.sound]
'P2bStatementCheck.zero_command_runnable' depends on axioms: [propext, Quot.sound]
'P2bStatementCheck.zero_command_no_decision' depends on axioms: [propext, Quot.sound]
'P2bStatementCheck.idle_iff_decision_refuted' depends on axioms: [propext, Quot.sound]
'P2bStatementCheck.empty_tape_has_decision' depends on axioms: [propext]
'P2bStatementCheck.three_command_frontier' depends on axioms: [propext, Quot.sound]
'P2bStatementCheck.three_command_terminated' depends on axioms: [propext, Quot.sound]
'P2bStatementCheck.three_command_not_settled' depends on axioms: [propext, Quot.sound]
'P2bStatementCheck.terminated_iff_finished_refuted' depends on axioms: [propext, Quot.sound]
'P2bStatementCheck.five_command_finished' depends on axioms: [propext, Quot.sound]
'P2bStatementCheck.observation_law_incompatible' depends on axioms: [propext, Quot.sound]
```

The independent guard probe was also rerun by the coordinator:

```sh
LEAN_NUM_THREADS=2 lake env lean -M4096 docs/research/2026-09-11-p2b-frontier-and-layers-evidence/agent/GuardPersistsProbe.lean > docs/research/2026-09-11-p2b-frontier-and-layers-evidence/guard-persists-parent-check.log 2>&1
```

Exit status: **0**. Its exact receipts are:

```text
'P2b.GuardPersistsProbe.before_request' depends on axioms: [propext, Quot.sound]
'P2b.GuardPersistsProbe.one_fiber' depends on axioms: [propext, Quot.sound]
'P2b.GuardPersistsProbe.decision_not_answer' does not depend on any axioms
'P2b.GuardPersistsProbe.one_command_loses_request' depends on axioms: [propext, Quot.sound]
'P2b.GuardPersistsProbe.one_command_no_interrupt_or_exit' depends on axioms: [propext, Quot.sound]
'P2b.GuardPersistsProbe.full_budget_loses_request' depends on axioms: [propext, Quot.sound]
'P2b.GuardPersistsProbe.full_budget_reparks_new_token' depends on axioms: [propext, Quot.sound]
'P2b.GuardPersistsProbe.full_budget_no_interrupt_or_exit' depends on axioms: [propext, Quot.sound]
'P2b.GuardPersistsProbe.guard_persists_counterexample' depends on axioms: [propext, Quot.sound]
```

`typeOfProgram_expandRefs` received source review only; no additional definite
counterexample was found. The other requested universal laws were not proved in
this preflight.

These are scratch theorem receipts, not a fresh whole-library axiom or closure
gate. The complete P2b gates were not run because there is no implementation
candidate to commit after the required stop:

- `lake build`.
- The whole-library axiom audit and module closure
  (`bash scripts/check-library-roots.sh`).
- `bash scripts/sweep.sh`, retaining its declared-red policy.
- `bash scripts/check-truth.sh` for the 31-program gate.
- `bash scripts/check-host-protocol.sh`.
- `scripts/generate.sh` and `scripts/check-generated.sh`, followed by
  `dune test engine` in `ocaml/`.

Earlier P2a gate results are not claimed as P2b verification. No generated file,
stamp, printed fixture, truth tape, comparator format, ordinal or wire changed.

Final `git diff --check` exited 0. `git status --short --branch` still showed no
tracked changes and HEAD remained `1774ecc7932477302bb68bf343800d1cf4a0692e`.
A receipt consistency check matched all 21 printed theorem reports against the
two fresh logs and found no forbidden proof escape in either scratch source.
Both Lean checks have finished and the independent agent is closed.
