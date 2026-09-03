# Effect4 Lean-core survey

Base: `/Users/pooks/Dev/lean4-effect4` @ `645067a` (main, clean).
Dependency: `effects` @ `a1171574…` (tag `v0.7.0`), `typescript` @ `31665ff…` (tag `v0.4.2`).
Scope: `Effect4/` (115 modules, 45 196 lines), `Effect4Test/` (128 modules, 33 007 lines),
`lakefile.toml`, `Effect4Test/Audit/AxiomGate.lean`, `COORDINATION.md`, the three `AGENTS.md`.
Out of scope (another reviewer): the TypeScript lowering rules themselves, `harness/`,
`generated/` goldens, `scripts/` beyond the trust gate, doc DX.

Every claim below was checked against the source or measured. Commands that were run:
`lake build Effect4` (cached, 139 jobs, exit 0), `lake env lean --profile` on two modules,
and three `lake env lean` probes over the compiled environment (`_example` visibility,
per-module `Classical.choice` reach). No file in any repo was modified.

**Headline health.** The library is in unusually good shape for its age (249 commits over
4 days): zero `sorry`, zero `axiom`, zero `unsafe`, zero `partial`, one `native_decide`,
a real fuel-sufficiency theorem, a real T1/T2 denotation, a working program logic, and an
axiom gate that is more thorough than most. The problems below are concentrated in three
places: (1) the trust gate has a blind spot and two admissions much wider than needed;
(2) the Flow v3 branch design has one under-specified case whose stated justification is
wrong; (3) ~1 400 lines of the target semantics are a triplicated 7-clause block law.

---

## Ranked findings

### 1. The axiom gate cannot see `example` declarations — 637 of them, one already carrying `native_decide`

**Category:** correctness

`Effect4Test/Audit/AxiomGate.lean:11-17` claims the gate is "intentionally exhaustive over
the compiled namespace rather than maintaining a hand-written theorem list", and enumerates
`environment.constants` (`:262`). Lean's `example` never enters the environment, so no
`example` is ever scanned.

Measured directly (`lake env lean` probe over
`Effect4Test.Counterexamples.Schema.EffectfulFieldProperties`): the module contributes **17
declarations**, none `example`-shaped, and **zero** reach `Lean.ofReduceBool` — yet its
source contains

```
Effect4Test/Counterexamples/Schema/EffectfulFieldProperties.lean:121
  example : Representation.effectfulFieldProperties recursiveWitness != [] := by
    native_decide
```

`Lean.ofReduceBool` is in `forbiddenAxioms` (`AxiomGate.lean:129`). The gate passes anyway.

Scale: `grep -c '^ *example '` over `Effect4/` + `Effect4Test/` gives **637** `example`
declarations, 266 of them in `Effect4Test/Schema/PayloadContract.lean` alone, 7 inside the
library itself (`Effect4/Stateful/RefFamily.lean`). Every receipt written as an `example` —
including all six DB-06 modality receipts in `Effect4Test/Semantics/LogicContract.lean:32-64`
— is outside the axiom ceiling. A `sorry` inside an `example` is likewise invisible: it emits
a warning, not an error, and the build stays green.

**Why it matters.** The trust boundary the whole assurance story rests on has a hole large
enough to hide `native_decide`, `Classical.choice`, and `sorry`, and there is already one
live instance.

**Proposed change.** The source tokenizer in `forbiddenTrustToken?` (`:180-232`) already
visits every token of every audited file; add `native_decide`, `sorry`, `admit`, `axiom`,
`extern` and `implemented_by` to the token check beside `unsafe`/`partial` (they are all
keywords or attribute idents and tokenize the same way). Separately, replace the
`native_decide` at `EffectfulFieldProperties.lean:122` with a `decide` or a named theorem,
and add a lint that refuses `example` in modules that carry receipts (or convert receipts to
named `theorem`s so they land in the environment). `scripts/test-source-trust-tokenizer.sh`
already exists as the harness for the new tokens.

**Effort:** S for the tokenizer, M to convert the receipts. **Risk:** low; the tokenizer
change is additive and self-tested.

---

### 2. Two blanket module admissions let 1 099 declarations reach `Classical.choice` where only 71 need it

**Category:** correctness

`AxiomGate.lean:36-84` admits whole modules for `Classical.choice`. The comment at `:57-64`
justifies it as "exact-module", but a module is not exact — it is every declaration in the
module, present and future.

Measured (probe over the compiled `Effect4` environment):

| module | declarations admitted | actually reach `Classical.choice` |
| --- | --- | --- |
| `Effect4.Target.TypeScript.EffectV4` | 440 | 14 |
| `Effect4.Target.TypeScript.Skeleton` | 413 | 10 |
| `Effect4.Meta.Derive` | 96 | 27 |
| `Effect4.Target.TypeScript.RegionLower` | 61 | 2 |
| `Effect4.Target.TypeScript.FlowLower` | 50 | 3 |
| `Effect4.Target.TypeScript.StructuredLower` | 23 | 6 |
| `Effect4.Target.TypeScript.Trace` | 16 | 9 |
| **total** | **1 099** | **71** |

Worse, the comment at `:70-73` asserts "its lowering functions carry no semantic law" and
"the skeleton's laws are stated over the `String`-free IR, not over `render`" — but
`Effect4/Target/TypeScript/Skeleton.lean:511` and `:526` declare two genuine bridge theorems

```
theorem emitNode_eq … : emitNode g (Shapes.ofStmt shapes) body fuel current
                          = TypeScript.Structure.emitNode g shapes body fuel current
theorem emitWith_eq … : emitWith g (Shapes.ofStmt shapes) body
                          = TypeScript.Structure.emitWith g shapes body
```

which say Effect4's emitter *is* the pinned package's emitter, node for node. Probed, they
are clean (`[propext, Quot.sound]`) — but the gate would not have noticed if they were not,
and they are the load-bearing link between Effect4's IR and the pinned `typescript` package.

**Why it matters.** The five-module comment is an assurance claim ("declares no theorem",
"no semantic law") that is false for one module and unenforced for all seven. A future
semantic theorem dropped into any of them silently acquires `Classical.choice`.

**Proposed change.** Delete `targetImplementationModules` and move its 71 real users into
`choiceImplementationDeclarations`, which already exists (`:86-115`) and already has a
staleness check (`:293-300`). Add a small `#effect4_print_choice_reachers` command (10 lines,
reusing `collectAxioms` over `declarations`) so re-pinning the list after a change is one
command rather than manual archaeology. Independently: move `emitNode_eq`/`emitWith_eq` into
their own module so they are never inside any exemption.

**Effort:** M. **Risk:** low — the gate fails loudly if the list is wrong in either direction.

---

### 3. `lake build` (the default target) is permanently red, so `#effect4_axiom_gate` never runs in it

**Category:** build / correctness

`lakefile.toml:3` sets `defaultTargets = ["Effect4", "Effect4Test"]` and `:12` sets
`globs = ["Effect4Test.*"]`, so `lake build` compiles all 128 test modules — including the
two declared-red ones in `test/fixtures/trust-gate/known-red.txt`
(`Effect4Test.Protocol.ByteParserContract`, `Effect4Test.Concurrency.RaceRepresentativeContract`,
red since 2026-08-31/09-01).

Beyond those two failing, the *module-closure* half of the gate makes it worse. `AxiomGate.lean:249-254`:

```
for source in sources do
  if source.normalize != sourceFile.normalize && !importedPaths.contains source.normalize then
    throwError "Effect4 module-closure gate: {source} is not reachable from the Effect4Test audit root"
```

`auditedSources` walks the whole `Effect4Test/` directory, and the two red modules are (correctly)
not imported by `Effect4Test.lean`. So `Effect4Test.lean` itself throws on the closure check
**before** the axiom scan at `:263-289` is ever reached. Verified by computing the import
closure: exactly those two modules are unreachable from `Effect4Test.lean`, and every other
module is reachable.

The axiom ceiling is therefore enforced only by `scripts/test-trust-gate.sh`, which excises
the red modules into a throwaway copy first (`test-trust-gate.sh:78-99`) — a deliberate and
well-documented design (`:5-16`), but it means AGENTS.md's development order step 4 ("the
package build, axiom inspection") cannot both be satisfied by `lake build`.

**Proposed change.** Two small edits that restore a green default:
1. `defaultTargets = ["Effect4", "Effect4TestGreen"]` with a new
   `[[lean_lib]] name = "Effect4TestGreen"`, `globs = ["Effect4Test"]` (no `.*`) — Lake then
   builds the umbrella plus exactly its transitive imports, i.e. the green battery and the gate.
   Keep `Effect4Test` with `globs = ["Effect4Test.*"]` as the explicit red-inclusive target.
2. Make the closure gate read `test/fixtures/trust-gate/known-red.txt` and exempt those
   modules (still failing on any *undeclared* unreachable module), so the closure check keeps
   its teeth without being defeated by the sanctioned red phase.

**Effort:** S. **Risk:** low; `test-trust-gate.sh` step 0 already cross-checks the declared
red set in both directions and will catch a mistake.

---

### 4. Flow v3 `branch`: a test with no boolean reading is decided by the tape, and the doc's justification for it is wrong

**Category:** correctness

`Effect4/Semantics/Runs.lean:145-157`:

```
| .branch test site onTrue onFalse args =>
    …
    match testValue env test with
    | some value => if answer = value then .choose … else .mismatch site site
    | none => .choose site answer (if answer then onTrue else onFalse) values rest
```

`testValue` (`:109`) is `some` only when the slot holds a `Val.bool`. Admission constrains
only the *type spelling*: `Effects/Flow/Raw.lean:186-193` `BranchTestWF` requires
`block.params[test.index]? = alphabet.boolTy`, and `Effects/Trace.lean:41-50` `Val` is an
untyped 8-constructor carrier with no relation to `Ty`. So an admitted flow whose test slot
holds `.nat 0` is a plain `choose`: the tape alone decides, and the advertised
"tape and value must agree, else refusal" contract does not hold there.

The module header at `Runs.lean:28-31` justifies the fallthrough:

> "A test operand with no boolean reading … is answered by the tape alone, which is what
> keeps `stuck` unreachable on an admitted flow (`plan_checked`)."

**This justification is false.** `PlanSized` has a `mismatch` constructor
(`Runs.lean:266`), and `plan_checked` discharges the `choose`/`branch` mismatch case with
`exact .mismatch _ _` (`:387`, `:411`). Refusing on `none` would satisfy `plan_checked`
exactly as well; nothing about `stuck` depends on the fallthrough.

The lowering makes the gap concrete: `Effect4/Target/TypeScript/Skeleton.lean:415-417`
renders `branchIf` as

```
decisions.report(site, test); if (test) { … } else { … }
```

a JavaScript truthiness test. `Val.nat 0` is falsy in the host and tape-determined in Lean.
The Lean machine mirrors `plan` here — `SkeletonSemantics.lean:1510-1522` handles the `none`
case by `cases w <;> …` and follows the tape — so Lean is internally consistent and the host
is the odd one out.

**Proposed change.** Make the `none` case refuse: `| none => .mismatch site site`. This
*simplifies* the design (one rule instead of two), makes the branch contract unconditional,
removes the third disjunct of `plan_mismatch_inv` asymmetry, and closes the host divergence.
`plan_checked` needs no change. Add a counterexample row for the flow that motivates it
(a `boolTy`-typed slot carrying a non-`bool`) and a `#guard` in
`Effect4Test/Target/TypeScript/MultiArgContract.lean`'s neighbourhood.

**Effort:** M (one line plus the proofs that case-split on `testValue`, ~6 sites).
**Risk:** medium — it changes the meaning of currently-admitted flows, so it needs a
counterexample row and a note in `docs/TRACE-DAG.md`.

---

### 5. `RunResult.refused` overloads two different refusals with no lemma separating them

**Category:** api / correctness

Flow v3 reuses `refused expected actual` for two distinct events:

* the tape names another site — `Effect4/Flow/Decision.lean:37-40` gives
  `.mismatch site decision.site` with `decision.site ≠ site`;
* a branch's tape entry names the right site but disagrees with the value —
  `Runs.lean:157` gives `.mismatch site site`, i.e. `expected = actual`.

The doc-comment at `Runs.lean:45-48` explains the encoding in prose ("refuses with that site
twice") but there is no theorem anywhere saying `Tape.read` never returns `mismatch d d`, so
nothing downstream can case on the discriminator soundly. `Tape.read_cons_ne`
(`Decision.lean:55-58`) takes `ne : actual ≠ expected` as a hypothesis rather than deriving
it, and no `read_mismatch_ne` exists.

**Proposed change.** Either (a) add
`theorem Tape.read_mismatch_ne : Tape.read t s = .mismatch e a → s = e ∧ (a ≠ e ∨ t = …)`
plus a `RunResult.refusalKind` classifier, or (b) — better — split the constructor:
`refusedSite (expected actual : DecisionId)` and `refusedValue (site : DecisionId)`. (b) is
self-documenting and removes the need for the lemma; it costs a `deriving DecidableEq`
re-elaboration and touches ~15 `#guard`s. Note that if finding #4 is taken, the `.mismatch
site site` case becomes the *only* value refusal and (b) gets cheaper still.

**Effort:** M. **Risk:** low-medium (wire goldens record `refused` pairs; check
`generated/traces/`).

---

### 6. ~1 400 lines of triplicated 7-clause block law across two modules

**Category:** cleanup / build

Three theorems state the same 7-way conjunction over `plan`'s shapes, each with its own
several-hundred-line case cascade:

| declaration | site | proof length |
| --- | --- | --- |
| `execList_skeletonBlock` | `Effect4/Target/TypeScript/SkeletonSemantics.lean:1251` | ~426 lines |
| `execList_skeletonBlockWith` | `Effect4/Target/TypeScript/SkeletonSemantics.lean:1933` | ~484 lines |
| `execList_skeletonBlockWith_bind` (private) | `Effect4/Target/TypeScript/StructureSemantics.lean:197` | ~540 lines |

Measured similarity between the second and third: **0.647** by `difflib` ratio, with
**253 of 295** distinct non-blank lines shared. The third is literally the second with
`Program.bind (…) H` wrapped around every conclusion and a generalized `Result`; its own
proof opens with `have terminal : afterFell … [] = Program.pure` (`StructureSemantics.lean:250`),
which is exactly the `H := Program.pure` specialization that would derive the second from it.

Copy-paste is visible in the build output: `lake build Effect4` emits the *same* unused-simp
warning at `SkeletonSemantics.lean:2387:43` and `StructureSemantics.lean:672:43`, both
`Option.bind_some` in an identical `simp only [kind, Bool.false_eq_true, ↓reduceIte,
List.nil_append, Lowering.performCatchResult, Option.some.injEq] at built`.

Each of the three also carries `set_option maxHeartbeats 1000000 in`
(`SkeletonSemantics.lean:1248`, `:1779`, `:2597`).

**Proposed change.** Two steps.
1. Replace the anonymous 7-way conjunction with a record, e.g.
   `structure BlockLaw (…) : Prop where ret … | jump … | perform … | choose … | exhausted …
   | mismatch … | performCatch …`. Named fields replace `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩`
   (`SkeletonSemantics.lean:1292`, `:1983`; `StructureSemantics.lean:252`) and make adding an
   eighth plan shape a one-line change instead of a three-site edit.
2. Keep `execList_skeletonBlockWith_bind` as the single proof (it is the most general), make
   it public, and derive `execList_skeletonBlockWith` from it at `H := Program.pure` via
   `Program.bind_pure_right`. Estimated saving: ~450 lines and one of the three
   `maxHeartbeats` bumps. `execList_skeletonBlock` genuinely differs (its continuation is
   existential in the machine, as `:1927-1932` explains) and should stay — but it should
   share the record.

**Effort:** L. **Risk:** medium; it is proof surgery on the T4 agreement spine, so do it
behind the existing `StructureSemanticsContract`/`SkeletonSemanticsContract` batteries.

---

### 7. Seven `plan` inversion lemmas live in the TypeScript target namespace

**Category:** api

`plan_ret_inv`, `plan_jump_inv`, `plan_perform_inv`, `plan_performCatch_inv`,
`plan_choose_inv`, `plan_exhausted_inv`, `plan_mismatch_inv` and `testValue_some` are
declared at `Effect4/Target/TypeScript/SkeletonSemantics.lean:861-1213`, inside
`namespace Effect4.Target.EffectV4` / `namespace Skel` (`:66`, `:71`). Their full names are
therefore `Effect4.Target.EffectV4.Skel.plan_ret_inv` — facts about `Effect4.Flow.plan`,
owned by `Effect4/Semantics/Runs.lean:114`, living in the TypeScript lowering namespace.

The consequence is already visible: `StructureSemantics.lean` imports `SkeletonSemantics`
and uses them 7 times, and nothing outside the TypeScript target can invert `plan` without
importing the skeleton IR. `docs/ARCHITECTURE.md` ("Planned source tree") assigns `Effect4/Semantics` the
"steps, runs" responsibility.

The section header is also stale: `SkeletonSemantics.lean:851-853` says "Six inversion
lemmas", and Flow v3 made it seven (`plan_performCatch_inv` at `:990`).

**Proposed change.** Move the eight declarations to `Effect4/Semantics/Runs.lean` (or a new
`Effect4/Semantics/PlanInversion.lean` if `Runs.lean` should stay at 545 lines), in namespace
`Effect4.Flow`. They are alphabet-generic already (`variable {Ty} {alphabet}` at `:859`), so
the move is mechanical. Fix the "Six" to "Seven".

**Effort:** S. **Risk:** low.

---

### 8. Six private theorems duplicated verbatim between `StructureOrder` and `StructureDominators`

**Category:** cleanup

`Effect4/Target/TypeScript/StructureDominators.lean:1` imports
`Effect4.Target.TypeScript.StructureOrder`, and then re-proves six of its `private` theorems:

| name | StructureOrder | StructureDominators | byte-identical |
| --- | --- | --- | --- |
| `findIdx_at_of_nodup` | `:121` | `:26` | yes (17 lines) |
| `index_rpo_at` | `:139` | `:44` | yes |
| `forward_target_later` | `:166` | `:49` | yes |
| `reachable_of_reducible` | `:475` | `:54` | yes |
| `graphOf_sourceClosed` | `:525` | `:59` | near (10 vs 11 lines) |
| `emitWith_reducible` | `:536` | `:71` | yes (12 lines) |

**Proposed change.** Drop `private` in `StructureOrder` (or mark them `protected`) and delete
the copies. If the intent is that they not escape the `Effect4.Target.Structured` namespace,
put them in a shared `Effect4/Target/TypeScript/StructureAux.lean` that both import.

**Effort:** S. **Risk:** none.

---

### 9. `length_filter_ne` / `length_le_of_nodup_subset` proved three times, and the code says so

**Category:** cleanup / api

The same pigeonhole pair exists in three modules across two packages:

* `.lake/packages/effects/Effects/Flow/Raw.lean:~445` (private, `BlockId`-specialized);
* `Effect4/Semantics/Fuel.lean:37,57` (private, general `α` with `[DecidableEq α]`);
* `Effect4/Semantics/Denotation.lean:393,416` (private, `BlockId`-specialized).

`Denotation.lean:390-392` states the reason outright:

> "upstream: lean4-effects (`Effects/Flow/Raw.lean` proves this privately for `BlockId`;
> `Effect4/Semantics/Fuel.lean` reproves it privately for a general `α`. A third copy is
> needed only because both are private)."

`Fuel.lean:31-35` explains the underlying constraint correctly: `List.Nodup.length_le_of_subset`
carries `Classical.choice`, which the trace lane's ceiling forbids.

Similarly `idBind`/`idMap`/`idPure` (three one-line `rfl` lemmas about `Id`) are duplicated in
`Effect4/Semantics/Runs.lean:236-238`, `Effect4/Semantics/Fuel.lean:158-160` and
`Effect4/Semantics/Approximation.lean:306-308`. And `erasedBlock` is defined twice,
`Effect4/Semantics/RegionSafety.lean:199` and `Effect4/Semantics/RegionTotal.lean:26`.

**Proposed change.** Add a public `Effects.ListAux` namespace to the `effects` package with the
choice-free pigeonhole pair (it is a natural export of a package whose whole point is the
ceiling), bump the pin, and delete all three private copies. Locally: hoist `idBind`/`idMap`/
`idPure` and `erasedBlock` to their nearest common ancestor (`Effect4/Semantics/Runs.lean`
and `Effect4/Semantics/RegionDenotation.lean` respectively).

**Effort:** M (needs an `effects` release). **Risk:** low.

---

### 10. 55 of 115 library modules (48 %) declare nothing; six of them are 100–409-line design essays

**Category:** cleanup / api

Computed by stripping block comments and blank/`--` lines:

```
EMPTY STUB MODULES: 55
```

25 are 9-line placeholders (`Effect4/Channel/*`, `Effect4/Schedule/*`, `Effect4/Layer/*`
except `LayerFamily`, `Effect4/Stateful/{Ref,Deferred,Queue,PubSub,SubscriptionRef}`,
`Effect4/Classification/*`, `Effect4/Transaction/*`, `Effect4/Meta/{Registry,Introspection,Emit}`,
`Effect4/Audit/*`, `Effect4/Semantics/{Configuration,Step}`, `Effect4/Data/{Canonical,Identifier}`,
`Effect4/Foreign/*`, `Effect4/Context/{Service,Environment,Requirement}`,
`Effect4/Target/TypeScript/{Type,Decode}`).

Six carry substantial prose and no code:

| file | lines |
| --- | --- |
| `Effect4/Schema/Getter.lean` | 409 |
| `Effect4/Schema/Value.lean` | 323 |
| `Effect4/Schema/Transformation.lean` | 295 |
| `Effect4/Schema/Foreign.lean` | 118 |
| `Effect4/Schema/Codec.lean` | 108 |
| `Effect4/Protocol/{Bytes,Admission,Identity,Profile}.lean` | 72/69/51/51 |

All 55 are imported by `Effect4.lean`, so they are 55 Lake jobs producing empty oleans.

Two secondary hazards. First, a naming trap: `Effect4/Stateful/Ref.lean` is empty while
`Effect4/Stateful/RefFamily.lean` is the real one; the same for `Effect4/Context/Service.lean`
(empty) vs `Effect4/Context/Key.lean`. Second, `docs/ARCHITECTURE.md`'s authority map assigns
design prose to `docs/`, yet ~1 300 lines of design argument now live in library stubs.

**Proposed change.** This is *deliberate* per `Effect4/AGENTS.md` ("Empty source stubs with no
exported declarations need neither record nor graph") and the README's phased-packet story, so
do not delete the placeholders. But: move the six essay-stubs' prose into `docs/` (they are
design rulings, not module documentation) leaving a 9-line placeholder like the rest, and drop
the 55 stubs from `Effect4.lean` — an umbrella that imports nothing is not a dependency, and
re-adding an import is one line when the packet opens.

**Effort:** M. **Risk:** low, but coordinate — `PORT-MANIFEST.md` may cite the stub paths.

---

### 11. `COORDINATION.md` is 2 699 lines with 47 stale claim rows and no live worktrees

**Category:** dx

Root `AGENTS.md` ("Development order") makes reading this file mandatory before any write. It is 176 KB,
85 sections, and the live "Current claims" table is 47 rows at `:30-84` followed by ~2 600
lines of append-only history.

Every claim row is stale. `git worktree list` shows one worktree at `645067a`; the tree is
clean; and the first claim row names "worktree `agent-a7d1f74bf61e7c52b`; uncommitted" for
`Effect4/Semantics/Fuel.lean` and `Effect4/Target/TypeScript/StructureLaws.lean`, both of
which are committed (`2328fa8`, `96b1ae2`). The file's own rule is "Release it by deleting the
row" (`:32-33`).

The header also contradicts itself: `COORDINATION.md:9` says "Last updated: 2026-08-31"
while the file contains sections dated 2026-09-03.

**Proposed change.** Split: `COORDINATION.md` keeps "Who is active" + "Current claims" +
"Working rules" (<120 lines, the thing every agent must read), and the 80 historical sections
move to `docs/COORDINATION-LOG.md` (append-only, referenced but not mandatory reading). Clear
the 47 dead rows in the same pass and drop the "Last updated" line in favour of git.

**Effort:** S. **Risk:** none. **Highest DX return per minute in this report.**

---

### 12. `scripts/test-trust-gate.sh` does a cold full rebuild for every run

**Category:** build

`test-trust-gate.sh:32-41` copies the sources and `.lake/packages` into a temp project but
**not** `.lake/build`, so the first `lake build` (`:58`) compiles all 243 modules from
scratch. There are then 4 more `lake build` invocations (`:104`, `:117`, `:147`, plus
`test-source-trust-tokenizer.sh` and `test-trust-boundaries.sh` reusing the probe), each
invalidating `Effect4Test/Audit/AxiomGate.lean` or `Effect4/Target/TypeScript/EffectfulField.lean`
and everything downstream.

Given the profile numbers below, that is on the order of 10–20 minutes of single-machine work
per gate run — on a memory-bound machine, the reason the gate is run rarely.

**Proposed change.** Add `.lake/build` to the copy at `:37-41`. Lake's traces are
content-hash based, so the initial build becomes a near no-op and only the deliberately
mutated modules and their dependents rebuild. Guard it: if the copied trace does not validate,
Lake rebuilds anyway, so the change is safe by construction.

**Effort:** S (one `cp -R`). **Risk:** low; verify once that the gate still detects the
planted `partial`/`unsafe`/`Classical.choice` fixtures.

---

### 13. `docs/ARCHITECTURE.md` states the wrong dependency pins

**Category:** cleanup (authority document)

`docs/ARCHITECTURE.md` ("Dependency direction"):

> "Effect4 has two external Lake dependencies: `effects` at
> `2447edd76649f035e989914ac899831d66e7dad2` and `typescript` at
> `cc62799055b1af7ce22b083afcfb30155c1ed4d0`, pinned in `lakefile.toml` and resolved at the
> same commits in `lake-manifest.json`."

Actual: `effects` at `a1171574…` (v0.7.0) and `typescript` at `31665ff…` (v0.4.2), verified
against `lakefile.toml:17,24`, `lake-manifest.json`, and `git rev-parse HEAD` in both
checkouts. The sentence asserts agreement with `lake-manifest.json` that does not hold.

`cc62799` is also cited as the live pin in two Lean sources:
`Effect4/Target/TypeScript/StructureOrder.lean:20` and
`Effect4Test/Counterexamples/Target/BreakScoped.lean:18`.

`docs/ARCHITECTURE.md` ("Planned source tree") additionally assigns `Effect4/Flow` "raw and checked first-order
graphs, blocks, regions, decisions and admission" — but raw/checked/blocks/admission moved to
the `effects` package; `Effect4/Flow/` now holds only `Region.lean`, `Decision.lean`,
`Interrupt.lean`.

**Proposed change.** Correct the three pins and the `Effect4/Flow` row. Better: make the pin
sentence a generated line, or replace the SHAs with tag names (`v0.7.0`, `v0.4.2`) plus a
gate in `scripts/check-internal-citations.sh` that cross-checks `lakefile.toml`.

**Effort:** S. **Risk:** none.

---

### 14. Ten counterexample IDs are cited in Lean but have no row in the register

**Category:** correctness (process)

Root `AGENTS.md` ("Counterexamples and claims"): "All counterexamples that can change a declaration or cutover
decision have a stable ID in `test/counterexamples/REGISTER.md`."

Cross-checking every `E4-*-CE-\d+` token in `Effect4/` + `Effect4Test/` against the 195 rows
of `REGISTER.md`:

```
ids cited in .lean but absent from REGISTER.md:
  E4-WIRE-CE-001, -003, -004, -005, -006, -007, -008, -009, -010, -012
```

All ten are cited in `Effect4Test/Protocol/ByteParserContract.lean` (`:33`, `:113`, `:129`,
`:213`, `:246`, `:293`, `:309`, `:336`, `:390`, `:459`) — the declared-red wire battery. They
appear nowhere in `test/` or `docs/`, so the register has no row for them at all, and
`scripts/check-internal-citations.sh` does not check ID resolution (it only rejects
line-numbered citations into six protected documents, `:17-27`).

Separately, 13 non-`MOVED` register rows are never cited from the Lean file the row itself
names (e.g. `E4-DATA-CE-001` names `Effect4Test/Data/RowContract.lean`;
`E4-TARGET-CE-002` names `Effect4Test/Counterexamples/Target/TypeScriptRender.lean`), so the
register→witness link is one-directional. `Effect4Test/AGENTS.md:19-23` asks for both.

**Proposed change.** Add the ten `E4-WIRE-CE-*` rows with status `RESERVED` (the register
already defines that status for exactly this case, `REGISTER.md:8-10`). Then extend
`check-internal-citations.sh` — or add a 30-line `check-counterexample-ids.sh` — with a
bidirectional set comparison: every ID cited in a `.lean` has a row, and every non-`MOVED`
row's named witness file cites the ID back.

**Effort:** S for the rows, S for the gate. **Risk:** none.

---

### 15. Frozen concurrency surface: 14 hand-maintained name lists, ~2 400 entries, in one 2 512-line file

**Category:** dx

`Effect4Test/Concurrency/FiberAssurance.lean` holds fourteen `private def` frozen lists:

| list | lines | ≈ entries |
| --- | --- | --- |
| `expectedInterruptOwned` | 81–145 | 62 |
| `expectedFiberOwned` | 146–227 | 79 |
| `expectedSchedulerOwned` | 228–593 | 363 |
| `authoredApiDeclarations` | 594–781 | 370 |
| `theoremReceipts` | 782–876 | 92 |
| `axiomReceipts` | 877–971 | 92 |
| `typeRows` | 972–990 | 32 |
| `leafReceipts` | 991–1007 | 14 |
| `forbiddenDuplicateDeclarations` | 1008–1022 | 12 |
| `graphEdges` | 1023–1187 | 14 |
| `supervisionOwned` | 1188–1895 | 705 |
| `supervisionApi` | 1896–2192 | 294 |
| `supervisionTheorems` | 2193–2331 | 136 |
| `supervisionShapes` | 2332–2513 | 147 |

`Effect4/AGENTS.md:47-50` warns that one new public declaration under `Effect4/Concurrency/`
"also moves the frozen surface census … and its generator counts, so plan both edits in one
packet". In practice a single new theorem requires editing up to six of these lists *plus*
regenerating the 237 KB `generated/fiber-assurance.tsv` *plus* possibly a row and a
`#check` ascription in the 4 005-line `Effect4Test/Audit/RuntimeCoverage.lean` (see the
`snapshotWitnesses` requirement in `Effect4Test/AGENTS.md:37-44`).

`scripts/generate-fiber-assurance.sh` generates the TSV projection but not the Lean lists,
which are authored.

**Why it matters.** This is the single biggest friction in adding anything to the concurrency
lane, and it is the friction most likely to produce a wrong-but-green edit (a name added to
`expectedSchedulerOwned` but not to `authoredApiDeclarations`).

**Proposed change.** Invert the direction: keep the *authored* facts (dispositions, graph
edges, forbidden duplicates, leaf routes — roughly 70 entries) in Lean, and derive the three
`*Owned` lists and `authoredApiDeclarations` from the environment at elaboration time,
comparing against `generated/fiber-assurance.tsv` as the frozen artefact. The checker already
computes `declarationsOwnedBy` (`FiberAssurance.lean:31-37`); the exact-surface property is
preserved by comparing to the TSV rather than to an inline literal, and the TSV is already
under a byte-for-byte drift gate (`scripts/check-fiber-assurance.sh`). Net: ~1 500 lines of
hand-maintained Lean deleted, one regeneration command instead of six edits.

**Effort:** L. **Risk:** medium — this is frozen assurance machinery; do it as its own packet
with the existing gate green before and after.

---

### 16. Nineteen unused-simp-argument warnings and one deprecation in the production build

**Category:** cleanup

`lake build Effect4` (exit 0, 139 jobs) emits 20 warnings:

* `Effect4/Semantics/Runs.lean` — 11 (`:435:64`, `:436:8`, `:438:64`, `:439:8`, `:441:54`,
  `:441:88`, `:446:82`, `:454:82`, `:470:45`, `:470:79`, `:516:49`, `:516:83`)
* `Effect4/Flow/Region.lean` — 4 (`:402:52`, `:406:83`, `:407:8`, `:408:61`)
* `Effect4/Target/TypeScript/SkeletonSemantics.lean` — 2 (`:1633:31`, `:2387:43`)
* `Effect4/Target/TypeScript/StructureSemantics.lean` — 1 (`:672:43`)
* `Effect4/Target/TypeScript/Trace.lean:42:11` — `` `String.mk` has been deprecated: Use
  `String.ofList` instead ``

The clustering in `Runs.lean:435-516` and `Region.lean:402-408` suggests the simp lists were
copied between the sibling `step`/`loop` law proofs.

**Proposed change.** Delete the 19 arguments the linter names and switch `String.mk` to
`String.ofList`. Then consider `-DwarningAsError=true` for the library target so warnings
cannot accumulate (or at minimum a CI grep).

**Effort:** S. **Risk:** none — the linter names the exact argument to drop.

---

### 17. Thirty-two `@[simp]` lemmas in a 45 000-line library, all in one area

**Category:** api

All 32 `@[simp]` attributes in `Effect4/` are in `Effect4/Schema/Representation.lean` (24),
`Effect4/Target/TypeScript/Schema.lean` (7) and `Effect4/Schema/Authoring.lean` (1). The
semantics, flow, runtime, concurrency and target-semantics modules — 1 366 public theorems
and 458 private ones — contribute none. There is one `attribute [local simp]`
(`Effect4/Schema/Check.lean:1600`) and no scoped simp set anywhere.

Consequence: every proof in those areas spells its unfolding list by hand
(554 `simp only [...]` occurrences in `Effect4/`), which is exactly what produced finding #16
and makes the block-law proofs of finding #6 so long.

**Proposed change.** Curate one scoped simp set per lane and tag the obvious rewriters:
`Tape.read_nil` / `read_cons_eq` / `read_cons_ne` (`Effect4/Flow/Decision.lean:49-58`),
`emit_run` (`Runs.lean:82`), `interpretRun_pure` / `interpretRun_vis`
(`Effect4/Semantics/Denotation.lean:185,191`), the `plan_*_inv` family once moved (finding #7),
and the `execList_cons_simple` / `execList_cons_control` / `execControl_*` unfolders in
`SkeletonSemantics.lean`. Use `scoped simp` so downstream users opt in. The `effects` package
already models this: `Effects/Flow/Block.lean:180+` tags its `argsAt_*` equations `@[simp]`.

**Effort:** M, incremental. **Risk:** low if scoped; medium if global (watch for loops in
`Representation`'s fold lemmas).

---

### 18. `autoImplicit` is on in 107 of 115 library modules

**Category:** correctness (hygiene)

Only eight `Effect4/` modules set `autoImplicit false`:
`Target/TypeScript/{StructureOrder,StructureDominators,StructureSemantics,StructureLaws,SkeletonSemantics}.lean`,
`Runtime/LiveStack.lean`, `Concurrency/{Supervision,FiberFamily}.lean`. The other 107 —
including every semantics module, `Effect4/Semantics/Runs.lean` among them — leave it on.

With `autoImplicit` on, a mistyped identifier in a theorem statement becomes a fresh
universe-polymorphic implicit binder rather than an error, which is precisely how a vacuous
or over-general theorem gets written and stays green. Note that `Runs.lean` uses `Ty` freely
with no `variable {Ty : Type _}` line — it *is* an auto-implicit throughout.

Interestingly, the newest modules (the Structure/Skeleton lane and the concurrency lane) all
set it false, so the convention exists and is simply not applied uniformly.

**Proposed change.** Add `set_option autoImplicit false` to the remaining 107 modules, one
area per commit, fixing the fallout (mostly adding explicit `variable {Ty : Type uTy}` lines).
Consider hoisting it to a package-level `leanOptions` in `lakefile.toml` once the tree is
clean, which also documents it once instead of 115 times.

**Effort:** L (mechanical but wide). **Risk:** low per module, and each module fails loudly.

---

### 19. `Effect4.Flow.Equiv` and the flow-level logic are fixed at `Ty : Type`

**Category:** api

`Effects.RawFlow` is universe-polymorphic in `Ty` (`Effects/Flow/Raw.lean:18`,
`structure RawFlow (Ty : Type uTy)`), and so is `FlowAlphabet` (`Effects/Flow/Block.lean:64`,
`FlowAlphabet.{uTy, uOp}`). But `Effect4/Semantics/Equivalence.lean:29` and
`Effect4/Semantics/Logic.lean:285` both declare `variable {Ty : Type}` — universe 0 only.

So the top-level composition story ("`Equiv` is the relation the lowering theorems are
instances of", `Equivalence.lean:16-19`) does not compose with a flow over a `Type 1`
type vocabulary, even though admission does.

**Proposed change.** Generalize both to `{Ty : Type uTy}`. Both files are short (131 and 395
lines) and neither has a proof that depends on the universe; this is a `variable` line change
plus universe annotations. Check `Effect4/Semantics/Denotation.lean` first, since `denote` is
what they quantify over.

**Effort:** S–M. **Risk:** low.

---

### 20. The fuel/termination and no-stuck theorems are `StateT σ Id`-only, and the headers do not say so

**Category:** api

`Effect4/Semantics/Fuel.lean` states its termination results only for `StateT σ Id`:
`step_progress {σ : Type}` (`:173`), `loop_budget_not_exhausted {σ : Type}` (`:251`),
`loop_fuelFor_not_exhausted` (`:325`), `run_fuelFor_finishes` (`:345`),
`runDefault_finishes` (`:364`), `run_fuel_ge_finishes` (`:372`), `run_not_failed` (`:449`),
`run_fuelFor_answered` (`:465`). Same in `Runs.lean`: `step_checked` (`:428`),
`loop_checked_not_stuck` (`:475`), `run_checked_not_stuck` (`:503`), `loop_fuel_mono` (`:521`).

By contrast `Effect4/Semantics/Denotation.lean`'s T1/T2 (`:240`, `:715`) are `[Monad M]
[LawfulMonad M]`, and `Equivalence.lean:55` correctly quantifies over general `M`.

The `Fuel.lean` and `Runs.lean` module headers (`:1-24` and `:6-31`) do not mention the
restriction. A reader is invited to believe "an admitted flow always finishes" holds for the
service monad they picked.

**Proposed change.** Either (a) generalize using the existing `DetRun M σ` class
(`Effect4/Semantics/Logic.lean:210-227`), which is exactly the "deterministic monad with a
run" abstraction these proofs need, or (b) at minimum add one sentence to each header naming
the restriction and pointing at T1/T2 for the general statement. (a) is the better answer and
`DetRun` already has both instances.

**Effort:** M for (a), S for (b). **Risk:** low.

---

### 21. `Effect4/Concurrency/Supervision.lean` theorem statements are machine-shaped ASCII one-liners

**Category:** cleanup / dx

Roughly 20 theorems in `Supervision.lean` are written with ASCII `forall`/`->` on single
lines of 170–563 characters, with all binders in the statement and `by intros; rfl` as the
proof. `:541` is 563 characters:

```
theorem Fiber.valid_iff :
    forall {χ : Type u} {β : Type v} {ε δ ι α : Type u}, forall f : Fiber χ β ε δ ι α, Fiber.Valid f ↔ f.children.Nodup ∧ (f.subscriptions.map Subscription.key).Nodup ∧ (Effect4.FiberStatus.Active f.core.status -> f.core.terminal = none ∧ …) ∧ … := by
  intros
  rfl
```

`awk 'length>160'` counts 12 such lines in `Supervision.lean` and 8 in `Scheduler.lean`.
Nothing else in the tree uses ASCII `forall`/`->` in a statement.

These are the declarations frozen by `FiberAssurance.lean`'s `supervisionTheorems`
(`:2193-2331`), so the shape is presumably a transcription of the frozen surface. The result
is that the most safety-critical statements in the concurrency lane are the least readable
ones, and a reviewer cannot diff them meaningfully.

**Proposed change.** Reformat to normal Lean: binders in the signature, `∀`/`→`, one clause
per line, and — for `Fiber.valid_iff` in particular — a `structure Fiber.ValidSpec` with named
fields instead of a 5-way `∧` of implications. Regenerate `generated/fiber-assurance.tsv`
after (the TSV records names and propositions, which are unchanged by formatting; verify with
`scripts/check-fiber-assurance.sh`).

**Effort:** M. **Risk:** low but touches frozen surface — needs a coordinated packet per
`Effect4/AGENTS.md:47-50`.

---

### 22. Kernel `decide` on fuel-20 region runs

**Category:** correctness / build

`Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean` closes four separation
theorems by kernel `decide` over whole region-flow executions:

```
:52   theorem … : machineAt failingRelease 20 [] ≠ runnerAt failingRelease 20 [] := by decide
:114  theorem … : machineAt decisionCycle 20 [] ≠ runnerAt decisionCycle 20 [] := by decide
:122  theorem … : … = runnerAt decisionCycle 20 [⟨⟨7⟩, true⟩] := by decide
:81,:93  (fuel 0 and 2)
```

`Effect4Test/Counterexamples/Runtime/ScopeRestorationBoundary.lean:133-145` does the same over
five scope-machine outcomes including a `Cause.combine`.

`by decide` forces the *kernel* to whnf the whole run; unlike `#guard` (which uses the
compiled evaluator at elaboration) this cost lands in type-checking and in every downstream
`collectAxioms`. There are 241 `by decide` occurrences overall, but these ~9 are the ones over
genuinely large terms.

**Why it matters.** It is not unsound — `Decidable` instances are honest here — but it makes
those modules the ones most likely to hit `maxRecDepth`/heartbeat limits after any change to
the region runner, and it hides the *reason* the two sides differ behind a boolean.

**Proposed change.** Where the point is a *separation*, extract the two concrete outcomes as
`def`s, prove each by `rfl` (or `#guard`-check them and prove the inequality by
`Outcome.noConfusion`/`simp`), and keep `decide` only for the small finite alphabet facts. At
minimum, add `set_option maxRecDepth` locally so a future failure is a clear diagnostic rather
than a stack overflow.

**Effort:** M. **Risk:** low.

---

### 23. The `ancestors` admission rule can be widened by a name collision

**Category:** correctness (latent)

`AxiomGate.lean:270-273`:

```
let bound :=
  if admitted declaration || (ancestors declaration).any admitted then
    auditImplementationAxioms
  else allowedAxioms
```

`ancestors` (`:143-147`) returns every proper name prefix, and `admitted` (`:266-268`) checks
`moduleOf? environment ancestorName` — i.e. *the module an ancestor declaration lives in*. So
if any declaration happens to be named exactly like an admitted module (say a
`structure Skeleton` in namespace `Effect4.Target.TypeScript`, giving the constant
`Effect4.Target.TypeScript.Skeleton`), then **every** declaration under that namespace — in
any module — inherits the `Classical.choice` admission.

Checked: no such collision exists today. The target modules declare into
`Effect4.Target.EffectV4`, not into their own module names, and
`Effect4.Target.TypeScript.Trace` (the one module whose name matches a namespace) has no
constant of that exact name.

**Proposed change.** Require the ancestor to live in the *same module* as the declaration:
`(ancestors declaration).any (fun a => admitted a && moduleOf? env a == moduleOf? env declaration)`.
That preserves the intended behaviour (equation lemmas and `match_n` auxiliaries live with
their parent) and removes the cross-module path entirely. Two lines.

**Effort:** S. **Risk:** none — if it over-tightens, the gate fails loudly with a name.

---

### 24. `Effect4/Schema/Check.lean` mutual admission predicates are unnamed 21-way conjunctions

**Category:** api

`Representation.FieldAdmissible` (`Effect4/Schema/Check.lean:710`) is a 60-line `match` whose
arms are anonymous conjunctions — 21 `∧` in the definition, with sibling helpers
`FieldAdmissibleList` (`:769`), `FieldAdmissibleElements`, etc. The characterization theorems
that unpack them are correspondingly wide:
`Representation.fieldAdmissible_objects_iff` (`:1439`, 5 `∧` over four `∀ … ∈ …` clauses) and
`Check.fieldAdmissible_filterGroup_iff` (`:1482`).

There is exactly one `attribute [local simp]` in the file (`:1600`) doing the heavy lifting.

**Why it matters.** Adding a `Representation` constructor (348 constructor lines in
`Effect4/Schema/Representation.lean`) means finding the right position in an unnamed
conjunction in several places; nothing names which clause failed when admission refuses.

**Proposed change.** Give the per-constructor obligations named `structure … : Prop` records
(one per shape), so `fieldAdmissible_*_iff` becomes projection lemmas and the refusal path can
name the failing field. This is the same shape as `Effects.FlowWF`
(`Effects/Flow/Raw.lean:207-216`), which does exactly this with eight named fields and is much
easier to work with — the tree already contains the good pattern.

**Effort:** L. **Risk:** medium — `Check.lean` is 1 827 lines with a large downstream battery.

---

### 25. `lake-manifest.json` pins `effects` by a 7-character abbreviated rev

**Category:** correctness (supply chain)

`lakefile.toml:19` and `lake-manifest.json` both carry `"rev": "a117157"` / `"inputRev":
"a117157"` for `effects`, while `typescript` uses the full 40-character SHA
(`31665ffca361ce2ceb2e57f3ec18f8c8500abda0`). Root `AGENTS.md` ("Reuse and compatibility") requires "pinned by exact
commit in `lakefile.toml`".

A 7-character prefix is not an exact commit: it is a prefix match against the remote's object
database, and it can become ambiguous as the repository grows. The comment above it
(`lakefile.toml:15-17`) also still reads "to be tagged v0.7.0", but `v0.7.0` exists and points
at that commit.

**Proposed change.** Replace with the full SHA `a11715748b04f2369e5031e3350f30b99862a07f`
(verified by `git rev-parse v0.7.0` in `~/Dev/lean4-effects`) in both files, and update the
comment to "tag `v0.7.0`".

**Effort:** S. **Risk:** none.

---

### 26. Twenty-two stale oleans from the pre-split module layout

**Category:** cleanup / build

`.lake/build/lib/lean/` contains 22 `.olean` files with no corresponding source, left over
from the `Effects`/`typescript` extraction:

```
Effect4/Algebra/{Handler,Handler/Category,Handler/Composition,Laws,MonadLaws,Program,
                 Signature,Sum,Universal}.olean
Effect4/Flow/{Admission (3.6 MB),Block,Checked,Raw}.olean
Effect4/Target/TypeScript/{Expr,Render}.olean
Effect4Test/Algebra/{AxiomReport,ExtractionContract,RetainedClosureContract}.olean
Effect4Test/Flow/{AdmissionContract,AxiomReport,DiagnosticPrecisionContract,PrivacyContract}.olean
```

~7 MB of dead artefacts. Harmless to Lake (it resolves by source), but they make
`.lake/build` a misleading picture of what exists, and `import Effect4.Flow.Raw` would fail
confusingly rather than cleanly.

**Proposed change.** `rm` exactly those paths (never `lake clean` on this machine). Better:
add a two-line check to an existing gate that lists oleans without sources, so this cannot
silently recur after the next extraction.

**Effort:** S. **Risk:** none.

---

### 27. `Effect4.lean` pulls `import Lean` into the production library

**Category:** build

`Effect4/Meta/Derive.lean:1` is `import Lean`, and `Effect4.lean:93` imports it. So the
`Effect4` umbrella — and every consumer of it — depends on the whole Lean metaprogramming
library. Only three library modules actually need the DSL:
`Effect4/Stateful/RefFamily.lean`, `Effect4/Concurrency/FiberFamily.lean`,
`Effect4/Layer/LayerFamily.lean` (the other 16 importers are batteries).

It is also the module with the largest `Classical.choice` exemption (finding #2) and a 5.3 MB
olean.

**Proposed change.** Add a `[[lean_lib]] name = "Effect4Meta"` for `Effect4/Meta/*` and the
three family modules, and remove `Effect4.Meta.Derive` from `Effect4.lean`. Downstream
consumers that only want the semantics then never elaborate `Lean`, and the target-lane
exemption stops being part of the library's advertised trust surface. (The three families
must move with it, since they *are* DSL invocations.)

**Effort:** M. **Risk:** medium — it changes what `import Effect4` gives you; check
`Effect4Test.lean` and `harness/`.

---

### 28. Per-module elaboration cost, measured

**Category:** build (baseline, not a defect)

Two `lake env lean --profile` runs on the largest modules:

| module | wall | dominant costs |
| --- | --- | --- |
| `Effect4/Schema/Representation.lean` (2 111 lines, 16 MB olean) | **14.2 s** | simp 3.78 s, type checking 3.24 s, blocked 2.17 s, pre-definitions 1.69 s, TC inference 1.62 s |
| `Effect4/Target/TypeScript/SkeletonSemantics.lean` (2 874 lines, 8 MB olean) | **8.6 s** | tactic execution 5.61 s, simp 5.52 s, type checking 2.2 s |

So no single module is pathological, and the `set_option maxHeartbeats 1000000` bumps at
`SkeletonSemantics.lean:1248,1779,2597` are comfortable rather than marginal. The build cost
is *breadth*: `Effect4Test.lean` transitively imports 242 modules, `Effect4.lean` 115.

Import-DAG hubs (internal fan-in, umbrellas excluded):

```
19  Effect4.Meta.Derive          (16 of the 19 are batteries; see #27)
13  Effect4.Schema.Representation
10  Effect4.Runtime.Runtime / Effect4.Concurrency.Scheduler / Effect4.Runtime.Scope
 9  Effect4.Semantics.Runs / Effect4.Semantics.Exit
```

Deepest transitive closures: `Effect4Test.Target.TypeScript.StructureSemanticsContract` (24),
`Effect4.Target.TypeScript.StructureSemantics` (22),
`Effect4Test.Counterexamples.Target.RegionSimulationBoundary` (22).

**Proposed change.** The DAG is healthy; no module imports far more than it uses. The one
lever is #27 (pull `Lean` out of the library root) and splitting the test target so a sweep
can build one lane — see the packet list.

**Effort:** —. **Risk:** —.

---

### 29. `Effect4Test` has no per-area targets, so a battery sweep is all-or-nothing

**Category:** build / dx

`lakefile.toml:10-12` defines a single `Effect4Test` lib over `Effect4Test.*`. There is no way
to build "the Schema batteries" or "the Flow batteries"; `Effect4Test.AGENTS.md:46` tells you
to "run the narrow file directly", i.e. `lake env lean <path>`, which re-elaborates the file
but gives no target-level caching or grouping.

**Proposed change.** Add per-area `lean_lib` targets over the existing directory structure:
`Effect4TestSchema` (`globs = ["Effect4Test.Schema.*", "Effect4Test.Counterexamples.Schema.*"]`),
and likewise Flow, Semantics, Target, Runtime, Concurrency, Audit. `lake build
Effect4TestSemantics` then becomes the narrow sweep command, and the red wire/race batteries
land in their own target that is *expected* to fail. Pairs naturally with finding #3.

**Effort:** S. **Risk:** none.

---

### 30. No `lake exe` entry point; 56 shell scripts are the only interface

**Category:** dx

`lakefile.toml` declares no `lean_exe`. Every gate is a shell script under `scripts/`
(56 files: 25 `check-*`, 8 `generate-*`, 20 `test-*`, 3 other). Nothing in `README.md` or the
`AGENTS.md` files enumerates them; `README.md:29-33` names only `scripts/test-trust-gate.sh`,
and root `AGENTS.md` ("Counterexamples and claims") names `scripts/report-effect-runtime-coverage.sh` and
`scripts/check-effect-runtime-census.sh`.

A newcomer (or a fresh agent session) has to `ls scripts/` and guess which of `check-x.sh`,
`generate-x.sh`, `test-x-gate.sh` to run and in what order.

**Proposed change.** Add `scripts/README.md` with one line per script (what it checks, what a
pass means, what it costs), grouped by lane, and a `scripts/all.sh` that runs the cheap ones.
The scripts already carry excellent header comments — `check-internal-citations.sh:1-40` in
particular states both what a pass means and what it does not — so this is aggregation, not
authoring. Reference it from `README.md`.

**Effort:** S. **Risk:** none.

---

### 31. `Effect4/Meta/Derive.lean` emits its per-program receipt as an `example`

**Category:** api

`Effect4/Meta/Derive.lean:400-404` emits, for every `effect_program`:

```
elabCommand (← `(example :
  Effect4.Target.EffectV4.performedNames (F := $famId) $spellingName $answerDefaultName …))
```

and the module header (`:44-50`) advertises it as "one receipt, checked by `rfl` at the
declaration site". Because `example` leaves no constant (finding #1), the receipt is checked
once and then vanishes: no `#print axioms`, no census join, no way for
`Effect4Test/Audit/RuntimeCoverage.lean` or `FiberAssurance.lean` to name it, and no
protection from the axiom gate.

**Proposed change.** Emit `theorem $(name).performedNames_eq : … := rfl` instead. It costs one
constant per program, gives the receipt a citable name (which the D5 discussion at `:52-62`
would benefit from), and brings it inside the ceiling.

**Effort:** S. **Risk:** none.

---

### 32. `plan`'s `performCatch` case is dead weight in the plain runner

**Category:** api

`Plan.performCatch` (`Effect4/Semantics/Runs.lean:100-102`) carries six fields, but the plain
`step` discards two of them (`:186`, `| .performCatch op request target env' _ _ =>`), and the
plain-runner path is provably identical to `.perform` — `Runs.lean:22-25` says so, and
`execList_skeletonBlock`'s seventh clause (`SkeletonSemantics.lean:1284-1291`) is
character-for-character its third.

So every consumer of `plan` pays for a seventh case that, at the plain-service face, is a
duplicate. The one consumer that needs the failure edge is `Effect4/Flow/Region.lean`.

**Proposed change.** Two options. (a) Keep `Plan` as is but add
`theorem plan_performCatch_eq_perform` so the seventh clause of every block law can be
`exact (…).3` instead of a repeated 60-line proof. (b) Drop the two error fields from
`Plan.performCatch` and have the region runner recover them from `block.term` (it already has
the block). (a) is cheap and immediately removes ~180 lines across the three block laws of
finding #6; (b) is cleaner but touches the region runner.

**Effort:** S for (a). **Risk:** low.

---

### 33. `README.md` states the wrong `effects` version

**Category:** cleanup

`README.md:8-9`:

> "The generic effect algebra is the [Effects](…) package, pinned at `v0.1.0`."

Actual pin is `v0.7.0`, and v0.2.0 already moved the first-order Flow into that package, so
the sentence understates what is external. The next sentence's inventory ("First-order Flow
admission … are implemented") also reads as if Flow admission lived here; it is in `effects`.

**Proposed change.** Update to `v0.7.0` and move "Flow admission" to the Effects sentence.
Consider generating the version from `lakefile.toml`.

**Effort:** S. **Risk:** none.

---

### 34. Register→witness citations are one-directional

**Category:** cleanup (process)

Thirteen non-`MOVED` `REGISTER.md` rows name a Lean witness file but the ID does not appear in
that file, e.g.

* `E4-DATA-CE-001` … `Effect4Test/Data/RowContract.lean`
* `E4-RUN-CE-026` … `Effect4Test/Counterexamples/…`
* `E4-TARGET-CE-002` … `Effect4Test/Counterexamples/Target/TypeScriptRender.lean`
* `E4-SEM-CE-008` … `scripts/test-trace-goldens-gate.sh`

`Effect4Test/AGENTS.md:19-23` asks for the witness to be "linked from the registry **and**
owning contract"; the reverse link is missing. Covered by the gate proposed in finding #14.

**Effort:** S. **Risk:** none.

---

### 35. Namespace/directory mismatches in the target lane

**Category:** cleanup

Files under `Effect4/Target/TypeScript/` declare into three different namespaces:

* `Effect4.Target.EffectV4` — `Skeleton.lean:67`, `EffectV4.lean:29`, `FlowLower.lean:43`,
  `RegionLower.lean:42`, `StructuredLower.lean:24`, `SkeletonSemantics.lean:66`
* `Effect4.Target.Structured` — `StructureOrder.lean:31`, `StructureDominators.lean:22`
* `Effect4.Target.TypeScript.Trace` — `Trace.lean:29`

and `Effect4/Semantics/Runs.lean`, `Fuel.lean`, `Denotation.lean`, `Logic.lean`'s second half
all declare into `Effect4.Flow`, not `Effect4.Semantics`. None of this is wrong, but nothing
records the intended mapping, so a reader cannot predict where a name lives and the
`AxiomGate` module lists (which are keyed by *module*, finding #2) look deceptively like
namespace lists.

**Proposed change.** Add a short "namespace map" table to `docs/ARCHITECTURE.md` (directory →
namespace → why), and consider renaming `Effect4/Target/TypeScript/Structure*.lean` to match
`Effect4.Target.Structured`. The `Effect4.Flow` naming for `Effect4/Semantics/*` is
deliberate and defensible — say so.

**Effort:** S. **Risk:** none.

---

## Quick wins (under an hour each)

1. **#16** — delete the 19 linter-named unused simp arguments and `String.mk` → `String.ofList`. Zero risk, removes all warnings from `lake build Effect4`.
2. **#26** — `rm` the 22 stale oleans under `.lake/build/lib/lean/Effect4{,Test}/{Algebra,Flow,Target/TypeScript/{Expr,Render}}`.
3. **#13 + #33 + #25** — fix the three wrong pins in `docs/ARCHITECTURE.md` ("Dependency direction"), `README.md:8`, and expand `lakefile.toml:19`'s abbreviated rev to the full SHA.
4. **#23** — two-line fix to `AxiomGate.lean:270-273` so `ancestors` cannot admit across modules.
5. **#12** — add `.lake/build` to the `cp -R` in `scripts/test-trust-gate.sh:37-41`.
6. **#31** — one-word change in `Effect4/Meta/Derive.lean:400`: `example` → a named `theorem`.
7. **#7 (partial)** — fix `SkeletonSemantics.lean:851` "Six inversion lemmas" → "Seven".
8. **#11 (partial)** — delete the 47 dead rows in `COORDINATION.md:30-84` and the stale "Last updated" line.
9. **#14 (partial)** — add the ten `E4-WIRE-CE-*` rows to `REGISTER.md` with status `RESERVED`.
10. **#8** — un-`private` six theorems in `StructureOrder.lean` and delete the copies in `StructureDominators.lean` (~50 lines).

---

## Packets

Ordered so each packet leaves the tree in a better state for the next.

### P1 — Trust gate repair (do first; everything else is judged by it)
**Findings:** #1, #2, #23, #3, #12
Extend the source tokenizer to `native_decide`/`sorry`/`admit`/`axiom`/`extern`/`implemented_by`;
replace the live `native_decide`; narrow `targetImplementationModules` to exact declarations
(1 099 → 71) with a generator command; scope `ancestors` to the same module; make the closure
gate honour `known-red.txt`; add a green default target so the gate runs on every build; warm
the trust gate's probe copy with `.lake/build`.
**Effort:** M–L. **Blocks:** nothing. **Unblocks:** every later packet, because after P1 a
green `lake build` actually means the ceiling held.

### P2 — Hygiene sweep (parallel with P1, no conflicts)
**Findings:** #16, #26, #13, #33, #25, #11, #14, #34, #30, #35
The quick-wins list plus the `COORDINATION.md` split, the counterexample-ID gate, and
`scripts/README.md`. Touches no `Effect4/` proof.
**Effort:** S–M.

### P3 — Flow v3 branch semantics
**Findings:** #4, #5, #32
Decide whether a `branch` on a non-`bool` test refuses (recommended: yes, and the doc's
`plan_checked` justification is wrong either way). If yes, split `RunResult.refused` into
site- and value-refusal while the case analysis is already open, and add
`plan_performCatch_eq_perform`. Freeze a counterexample row first — this is a breaker packet
by `AGENTS.md`'s development order.
**Effort:** M. **Depends on:** P1 (so the resulting axiom claims mean something).

### P4 — Plan inversion ownership
**Findings:** #7, #17 (partial)
Move the seven `plan_*_inv` lemmas plus `testValue_some` from
`Effect4.Target.EffectV4.Skel` to `Effect4.Flow`, tag the obvious rewriters `scoped simp`.
**Effort:** S–M. **Depends on:** P3 (its case analysis changes `plan_mismatch_inv`).
**Unblocks:** P5.

### P5 — Block-law de-duplication
**Findings:** #6, #9 (local half)
Introduce the `BlockLaw` record; keep `execList_skeletonBlockWith_bind` as the single general
proof and derive `execList_skeletonBlockWith` at `H := pure`; hoist `idBind`/`idMap`/`idPure`
and `erasedBlock`. Expected: ~450–600 lines removed and one `maxHeartbeats` bump dropped.
**Effort:** L. **Depends on:** P4. **Highest cleanup return in the tree.**

### P6 — Library/metaprogramming split and test targets
**Findings:** #27, #29, #10
Move `Effect4/Meta/*` and the three family modules to an `Effect4Meta` lib; add per-area
`Effect4Test*` targets; drop the 55 declaration-free stubs from `Effect4.lean` and relocate
the six essay-stubs' prose to `docs/`.
**Effort:** M. **Depends on:** P1 (the target list changes in both).

### P7 — Universe and hygiene generalization
**Findings:** #18, #19, #20
`autoImplicit false` across the remaining 107 modules, area by area; generalize
`Equiv`/`Logic`'s flow half to `Type uTy`; either generalize the fuel theorems over `DetRun`
or document the `StateT σ Id` restriction in the two headers.
**Effort:** L, but trivially splittable by directory. **Depends on:** nothing; do it during
quiet periods.

### P8 — Frozen-surface ergonomics (the big one; schedule last)
**Findings:** #15, #21, #24, #22
Derive `FiberAssurance`'s four largest lists from the environment against the already-gated
TSV instead of inline literals; reformat the ASCII-`forall` statements in `Supervision.lean`
and give `Fiber.Valid` a named record; give `Check.FieldAdmissible` per-shape records; replace
the fuel-20 kernel `decide`s with `rfl` on extracted outcomes.
**Effort:** L. **Depends on:** P1 and P2. **Risk:** highest in this report — it edits frozen
assurance machinery, so it needs `check-fiber-assurance.sh` and
`check-effect-runtime-census.sh` green before and after, in its own packet, with a
`COORDINATION.md` claim.

---

## Part II — the `effects` boundary and the drift sweep

Two further passes: one over `~/Dev/lean4-effects` (the `effects` dependency at `v0.7.0`)
and its boundary with Effect4, one over doc-comment and naming drift in `Effect4/`. Every
claim below was re-verified against the source by hand before inclusion; a handful of
candidate findings that did not survive verification are not listed.

---

### 36. `Effects.RegionWF` *is* the checker — no clause structure, no soundness law, and Effect4 unfolds a `where`-bound auxiliary to work around it

**Category:** correctness

`~/Dev/lean4-effects/Effects/Flow/Region.lean:224-226`:

```
/-- Every region clause holds. -/
def RegionWF [DecidableEq Ty] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty) : Prop :=
  flow.check alphabet = none
```

Compare the flow layer one directory up, which does this properly: `FlowWF`
(`Effects/Flow/Raw.lean:224-232`) is a structure with **eight** named Prop fields, and
`Effects/Flow/Admission.lean:1991 flowWF_iff_clauses` / `:2068 clause_all_complete` prove the
checker equivalent to it. The region layer has no counterpart: `CheckedRegionFlow.regions`
carries only "the `Option`-alternative chain returned `none`", which is a statement about a
program, not about the flow.

The cost lands downstream. `Effect4/Semantics/RegionSafety.lean:38-43` has to unfold the
checker to recover anything usable:

```
private theorem term_checked … : RegionFlow.checkBlock.checkTerm alphabet flow block = none := by
  simp only [RegionWF, RegionFlow.check, alternative_none] at wf
  … unfold RegionFlow.checkBlock at checked
```

`checkBlock.checkTerm` is a `where`-bound auxiliary (`Region.lean:180-181`), not API, and
`RegionSafety.lean:29` reimplements an `alternative_none` lemma to decompose `<|>`.

**Proposed change.** Give the region layer a `RegionWF` structure with one field per clause
plus `regionWF_iff_check`, mirroring `flowWF_iff_clauses`, and publish per-clause projections
so no downstream module ever unfolds `check`. **Effort:** L. **Risk:** medium — touches
`CheckedRegionFlow`, `admitRegions`, `RegionSafety`, `RegionTotal`. Requires an `effects`
release and a pin bump.

---

### 37. The region module's own docstring and contract contradict the v0.7.0 `performCatch` ruling

**Category:** correctness (doc), and a real expressiveness gap

`Effects/Flow/Region.lean:10-11` and `~/Dev/lean4-effects/test/contracts/flow-regions.contract.md`
("Semantics pinned here") both say:

> "A failure inside a region closes it, and every enclosing region, with the failure."

But `~/Dev/lean4-effects/test/counterexamples/REGISTER.md`, row `EF-FLOW-CE-007`, lists
exactly that as the **attacked** statement:

> "A caught failure unwinds the region it was raised in, so the failure successor of a catch
> is reached with the region already closed"

Effect4 already documents the corrected semantics — `Effect4/Flow/Region.lean:22-27`,
"A Flow v3 `performCatch` is the exception: its failure is *caught*, so it does not unwind."
The upstream doc and contract were not updated when v3 landed.

There is a substantive point underneath the doc bug: `checkBlock`'s `.plain term` arm runs
`targetsLabelled block.region term.successors` over **both** of a `performCatch`'s edges, so
the failure edge is *forced* to stay in the same region. Catch-and-unwind is therefore not
expressible in the region layer at all — which may be the right ruling, but it is currently
an accident of a successor-label check rather than a stated design.

**Proposed change.** Correct `Region.lean:10-11` and the contract to distinguish uncaught
failure (unwinds) from `performCatch` (does not); state explicitly whether catch-and-unwind is
a v0.8 terminator or a non-goal. **Effort:** S for the doc repair. **Risk:** none for the doc.

---

### 38. Effect4 declares into its dependency's root namespace

**Category:** api

`Effect4/Semantics/Denotation.lean:36-48` opens `namespace Effects` — the upstream package's
root — and adds a declaration there:

```
namespace Effects
…
/-- … upstream: lean4-effects (`Effects/Family.lean`, beside `Alphabet.toFamily`). -/
abbrev FlowAlphabet.toAlphabet {Ty : Type uTy} (alphabet : FlowAlphabet.{uTy, uOp} Ty) :
    Alphabet.{uTy, uOp} Ty := ⟨alphabet.Op, alphabet.requestTy, alphabet.answerTy⟩
end Effects
```

Its own comment says where it belongs. `docs/ARCHITECTURE.md` ("Planned source tree") states the rule it breaks:
Effects is "consumed through the pinned dependency, never re-declared here".

Four more declarations are upstream-shaped without squatting: `reachableNoChoose_trans`
(`Denotation.lean:434`), `reachSet_length_lt_of_edge` (`:447`), `lookupBlock_id`
(`Effect4/Semantics/Fuel.lean:73`, five call sites) and `mem_blockIds_of_lookup` (`Fuel.lean:80`).
`reachSet_length_lt_of_edge` in particular is the *one* consequence Effect4 wants from the
whole `insertAll`/`saturate` apparatus (see #39).

**Why it matters.** An upstream release that adds `Effects.FlowAlphabet.toAlphabet` — which
its own comment invites — becomes a build break that reads as an upstream bug.

**Proposed change.** Move the five declarations upstream in one `effects` release and delete
them here; nothing should remain in `namespace Effects` outside the effects package. The
axiom gate already knows each declaration's owning module, so this can be enforced with three
lines beside the closure check. **Effort:** S–M. **Risk:** low.

---

### 39. `effects` has inverted visibility: the two lemmas Effect4 needs are `private`, the fourteen it doesn't are public

**Category:** api (this is the upstream half of finding #9)

`Effects/Flow/Raw.lean:493,514` — `private theorem length_filter_ne`, `private theorem
length_le_of_nodup_subset`: the two Effect4 reproves twice.

Meanwhile `RawFlow.insertAll`, `expand`, `mem_insertAll`, `length_le_insertAll`,
`subset_of_length_insertAll_eq`, `nodup_insertAll`, `insertAll_subset`, `expand_subset`,
`saturate_sound`, `saturate_closed_or_grows`, `saturate_subset`, `mem_saturate_of_mem`,
`mem_of_closed`, `noChooseSuccessors_subset` (`Raw.lean:303-489`) are all **public**, and a
full grep of `Effect4/` + `Effect4Test/` uses **none** of them — only `RawFlow.reachSet` (1),
`RawFlow.mem_reachSet` (4) and `RawFlow.nodup_saturate` (1).

So the package exports its saturation scaffolding and hides its pigeonhole conclusion, which
is exactly backwards.

**Proposed change.** In one `effects` release: publish the generic-`α` pigeonhole pair (or a
small `Effects.ListAux`), take `reachSet_length_lt_of_edge` and `reachableNoChoose_trans`
upstream from `Effect4/Semantics/Denotation.lean:434,447`, and make the `insertAll`/`saturate`
scaffolding `private` or move it to a `Raw.Internal` namespace. Then delete the three
duplicated copies in Effect4. **Effort:** M. **Risk:** low (additive upstream, deletions
downstream).

---

### 40. An unknown `release` operation escapes region checking when the acquired operation is also unknown

**Category:** correctness

`Effects/Flow/Region.lean:199-204`:

```
match alphabet.lookup operation, alphabet.lookup release with
| some acquired, some releaser =>
    if alphabet.requestTy releaser = alphabet.answerTy acquired then none
    else some ⟨.acquireRelease, some block.id, block.region⟩
| some _, none => some ⟨.acquireRelease, some block.id, block.region⟩
| none, _     => none
```

`RegionFlow.eraseTerm` (`Region.lean:89`) drops `release` entirely
(`acquire op req _ target args ↦ perform op req target args`), so the release operation never
appears in the erased graph and the v2 `OperationsWF`/`unknownOperation` clause never sees it.
When the *acquired* operation is unknown, the `| none, _` arm returns no region diagnostic and
v2 reports only the acquired operation; the unknown release surfaces only on a second round,
after the first is fixed.

Not unsoundness — `admitRegions` still refuses the flow — but it defeats the "the first
failure names the real problem" discipline that `E4-FLOW-CE-016` and the ordered-diagnostic
work exist to establish.

**Proposed change.** Split the arm so `| none, none` and `| none, some _` still emit
`acquireRelease` when `alphabet.lookup release = none`. **Effort:** S. **Risk:** low — the
only behaviour change is an extra diagnostic on flows that were already refused.

---

### 41. Four carriers for "a named operation with a request and an answer type", and the middle one has no consumer and no bridge

**Category:** api

* `Effects.Signature` (`Effects/Algebra/Signature.lean:13`) — `Op`, `Answer`. Canonical for
  semantics: `Program`, `Handler`, `interpret`, sums and freeness are all stated over it.
* `Effects.Family` (`Effects/Family.lean:22`) — `Name`, `Param`, `Answer`, `Type`-valued.
  Canonical for services: `Service`, `toHandler`/`ofHandler`, `Service.traced`, and the DSL
  emitter at `Effect4/Meta/Derive.lean:292-337`.
* `Effects.Alphabet Ty` (`Effects/Family.lean:63`) — `Op`, `requestTy`, `answerTy`, code-valued.
* `Effects.FlowAlphabet Ty` (`Effects/Flow/Block.lean:66`) — the same three plus `id`,
  `operationId`, `lookup`, `errorTy`, `boolTy` and two lookup laws. Canonical for admission.

`Alphabet` has **no** consumer inside `Effects/` (only `EffectsTest/Family/TowerSmoke.lean:20,29`),
and the package never relates it to `FlowAlphabet` — the bridge exists only as Effect4's
namespace-squatting `FlowAlphabet.toAlphabet` (finding #38). So the "first-order carrier with
its own embedding theorem" that `~/Dev/lean4-effects/docs/CLAIM-BOUNDARY.md:88-89` promises is
half-built.

**Proposed change.** Keep `Signature` (semantics) and `Family` (services) canonical; make
`FlowAlphabet` the single first-order table and define `Alphabet` as a projection of it
upstream — or delete `Alphabet` and give `FlowAlphabet` a `toFamily` directly.
**Effort:** M. **Risk:** low–medium (`Alphabet.toFamily` is public API).

---

### 42. `Effects/Morphism.lean` and `Effects/Transport.lean`: 189 lines, no consumer, no contract, no receipts, and the docs disagree about whether they exist

**Category:** cleanup

Zero code-level uses in Effect4: grep for `Signature.Hom|MonadHom|Handler.pull|Handler.mapHom|interpret_map|interpretHom|Signature.empty|Program.map` across `Effect4/` and `Effect4Test/`
returns prose only, and `Effect4/Semantics/RegionDenotation.lean:42-45` explicitly rejects
them ("no `MonadHom`, no `Handler.mapHom`, no `interpretHom` and no `interpret_mapHom`").
Zero mentions in `EffectsTest/` for `interpret_map` — which `Effects/Morphism.lean:9` calls
"One law" — or for `interpret_mapHom`, `through_eq_mapHom`, `Program.map_id`, `Program.map_comp`,
`Service.toHandler_ofHandler`, `Service.ofHandler_toHandler`. No packet in `test/contracts/`.

The docs contradict each other three ways: `CLAIM-BOUNDARY.md:63` calls transport "a later
`Effects` packet"; `:81-86` says it landed in v0.2.0; `docs/ALGEBRA-DAG.md:27-28` says signature
maps and tower transport are "deliberately outside it". `CLAIM-BOUNDARY.md:77-79` concedes they
were "stood up … ahead of their contract packets … batteries follow". They did not follow.

**Proposed change.** Either write the contract, battery and axiom receipts, or move both
behind an unlisted `Effects.Experimental` root and say so in exactly one place.
**Effort:** M. **Risk:** low.

---

### 43. `FlowAlphabet.errorTy` and `boolTy` are unconstrained spellings with no failure-capability predicate

**Category:** correctness (upstream root of finding #4)

`Effects/Flow/Block.lean:73-79`. Nothing in `FlowWF` relates either field to anything:
`errorTy` appears only in `SlotWF`'s `performCatch`/`edge = 1` arm (`Raw.lean:141-147`),
`boolTy` only in `BranchTestWF` (`Raw.lean:185-191`). Admissible today: `boolTy = errorTy op =
requestTy op = answerTy op` for every `op`; a `performCatch` on an operation that can never
fail; a `branch` whose successors bear no relation to true/false.

The block comment at `Block.lean:75-77` — "An operation that cannot fail declares the
alphabet's own empty spelling" — describes a convention the type cannot express, since `Ty` is
a code type with no emptiness predicate. `CLAIM-BOUNDARY.md:241-246` disclaims this
deliberately, so it is not a broken promise; but it does mean `performCatch` admission is
weaker than it reads, and it is the upstream half of the branch-value hole in #4.

**Proposed change.** `errorTy : Op → Option Ty`, with a new clause refusing `performCatch` on
a `none` operation; or an alphabet-level `emptyTy : Ty` with the same comparison discipline.
**Effort:** M. **Risk:** medium — changes the frozen v3 `FlowAlphabet` row, so it is a breaker
packet upstream.

---

### 44. The v3 landing rewrote the frozen v2 battery, made its docstring false, and left the v2 contract behind

**Category:** dx (process)

Verified counts: `Effects/Flow/Admission.lean:349-368` `scan` has **18** entries;
`AdmissionClause` has **18** constructors. But:

* `EffectsTest/Flow/FlowV2Contract.lean:243` — "The fixed scan order: the thirteen v1 clauses,
  then the four new ones" (= 17) above a list of 18; `.branchTestType` was inserted by the v3
  commit.
* `~/Dev/lean4-effects/test/contracts/flow-v2.contract.md:246` — "`AdmissionClause` has exactly
  seventeen constructors in this order". `git diff --stat e86f141..a117157 -- test/` does not
  touch this file.
* `Effects/Flow/Region.lean:15` — "The seventeen v2 clauses check the erased graph".

The same diff also loosened acceptance conditions inside the breaker-owned v2 battery
(`duplicateDecisionId` from an explicit `RawTerm.choose` match to `RawTerm.decision?`;
`unknownOperation` from a `.perform` match to `operation?`), which `EffectsTest/AGENTS.md:10-12`
forbids. The v3 packet *does* authorise the supersession (`flow-v3.contract.md:356-357`), but
the v2 artefacts were left inconsistent, and `FlowV2Contract.lean:243-261` is now
byte-identical to `FlowV3Contract.lean:205-223`.

**Proposed change.** Mark `flow-v2.contract.md` superseded with a pointer to v3, fix the
docstring, and delete the duplicated `scan` pin from the v2 battery — v3 owns it, with
`#guard scan.length == 18`. **Effort:** S. **Risk:** none.

---

### 45. `Effects`' diagnostic API has no library consumer, and there is no all-diagnostics entry point

**Category:** api

`Effect4/` (the library, not the batteries) contains zero references to `Effects.Diagnostic`,
`AdmissionClause`, `CheckSite`, `DiagnosticPayload`, `diagnoseAt`, `FirstDiagnostic` or
`RegionRefusal`. It consumes only `admit`, `CheckedFlow`, `erase`, `erase_wf`, `erase_admit`.
Roughly 1 500 of `Admission.lean`'s 2 299 lines serve the unconsumed half.

`admit` returns `Except (Diagnostic Ty) (CheckedFlow alphabet)` — exactly one diagnostic
(`Admission.lean:2186-2194`) — and `firstDiagnostic?` is `private` (`:2115`), so a caller
wanting every failure must loop `diagnoseAt` over `scan` itself. There is no `admit?`.

**Proposed change.** Add `diagnoseAll : … → List (Diagnostic Ty)` — a two-line
`scan.filterMap (diagnoseAt …)` whose emptiness law is already `clause_all_complete` — and make
it the documented reporting path; or move `Diagnostic`/`preciseFailure` into
`Effects.Flow.Admission.Diagnostics` so the compile cost is opt-in.
**Effort:** S for the entry point, L for the split. **Risk:** low.

---

### 46. The two axiom gates have drifted apart

**Category:** build

`Effect4Test/Audit/AxiomGate.lean:143-147` added `ancestors` so an equation lemma or `match_n`
auxiliary inherits its parent's admission (`:270-273`).
`~/Dev/lean4-effects/EffectsTest/Audit/AxiomGate.lean:220-227` has neither, and judges every
generated auxiliary on its own — harmless while its exemption list is one module, a spurious
failure the moment Effects admits a real declaration.

Conversely, Effects kept the missing-directory guard (`EffectsTest/Audit/AxiomGate.lean:175-179
leanSources`) that Effect4 dropped (`Effect4Test/Audit/AxiomGate.lean:236-243` walks unguarded).
Everything else in the two ~330-line files is a namespace/message rename.

The upstream gate also confirms finding #1 from the other direction: it enumerates
`environment.constants` (`:205-213`) and its token scan recognises only `unsafe`/`partial`
(`:146-149`), so it has exactly the same `example` blind spot — 66 `example`s vs 10 `theorem`s
in `EffectsTest/`. Lean's own source is the proof: `Lean/Elab/MutualDef.lean:1195-1197`,
`if isExample views then withoutModifyingEnv do`.

**Proposed change.** Factor the gate into one shared source (a third tiny package, or a
`scripts/` template with a generated-diff check) so a hardening lands in both. Interim:
backport `ancestors` to Effects and `leanSources` to Effect4, and apply #1's token list to both.
**Effort:** M. **Risk:** low.

---

### 47. The trust-gate fixtures reproduce the gate's blind spots, and `opaque` is unflagged by either gate

**Category:** dx

`scripts/test-trust-gate.sh:128-148` plants three things: `partial`, `unsafe`, and a
`noncomputable def` reaching `Classical.choice`. It never plants a `sorry`, a `native_decide`,
an `opaque`, or any of those inside an `example` — so the suite cannot detect finding #1, and
cannot detect that `opaque` passes both gates (`.opaqueInfo` sets neither `isUnsafe` nor
`isPartial`, and `collectAxioms` traverses the body without objecting to the opacity).

**Proposed change.** Add `sorry.lean.txt`, `native-decide.lean.txt`, `opaque.lean.txt` and
`example-sorry.lean.txt` fixtures with expected rejections, and fix both gates until they pass.
This is the acceptance test for packet P1. **Effort:** S. **Risk:** none.

---

### 48. `effects` has no axiom report for Flow v3, regions, morphism, transport or family — twelve exported theorems uncovered

**Category:** dx

`EffectsTest/AGENTS.md:22-23`: "Axiom reports cover every exported theorem and record actual
dependencies." There are three reports — `Algebra/AxiomReport.lean` (60 entries),
`Flow/FlowV2AxiomReport.lean` (16), `Trace/AxiomReport.lean` (15). Uncovered:
`Effects/Morphism.lean`'s `interpret_map`, `Program.map_id`, `Program.map_comp`;
`Effects/Transport.lean`'s `interpret_mapHom`, `through_eq_mapHom`; `Effects/Family.lean`'s
`Service.toHandler_ofHandler`, `Service.ofHandler_toHandler`; `Effects/Flow/Region.lean`'s
`admitRegions_ok_erase`; and Flow v3's four `argsAt`/`arityAt` laws. There is no
`FlowV3AxiomReport.lean` or `RegionAxiomReport.lean`.

**Proposed change.** Add the two missing report modules and a Morphism/Transport/Family one,
or soften the AGENTS claim to what the gate actually guarantees. **Effort:** S. **Risk:** none.

---

### 49. `effects` compiles its library with `autoImplicit` on too

**Category:** build (cross-package companion to #18)

No `leanOptions` in `~/Dev/lean4-effects/lakefile.toml`, and `set_option autoImplicit false`
appears five times — all in `EffectsTest/`. So the module that owns the admission boundary
relies on auto-binding: `Effects/Flow/Raw.lean:27 def lookupBlock (raw : RawFlow Ty) …` has `Ty`
and its universe auto-bound. With `relaxedAutoImplicit` also on, a mistyped type name becomes a
fresh universe-polymorphic implicit rather than an error.

**Proposed change.** `leanOptions = { autoImplicit = false, relaxedAutoImplicit = false }` on
both packages' library targets, adding explicit `variable {Ty : Type uTy}` bindings.
**Effort:** M upstream, L downstream. **Risk:** low but wide.

---

### 50. Four `.lean` doc-comments cite modules and files that do not exist

**Category:** cleanup

All verified absent:

* `Effect4/Context/Key.lean:20` and `:317-318` cite `Effect4.FlowAlphabet` and
  `Effect4/Flow/Block.lean` — the type is `Effects.FlowAlphabet` and the file is
  `Effects/Flow/Block.lean` in the dependency. This citation is the *sole* justification given
  for `ServiceUniverse` being allowed to hold a Lean `Type`, so a reader who follows it cannot
  check the precedent.
* `Effect4Test/Protocol/ByteParserContract.lean:2` cites
  `test/contracts/wire-byte-parser.contract.md`; `test/contracts/` has 43 files and that is not
  one of them. Since this battery is intentionally red, its header is the only spec of what
  "green" means. The same file at `:54` cites `Effect4/Flow/Admission.lean`, also moved out.
* `Effect4/Target/TypeScript/Skeleton.lean:40-44` — three errors in one paragraph: it cites
  "§6, §7" (this file has sections 1–5 only, at `:72,:117,:186,:378,:457`); it names
  `Skeleton.exec`, which exists nowhere (the real names are `Skel.execList` and
  `Skel.execControl`, `SkeletonSemantics.lean:184,197`); and it says those names are "each
  marked `to be unified with Denotation.lean`", a string that occurs exactly once in the
  repository — in this sentence claiming it occurs elsewhere. This paragraph is the merge plan
  for the two denotation branches.
* `Effect4/Target/TypeScript/Lower.lean:13-15` — "its eight rules are the second half of the
  census". `Rule.all` (`:95-104`) has 29 entries in five groups; the dispatch group is 8 of 29.

Also: three module headers still say "Flow v2" over code that handles v3 —
`FlowLower.lean:6` ("dispatch-form lowering of an admitted Flow v2 graph") above
`:112 | .performCatch …` and `:127 | .branch …`; `ScriptFlow.lean:7,218`; `ScriptDenotation.lean:10`.
(The "v2" in `RegionLower.lean:184`, `Approximation.lean:1811`, `RegionDenotation.lean:901`
correctly names the erasure target — leave those.)

**Proposed change.** Repoint all of them; write or drop the wire contract. Then extend
`scripts/check-internal-citations.sh` — which today only rejects line-numbered citations into
six protected documents — with a resolver for `<path>.<ext>` tokens appearing in `.lean`
doc-comments, which would have caught every one of these.
**Effort:** S for the fixes, S–M for the resolver. **Risk:** none.

---

### 51. Three dead declarations

**Category:** cleanup

* `Effect4/Semantics/Approximation.lean:839 def loopChain` — one occurrence in the whole tree,
  its own definition. Its sibling `runChain` (`:904`) is used at `:915`, `:954`, `:965`, and
  the `runColimit`/`runColimitDefault` pair at `:911`/`:922` has no loop-level counterpart.
  This is the only fully unreferenced `def` in `Effect4/`.
* `Effect4Test/Schema/PayloadContract.lean:78 payloadBoundaryExpectedOwners` (15 rows) and
  `:97 payloadBoundaryForbiddenImports` (4 rows) — two occurrences in the tree, their own
  definitions. The docstring at `:75-77` says why: "Expected declaration-owner rows for the
  *future* environment inspection." A reader of the contract sees a forbidden-import list and
  reasonably assumes it is enforced; `Effect4.Schema.Payload` importing `Effect4.Schema.Value`
  would pass green today.
* `Effect4/Schema/Authoring.lean:130-132,137-138` — `Check.stringFinite`, `stringBigInt`,
  `stringSymbol`, `capitalized`, `uncapitalized`: five of eleven one-line `Check.named`
  wrappers with zero references, while the other six and the four parameterised ones are all
  consumed.

**Proposed change.** Delete `loopChain` (or add the `loopColimit` that would use it); wire the
payload-boundary lists into `Effect4Test/Schema/PayloadSurface.lean`, which already runs
`MetaM` environment inspection, or delete them and record the gap in the contract packet; give
the `Check` wrappers a `census` list with a completeness receipt the way
`RepresentationTag.census` has (`Effect4/Schema/Representation.lean:36-107`), or delete the
five. **Effort:** S each. **Risk:** none.

---

### 52. `?` means "returns `Option`" everywhere except `Supervision.lean`, where it means "returns `Bool`"

**Category:** api

`Effect4/Concurrency/Supervision.lean:141,149,163` — `Globals.extends?`, `Globals.ownsChildren?`,
`Fiber.valid?` all return `Bool`. `:177 Fiber.published?` in the same file returns `Option`, as
do ~35 `?`-suffixed declarations elsewhere (`Cause.error?`/`defect?`, `Scope.closingExit?`,
`Skeleton.literal?`/`spec?`, `ScopeMachine.request?`/`result?`/`restore?`, …). Lines `:197-198`
put both conventions side by side: `if f.valid? then` next to `match f.published? with`.

Compounding it, the same file uses the unsuffixed name for the `Prop`: `:128 Globals.Valid :
Prop` beside `:141 Globals.extends? : Bool`, and `:153 Fiber.Valid : Prop` beside `:163
Fiber.valid? : Bool`.

**Proposed change.** Rename the three `Bool` predicates (`isValid`, `extendsB`, `ownsChildrenB`)
or replace them with `decide`-wrapped `Valid`. **Effort:** S mechanically. **Risk:** **high** —
these names are frozen by `Effect4Test/Concurrency/FiberSupervisionContract.lean`,
`FiberAssurance.lean`'s `supervisionApi`/`supervisionTheorems`, and
`generated/fiber-assurance.tsv`. Do it inside packet P8, never alone.

---

### 53. `Effect4/Semantics/FrameSimulation.lean` documents its own layering violation and never resolves it

**Category:** cleanup

`Effect4/Semantics/FrameSimulation.lean:74-80`:

> "This module sits **above** both `Effect4/Semantics/*` and `Effect4/Runtime/Runtime.lean` …
> if the merge prefers strict directory layering the module moves to
> `Effect4/Runtime/FrameSimulation.lean` unchanged."

It is the only module under `Effect4/Semantics/` that imports `Effect4/Runtime/`, reversing the
direction `docs/ARCHITECTURE.md` ("Dependency direction") declares, and it is why its namespace is
`Effect4.FrameSimulation` rather than `Effect4.Flow` like its seven directory-mates.
`Effect4.lean:52-54` carries a matching fence comment.

**Proposed change.** Take the move the header already sanctions ("unchanged"), or record the
decision to keep it and delete the paragraph. **Effort:** S. **Risk:** low — the
`Effect4Test/Semantics/FrameSimulation*` imports move with it.

---

### 54. Namespace layout has no recorded map, and two directories use three each

**Category:** api / dx (the concrete form of finding #35)

`Effect4/Target/TypeScript/` (18 modules) declares into four namespaces:
`Effect4.Target.EffectV4` (10 modules: EffectV4, FlowLower, Lower, RegionLower, ScriptDenotation,
ScriptFlow, Skeleton, SkeletonSemantics, StructureSemantics, StructuredLower),
`Effect4.Target.Structured` (StructureDominators, StructureLaws, StructureOrder),
`Effect4.Target.TypeScript.<Module>` (EffectfulField, Schema, Trace), and flat `Effect4`
(Simulation). Note that `StructureSemantics` lands in `EffectV4` while the three modules it is
*stated against* land in `Structured`.

`Effect4/Semantics/` (14 modules) declares into five: `Effect4.Flow` (Approximation,
Equivalence, Fuel, RegionDenotation, RegionSafety, RegionTotal, Runs), flat `Effect4` (Cause,
Exit, Frontier, Observation), `Effect4.FrameSimulation`, `Effect4.RegionSimulation`,
`Effect4.Logic` — plus the `namespace Effects` block of finding #38.

**Proposed change.** Do not renumber everything — the contract batteries name declarations
fully qualified and a rename cascades into `generated/`. Instead: add a namespace-map table to
`docs/ARCHITECTURE.md` (directory → namespace → why), fix the one genuine defect (#38), and fold
`Effect4.Target.Structured` into `Effect4.Target.EffectV4` only if packet P5 already reopens
those files. **Effort:** S for the map, L for a rename. **Risk:** none / high respectively.

---

### 55. Prose conventions: three header styles, a routed-around alias, one word overloaded three ways, and a spelling split

**Category:** dx

* **Module headers** come in three shapes: `# Semantics.Runs` (path, `Runs.lean:7`),
  `# Semantics.Cause.lean` (path *with* extension — `Cause.lean`, `Runtime/Runtime.lean` and
  ~55 others; `Semantics.Cause.lean` is not a module name in any Lean sense), and prose titles
  (`# Finite canonical rows` in `Data/Row.lean`, `# Binary first-completion races` in
  `Concurrency/Race.lean`, ~20 more).
* **`abbrev Mask`** (`Effect4/Semantics/Observation.lean:32`) is immediately routed around: the
  table two lines below (`:37-39`) writes `Effects.Trace.Mask.outcomeOnly` / `.m1` / `.m2`, and
  downstream `RegionSimulation.lean:208` writes `Effects.Trace.Mask` while
  `Target/TypeScript/Trace.lean:93` writes `Effect4.Trace.Mask` — three spellings of one type.
* **`point`** names three unrelated things on the same Flow-v3 lowering path:
  `Effect4/Flow/Interrupt.lean:67 inductive Point` (an interruptible point),
  `Effect4/Semantics/RegionSimulation.lean:160,234,255,277,290,357 point : Config`, and
  `FlowLower.lean:103,122` / `RegionLower.lean:127` / `StructuredLower.lean:154`
  `let point : List Skeleton`.
* **British/American split**: `Effect4/Protocol/Admission.lean:19` "unknown-profile behaviour"
  vs `Effect4/Schema/Check.lean:53` "unknown-profile behavior" — the same coined phrase, and
  `Check.lean` itself uses the British form at `:99`, `:472`, `:479`. Tree-wide: `behaviour` 20 /
  `behavior` 8, `modelled` 22 / `modeled` 0, `labelled` 37 / `labeled` 1. The prose is otherwise
  consistently British. (`Effect4Test/Schema/StructuralAssurance.lean:121` registers the symbol
  `` `Effect4.Schema.Behavior `` — a *name*, so pin it deliberately either way.)
* Minor: `Effect4/Target/TypeScript/Skeleton.lean`'s `Lowering` builders track their
  constructors except two — `chooseIf` wraps `.decide` (`:249`/`:157`) and `performCatchResult`
  wraps `.performCatch` (`:259`/`:158`) — and the same concept is spelled `choose` (flow term),
  `decide` (skeleton), `"choose-if"` (rule id) across three layers, while its v3 twin is
  `branch`/`branchIf`/`"branch-if"` throughout. Rule id strings are pinned by
  `docs/LOWERING-COVERAGE.md`, so they must not move.
* Minor: `Effect4Test.lean` is an incomplete manifest by design (126 imports, 128 modules) but
  says nothing about it; add a comment at the omission point naming the two red modules and
  pointing at `known-red.txt`.

**Proposed change.** Normalise headers to `# <Dir>.<Module>`; delete or consistently use the
`Mask` abbrev; rename the two non-interrupt `point` binders (all local, zero risk); add the
behaviour/behavior pair to a spell list. **Effort:** M, all mechanical. **Risk:** none.

---

## Revised quick wins

Add to the ten above:

11. **#50** — repoint the four dangling citations (`Context/Key.lean:20,317`,
    `ByteParserContract.lean:2,54`, `Skeleton.lean:40-44`, `Lower.lean:13-15`) and drop
    "Flow v2" from the three v3-handling headers.
12. **#40** — split the `| none, _ => none` arm at `Effects/Flow/Region.lean:204`.
13. **#44 + #46 counts** — fix "seventeen"/"seven"/"thirteen v1 clauses" at
    `Effects/Flow/Region.lean:15`, `Effects/Flow/Admission.lean:2196,2209`,
    `EffectsTest/Flow/FlowV2Contract.lean:243`, `flow-v2.contract.md:246`, and
    `~/Dev/lean4-effects/README.md:14` ("v0.1.0" → v0.7.0).
14. **#51** — delete `loopChain` (`Approximation.lean:839`).
15. **#53** — move `FrameSimulation.lean` to `Effect4/Runtime/`, as its own header instructs.

## Revised packets

The eight packets above stand. Three take on upstream work, and one is new:

* **P1 (trust gate)** now also covers **#46** (backport `ancestors`/`leanSources`, share the
  gate source) and **#47** (the four missing fixtures — these are P1's acceptance test).
* **P2 (hygiene)** now also covers **#50**, **#51**, **#53**, **#55**, and the count fixes in
  **#44**.
* **P3 (Flow v3 branch semantics)** now also covers **#43** upstream (`errorTy : Op → Option Ty`)
  and **#37**'s doc repair — both are the same packet's subject matter, and #43 makes #4's
  refusal rule checkable at admission rather than at run time.
* **P9 — `effects` boundary release (new).** Findings **#36**, **#38**, **#39**, **#41**,
  **#42**, **#45**, **#48**, **#49** (upstream half), **#40**. One `effects` release plus a pin
  bump here: give the region layer a clause structure, publish the pigeonhole pair and take the
  two `reachSet` theorems upstream, privatise the saturation scaffolding, delete Effect4's
  `namespace Effects` block, resolve `Alphabet` against `FlowAlphabet`, decide Morphism/Transport's
  fate, add `diagnoseAll` and the two missing axiom reports. Schedule after P1 (so the upstream
  gate is hardened first) and before P5 (which will want the shared list lemmas).
  **Effort:** L. **Risk:** medium — it is a dependency release, so Effect4 pins the old commit
  until it lands and every change is additive-then-deleting.
