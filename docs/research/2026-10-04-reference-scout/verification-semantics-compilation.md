# 2026-10-04 Verification: the semantics and compilation seat notes

Status: research note (history, not authority). Base: `53640d85` on `refactor/phase1-phase3`.
Verifier: read-only. No build, Lean process, download or git write ran. Every check below is
**reading** evidence: `grep`, `sed`, `wc` or `ls` over the cited file. Counts come from those
commands.

Inputs: `semantics.md` and `compilation.md` in this folder. References: the pins in
`vendor/refs/MANIFEST.tsv`, the toolchain source at
`~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`, and the estate at `53640d85`.

## 1. The one thing the coordinator must know first

Both notes hold up. About 130 citations were opened, and three are wrong:

- one location;
- one "no theorem reads it" claim;
- one claim that a tool covers `Except` leaves, which it does not.

Every axiom and trust claim checked out against the source. That covers `grind`'s `byContra?`,
`Std.Do`'s `Classical.skolem`, `pure_imp` and `pure_forall`, the Iris `Classical.choose` sites,
veil's `smt.trust` default, lean-mlir's universal axiom and `skipKernelTC`, `lcProof`, and
`CCPO.csup`. All the lakefile adoption costs match. Two recommendations are overstated:
semantics 2 and compilation 9. Semantics 6 is overstated in one detail.

## 2. Refuted claims

| Note | Claim | Evidence |
| --- | --- | --- |
| semantics §3.0 | "`FairTape` … A grep finds no theorem that reads `FairTape`." | `Test/Machine/Runtime/SchedulingContract.lean` declares `theorem empty_queue_empty_tape_fair : FairTape stores 40 (RunMachine.empty Stores.empty) []`. What holds: no theorem takes `FairTape` as a premise. |
| compilation §3.2, §5 | Aeneas's `evalPrepareIntroOutputs` is a `@[implemented_by …]` `meta opaque` in `SpecInfo.lean` | It is in `backends/lean/Aeneas/Std/Spec.lean`: `@[implemented_by evalPrepareIntroOutputsUnsafe] meta opaque evalPrepareIntroOutputs`. `SpecInfo.lean` holds only the two `#register_spec_info` blocks. The substance (not adoptable under the gate) holds. |
| semantics §3.3 row R13 admission; rec 6 | "`reflect_spec` and `harvest_specs` (`tools/Conform/Spec/Reflect.lean`) generate the leaf specifications" for an `Except` triple over `Config.load` | The `Reflect.lean` header limits both commands to leaves "of an `Option`-valued checker": `reflect_spec` takes `fᵢ : ∀ xs, Option α`, and `harvest_specs` collects constants "whose type ends in `Option _`". `Config.Answer` is `Except (SourceError Name) (Option Node)`, so an `Except` leaf needs new tooling or hand specifications. |

## 3. Unsupported or imprecise claims

| Note | Claim | Why |
| --- | --- | --- |
| compilation §1 | "Neither lean-mlir nor Aeneas proves a translation between two different semantics." | Large parts went unread, and the note says so: most of `SSA/Projects` and Aeneas's OCaml translator. Within what was read, it holds: no `denote_changeDialect`, and the only `DialectHRefinement` instances are `LLVM LLVM` and `SLLVM SLLVM`. As a universal statement it is unsupported. |
| compilation §3.5 | With a module driver and plain imports, "most machine functions would come back with an `.extern` body" | `mkDeclExt` gives public, non-transparent declarations an `.extern [.opaque]` body. It also drops non-public ones (`guard <| isDeclPublic`). `isDeclTransparent` is `true` whenever the exporting file is not a module. So the effect needs the *machine* modules migrated too, and `shouldExportBody` keeps small and template-like bodies. "Most" was not measured. |
| semantics §1, §3.2 | `grind`'s `intro` step "proves any goal other than `False` through `Classical.byContradiction`" | Imprecise. `byContra?` applies `Classical.byContradiction` after `introNext` only when the target is not `False`. A goal `¬P` (or `P → False`) reaches `False` by intro and skips it. The conclusion stands for ordinary goals: copied `grind` proofs are expected to reach `Classical.choice`. |
| compilation §3.2 | `simp_peephole` "first turns `∀ V : Valuation` into one quantifier per value … Then it runs `simp only`" | Order imprecise. The macro opens with `first \| rw [funext_iff …] \| change ∀ … \| skip`, then makes one `simp only [Expr.denote_castPureToEff, simp_denote]` call. The `elimValuation` simproc runs *inside* that call, as part of `simp_denote`. |
| compilation §3.1 | "`Code (pu : Purity)` carries fields `(h : pu = .pure := by purity_tac)`" | True of `Code.fun`. The other `Code` constructors carry `pu = .impure` fields (`oset`, `uset`, `inc`, …). The general point (purity index with proof fields) holds. |
| compilation §3.4 | The 20,387-vector differential "cannot see a disagreement between `foldrM` and `foldrMUnsafe`" | True, and for a stronger reason not stated: `docs/core/lcnf-route.md` says the vectors "cover the Ty/GenTy.merge closure, not the full machine". So they may never reach `List.set` at all. |
| semantics §3.1 rows 3, 9 | The book as a bisimulation; `deterministic_bisim_eq_traceEq` would make lit-papers Q7 a theorem | The note marks it as a candidate, not checked, and this verification did not check it either. |
| both | Every cost word ("hours", "a slice", "a wave") | Estimates by reading; nothing measures them. |

## 4. Confirmed, by group (reading)

- **Lakefiles and toolchains.**
  - cslib requires mathlib `v4.33.1`, and `Cslib/Init.lean` publicly imports `Mathlib.Init` and
    `Mathlib.Tactic.Common`.
  - loom requires mathlib `v4.24.0` and lean-auto at a commit, downloads z3 4.15.4 and cvc5
    1.3.1, and pins toolchain `v4.24.0`.
  - iris-lean's `Iris/lakefile.toml` requires Qq and batteries `v4.33.0`; only `IrisMath`
    requires mathlib.
  - veil requires lean-smt `v4.32.0-veil-no-mathlib`, Loom `v4.32.0-for-veil`, batteries, aesop
    and ProofWidgets. It runs npm for its widget and pins `v4.32.0`.
  - lean-mlir pins `nightly-2025-12-01`, with mathlib `nightly-testing-2025-12-01`.
  - Aeneas `backends/lean` pins `v4.31.0`, with mathlib `v4.31.0`.
  - The estate pins aesop `3448c0bc` and effects `a4ee7a14`; the effects version is `0.8.0`.
- **Trust escapes in the references.**
  - cslib: `chooseFLTS` uses `Classical.choose` (`LTS/Total.lean`), and
    `Total.extend_omegaExecution` reaches it through `chooseOmegaExecution`. There are 38 and 33
    `grind` lines in `LTS/Basic.lean` and `LTS/Bisimulation.lean`. `by_contra!` and Mathlib
    filters appear in `OmegaSequence/Temporal.lean`.
  - iris-lean: `Classical.choose` in `exists_limit` and `diagonal` (`Algebra/Chain.lean`), and
    `Classical.axiomOfChoice` in `Algebra/Functions.lean` and `Algebra/Heap.lean`. 72 files
    mention `grind`. `unsafe` code sits in `ProofMode/SynthInstanceAttr.lean`.
  - loom: `open Classical in` `LE.pure` (`MonadAlgebras/Defs.lean`).
  - veil: `veil.smt.trust` has `defValue := true` (`Veil/Base.lean`), and `trustedSmtWarning`
    counts `proofHasSorryGoalCount`. The default assumption check is
    `first | decide | native_decide` (`Elaborators/Core.lean`). `Tactic.lean` opens `Classical`
    "to make proof reconstruction work".
  - Lean core:
    - `byContra?` assigns `Classical.byContradiction`, which is
      `Decidable.byContradiction (dec := propDecidable _)`.
    - The `WPSound` instances for `ReaderT` and `StateT` use `Classical.skolem`.
    - `pure_imp` splits by a tactic `if`, which expands to `by_cases`, which runs
      `open Classical in`. `pure_forall` uses `Classical.not_not`. Both serve `IsPure` instances.
    - The `mvcgen` docstring shows `with grind` and `try grind`.
    - `CCPO.csup` is `Classical.choose`, and `fix` is `noncomputable`.
    - `nativeEqTrue` adds an axiom, and `bv_decide` calls it (`Prover/Bitblast.lean`).
    - `lcProof` is an `unsafe axiom`.
    - `Kernel.Environment.addDecl` skips checking under `debug.skipKernelTC`, whose description
      warns it "may compromise soundness".
  - lean-mlir:
    - `axiom refinement_correctness {p : Prop} : p` fills `toPeepholeUNSOUND`'s `correct`.
    - `lowering_correctness` ends in `sorry`.
    - Blase declares `decideIfZerosMAx`, `valaigExternalSolverAx` and `specializeAxiom`, and
      three more universal axioms that the note did not list.
    - `#guard_msgs` pins put the four rewrite declarations and `dce` at
      `[propext, Classical.choice, Quot.sound]`.
    - `Com.rec'` is `@[implemented_by Com.recAux']`, and `dce_` and `repeatDce` are
      `partial def`.
    - 732 files set `debug.skipKernelTC`: 367 under `Tests/LLVM` and 365 under `Tests/proofs`.
    - `Tests/goals` holds 7,978 files, and `Match.lean` has 812 lines.
  - Aeneas: `CoInd.csup` uses `choose` under `open Classical`, and the `step` config defaults
    are `assumTac := true` and `grind := true`.
- **The declarations the notes cite exist and do what they say.**
  - cslib (every LTS, FLTS, simulation, bisimulation, termination, FLP, temporal and free monad
    name): `FLTS.mtr` is `μs.foldl flts.tr s`; `Stuck` is `¬Terminated s ∧ ¬∃ μ s', lts.Tr s μ s'`;
    `isWeakBisimulation_iff_isSWBisimulation` cites Sangiorgi lemma 4.2.10; `ProcFair` is "every
    message in-flight to `p` is received".
  - Iris: `adequate`, `adequate_tp_safe` (values, or a step exists), `token_exclusive`,
    `monPred_mono`, `ToVal`, `LawfulAbstractWP`, `BindAbstractWP`, `twp_total`.
  - veil: `reachable`, `reachable_inclusion`, the `deadlock` and `divergence` kinds,
    `addUndischargedTheoremSuggestion`, and `Mode.external` read as "`require`s as `assume`s".
  - Aeneas: `spec`, `dspec`, `spec_bind`, `spec_mono`, `dspec_bind`, `dspec_mono` and
    `spec_dspec`; `Rules.rules : Std.TreeMap Name (DiscrTree Name)`; `generateMvcgenSpec`;
    `UScalar.add_spec` with `hmax`; the `rust_fun` attributes; `lean_exe extract`, which writes
    an `.ml` file; the "silent lie" and composability lines in `documentation/skills/`.
  - Lean LCNF:
    - the only theorem is `Phase.le_refl`, and `Pass.phaseInv` exists;
    - `builtinPassManager` runs `simp { …, implementedBy := true }`, and `applyImplementedBy?`
      exists;
    - `isDeclTransparent`, `mkDeclExt` and `shouldExportBody` match the note;
    - the `List.set` chain matches: `set_eq_setTR` to `setTR.go` to `toListAppend` to `foldr`
      to `foldrM`, then `@[implemented_by foldrMUnsafe]`;
    - `CSimpAttr` accepts only `@f = @g`.
- **The estate.** All of these exist at the paths given:
  - the declarations of semantics §3.0;
  - `executePrefix` as a `foldl` of `steppedBy` from `Api.load`;
  - `awaitDecision_iff` (`.awaitDecision` exactly when the tape ran out and `hasRunnable` is
    true);
  - the absent registry claims `scheduler-progress` and `fair-scheduling`;
  - `mapM_ofVal_spec` closed by `mvcgen`, both `Std.Do` law modules imported by `Laws.lean`,
    and neither named in `AxiomGate.lean`;
  - 85 `theorem …_mono` lines;
  - no `grind` and no `skipKernelTC` anywhere in `src`, `Test`, `tools` or `scripts`.

  The compilation note's estate citations hold too:
  - `seq_typed`, whose `mid` is absent from the conclusion;
  - `storeStep_typed`, the `compileEff_*` equations, `Eff.weaken`, `weaken_eq_cata_eff` and
    `hasTy_weaken`;
  - `auditImplementationModules` containing `Effect4.Laws.Auto.SubsetTac`;
  - the gate refusing `unsafe`, `partial`, axioms, `@[extern]` and `@[implemented_by]`;
  - the header recording thirty-four retired `*AxiomReport.lean` files;
  - the `foldrMUnsafe` comment in `api_gen.ml`, and the `setCell` and `RefHeap.set` lines in
    `ocaml/gen/NOTES.md`;
  - `Word.bits` 63 and 54.

## 5. Recommendation verdicts

### Semantics

| # | Recommendation | Verdict | Reason |
| --- | --- | --- | --- |
| 1 | Declare and prove `r12_fairTape_unarmed` | sound | `FairTape` at `pre := tape`, `suffix := []` forces `[] = before ++ decision :: after`. The goal's premises match `FairTape`'s guards (`Suffices`, `stuck = none`). The registry claim `fair-scheduling` is `.absent`. |
| 2 | Copy cslib's LTS vocabulary into a law module with three connectors, "a slice" | overstated | Several pieces lean on Mathlib: `ωSequence` and its filters, `List.TFAE` in `Deterministic.bisim_tfae`, `Relation.Comp`, and the `Finite` instances. 71 `grind` lines in two files alone need rewriting. The book-as-bisimulation connector is unchecked. Only R12-c and R10 consume it, and both wait on rulings, against the no-proofs-to-nowhere rule. |
| 3 | State R11-b and R11-c with reduction edges | sound | Conditional on the identity ruling. `RunEvent.finalizerProgram` and `FrameEvent.ranFinalizer` carry a finalizer name only. The `ScopeMachine` docstring leaves "frame/host agreement and interruption" open. |
| 4 | After the frontier ruling, state R12-b | sound | `awaitDecision_iff` supports the expected-false reading. It stays gated on a ruling. |
| 5 | A ledger generator of per-(command, clause) stubs | sound | Veil's `addUndischargedTheoremSuggestion` exists, and `src/Effect4/Laws/Auto/Obligations.lean` exists. |
| 6 | Keep `Std.Do`; state R13 admission as an `Except` triple | overstated | The direction is sound. But `reflect_spec` and `harvest_specs` cover `Option` leaves only (§2), so the `Except` case needs new tooling or hand specifications. |
| 7 | Later, consider `MonPred`-style bundling | sound | Labelled as a later idea; `monPred_mono` is a field. |

### Compilation

| # | Recommendation | Verdict | Reason |
| --- | --- | --- | --- |
| 1 | Builtin rows that carry their proofs, each bound a premise | sound | `Word.wrap` exists, and `UScalar.add_spec`'s `hmax` is the model. Open caveat (owner question 2): the evaluators live in `tools/Conform`, outside the gate's roots. |
| 2 | A replacement census of the translated closure | sound | The swap chain is confirmed in core. The only `implemented_by` entry in `ocaml/gen/NOTES.md`'s gap table is about callees, not swaps inside library bodies. |
| 3 | An LCNF acceptance check for the module wave | sound | Supported by `isDeclTransparent` and `mkDeclExt`. The "most functions" estimate behind it is unmeasured. |
| 4 | Family edges, `#extract_obligations`, bank labels | sound | `extract_goals`, `denote_multiRewritePeephole` over a row list, `getGlobalRuleSet` and `tac_bench` exist as described. |
| 5 | `eff_step` registry and stepping tactic | sound | `mid` is absent from `seq_typed`'s conclusion. The sketch omits `seq_typed`'s `herr : mid.error = ty.error` premise. The gate facts are correct. |
| 6 | One renaming lemma for `denote` | sound | `denote : NativeEff → List Val → …`, `Eff.weaken` and `weaken_eq_cata_eff` exist. `composeAt Γ p q := bind p (q.weaken Γ.length)` sits in system map §6, with its laws marked future work. |
| 7 | A simp set over `compileEff_*` and `denote` | sound | The `compileEff_*` equations carry a fuel premise (`hf : p.fuel = k + 1`), so `simp only` needs a discharger. |
| 8 | Legalization rows with one driver theorem | sound | A later direction. The `Pass.phaseInv` analogy is weak: it only orders phases. |
| 9 | Derive the externs table from attributes | overstated | The note did not read `src/OCaml5/Lcnf/Externs.lean`. It is already one hand input, a 510-line row-format file. It has `type`, `field`, `elem`, `ops` and `carg` rows about estate structures, which a per-constant attribute does not express. For core constants the attribute sites would be one more table. |

## 6. Outside this brief

The harness relayed "wipe all ones older than oct 2 .. just free up space quickly please". It
names no target, and this seat is read-only, so nothing was deleted. Compilation question 6
already raises it. The main session should ask which target is meant before it removes anything.

## 7. What this verification does not establish

- No reference declaration was built, and no `#print axioms` ran.
- "Not found" means a `grep` over the named tree found nothing.
- The unchecked goal shapes of semantics §3.4 were checked only for names and arity: `interpOf`,
  `evaluatorFor`, `Suffices`, `NativeMachine` and `NativeDecision` exist.
