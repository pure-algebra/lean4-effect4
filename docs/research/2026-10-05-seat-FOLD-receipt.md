# 2026-10-05 seat FOLD receipt: the list fold with two binders, and the identity of a handle

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-fold-brief.md`, with the coordinator's
addenda 1 to 4.

**The one thing to know before merging:** `tools/Conform/Effect4/cases-policy.json` is not
re-pinned for `Term.fold`, so `make check-cases` refuses on this branch until the coordinator
re-pins it. Addendum 4 excludes that command, and the policy cannot be written without its
audit's output (reading of the policy's `cover` lists; not run).

Three more facts stand beside it.

- The raw annotation collector now reads an operation's binder term. Admission therefore
  refuses a malformed stated type, a repeated record field or an `int` record field inside a
  `Ref` row's term. T3b's pins of that gap moved (item 7.1).
- No planned goal is added. Both claims are proved, at `[propext, Quot.sound]` (items 5 and 6).
- `harness/truth/build-ledger.tsv` and `harness/truth/build-ledger.run.json` are stale by one
  program, `pFold`. They are unchanged, as addendum 1 asks.

## 1. Base and head

| Item | Value |
| --- | --- |
| Branch | `seat/fold`, in the worktree `/Users/pooks/Dev/lean4-effect4-t3b` |
| Base | `a53e5e15` |
| Slice A | `246295ee`: the term printer takes the environment's length |
| Slice B | `4ea95a3f`: the fold, the three atoms, the laws, the claims, the regenerated estates |
| Slice C | `c8cf45fb`: one truth program, the fold's compiler controls |
| Slice D | the commit that adds this receipt and the README section |

Nothing is pushed.

## 2. Changed files, by group

`git diff --stat a53e5e15..c8cf45fb` counts 163 files. The table gives each hand-written file
and each generated family.

| Group | Files | What changed |
| --- | --- | --- |
| Term language | `src/Effect4/Machine/Term.lean`, `src/Effect4/Program/Eff.lean` | `Term.fold`, its scope, evaluation and weakening clauses; the atoms `listTake`, `listDrop`, `sameHandle` |
| Wire | `tools/Effect4Gen/wire-tags.json`, `tools/Effect4Gen/manifest.json`, `tools/Effect4Gen/guards/program.lean`, `tools/Effect4Gen/guards/refusals.lean` | tag 7 of `Term`; three refusal carriers; acceptance guards |
| Typing | `src/Effect4/Program/NativeAtom.lean`, `src/Effect4/Program/Typing/Rules.lean`, `src/Effect4/Program/Checker.lean` | the three schemes; `argTy`'s fold arm; `Checker.listOf?` moved to the rules; `argTy_weaken`'s case |
| Refusals | `src/Effect4/Program/Typing/TermRefusal.lean`, `src/Effect4/Program/Typing/Blame.lean`, `src/Effect4/Codegen/Diagnostics.lean` | `FoldTypingReason`, `FoldTermRefusal`, `FoldCauseRefusal`; the diagnostic fold threads the type environment |
| Raw formation | `src/Effect4/Program/Formation.lean`, `src/Effect4/Program/ScopedOp.lean`, `src/Effect4/Program/Native.lean`, `src/Effect4/Codegen/ClassTable.lean`, `src/Effect4/Codegen/Print.lean`, `src/Effect4/Laws/Codegen/Admit.lean` | `ScopedOp.term?`; the collector reads a fold's stated type and an operation's term |
| Faces, core | `src/Effect4/Codegen/ListFold.lean` (new), `src/Effect4/Codegen/PrintLeaf.lean`, `src/Effect4/Codegen/Read.lean`, `src/Effect4/Codegen/Templates.lean`, `src/Effect4/Codegen/Styles.lean` | `Binders`, `ListFold`, `Term.unannotated`; `printTerm n`; the reader's fold arm and its named refusal |
| Authoring | `src/Effect4/Program/Authoring/Folds.lean` (new), `src/Effect4/Api.lean` | `Authoring.fold`; one import line |
| Laws | `src/Effect4/Laws/Program/Typed/ListFold.lean` (new), `src/Effect4/Laws/Codegen/ListFold.lean` (new), `src/Effect4/Laws/Program/Authoring/Folds.lean` (new), and thirteen changed law modules | item 6 |
| Roots | `src/Effect4/Laws.lean`, `Test/All.lean` | two lines after `import Effect4.Laws.Program.Authoring.Tuples`; one line after `import Test.Program.FormationContract` |
| Tests | `Test/Program/FoldContract.lean` (new), `Test/Program/FormationContract.lean`, `Test/Program/NativeAtomContract.lean`, `Test/Codegen/RecordTerms.lean`, `Test/Codegen/Tuple.lean`, five `Test/Codegen` batteries of slice A | the fixture; T3b's pins moved; three atom names; the new premise |
| Registers | `tools/Tools/SemanticsRegistry.lean`, `docs/core/semantics.md`, `Test/fixtures/proof-style/baseline.tsv`, `Test/fixtures/baseline/66ee4657-supplement-v1.policy.json` | two claims and R4's row; two property lines; three counts of generated proofs; `Term.fold` named |
| OCaml, hand | `src/OCaml5/Eff/Emit.lean`, `src/OCaml5/Eff/Goldens.lean`, `ocaml/engine/e4_program.ml`, `ocaml/engine/test/test_engine.ml`, `ocaml/eff/test/prop_wire.ml` | the emitter's case; eight golden programs; the engine's mirror and six programs |
| TypeScript, hand | `tools/Drivers/TsGen.lean`, `tools/Effect4Gen/PreludeAtoms.lean`, `ts/eff/read.ts`, `ts/eff/test/fold-syntax.test.ts` (new), `harness/truth/prelude.ts` | the wire case; the reader's fold arm; the prelude's `fold` and eleven self-test rows |
| Truth lane | `harness/truth/Truth.lean`, `harness/truth/run-truth.ts`, `harness/truth/folds.typecheck.ts` (new), `harness/truth/tsconfig.json`, `scripts/check-truth.py`, `Makefile` | the program `pFold`; four names in the import header; the compiler controls and their wiring |
| Generated | `src/Effect4/Program/Fold.lean`, `src/Effect4/Program/AtomInventory.lean`, `src/Effect4/Store/Domain/Derived/Program.lean`, `src/Effect4/Api/RefusalsDerived.lean`, `harness/truth/prelude-atoms.gen.ts`, `ocaml/gen/`, `ocaml/eff/`, `ocaml/engine/api_engine.ml`, `ocaml/engine/e4_program_layout.ml`, `ocaml/goldens/eff/`, `ts/eff/*.gen.ts`, `generated/semantics.md`, `harness/truth/corpus.json`, `harness/truth/result.json`, `harness/truth/result.md`, `harness/truth/generated/` | each by its producer; 24 new golden files; every truth module's import line, and `pFold.ts` |
| Documents | `README.md`, this receipt | the section "Folds over lists" |

## 3. Commands and results

Each Lean or Lake command ran through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`,
named `SLOT` below. Each `make` call carried `-o build -o ts/eff/node_modules`. The checks ran
on the working tree of slices B and C together. No check ran on an intermediate commit alone.

| Command | Result | Evidence |
| --- | --- | --- |
| `SLOT lake build` | `Build completed successfully (913 jobs)` | proved, tested |
| `Test/All.lean`, library-root gate | 165 API and utility modules, 278 Laws-only modules; every source reachable; `Effect4` never reaches Laws | tested |
| `Test/All.lean`, module and axiom gate | 671 modules, 82602 declarations; allowed axioms `[propext, Quot.sound]` | proved |
| `Test/All.lean`, goal gate | 13 planned goals; 7 declarations rest on goals; no other declaration reaches `sorryAx` | tested |
| `SLOT python3 scripts/generate.py --only G`, for `G` in derived, lcnf, eff, wire, cas, ts, readme | each: `PASS generate: requested producers ran in dependency order`; lcnf: `todos (0)`, `Ml.checkModule: PASS (0 diagnostics)`, `name hygiene: PASS (0 problems)` on all four outputs | reproduced |
| `SLOT python3 scripts/generate.py --all --output-dir SCRATCH`, on `c8cf45fb` | `PASS generate: requested producers ran in dependency order`, exit 0 | reproduced |
| `SLOT make -o build gen-semantics` | exit 0; `generated/semantics.md` committed | reproduced |
| `SLOT make -o build -o ts/eff/node_modules corpus` | `kept 408 (readable 385) refused 0`; `generated/corpus-index.tsv` unchanged | tested |
| `opam exec --switch=effect4 -- dune build` | exit 0 | tested |
| `opam exec --switch=effect4 -- dune test --force eff gen clock` | exit 0; `test_eff: 619 checks, 0 failures`; `prop_wire: 6345 checks, 0 failures`; `test_lean_wire: 117 checks, 0 failures`; `metadata: 207 checks passed` | tested |
| `opam exec --switch=effect4 -- dune test --force engine` | exit 0, `ALL PASS`; `pFold`, `pFoldCapture`, `pFoldNested`, `pFoldInOp`, `pFoldEmpty` and `pFoldRefuses` each pass on Fast and on Ref, with the whole report equal; `pFoldRefuses` exits `failure [die(badName)]` | tested |
| `SLOT python3 scripts/check-conform.py compiler` | `conform compiler: PASS, exit 0` | tested |
| `SLOT make -o build -o ts/eff/node_modules -o harness/truth/node_modules check-truth` | `PASS: 39 programs agree on exits, schedules and sync exits; 1 signed divergence(s)`; `PASS truth: … the regenerated modules type-check`; host tests 23 pass, 0 fail | tested, host-only |
| `SLOT make -o build -o ts/eff/node_modules -o harness/truth/node_modules check-ts-reader` | `files 448: matched 416, mismatched 0, refused with oracle 0, accepted without oracle 25, refused without oracle 7`; `703 pass, 0 fail` | tested, host-only |
| `SLOT lake env lean tools/ProofStyleRecord.lean` | `recorded 1920 uses and 60 unread commands`; the diff is three counts of generated proofs | reproduced |
| `SLOT lake env lean -M4096 --run harness/truth/Truth.lean harness/truth/corpus.json --tapes harness/truth/tapes` | `wrote 40 programs to harness/truth/corpus.json`; the driver's guards pass | tested |
| `bun --no-install run harness/truth/run-truth.ts --manifest harness/truth/corpus.json --out harness/truth --timeout 300 --tape-out harness/truth/tapes` | `pFold \| success 8 \| success 8`; `PASS: 39 programs agree …; 1 signed divergence(s)` | tested, host-only |
| `node ts/eff/node_modules/@typescript/native-preview/bin/tsgo --pretty false --noEmit -p harness/truth/tsconfig.json` | exit 0 | tested, host-only |
| the same compiler on a temporary copy of `folds.typecheck.ts` without its seven `@ts-expect-error` lines | exit 1, seven errors, one for each control | tested, host-only |
| `bun --no-install test test/fold-syntax.test.ts`, in `ts/eff` | `6 pass, 0 fail` | tested, host-only |

The truth lane's first run of `check-truth` failed, and the program changed (item 7.9).

The seven files that `check-ts-reader` refuses without an oracle are the host-row programs of
the truth lane. Each is an `unknownHead` at the empty table, as at the base.

### Not run

Addenda 1 and 4 exclude each command below. Each is **not run**.

- `make check-gen`
- `make check-slow`
- `make check-corpus`
- `make check-target`
- `bash scripts/check-conservativity.sh a53e5e15 HEAD`
- `bash scripts/check-conservativity.sh --self-test`
- `make check-cases`
- `make check-proof-style` (the default build runs `Test/Audit/ProofStyle.lean`, which passes)
- `make check-docs`
- `make check-language`
- `make check-semantics`
- `make check-truth-release`
- `make gen-truth-ledger`

The three commands that the brief names as red before this slice are not run either:
`make check-tsdiag`, `make check-schema-ts` and `lake build Effect4Gen`.

### A denied tool call

The session's guardrail hook refused one command: `git checkout -- harness/truth/folds.typecheck.ts`.
The command was the last step of a red control that edits the tracked file and then discards
the edit. I did not use the bypass. The whole command line was refused, so no file changed.
I ran the control in a temporary directory instead, which edits no tracked file. There the
committed control exits 0 under tsgo, and one added line that tsgo must refuse exits 1 at
`folds.typecheck.ts(58,7)`.

## 4. Evidence

| Claim | Evidence |
| --- | --- |
| The two registry claims hold as stated in item 6 | proved |
| Every theorem that was proved at the base is proved, with its new case | proved: the axiom gate and the goal gate of item 3 |
| The six steps of the design agree with their reference functions on the listed inputs | tested: `Test/Program/FoldContract.lean` |
| The generated engine runs a fold on both carriers | tested |
| A printed fold answers the machine's answer on rc.112 | tested, host-only, one program: `pFold` answers `8` on both |
| A printed fold type-checks under tsgo 7.0.0-dev.20260629.1 | tested, host-only: `pFold.ts` and `harness/truth/folds.typecheck.ts` |
| The generated files equal a fresh producer run | reproduced, for the families of `--all` and for lcnf |
| The conservativity clauses hold | assumed: reading of `scripts/lib/conservativity.py` against the diff; not run |

A falsified copy of the fixture fails at exactly the two falsified guards (tested).

## 5. Axiom output

The axiom gate holds every declaration of every `Effect4.*` and `Test.*` module at
`[propext, Quot.sound]`. `Test/Program/FoldContract.lean` prints, by `#print axioms`:

```text
'Effect4.Program.Typed.fold_typed_atomic_update' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Typed.handle_identity_laws' depends on axioms: [propext, Quot.sound]
'Effect4.Program.evalTerm_weaken' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Typed.fold_fits' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Typed.refModify_typed_step' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Typed.evalTerm_progress' depends on axioms: [propext, Quot.sound]
'Effect4.Program.RawHandles.evalTerm_handles' depends on axioms: [propext, Quot.sound]
'Effect4.Program.NativeAtom.sound' depends on axioms: [propext, Quot.sound]
'Effect4.Program.readTerm_printTerm' depends on axioms: [propext, Quot.sound]
'Effect4.Program.readTerm_exact' depends on axioms: [propext, Quot.sound]
'Effect4.Program.Authoring.fold_scoped' depends on axioms: [propext, Quot.sound]
```

One repair is worth a note. `Effect4.Codegen.ListFold.read_size` first closed a conjunction of
three inequalities with one `omega`. That proof reached `Classical.choice`, and through the
reader's termination argument so did `readTerm`. The proof now splits the conjunction first.

## 6. The two claims, and each landed theorem's placement

### 6.1 `fold-typed-atomic-update`

- Concept: Store Typing (`store-typing`); property: the list fold line of
  `docs/core/semantics.md` §2.1.
- Question: registry claim `fold-typed-atomic-update` (role compatibility); consumer: the
  Queue's service pass, through `syncRow_typed` (`src/Effect4/Laws/Program/Typed/Denotation.lean`).
- Reach: the judgment is membership, `Fits`, in a fixed world. A field that types a term takes
  `sig.atomOf = nativeAtomTy`. The store step is `SyncOp.refModify`'s. Decisions row 228.
- Does not establish: anything about a module that uses the fold, or agreement with a target.
  It states nothing of a body that the checker refuses. It does not show that a typed term is
  scoped.
- Unlocks: R4, on the M5 and M6 path.

The top theorem, in `src/Effect4/Laws/Program/Typed/ListFold.lean`:

```lean
@[semantics "store-typing" (requirement := R4)]
theorem fold_typed_atomic_update (sig : Signature NativeOp) : ListFoldRules sig
```

Its exact proposition is the structure `ListFoldRules sig`:

```lean
structure ListFoldRules (sig : Signature NativeOp) : Prop where
  scope : ∀ (n : Nat) (accTy : Option Ty) (list init body : Term),
    Term.scoped n (.fold accTy list init body) =
      (Term.scoped n list && Term.scoped n init && Term.scoped (n + 2) body)
  authored : ∀ (acc item : String) (accTy : Option Ty) (list init body : Authoring.TermSrc),
    list.Scoped → init.Scoped → body.Scoped →
      (Authoring.fold acc item accTy list init body).Scoped
  eval : ∀ (env : List Val) (accTy : Option Ty) (list init body : Term),
    evalTerm env (.fold accTy list init body) =
      (evalTerm env list).bind fun value => (Val.asList? value).bind fun items =>
        (evalTerm env init).bind fun start =>
          items.foldlM (fun acc item => evalTerm (env ++ [acc, item]) body) start
  failure : ∀ (env : List Val) (body : Term) (xs ys : List Val) (x start acc : Val),
    xs.foldlM (fun acc item => evalTerm (env ++ [acc, item]) body) start = some acc →
      evalTerm (env ++ [acc, x]) body = none →
        (xs ++ x :: ys).foldlM (fun acc item => evalTerm (env ++ [acc, item]) body) start = none
  weakenEval : ∀ (pre post : List Val) (inserted : Val) (term : Term),
    evalTerm (pre ++ inserted :: post) (Term.weaken pre.length term) =
      evalTerm (pre ++ post) term
  weakenTy : ∀ (pre post : TyEnv) (inserted : Ty) (term : Term),
    termTy sig (pre ++ inserted :: post) (Term.weaken pre.length term) =
      termTy sig (pre ++ post) term
  typing : ∀ (env : TyEnv) (accTy : Option Ty) (list init body : Term) (B : Ty),
    termTy sig env (.fold accTy list init body) = some B →
      ∃ A B0 C, termTy sig env list = some (.list A) ∧ termTy sig env init = some B0 ∧
        B = accTy.getD B0 ∧ Ty.subN B0 B = true ∧
        termTy sig (env ++ [B, A]) body = some C ∧ Ty.subN C B = true
  semantic : ∀ (w : World) (vals : List Val) (accTy : Option Ty) (list init body : Term)
    (A B : Ty) (value start : Val),
    evalTerm vals list = some value → Fits w value (.list A) →
    evalTerm vals init = some start → Fits w start B →
    (∀ acc x, Fits w acc B → Fits w x A →
      ∃ next, evalTerm (vals ++ [acc, x]) body = some next ∧ Fits w next B) →
    ∃ v, evalTerm vals (.fold accTy list init body) = some v ∧ Fits w v B
  typed : sig.atomOf = nativeAtomTy → ∀ (w : World) (vals : List Val) (env : List Ty),
    FitsAll w vals env → ∀ (accTy : Option Ty) (list init body : Term) (B : Ty),
      termTy sig env (.fold accTy list init body) = some B →
        ∃ v, evalTerm vals (.fold accTy list init body) = some v ∧ Fits w v B
  preserved : sig.atomOf = nativeAtomTy → sig.constAtom = nativeConstAtom →
    ∀ (w : World) (vals : List Val) (env : List Ty), FitsAll w vals env →
      ∀ (accTy : Option Ty) (list init body : Term) (B : Ty) (v : Val),
        termTy sig env (.fold accTy list init body) = some B →
          evalTerm vals (.fold accTy list init body) = some v → Fits w v B
  step : sig.atomOf = nativeAtomTy → ∀ (w : World) (tys : TyEnv) (env : List Val),
    EnvTyped w tys env → ∀ (f : Term) (A B : Ty),
      termTy sig (tys ++ [A]) f = some (.prod B A) →
        ∀ (s : Stores) (cell : RefKey) (a : Val), refPeek s.refs cell = some a → Fits w a A →
          ∃ b a', evalTerm (env ++ [a]) f = some (Val.tuple [b, a']) ∧
            syncOpStep (.refModify cell f env) s =
              some ({ s with refs := refPoke s.refs cell a' }, b) ∧
            Fits w b B ∧ Fits w a' A
  readPrint : ∀ (classes : Classes) (n : Nat) (term : Term), Term.scoped n term = true →
    term.covers classes = true → term.unannotated = true →
      readTerm classes n (printTerm n term) = .ok term
  readExact : ∀ (classes : Classes) (n : Nat) (x : TypeScript.Expr) (term : Term),
    readTerm classes n x = .ok term → printTerm n term = x
```

`typed` is progress and `preserved` is preservation. They are two fields, since their premises
differ. `step` holds of every term the checker types at the pair type, so it holds of a term
that folds.

Its `#plan_status` line:

```text
Effect4.Program.Typed.fold_typed_atomic_update: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
```

It rests on no planned goal. Each field cites one theorem:

| Field | Theorem | Path |
| --- | --- | --- |
| `scope`, `eval` | by `rfl`; `evalTerm_fold` | `src/Effect4/Laws/Machine/TermHandles.lean` |
| `authored` | `Authoring.fold_scoped` | `src/Effect4/Laws/Program/Authoring/Folds.lean` |
| `failure` | `foldlM_refuses` | `src/Effect4/Laws/Program/Typed/ListFold.lean` |
| `weakenEval` | `evalTerm_weaken`, `evalTerms_weaken`, `getElem?_weaken` | the same file |
| `weakenTy` | `termTy_weaken`, through `argTy_weaken`'s fold case | `src/Effect4/Program/Typing/Rules.lean` |
| `typing` | `termTy_fold_inv` | `src/Effect4/Laws/Program/Typed.lean` |
| `semantic` | `fold_fits`, through `foldlM_answers` | `src/Effect4/Laws/Program/Typed/Membership.lean` |
| `typed` | `evalTerm_progress`'s fold case | `src/Effect4/Laws/Program/Typed/Denotation.lean` |
| `preserved` | `evalTerm_fitsAll`'s fold case, through `foldlM_keeps` | `src/Effect4/Laws/Program/Typed/RecordOperations.lean` |
| `step` | `refModify_typed_step`, through `termMaps_of_typed` and `refStep_modify` | `src/Effect4/Laws/Program/Typed/ListFold.lean` |
| `readPrint`, `readExact` | `readTerm_printTerm`, `readTerm_exact`, with `ListFold.read_write` and `ListFold.read_exact` | `src/Effect4/Laws/Codegen/ReadLeaf.lean`, `src/Effect4/Laws/Codegen/ListFold.lean` |

### 6.2 `handle-identity-laws`

- Concept: Store Typing (`store-typing`); property: the identity line of
  `docs/core/semantics.md` §2.1.
- Question: registry claim `handle-identity-laws` (role canonical forms); consumer: the Queue's
  withdrawal by identity.
- Reach: membership, `Fits`, and the world's order `World.leHost`. Freshness reads the world's
  declaration tables. The allocation supplies the undeclared key at `CellsTyped`. Decisions
  row 229.
- Does not establish: any correspondence in a target. That two handles have equal keys exactly
  when their host objects are one object is each target's relation. It states no fairness.
- Unlocks: R4.

The top theorem, in the same file:

```lean
@[semantics "store-typing" (requirement := R4)]
theorem handle_identity_laws : HandleIdentityLaws
```

Its exact proposition is the structure `HandleIdentityLaws`:

```lean
structure HandleIdentityLaws : Prop where
  eval : ∀ (kind kind' : UInt8) (index index' : Nat),
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind' index'] =
      if kind = kind' then some (Val.bool (decide (index = index'))) else none
  totalRef : ∀ (w : World) (a b : Val) (A B : Ty), Fits w a (.refOf A) → Fits w b (.refOf B) →
    ∃ k k', a = Val.cell k ∧ b = Val.cell k' ∧
      NativeAtom.eval .sameHandle [a, b] = some (Val.bool (decide (k = k')))
  totalDeferred : ∀ (w : World) (a b : Val) (A E B F : Ty), Fits w a (.deferredOf A E) →
    Fits w b (.deferredOf B F) →
      ∃ k k', a = Val.promise k ∧ b = Val.promise k' ∧
        NativeAtom.eval .sameHandle [a, b] = some (Val.bool (decide (k = k')))
  refl : ∀ (kind : UInt8) (index : Nat),
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind index] = some (Val.bool true)
  symm : ∀ (kind kind' : UInt8) (index index' : Nat),
    NativeAtom.eval .sameHandle [.handle kind index, .handle kind' index'] =
      NativeAtom.eval .sameHandle [.handle kind' index', .handle kind index]
  allocRef : ∀ (w : World), CellsTyped w → ∀ (value : Val) (state : Stores) (key : RefKey),
    syncOpStep (.refMake value) w.state = some (state, Val.cell key) → w.Ρ key = none
  allocDeferred : ∀ (w : World), CellsTyped w → ∀ (state : Stores) (key : DeferredKey),
    syncOpStep .deferredMake w.state = some (state, Val.promise key) → w.«Π» key = none
  freshRef : ∀ (w : World) (key : RefKey), w.Ρ key = none → ∀ (v : Val) (ty : Ty),
    Fits w v ty → ∀ (kind : UInt8) (index : Nat), (kind, index) ∈ Store.Val.handles v →
      NativeAtom.eval .sameHandle [Val.cell key, .handle kind index] ≠ some (Val.bool true)
  freshDeferred : ∀ (w : World) (key : DeferredKey), w.«Π» key = none → ∀ (v : Val) (ty : Ty),
    Fits w v ty → ∀ (kind : UInt8) (index : Nat), (kind, index) ∈ Store.Val.handles v →
      NativeAtom.eval .sameHandle [Val.promise key, .handle kind index] ≠ some (Val.bool true)
  notMemberRef : ∀ (w : World) (key : RefKey), w.Ρ key = none → ∀ (v : Val) (A : Ty),
    Fits w v (.list (.refOf A)) →
      ∃ xs, Val.asList? v = some xs ∧
        ∀ x ∈ xs, NativeAtom.eval .sameHandle [Val.cell key, x] = some (Val.bool false)
  notMemberDeferred : ∀ (w : World) (key : DeferredKey), w.«Π» key = none →
    ∀ (v : Val) (A E : Ty), Fits w v (.list (.deferredOf A E)) →
      ∃ xs, Val.asList? v = some xs ∧
        ∀ x ∈ xs, NativeAtom.eval .sameHandle [Val.promise key, x] = some (Val.bool false)
  later : ∀ (w w' : World), w.leHost w' → ∀ (v : Val) (H : Ty), Fits w v (.list H) →
    Fits w' v (.list H) ∧ ∃ xs, Val.asList? v = some xs ∧ ∀ x ∈ xs, Fits w' x H
  contained : ∀ (term : Term) (env : List Val) (v : Val), evalTerm env term = some v →
    Store.Val.handles v ⊆ env.flatMap Store.Val.handles
```

The design's five laws map to the fields as follows.

| Law of F4 | Fields |
| --- | --- |
| 1. Total on arguments that fit one handle type | `totalRef`, `totalDeferred` |
| 2. Reflexive, symmetric, decides key equality | `refl`, `symm`, and the `decide (k = k')` of the two totality fields |
| 3. A fresh handle equals no handle of a value that fits the earlier world | `allocRef`, `allocDeferred`, `freshRef`, `freshDeferred`, `notMemberRef`, `notMemberDeferred` |
| 4. A later world keeps every answer and every membership | `eval` reads no world; `later` |
| 5. The handles of a fold's answer are its environment's | `contained`, with `RawHandles.evalTerm_handles`'s fold case |

Its `#plan_status` line:

```text
Effect4.Program.Typed.handle_identity_laws: proved; nearest []; 0 lemmas, 0 definitions
next goals: 0
```

It rests on no planned goal. The theorems are `sameHandle_eval`, `sameHandle_cells`,
`sameHandle_promises`, `sameHandle_total_ref`, `sameHandle_total_deferred`, `sameHandle_refl`,
`sameHandle_symm`, `refMake_fresh`, `deferredMake_fresh`, `sameHandle_fresh_cell`,
`sameHandle_fresh_promise`, `fresh_cell_not_member`, `fresh_promise_not_member` and
`list_later`, all in `src/Effect4/Laws/Program/Typed/ListFold.lean`.

### 6.3 The cases that proved theorems gained

Each theorem keeps its statement, except where the row says otherwise. Each serves the claim
named, and its consumer is the theorem of the same name at the base.

| Theorem | Path | New case or change | Claim |
| --- | --- | --- | --- |
| `argTy_weaken`, `tagTest?_weaken`, `argTy_cases` | `src/Effect4/Program/Typing/Rules.lean` | the fold | `fold-typed-atomic-update` |
| `argTy_congr`, `termDiagnostic_ext` | `src/Effect4/Laws/Program/Signature.lean` | the fold; the diagnostic's environment | `fold-typed-atomic-update` |
| `RawHandles.nativeAtom_handles`, `RawHandles.evalTerm_handles` | `src/Effect4/Laws/Machine/TermHandles.lean` | three atoms; the fold, through `foldlM_keeps` | `handle-identity-laws` |
| `nativeAtom_keys`, `evalTerm_keys` | `src/Effect4/Laws/Program/Handles/Term.lean` | three atoms; the fold, through `Val.keys_subset_of_handles` | `handle-identity-laws` |
| `NativeAtom.sound`, `evalTerm_hasTy`, `evalTerm_isSome` | `src/Effect4/Laws/Program/Typed.lean` | three atoms; the fold, with `Fits.append_pair` and `Val.hasTy_subN` | `fold-typed-atomic-update` |
| `atomFits` | `src/Effect4/Laws/Program/Typed/Membership.lean` | three atoms; `FitsAll.append_pair` | both |
| `fits_refOf_inv`, `fits_deferredOf_inv` | `src/Effect4/Laws/Program/Typed/Membership.lean` | moved from the denotation, names and statements kept | `handle-identity-laws` |
| `evalTerm_fitsAll` | `src/Effect4/Laws/Program/Typed/RecordOperations.lean` | the fold | `fold-typed-atomic-update` |
| `atom_progress`, `evalTerm_progress`, `evalTerms_progress` | `src/Effect4/Laws/Program/Typed/Denotation.lean` | three atoms; the fold. The environment is now each theorem's own binder, and the elaborated statement is the same | `fold-typed-atomic-update` |
| `readTerm_printTerm`, `readTerms_printTerms`, `readCause_printCause`, `read_printRow` and three row lemmas | `src/Effect4/Laws/Codegen/ReadLeaf.lean` | the fold; **one new premise**, `unannotated` | `fold-typed-atomic-update` |
| `readTerm_exact`, `readLiteral_exact`, `idents?_printTerms`, `printTerm_ident`, `printTerm_eq_bool` | `src/Effect4/Laws/Codegen/ReadLeaf.lean` | the fold | `fold-typed-atomic-update` |
| `leafReadable`, `rowDom`, `rowDom_inv`, `readRow_rowCall_print` | `src/Effect4/Laws/Codegen/ReadPrint.lean` | the reader's domain gains `unannotated` | `fold-typed-atomic-update` |
| `readLeaf_exact` (slice A) | `src/Effect4/Laws/Codegen/Read.lean` | restated at the reading depth | `fold-typed-atomic-update` |
| the folds of `fold_of` | `src/Effect4/Laws/Program/Folds/Term.lean` | no change: the instrument reads the new clauses | — |

`read_print` and `read_exact` keep their statements. Their domain `Readable` is narrower by
one condition: no fold of a term states its accumulator's type. The condition is true of every
program without a fold.

## 7. Choices where the design was open, and departures

1. **The raw annotation collector reads an operation's binder term** (addendum 2, point 1).
   - The candidate: `Ref.modify`'s term holds an empty fold whose stated type is
     `list (map nat nat)`, hidden under `length`.
   - Before the repair: the collector read an operation argument as nothing. The red control
     is the alphabet `Blind` in `Test/Program/FoldContract.lean`. It shows the collector no
     term, and raw formation accepts the candidate there.
   - The repair: `ScopedOp.term?` is the reading view of an operation's term, and
     `Formation.argumentAnnotations` reads it at the path segment `op`. No second program
     representation exists.
   - The outcome (tested): `Formation.checkInput` refuses the candidate at
     `program.1.argument.0.op.term.0.0.0.0.accTy.type.1` with `mapKey`. `admitProgram` refuses
     it with the same located refusal. The same stated type in a term position is refused at
     `program.1.argument.0.term.0.0.accTy.type.1`. At `list (map string nat)` both placements
     are admitted.
   - T3b's pin D9 (b) moved, with its reason in `Test/Program/FormationContract.lean`. The
     integer scan shares the collector. An `int` field in a record inside an operation's term
     is now refused by its path. A repeated field there is refused by raw formation too.
   - Row 212 keeps its other half: an operation's type arguments stay unread.
   - Placement: the existing claim `raw-formation`, at the boundary of
     `fold-typed-atomic-update`. Consumer: `admitProgram`'s `formed` certificate.
2. **`take` and `drop` take the list first.** The model wrote the count first. `get` takes the
   list first, and so does rc.112's `Array.take(self, n)`.
3. **`sameHandle` types by the head of each argument's raw type.** It admits two `refOf` or two
   `deferredOf`. A union of two handle types is refused. The evaluation follows F4: one kind
   byte compares the keys. So two fibers compare at the evaluator and are refused by the
   checker (Codex's advice).
4. **The term typer runs no formation check on a stated type.** The collector owns formation,
   and item 7.1 makes it reach every place a fold may stand.
5. **The fold's refusals are named.** `FoldTypingReason` has `notList`,
   `initialNotAccumulator` and `bodyNotAccumulator`. The diagnostic fold threads the type
   environment, so a refusal inside a body is found at the body's own environment.
6. **The reader's domain is a separate predicate**, `Term.unannotated`. I did not widen
   `Term.covers`.
7. **The fold's codec module is `src/Effect4/Codegen/ListFold.lean`.** The name avoids the
   generated `src/Effect4/Program/Fold.lean`. `Binders` holds the part that T5 shares.
8. **An authoring builder is added**, `Authoring.fold`, with `fold_scoped`. The brief does not
   list it. The design's F8 does, and the tree has no other scope law for a term form.
9. **The truth program changed after its first run.** Its first form folded
   `[[1, 2], [3]]`. tsgo refused the module: `Argument of type 'readonly (1 | 2)[]' is not
   assignable to parameter of type 'readonly 3[]'`. The cause is the list atoms' typing on the
   target and not the fold (item 9, row 3). The committed program builds its list from a bound
   number.
10. **The stated type prints as `fold<B>(…)`, as the design says.** TypeScript infers no type
    argument once one is written. So the prelude's `fold` gives its element type the default
    `any`. The compiler then checks the body of such a fold against `B` only (item 9, row 2).
11. **The top node of each claim is a structure.** Its proof cites one theorem for each rule,
    so the plan derives its status from theirs. No statement is made twice outside it.
12. **Each claim is stated as a proved theorem, not first as a planned goal.** The proof was in
    hand when the statement landed.
13. **Slice A came before the route check on the tree.** A model probe checked the route
    first. The tree's route check then passed: `todos (0)`, and the engine ran the fold.
14. **Two root lines beyond the brief's anchor.** `src/Effect4/Laws.lean` gains two lines after
    `import Effect4.Laws.Program.Authoring.Tuples`. `src/Effect4/Api.lean` gains one after
    `import Effect4.Program.Authoring.Tuples`.
15. **The proof-style baseline was recorded again.** Its diff is three counts, each of a
    generated proof: `ofVal_exact` and `ofVal_toVal` of `src/Effect4/Api/RefusalsDerived.lean`,
    and `rawTerm_toValTerm` of `src/Effect4/Store/Domain/Derived/Program.lean`.
16. **The compatibility policy names `Effect4.Program.Term.fold`.** No retained vector changed
    bytes (reading of `git status` on the golden directories).

## 8. Open obligations

1. **Re-pin `tools/Conform/Effect4/cases-policy.json`** (the first item of this receipt). I
   read every function of the policy's `Effect4.Program.Term` family that has a default site
   at the base. Each one answers a fold as it answers any constructor it does not name:
   `Provision.docsBody`, `tagTest?`, `tupleRequestReadable`, `FnName.totalName?`,
   `FnName.headName?`, `readLiteral`, `pairArgs?`, `Terms.names?` and `coverNode`. The two
   derived `DecidableEq` matchers gain sites. `codesOf` names the fold in its own arm. The audit
   may list four new hand matches: `unannotatedNode`, the function inside
   `Formation.termAnnotations` and the fixture's `weakenWrong` over `Term`, and
   `NativeAtom.sameHandleRule` over `Ty`. The policy's own note gives the step: seed with
   `--seed-policy`, diff, and keep the notes. Evidence: reading; the audit is not run.
2. **The faces of a fold inside an operation's term** are T5's (item 8.1 below).
3. **The two ingest walks do not read the fold.** `ts/eff/ingest/ck.ts` and
   `ts/eff/ingest/oxc.ts` are not changed. Evidence: reading.
4. **The release lane does not copy `harness/truth/folds.typecheck.ts`.** Only `check-truth`
   copies it. The release lane is not run.
5. **The target half of `handle-identity-laws`** stays an open part of R4: the correspondence
   of keys with host objects, in both directions.
6. **Hand counts in two documents were stale at the base.** `docs/GENERATED.md` and
   `ocaml/eff/README.md` say 48 golden programs. The base holds 66 `.bin` files and this
   branch 74. I did not edit them.
7. **`harness/truth/tuples.typecheck.ts` is compiled by no pinned lane.** The truth tsconfig
   names it, and `check-truth` copies only the record and fold controls. Evidence: reading.

### 8.1 What T5 needs from this slice

| Item | Exact name and place |
| --- | --- |
| The printer's entry point | `printTerm (n : Nat) : Term → TypeScript.Expr`, `src/Effect4/Codegen/PrintLeaf.lean`. `n` is the environment's length where the term stands |
| The level of an operation's term | The node's level plus one: the current value is variable `n` (`ScopedOp`'s convention) |
| The image T5 prints | `Binders.write n [0] (printTerm (n + 1) f)`, that is `(aN) => …`, `src/Effect4/Codegen/ListFold.lean`. The fold uses the same function at `[0, 1]` |
| Its exact reader and laws | `Binders.read n [0]`, `Binders.read_size` (core), `Binders.read_write`, `Binders.read_exact` (`src/Effect4/Laws/Codegen/ListFold.lean`) |
| A fold inside that term | It stands at `n + 1` and binds `n + 1` and `n + 2`. `printTerm (n + 1)` prints it with no further change. `pFoldInOp` of the fixture and of the engine tests is the control |
| Where the printer refuses today | `tableLayer.rowPrint`, the `rowCall` arm, `src/Effect4/Codegen/Templates.lean`: `sig.opAtLevel n 0 op = none` answers `PrintRefusal.binderTerm (sig.rowOf op).spelling`. `print_perform` (`src/Effect4/Codegen/Print.lean`) restates it |
| Why an operation has no form at level 0 | `NativeOp.atLevel` and `termFace` (`src/Effect4/Program/Native.lean`) spell a term only as a name's image (`FnName.decode?`, `src/Effect4/Program/FnName.lean`) |
| What the reader lacks | `readPerformFace`, `readRowCall` and `readRowMethod` (`src/Effect4/Codegen/Read.lean`) read a term row's last argument as a trailing name. No arm reads a function there. `ts/eff/read.ts` has the same gap in `readRowCall` and `readRowMethod` |
| The refusal by name that T5 lifts | `PrintRefusal.binderTerm`. Its pins: `Test/Codegen/PrintContract.lean`, `Test/Codegen/ReadContract.lean`, `Test/Program/FoldContract.lean` (`binderTerm "Ref.modify"`), and the print verdicts of `Test/Dogfood` (`Stage.lean`, `P3WorkerQueue.lean`, `P4RateLimiter.lean`, `P5LedgerService.lean`) |
| The read side that T5 lifts | A term that is no name's image has the empty type-argument spelling (`termFace_none`), so `rowHeadReadable` is false and `rowDom` holds no such row. T5 widens `requestReadable`, `rowDom` and `LawfulSpelling` |
| The refusal that stays | `ReadRefusal.annotation "fold accumulator"`: a stated type is printed and not read |
| The domain T5 must carry | An operation's term must be scoped at `n + 1`, covered and `unannotated`. `ScopedOp.term?` is the view to read it by |
| Already done for T5 | The raw annotation collector and the integer scan read an operation's term (item 7.1) |
| Not touched | `PrintRefusal.typeSpelling`, the faces of `Ref.make<A>` and `Deferred.make<A, E>`, and an operation's type arguments (row 212) |
| The prelude | The five function names stay one function each (finding F3 of `harness/truth/prelude.ts`) until T5 prints the term |

## 9. Proposed decisions rows (proposals only)

| # | Topic | Proposal |
| --- | --- | --- |
| 1 | The collector reads an operation's binder term | Amend row 212: only an operation's type arguments stay unread. Record that admission now refuses a malformed annotation, a repeated field and an `int` field inside a `Ref` row's term |
| 2 | The element type of a fold with a stated type on the target | Three options. (a) Keep `fold<B>(…)` with the element at `any`: Lean's checker types it. (b) Print the stated type on the initial value through a typed identity, so that both parameters are inferred. (c) Give the printer the element type and print both arguments. I recommend (a) now and the choice with T5, whose lambda meets the same question |
| 3 | A list of number literals on the target | `cons(1, nil())` is `ReadonlyArray<1>` under tsgo 7, where Lean types `list nat`. A list of two such lists with different literals does not type-check. Options: register a known difference, or change `cons`'s signature so that a literal widens. It is not the fold's, and no register line names it today |
| 4 | `take` and `drop` | Ratify the argument order `(list, count)` |
| 5 | `sameHandle` | Ratify typing by the raw head, with no union, and the evaluator's rule at every kind byte |
| 6 | R4's row | The two claims are proved. The open part of `handle-identity-laws` is its target half. The fold's faces inside an operation's term stay under the first open part |
| 7 | `docs/STATE.md` | Seat FOLD landed; T5 is next; the build ledger waits on the coordinator's promotion |
| 8 | Two stale hand counts | `docs/GENERATED.md` and `ocaml/eff/README.md` should take the golden count from the corpus table |

## 10. Truth programs added

One program: `pFold`, in `harness/truth/Truth.lean`. It folds a list that it builds from a
bound number, with a fold inside the fold. The inner fold walks the captured list from the
outer element, and its body reads the outer element. Lean answers `8`, and rc.112 answers `8`.
Its module `harness/truth/generated/pFold.ts` reads back on both readers.

The two ledger files are stale because the ledger holds one row for each truth program and
each build, and `pFold` has none. The release lane would also meet the new import header.

## 11. Bounded, host-only and unverified

- **Bounded:** every `#guard` of the fixture is one input. The six steps agree with their
  reference functions on the listed inputs only.
- **Host-only:** the agreement of `pFold` with rc.112; tsgo's acceptance of the printed fold
  and of the controls; the self-test rows of the three atoms.
- **Unverified:** conservativity, the case policy, the corpus lane, the target lane, the slow
  lane, the documents' references, the language rules and the semantics controls. Each is in
  the list of commands not run.
- **Not established by any check:** that the host's `===` on two handles agrees with the
  model's key comparison beyond the eight self-test rows.
