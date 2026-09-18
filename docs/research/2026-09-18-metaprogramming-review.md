# The metaprogramming book against this proof graph (2026-09-18)

Read: the overview, expressions, `MetaM`, syntax, elaboration, tactics and the cheat sheet of
*Metaprogramming in Lean 4* (leanprover-community, `main`). Not read: macros beyond the overview,
DSLs, the extras on options, pretty printing and universes. Every API named below was checked to
exist in the pinned toolchain (v4.33.1) and Batteries (probe `Q4_api.lean`; `theorem_wanted` is
axiom-free, `#print axioms` on its placeholder is empty). This note is the re-plan of what
remains of row 41 after step 0 landed (`2026-09-18-position-census-design.md` §3a), written as
"what the API does that the current code does by hand".

## 0. The three things the book changes

1. **Generate into the environment, not into files.** `fold_of` already does this. A command
   elaborator has the environment, quotations and IO (`CommandElabM`); a generated declaration
   is a syntax quotation elaborated in place with `elabCommand`, and hygiene handles the binders.
   The skeleton emitter I wrote builds *strings* and writes a file that then needs a drift check,
   a separate driver, and a `pp.fullNames` printer with line-wrapping workarounds. All of that
   disappears: `typed_state_skeleton RState RCmd` runs where `State.lean` now sits and the `Ok`
   structures exist from that line on.
2. **State the obligations as declarations, match them by definitional equality.** Batteries'
   `theorem_wanted name binders : T` elaborates `T` and adds a private placeholder with no axiom.
   The ledger of step-preservation obligations becomes a generated list of `theorem_wanted`s; a
   witness is a theorem whose type is `isDefEq` to the wanted's, checked by opening both with
   `forallMetaTelescope` at a raised metavariable depth. No name-matching, no head checks, no TSV.
3. **Attribute obligations to matcher arms, and prove the frame automatically.**
   `matchMatcherApp?` recovers the alternatives of a `match` in a definition's body, so a write
   site is attributed to the constructor arm that contains it: the row is (definition, arm,
   owner, written fields). For each (owner, written-field set) one **frame lemma** is generated
   — "`Ok` of `x`, plus the clauses of the written fields, gives `Ok` of `{ x with … }`" — and
   proved by the generated rule set: the structure's constructor (`repeat constructor`), the
   accessors as forward rules, projection reduction. The hand proofs that remain are exactly the
   written fields' clauses, which are the protocol.

## 1. Chapter by chapter: what the code does by hand that the API does

| chapter | API | where the tree does it by hand today | the change |
| --- | --- | --- | --- |
| syntax | `declare_syntax_cat`, typed `TSyntax`, `` `(term| $e) `` antiquotations, `mkIdent` | `Typed/Sources.lean` rows carry the expected type as a **string** (`"x.id"`) interpolated into emitted text | a `typed_position` command with a `term` antiquote: `typed_position RunFiber.exit := exit (fiber x.id)`; the term is elaborated against `Expect` at the row, not pasted later; rows are stored in an environment extension (`registerSimplePersistentEnvExtension`) the gate and the skeleton read |
| elaboration | `elabCommand`, `runTermElabM`, `Term.elabTermEnsuringType`, `withRef` | `TypedStateGen.lean` writes Lean source with `IO.FS.writeFile`; `Test/Audit/TypedStateEmit.lean` regenerates; `check-gen`-style drift is owed | quotation-built `structure`/`def`/`attribute` commands elaborated in place; errors are reported at the row's syntax through `withRef` |
| MetaM | `forallTelescope`, `forallTelescopeReducing`, `whnf` with transparency, `instantiateMVars` | `instArgs` hand-instantiates constructor binders; `whnf` at default transparency plus a hand `stops` list | `forallTelescopeReducing` on the constructor type applied to the parameters; the stop list stays (it is a *design* choice about carriers, not a workaround) |
| MetaM | `mkAppM`, `mkProjection`, `getStructureFieldsFlattened` | clause text `P.program w e x.current` assembled from strings | build the clause as an `Expr` with `mkAppM` when a statement must be checked, and as syntax when it must be declared; never as text |
| MetaM | `isDefEq`, `forallMetaTelescope`, metavariable depth | the design's ledger join was a head check on the witness's conclusion | statement matching: open the wanted and the witness with `forallMetaTelescope`, `isDefEq` under `withNewMCtxDepth` so nothing outside is assigned |
| MetaM | `matchMatcherApp?`, `getMatcherInfo?`, `Meta.transform`, `forEachExpr` | `writeSites` is a raw `Expr` recursion that cannot say which `match` arm holds a site | per-arm attribution; `forEachExpr` for the walk under binders |
| tactics | `TacticM`, `liftMetaTactic`, `MVarId.constructor`, `evalTactic (← `(tactic| …))`, `isExprDefEq`, `closeMainGoal` | none yet | not a bespoke tactic: the book's own advice is to reach for search when the logic is uniform; the frame proofs are an `aesop` rule set, the rest is hand |
| cheat sheet | the monad stack: `CoreM ⊂ MetaM ⊂ TermElabM`, `CommandElabM` beside them | `evalRows` runs the table through `Term.evalTerm` behind `implemented_by` | with rows in an environment extension there is nothing to evaluate |

Two things the book confirms about what is already right: the census walks types with `whnf`
and `forallTelescope` (the recommended pair), and the invariant as *structures* is what makes
`constructor`/accessor search complete on the frame.

## 2. The re-plan, R1–R8

- **R1 The skeleton in place.** Replace `TypedStateGen`'s string emission by quotations:
  `` `(structure $(mkIdent okName) (P : Preds W) (w : W) (e : Expect) (x : $ownerTy) : Prop where $fields*) ``
  and `elabCommand`. `Typed/State.lean` becomes the command call. Delete `TypedStateEmit.lean`.
  The `Expect` inductive and `Preds` are declared the same way. Source rows move to a
  `typed_position` command in `Sources.lean` writing an environment extension; the gate reads it.
- **R2 Layer 1, by hand.** The `Preds` instance is the typing content and stays hand-written:
  `W := ⟨Γ, Π, s⟩` with `WorldLe`; `program := Typed (Ψ_S.sum Ψ_F)` from `Laws/Effects/Protocol`;
  `OpOk`/`AnswerOk` by recursion on `FiberOp`; `StackOk` (the typed context), `PendingOk`,
  `RaceOk`, `ServiceOk` (the requirement row against the context, which is what discharges
  `missingScope`), `ResumeOk`, `CaptureOk`, `InterruptOnly`; the columns `HeapNat` (exists) and
  the promise table. This is where the three rulings land as definitions.
- **R3 The ledger as `theorem_wanted`.** `typed_state_obligations driveStep evaluateR popR
  fireObserver exitFiber stepDecisionState` runs the write census with arm attribution and, per
  (definition, arm, owner, written typed fields), elaborates `theorem_wanted keeps_<def>_<arm> :
  <template>` unless a witness with a defeq type exists. The template is built from the
  definition's type by `forallMetaTelescope`: owner-typed arguments get `Ok` hypotheses,
  program arguments `P.program`, answer functions `P.continuation`; owner-typed result
  components get `Ok` at some `w'` with `WorldLe w w'`. The command prints wanted/proved counts.
  This replaces `generated/typed-state-obligations.tsv` and the witness-join module.
- **R4 Frame lemmas, generated and proved.** From the same census, one
  `theorem frame_<Owner>_<fields>` per (owner, written-field set), proved by
  `aesop (rule_sets := [TypedState])`; a failure is reported by the command as a real
  obligation. Registered in a dedicated rule set `TypedState` (`declare_aesop_rule_sets`), not
  the default set, so the seats' announce-rule-changes rule is respected.
- **R5 Witnesses by hand** are then: apply the arm's frame lemma; the goals left are the
  clauses of the fields the arm writes — `AnswerOk` for an answer produced, `P.program` for
  installed code, `StackOk` after a push or a pop, the column after a store step. That is the
  protocol, arm by arm, and nothing else.
- **R6 The read census on matches.** With `matchMatcherApp?` the `journal` check becomes real:
  a `RunEvent` payload read anywhere in the step's closure fails the gate.
- **R7 Statement checks for S3** by `isDefEq` against computed templates, not copied text (the
  tree retired hand-copied statement pins on 2026-09-13 for being copies; a computed one is not).
- **R8 What stays.** `Positions.lean`'s walk; the gate; the source vocabulary; layer 0.

Order: R1 → R2 → R4 → R3 → S1 (`denoteR_typed`, by `Typed.bind`/`Typed.inl` and the combinator
lemmas) → R5 row by row → S3 with R7.

## 3. The debt register, as the census and the tree name it

What "refused" means: a position or edge whose typing source is named as debt, and every
refusal tag or counterexample row in the tree that touches a typed position. Read tonight:

| item | where | what it means for the invariant |
| --- | --- | --- |
| `ScopeState.closed.exit` (edge row `refused`) | `Sources.lean`; composed graph §9 | the release's exit parameter: the checker types it at the acquire's exit, rc.112 at `Exit<unknown, unknown>`; a checker defect, DI owed |
| `Stores.externals` (edge row `refused`) | `RSTEP-FB-HOST`, DI-57 | external rows park forever on the reference; the table-aware slice's typed-tape hypothesis, same `AnswerOk` clause |
| `STORES-FB-COMPLETION` | `StoresLaws.lean:19` | completions are outside `Stores.WF`: the promise table `Π` is the column; `E4-STORES-CE-003` says it must also keep an `ofRefGet` cell live |
| `SCHED-FB-REFUSE` | `Sched.lean` header; `Compile.lean:979-1016` | `FiberOp.refuse` is the compiler's wrong-shape defect for action arguments; unreachable under typing is an S1 obligation on the action arms |
| `SCHED-FB-FRONTIER`, `RSTEP-FB-FRONTIER`, `RDEN-FB-UNSUPPORTED` | `DenoteR.lean:603` | a `.program`-kind row denotes `pending .unsupported`: no exit, the invariant holds, and it is a feature gap to list per row, not a typing gap |
| `RSTATE-FB-STORE-CODE` | `InterpR.lean:133` | `denoteStored` decodes three shapes; `CompletionShaped` already carries it |
| `RSTATE-FB-EVALUATOR-FIELD` | `Sources.lean` hook rows `none` | 7 of 43 hooks the reference never calls; the read census on matches (R6) makes that a checked fact |
| `TYPED-FB-INT`, `E4-TYPED-CE-002` | `Program/Typed.lean` | `.int` has no inhabitant; no typed value reaches it |
| `E4-PROGRESS-CE-002` | `Progress.lean` | `HeapNat` is an invariant of typed operations only; the world is over typed runs |
| `missingScope` / `missingService` | `Fibers.lean:1436`, `:1446`, `InterpR.lean:395` | a `forkScoped`/`ambientScope`/`service` with no provider dies; `ServiceOk` connects the requirement row to the context (R2) |
| `Stuck.unknownFiber/unknownScope/unknownRace` | `Fibers.lean:389-392` | halts; a progress corollary: handles come from forks and makes, so they exist |
| `walkR` `Cause.die badName` | `InterpR.lean:245-256` | the generator walk on a malformed block; S1's hook body for `gen` |
| `badShapeExit` sites: 76 + 11 + 1 | `DenoteR`, `InterpR`, `EvaluateR` | 59 are `evalTerm`/decoder `none` arms; the decoders without a totality lemma are `Val.scope?`, `Val.fiber?`, `Val.context?`, `Val.memoMap?`, `reasonsOfVal`, `sleepMillisOf`, `awaitCellOf`, `exitOfVal`, `memoHit?` (nine); `evalTerm_isSome`, `causeOf_isSome_of_causeTy`, `syncOpOf_isSome` exist |
| `interp.asyncFiberError` | `Fibers.lean:2186` | an external answer for a missing fiber; table-aware |

Nothing else in the `-FB-`/`-CE-` registers names a typed position.
