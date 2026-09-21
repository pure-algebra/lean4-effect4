# The foundations plan solidified, and the next two slices

Read at `10d5c009` plus the uncommitted foundations review (`docs/core/post-phase-c-synthesis.md`,
evidence in `docs/research/2026-09-20-foundation-review-evidence/`). This note checks the review
against the tree, goes two steps further where the checks led, makes the decisions the next
slices need, and dispatches the two slices we understand well enough to land with confidence.
Everything here was checked by reading or by a Lean probe in this session (§6); nothing is
carried over from an earlier receipt's numbers. Rulings that belong to the owner are named as
such and not made.

## 0. Verdict

- **The review's findings hold.** F1 (the generated predicates drop target, token, path and
  root), F2 (the accepted order is world → protocols → assembly; my look-ahead's "M2b first" is
  withdrawn), F4 (`actionAt_raceAll` is false as stated), F5 (memo uniqueness alone is not
  inductive; a supply bound alone permits duplicates), F7 (the write census runs without its
  source record and so over-approximates). I replicated its three probes and read every line it
  cites.
- **F4 is a class, not an instance.** `include h` binds a section hypothesis into *theorems*
  only; a `def` still gets a variable only when it mentions it (probe: `IncludeProbe.lean`).
  Every obligation is a `def`, every backing law a `theorem`, so every obligation declared
  inside an `include` section silently drops the included hypotheses. Seven do: the four in
  `Intro/Weight.lean` and three in `Simulation/Actions.lean` (`fork_rel`, `forkIn_rel`,
  `raceAll_rel` lack `MachineOk`, `BMeans` and `FMeans`: 15/18, 16/19 and 11/14 binders
  against their theorems). Of the Weight four, `raceAll` is false (the review's
  counterexample) and the other three are true without the premise (my probe, §6). The
  Phase C `omit` campaign was the *same* asymmetry from the other side: a theorem picks up a
  section's instance variables, a def does not.
- **The fix is structural, and small.** Make `ProofGraph.Obligation` a `Prop` and declare
  obligations as theorems. Obligation and law then obey one binder rule, the two defect
  classes cannot recur, and the seven mismatches repair themselves at the declaration, to be
  recorded as explicit amendments with their counterexamples. This is slice 1's core.
- **The abstraction the whole graph hangs on is the typed continuation stack.** Frames are
  typed arrows between exit types, a stack composes them, the current program is typed at the
  stack's input, and a resume is typed by a ghost token table that only grows. This is the
  textbook typing of a CK/CEK machine and it is what the evaluator's own `saveAnswerR`/`popR`
  pair does. Slice 2 puts that interface into the generator and the world; the semantics that
  fill it come from M3a.
- **Two slices are dispatched below** (§2, §3), a third is written and disjoint (§4). Confidence:
  slice 1 high, slice 2 high in shape, slice 3 high; M3a is the first slice with open design
  content (allocation certificates, source admission) and is not dispatched here.

## 1. Decisions made now, with their backing

| # | decision | backing | who |
| --- | --- | --- | --- |
| D1 | **Obligations are theorems.** `structure Obligation (p : Prop) : Prop`; every `def X … : Obligation …` becomes `theorem X … : Obligation …`. Placeholders (`ProofWanted`, Batteries) stay defs: `#proof_wanted` builds them from the closed proposition and they are never declared inside sections | `IncludeProbe.lean`; the 130 `omit`s of Phase C; the seven binder mismatches | coordinator (instrument) |
| D2 | **Explicit references.** `#obligation_proved X := term` elaborates `term` at exactly `X`'s proposition, checks its axioms, publishes `X.checked`. The gate accepts a validated `X.checked` when the search fails. Binder reorder or specialization is an adapter *term*, never a name match. Search and reference share the stale-marker rule | review F4, A1; `ProofRef.validate` already does the check | coordinator (instrument) |
| D3 | **Typed stack.** `FrameAccepts w tin tout : ScopeFrame → Prop` (seven arms), `StackAccepts w tin tout : List ScopeFrame → Prop` (nil at `t t`, cons composes through a middle type), `SavedOk w final x := ∃ tin, TypedProg w tin x.current ∧ StackAccepts w tin final x.stack ∧ InterruptProvenance x` | `popR` delivers into the top frame and the frame's `next ex` is the new `current`; `saveAnswerR` pushes `.answer next` (EvaluateR.lean:70–100, 137–146); typed abstract machines | coordinator; rows 48/86 content |
| D4 | **Resume typing by a ghost token table.** `World.Θ : FiberId → Nat → Option EffTy`, extended when a fiber parks (`nextToken` is fresh and increments, so Θ only grows: a table extension like Γ/Π/Ρ). `ResumeOk w target token code := ∀ ty, Θ target token = some ty → TypedProg w ty code`. Active delivery: `parked = withGuard token` ⇒ `Θ id token = some tin` is a clause of the machine relation; stale: the command is ignored (`Fibers.lean:1834–1847`), which is `ParkHandshake`'s inert disjunct | the resume arm; `Pending.token`; `Parked.withGuard`; F3's warning that a conditional lookup is monotone only with support, which the machine clause supplies | coordinator; row 86 |
| D5 | **A capture is typed whole.** `CaptureOk w c` receives the `Capture` (env, ctx, path, root) and is defined at M3a through the checker's environment at `(root, path)`; the generator hands the owner value to the predicate | F1's erasure probe; `Capture` fields | coordinator; row 86 |
| D6 | **World validity is separate from world order** and is slice 3: domains agree with the machine (Γ with fiber ids, Ρ with `refs.length`, Π with `cells.length`, Θ with parked tokens), stored cells fit, `ofRefGet` completions name live typed cells. Allocation exclusion is a corollary of domain agreement. Transport of `ValueOk`/`CompletionOk` is under `World.le` *and* unchanged external allocation, which the empty-host profile gives | World.lean's own doc comment; F3; `Val.hasTy`'s `allocated` argument | coordinator; row 87 |
| D7 | **`Expect.root` resolves to `Γ Api.root`**; no new world field. `Expect.hook` is M5's | `loadR` makes the root fiber with id `Api.root` | coordinator |
| D8 | **The decision domain is `Guard.Reachable`** (decision prefixes from `Api.load`) with typed host answers (`AnswersOk`: each supplied `Completion` fits its external row). No `LegalDecision` beyond that: a malformed decision is ignored by the machine and the invariant must survive it | `Guard/Core.lean:31`; `RunDecision`; the resume arm | recommendation for M3a; owner sees it at the statement |
| D9 | **Order**: slice 1 → slice 2 ∥ slice 3 → M3a (protocols, source admission, `TypedProg`) → M3b/M4 (assembly, `popR`/`saveAnswer` first) → M5 → M6 (with F5/F6 when the first coupled update needs them) → M7. Residue proofs (site membership, trace agreement, holder factorization) and the memo slice proceed beside | review §6; F2 | coordinator |
| D10 | **Memo**: `MemoIdsOk s := (s.memo.map (·.id)).Nodup ∧ ∀ m ∈ s.memo, m.id.index < s.nextName`, the shape `ScopeKeysFresh` already uses; its own slice with regeneration and OCaml validation, after the residue | `memoFork` mints `⟨st.nextName⟩` (Stores.lean); `MemoProbe.lean` | coordinator; row 78 |
| D11 | **Register**: rows 86–88 as the review wrote them. Rows 20, 48, 51, 52 and 79 carry the owner's 2026-09-20 rulings only in chat; the text to write is in §7 and waits for one word from the owner | the project rule that a ruling exists when written | owner |

## 2. Slice 1: obligations are theorems; the statement audit; explicit references

**Goal in one sentence:** an obligation and its law obey the same binder rule, every frozen
statement is compared with its backing theorem, the seven mismatches are amended with their
counterexamples on record, and the ledger can take an explicit checked reference.

**Files.**
- `tools/ProofGraph/Ledger.lean`: `Obligation` becomes `Prop`. `addWanted` unchanged.
- `src/Effect4/Laws/Auto/Obligations.lean`: `#obligation_proved X := term` (elaborate `term`
  against `X`'s proposition; `collectAxioms` ⊆ `[propext, Quot.sound]`; `addTheorem X.checked`);
  the gate accepts a validated `X.checked` on search failure; the stale-marker and
  repeat-validation paths are shared by both routes.
- Every file with an obligation (40 files, 245 declarations: 97 one-line headers, 148
  multi-line): `def` → `theorem` by script, no other edit. Where the theorem form now includes
  an unused section variable in a file that does not silence the linter, add the same
  `omit … in` its neighbouring law carries.
- `src/Effect4/Laws/Program/Intro/Weight.lean`: the four `M1Origin.actionAt_*` obligations
  now bind `h` by construction. Record the amendment: `actionAt_raceAll` was false without it;
  `actionAt_fork`, `actionAt_forkIn`, `actionAt_not_forkScoped` were true without it (probe).
- `src/Effect4/Laws/Program/Simulation/Actions.lean`: `M1Origin.fork_rel`, `forkIn_rel`,
  `raceAll_rel` now bind `hok hm hf`. Attempt a counterexample to the premise-free form
  (two unrelated machines); if it is not finite-checkable in an hour, amend on the binder
  mismatch alone and say so in the receipt.
- `test/Counterexamples/Machine/Semantics/ActionAtRaceAllPremise.lean` (new): the review's
  `universal_missing_premise_false` as a battery theorem; a row in
  `test/Counterexamples/REGISTER.md` under a new `E4-SCHED-CE-` id (next free number).
- `test/Audit/Obligations.lean`: four controls: a direct reference closes what the search
  cannot; a direct reference with a live marker is stale; a term at the wrong proposition is
  refused; an obligation declared under `include h` binds `h` (binder count).
- `test/Audit/ProofGraph.lean`: one control that an `Obligation` theorem validates as evidence.

**Statements first.** Before the script runs, `#check` every obligation whose namesake theorem
exists and print binder counts side by side (the `IncludeAudit.lean` probe generalised to the
tree). Any pair with a mismatch beyond the seven is a finding for the receipt before it is a
fix.

**Then the explicit references.** For each open obligation whose backing theorem is in the
tree (the receipt's thirty-one, less the seven amended), write `#obligation_proved X := thm` or
an adapter term, remove the marker in the same edit, rebuild the module. No forecast: the
receipt reports what closed and what did not, by name.

**Deletions.** None. The `omit`s stay (they now do the same work on both sides).

**Build and check.** `lake build ProofGraph Effect4.Laws.Auto.Obligations Test.Audit.ProofGraph
Test.Audit.ProofGraphSearch Test.Audit.Obligations`, then each touched law module, then
`make build` and `make check` (every gate in the tree re-runs).

**Finish.** Build and check green; the binder audit printed in the receipt with zero
mismatches; the seven amendments listed old/new with their evidence; the counterexample row
registered; the explicit references listed by name. Stop on: any obligation whose theorem
form fails to elaborate for a reason other than an unused section variable; any obligation
whose namesake has a different proposition and no honest adapter.

## 3. Slice 2: owner-level rows and the typed-stack interface

**Goal in one sentence:** the generated skeleton can state the correlations its consumers
need, the world carries the token table, and the stack interface is declared, parameterised
in `TypedProg` until M3a fills it.

**Files.**
- `src/Effect4/Laws/Program/Typed/Vocabulary.lean`: `Source.owner (pred : String)`. On a
  structure name the clause is `P.pred w e x`; on a constructor name it is the arm
  `| .c a₁ … aₙ => P.pred w e a₁ … aₙ`. Every position and edge beneath is covered and
  accounted; a second row beneath an owner row is a duplicate-coverage error.
- `src/Effect4/Laws/Program/Typed/TypedStateDecl.lean`: the two emission shapes; `addPred`
  with the owner's or constructor's field types; the accounting pass extended.
- `src/Effect4/Laws/Program/Typed/Sources.lean`: `RSaved` → `.owner "SavedOk"` (replacing the
  `current`, `stack`, `interruptedCause` rows and the six `ScopeFrame` rows beneath the stack);
  `Task.resume` and `Cmd.resume` → `.owner "ResumeOk"` (replacing the two `.answer` rows);
  `Capture` → `.owner "CaptureOk"` (replacing `env` and `ctx`). `RunMachine.races` stays a
  whole-field custom row; `ServiceOk` stays on `RunFiber.context` and `Env.Service.value`.
- `src/Effect4/Laws/Program/Typed/State.lean`: `saved_from_clauses` and its obligation go
  (the saved frame is one clause now); the `#typed_state` count pin is refreshed from output.
- `src/Effect4/Laws/Program/Typed/World.lean`: `Θ : FiberId → Nat → Option EffTy` on `World`,
  `World.le` extended by `TableExtends` on Θ (curried through the fiber), `World.addToken`,
  `park_extension` as an obligation with a marker (proof in slice 3 or M3b), the existing
  extension theorems' proofs updated for the new field.
- `src/Effect4/Laws/Program/Typed/Contracts.lean` (new, statements only): `section` over
  `(TypedProg : World → EffTy → RProgram → Prop)`; `FrameAccepts`, `StackAccepts`, `SavedOk`,
  `ResumeOk`, `InterruptProvenance` (interruption recorded by the scheduler, distinct from a
  typed failure), and the shape of `CaptureOk` with its environment relation as a parameter.
  A `#guard`-free positive example: a two-frame stack whose middle type differs from its ends.
- `src/Effect4/Laws/Program/Typed/Frames.lean`, `test/Audit/FrameRules.lean`,
  `test/Audit/PositionCensus.lean`, `test/Audit/TypedStateDecl.lean`,
  `test/Program/TypedStateRulesRed.lean`: regenerate, re-pin from fresh output, and add the
  owner-row controls: omitted owner (a structure named by no row and no field rows), duplicate
  coverage, constructor form, and the three erasure probes turned around: a `Preds` instance
  whose `ResumeOk` reads the token and a `TaskOk` that differs between two tokens.

**Statements first.** Write `Contracts.lean` and the Sources rows before touching the
generator; elaborate `Contracts.lean` alone. Then the generator; then the pins.

**Deletions.** `saved_from_clauses` (theorem and obligation); the eight replaced source rows.

**Build and check.** `lake build Effect4.Laws.Program.Typed.Contracts`, then
`make check-typed-state`, then `lake build Effect4.Laws.Program.Typed.World
Effect4.Laws.Program.Typed.State Effect4.Laws.Program.Typed.Frames Test.Program.TypedStateRulesRed
Test.Audit.PositionCensus`, then `make build` (World's dependants) and `make check`.

**Finish.** The kernel print of `Preds` shows `SavedOk : W → Expect → RSaved → Prop`,
`ResumeOk : W → Expect → FiberId → Nat → RProgram → Prop`, `CaptureOk : W → Expect → Capture →
Prop`; the position gate still reports every position sourced with the same two refusals; the
frame counts are re-pinned; the four new controls pass; `Contracts.lean` elaborates with its
positive example. Stop on: a position the owner row cannot cover without a field the census
does not visit; a frame rule the generator cannot state for an owner clause.

## 4. Slice 3, ready and disjoint: world validity and transport

Owns `Typed/World.lean` and a new `Typed/Validity.lean`. `WorldValid w m` (D6): domain
agreement for Γ/Π/Ρ/Θ, every stored cell fits its declaration, every `ofRefGet` names a live
typed cell, every parked guard has its token in Θ. Transport lemmas: `ValueOk`, `CompletionOk`,
`HeapTypedAt`, `PromiseTypedAt` under `w.le w'` with `w.state.externals.allocated =
w'.state.externals.allocated`. Allocation exclusion as a corollary. Witnesses: one valid world
of a loaded program; negatives for a ghost key at the next index, a changed spelling, a wrong
nested handle type, a dangling `ofRefGet`. It touches no file slice 2 touches except
`World.lean`'s field list, so it runs in a worktree beside slice 2 and merges after.

## 5. Tooling to build, in the order it pays

1. **Obligations as theorems** (slice 1): removes two defect classes; cost one type and a script.
2. **`#obligation_proved`** (slice 1): explicit evidence without shaping rules for the search.
3. **Owner-level rows** (slice 2): the generator can state relations, not only leaves.
4. **A binder audit command** (slice 1, from the probe): `#obligation_audit NS` prints every
   obligation under `NS` beside its namesake theorem's binders; a mismatch is an error. Cheap,
   and it is the control that would have caught F4 at Phase B.
5. **Per-written-set frames and the coverage join** (F6/F5): only when M6's first coupled
   update shows the per-field rules are the bottleneck. Not before.
6. **`#answer_gate`** (M3a): the constructor-to-clause inventory for the two protocols, derived
   from the constructors with their dependent answer types.

## 6. Checks run in this session

| probe | result |
| --- | --- |
| `Effect4RaceObligationProbe.lean` (review's) | replicates: `[propext]`, the frozen statement refuted at `getId` |
| `Effect4FoundationProbe.lean` (review's) | replicates: `Preds` twelve fields, not a class; resume and capture erasure `[propext]`; `conditional_not_monotone` no axioms |
| `Effect4MemoProbe.lean` (review's) | replicates; `memoFork` mints `⟨st.nextName⟩` and bumps it (read) |
| `IncludeProbe.lean` (new) | `include h`: `probeDef : Nat` has no `h`; `probeThm : ∀ {n}, n = n → True` has it |
| `IncludeAudit.lean` (new) | binder counts obligation/theorem: `fork_rel` 15/18, `forkIn_rel` 16/19, `raceAll_rel` 11/14, `actionAt_fork` 6/8, `actionAt_forkIn` 7/9, `actionAt_not_forkScoped` 6/8, `actionAt_raceAll` 6/7 |
| `AdjacentProbe.lean` (new) | `actionAt_fork`, `actionAt_forkIn` true without `h` (residual goals reflexive); `actionAt_not_forkScoped` closes |
| `PredsProbe.lean`, `PredsProbe2.lean` (new) | the generated `RunMachineOk`, `RunFiberOk`, `StoresOk`, `DispatcherOk`, `BucketOk`, `TaskOk`, `CmdOk`, `CaptureOk`, `ScopeStateOk`, `FinNameOk`, `CompletionOk`, `ValueOk` printed; `RunFiberOk` types the frame at `Expect.fiber x.id` and everything else at the inherited `e` |
| other `include` sections | Pending's four obligations sit outside their section and bind `_hf` explicitly; Drive's ten sit outside; only Weight and Actions are affected |

The new probes are retained in `docs/research/2026-09-20-foundations-plan-evidence/`.

## 7. For the owner

- **One word writes five rulings.** Rows 20 (the fork-site path: yes, on `Origin.forked`),
  48/51/52 (M3 content, one stroke), 79 (R79.1–R79.5 adopted) as given in session on
  2026-09-20. If confirmed, the status cells get "ruled 2026-09-20 (owner)" with the text of
  the packet's §2.7, and row 79's status names the holder factorization and the trace
  agreement as the open proofs.
- **Row 84** (the first transaction fragment) and **the clock** (review F4 of the landing)
  remain unanswered; neither blocks slices 1–3.
- **Parallel seats.** Slice 3 is disjoint from slice 2 except for `World.lean`'s field list.
  Two seats need two worktrees; one seat does 1, then 2, then 3.
