# Verification of seat ALGEBRA (formal pass, 2026-10-01)

Status: adversarial verifier's note, 2026-10-01. Tree: `refactor/phase1-phase3` at `ea5b28b5`
(docs only after `efd67af1`; build products checked newer than every source the probes import).
Nothing tracked was edited; no `lake build`, `make`, generator, `git add` or `git commit`. The
seat's files were not touched. My probes are `verify-*.lean` beside this note, their logs in
`verify-logs/`, and `verify-rerun.sh` reruns everything through the one-compiler lock.

Evidence words: **proved** (a kernel theorem I ran, axioms printed at `[propext, Quot.sound]`
or less), **tested** (a finite check I ran), **reading** (code or notes read, not run),
**assumed**. Literature is marked read (with the note that records the reading), by name, or
assumed; I opened no paper.

## The one thing

**ALG-01 is right, and stronger than the seat proved. But its example command and its amendment
are wrong in two places that matter for dispatch.**

- **Stronger.** The declared M6 obligation `M6Ledger.step_loop` (`Typed/Assembly.lean:170-171`)
  is false (proved, `verify-StepLoop.lean`, `step_loop_refuted`). The witness: load `Ref.make(5)`
  and put the seat's frame `.answer badNext` under the root. That machine is a `TypedState` at
  the initial world (`typed_mBad`), because no cell is declared there, so no success fits the
  frame's input type and its clause holds vacuously. One `loop` allocates cell 0, after which no
  world types the machine. With a frame typed into `unit`, the same step keeps the typed state
  (`step_loop_good`, the green control). The seat's Kripke judgment refuses the bad frame
  (`bad_not_kripke_initial`).
- **Wrong command.** The breaking step is `loop`, not `evaluate`. `evaluate` only marks the fiber
  running and queues `loop` (`Machine/Fibers.lean:1849-1856`); the store operation runs in `loop`
  (`EvaluateR.lean:297-304`). On the same bad machine, `evaluate` keeps the typed state at the same
  world (proved, `evaluate_keeps`).
- **Incomplete amendment.** "Re-instantiate `popR_typed` at the current world" and "close the
  hook protocols, or wrap them as in P2" do not re-establish the invariant.
  - `popR_typed`'s conclusion is the one-world `SavedOk`.
  - After an iterator resume, the walk pushes a frame whose protocol `HookLaws` supplies at one
    world (`Stack.lean:253-274`; the loop arm `:276-289`). With wrapped premises its intermediate
    type can differ between later worlds. Proved, `verify-WrapWalk.lean`: `HookLaws` holds, the
    one-world walk types the output, and the output has no Kripke typing (`output_not_kripke`).
  - What it takes:
    - close `IteratorProtocol`, `LoopProtocol` and the async clause in their own definitions;
    - restate `HookLaws` and the walk over Kripke stacks;
    - give `saveAnswerR_typed` and `deliver_active` Kripke premises.

  This changes statements only, no runtime code. It belongs under decisions row 87
  (coordinator, open: "which hypotheses make concrete typing monotone"). It edits the same frame
  contract as row 117's pending amendment, and enters through H1's statement restatement
  (addendum 6: "Statements only"), before any M6 proof.

## Verdicts

| id | verdict | evidence |
| --- | --- | --- |
| ALG-01 | confirmed | Reran P2: log byte-identical. **Proved** at the step level, beyond the seat's reading: `step_loop_refuted` refutes `M6Ledger.step_loop` at a concrete typed state (above). Controls, **proved**: `step_loop_good` (green), `bad_not_kripke_initial`, `evaluate_keeps`. Severity is right: a declared obligation is false. The claim's example is wrong (`evaluate` allocates nothing; the command is `loop`), and the amendment is incomplete (missed items 2 and 3). In-tree evidence of the drift, **reading**: `guard_inv`'s docstring says a guard's typing is "exactly" `FrameAccepts.resume` (`Residual.lean:231-232`), but the guard arm quantifies over later worlds (`:201-207`) and the frame arm does not (`Contracts.lean:33-36`). |
| ALG-02 | confirmed | Reran P2: `typedProg_mono` and six helpers at `[propext, Quot.sound]`; `storePre_mono` and `fiberPre_mono` case on all 31 and 40 rows (Lean checks exhaustiveness). Only the guard body uses the induction hypothesis (P2:156-160, reading). The statement matches `M3bWorld.typedProg_mono` (`Residual.lean:424-425`) up to binder order (reading), so `#obligation_proved` needs a wrapper in the ledger's order. |
| ALG-03 | confirmed | **Reading.** No `denoteR_typed` and no `Fits`-level term lemma exists under `src/` or `Test/` (grep). S1 is named in the typed-state plan (`2026-09-18-typed-state-plan.md:98`) and the slices 3-6 brief (`:468`). Only `evalTerm_hasTy` at the coarse `Val.hasTy` exists (`Laws/Program/Typed.lean:971`). "Fundamental property" is the right name: the fundamental lemma of logical relations, that every syntactically typed term lies in the semantic relation (by name). The types seat's TY-07 found the term-level half independently. |
| ALG-04 | partly | The fact is **proved** (P6 reran). **Literature: a loose analogy.** Hazel's Bind holds for neutral contexts (de Vilhena Fig. 2.4, read via papers review §1.3 and G8): the side condition is on the context, which must hold no handler frame. Here the context `bind k` is always neutral, and the failure comes from the program. `unguard` is a non-local exit whose continuation the machine drops (`EvaluateR.lean:190`, `:100`), and in the bracket encoding `bind` after a guard is the guard's taken branch. The matching principle is Timany and Birkedal's "non-local control flow breaks the bind rule" (as de Vilhena §2.4 cites it; read via papers review G8). **Amendment, option (a) refuted** (proved, `bind_not_typed`): `guardR .onFailure (pure (success (nat 1)))` has no closing marker outside its guard body and is typed at `nat`. A continuation typed into `unit` on every exit still yields an untyped `bind`, because the guard's skipped exit bypasses the continuation (`popR` skip, `EvaluateR.lean:79-96`). **Option (b) works** (proved, `seq_typed` with `close_typed`): the compatibility lemma for `(guardR .onSuccess a).bind (seqR k)`, which is the shape `denoteR` sequences with. |
| ALG-05 | partly | `Typed.inr` and `Typed.refine` **proved** (P6 reran, no axioms). The tree's `Protocol.lean` indeed has only `inl` (reading). But both already exist as research proofs: `inr_iff` (`2026-09-30-model-probe/pedigree/Conservativity.lean:92`) and `typed_along`, which is refinement along any signature map (`:266`). `c4_iff` (`VerifyConservativity.lean:84`) composes C4's generic half. The model-probe synthesis records that half as proved and C4 as owed for `TypedProg` (`synthesis.md:203`). The generic `Typed` has no consumer on the M5-M7 path, since `TypedProg` is its own inductive. Promote the pedigree lemmas rather than add new ones; the owed work is C4 for `TypedProg`. |
| ALG-06 | confirmed | Reran P1. `sum_is_coproduct` is the coproduct in the literature's sense. Both injections are monad morphisms (`IsMonadMorphism` preserves `pure` and `bind`, `Algebra/Universal.lean:27-34`), and the copairing exists and is unique among monad morphisms into a lawful monad (**proved**). The package has every ingredient but not the composed statement (`Algebra/Sum.lean:36-186`, reading). Overlaps the seat did not cite: `interpret_along` (pedigree `Conservativity.lean`, with `LawfulMonad`) is the restriction law along any signature map, and P1's restriction needs no monad law. DB-01's sum-of-theories caveat is already an item of the in-flight refresh brief (`2026-10-01-design-basis-refresh-brief.md:53-54`), under row 111's ruling that C1-C8 go into DB-01. `sum_not_tensor` is constructor disjointness: right, but carries no content beyond freeness. |
| ALG-07 | confirmed | Reran P3. **Reading:** no append law for `replayEval` exists in the tree (grep over `Laws/`, `Machine/`). `behaviour_unique` is the uniqueness half of finality for Mealy machines in the finite-word presentation (Rutten, Jacobs ch. 2; by name). |
| ALG-08 | partly | Reran P4: `conv_fixpoint`, `conv_least`, `conv_unique` and the red control **proved**. These are Elgot's fixpoint law, Kleene leastness and single-valuedness for the limit; `Iter.lean`'s own header says "Elgot iteration cut at a budget". **Severity overstated**: by the seat's own definitions this is tidiness. The laws hold, are cheap, and no M5-M7 theorem uses them. Their consumer now is DB-04's wording in the in-flight design-basis refresh, whose DB-04 cites an "Elgot … pedigree" (`2026-10-01-design-basis-refresh-brief.md:57-58`). Home: `Conv` uses `runP` over `StoreSig`, so the lemmas go beside `DenoteB.lean`; `Iter.lean` is generic over the signature. |
| ALG-09 | partly | Reran P4: `put_get`, `get_get`, `put_put` on live cells and `put_get_dead_fails` **proved**; "comodel" is the right notion (Plotkin and Power 2008, by name). **Severity overstated**: the seat itself says the laws are owed only when a form declares a state equation, so this is tidiness. Step-level put-get already exists (`refStep_get_after_set`, `Machine/Stores.lean:968`), and so does arena-level non-interference of distinct cells (`peek_poke_other`, `Laws/Machine/Arena.lean:30`). |
| ALG-10 | confirmed | **Reading**, anchors checked: `fiberRefusal` (`Sched.lean:32-39`, `:216-218`); `run_eq_meaning` (`Agreement/Machine.lean:1922`); `loopAgreement` (`Agreement/Loop.lean:839`); `run_eq_ref` at the empty table with no oracle (`RuntimeR.lean:203-215`). The finding corrects the model-probe synthesis's level-3 row, "the machine as runner … holds as a reading" (`synthesis.md:730`), and `2026-09-30-full-program-model-requirements.md:42`; the seat cites neither. |
| ALG-11 | confirmed | **Reading**: `hom_eq_cata_eff` (`Program/Fold.lean:1270`); `program_is_free` (`Algebra/Universal.lean:98`); `fold_of …denote` (`Laws/Program/Folds/Denote.lean:21`); system map §6 ("raw bind is not categorical composition", "laws are future work"). Minor: the positional-variable sentence is `Program/Eff.lean:22`, not `:12-15`. |
| ALG-12 | confirmed | Reran P5. The identification is already in lit-papers Q2 (`2026-09-07-lit-papers.md:123`); within `denoteR`, `guardR` is the only producer of `guard_` (`DenoteR.lean:62` only re-wraps an existing one; reading). One nuance the note's gloss misses: `controlErasure` sends `unguard ex` to `pure ex` (`DenoteR.lean:105-111`), so erasure runs the continuation on exits the guard skips, which the machine bypasses. "On one fiber a scope is plain sequencing" therefore holds only for continuations that pass skipped exits through, as `seqR` does (`DenoteR.lean:47-49`). That is the invariant `denoteR_straight` relies on. The frozen contract already pins a scope-versus-bind red control (`cleanup_boundary_distinct`, `Test/Program/DenoteRContract.lean:240`). |
| ALG-13 | confirmed | **Reading**: `FairTape` is used only by `SchedulingContract.lean:61` and its contract packet. DESIGN-BASIS already records "Divergence adequacy: **pending**" (`DESIGN-BASIS.md:732`). |
| ALG-14 | confirmed | **Reading**: `Provision.lean:35-41` claims `build_total` "is proved once"; it was cut at `b08f3b58` (traversal census; grep finds no `build_total` in `src/` or `Test/`). The model probe already flagged it as a coordinator small fix (`synthesis.md:773`, `:860`). The "adjunction" misnomer is new, and also appears in that synthesis (`:318`, `:949`). |
| ALG-15 | confirmed | **Reading**: row 117 (`decisions.md:210`) and the proposed `E4-TYPED-CE-008` (addendum 6, H2 item 4). Not new; the seat says so. Literature: the graded-monad reading (Katsumata 2014, by name) holds via the graded reader monad. The closer named notion for "what the context must provide" is a flat coeffect (Petricek, Orchard and Mycroft 2014, implicit parameters; by name), a wording option for DB-17. |
| ALG-16 | confirmed | Reran P7. Rows are canonical, so the union laws are equalities (`Row` with `DecidableEq`, `Data/Row.lean:30-33`, `:464-506`): the free join-semilattice with bottom on keys, with relative complement. **Strengthened**: the seat's "regroup `provideMerge` chains freely" had no theorem in the tree. It is now **proved** on the whole layer type (`provideMerge_assoc`), and the tree's row law extends to the error column (`provide_provide`), because `Ty.join_assoc` is proved (`Laws/Program/TypeAlgebra.lean:433`). The docstring at `Provision.lean:119-122` calling it "owed" is stale. |
| ALG-17 | confirmed | **Reading**: `StepKeeps` (`Lift.lean:48-54`); the tree's own name "the frame law" (`:131`, `:168`); `Projects` is a step-commuting abstraction with an invariant, `Refines` a forward simulation that also preserves frontiers (`Refinement.lean:20-37`). Literature by name. |
| ALG-18 | confirmed | **Reading**: `Fits` (`Membership.lean:87-148`) and its transport laws. With only first-order values, `Fits` is the value part of a unary Kripke relation, a store typing in TAPL's sense (by name). The Kripke clauses live in `TypedProg`'s continuations, and must also live in the saved stack (ALG-01). |
| ALG-19 | refuted | "(row 38)" at `coherence-principle.md:568` points to that document's own census table: row 38, "run observations / K5 / final / no finality" (`:144`). It is not decisions row 38. The amendment is also wrong: `behaviour_unique` concerns the session `Runner` (census row 27). It would not discharge row 38, which asks that equal `obs` imply equal runs. |

## What the seat missed

1. **The step-level witness, and the command.** The seat's "step_evaluate is false" was reading
   and names the wrong step. `step_loop_refuted` refutes the ledger's `step_loop`;
   `evaluate_keeps` shows `evaluate` is harmless on the same state. By reading, every step that
   grows a table that `Fits` reads fails the same way:
   - `loop` and `deliver`, where a store or fork operation grows Ρ, Π or Γ;
   - `launch`, where a race entrant grows Γ;
   - `decision_preserves`, which drives these commands.

   A park grows only Θ, which no `Fits` reads. That breaks the conditional lookups instead, which
   is CE-016's family.

   Register `step_loop_refuted` as the counterexample: it is a stronger witness than the
   judgment-level control. The ID is the coordinator's: the next `E4-TYPED-CE` after 008, or the
   next SCHED number after 019.
2. **The walk must be restated.** `popR_typed` (`Stack.lean:105`) concludes the one-world
   `SavedOk`, so even with Kripke input it hands back no Kripke stack. A Kripke copy of the walk
   is needed; its arms are the same, and the tails come from the input.
3. **Hook protocols must be closed in their definitions, not wrapped at the frame.**
   `output_not_kripke` is the red control: with wrapped premises, the protocol pushed after a
   resume may pick its intermediate type per world. Concretely:
   - `IteratorProtocol.step.next` and `LoopProtocol.step.next` quantify over later worlds, with
     their `resume`/`continue` tails at the answer's world;
   - so does `frameProtocols.asyncFinalizer`'s cancellation clause;
   - `HookLaws` then returns protocols that are monotone by construction.

   That `hookLaws_interpR` still goes through by unpacking under this shape is reading, not
   probed.

   Row 87 already warns against "independent existential type choices".
4. **Ownership and sequencing.** Two rows already own this question and the seat cites neither
   for ALG-01; H1 is the vehicle it did name:
   - **Row 87** (coordinator, open) asks which hypotheses make concrete typing monotone; ALG-01
     is that question for frames. Amend row 87 rather than add a row.
   - **Row 117** (open) is the pending stronger saved-frame contract: loop, iterator,
     preempted-catch and `.scoped`, vacuous at answer `never`.
   - **H1** (row 133, addendum 6, "statements only") restates `TypedState` and the step
     statements now.

   ALG-01, row 117 and CE-016 are one family: a clause that holds vacuously where it is checked
   and comes alive later, whether by a new cell, an empty answer type, or an unallocated token. A
   cheap guard against the next one: declare world-monotonicity of each owner predicate of
   `preds`, with freshness premises on the conditional lookups, as `M3bWorld` obligations. A
   missing case then fails as a statement, not as a counterexample.
5. **Why no gate caught it.** The vocabulary's Kripke `continuation` source
   (`Vocabulary.lean:31-32`) is used by no row of `Sources.lean`. `RSaved` is an opaque
   `.owner "SavedOk"` (`Sources.lean:31`), so the position gate cannot see that the frame
   clause is not Kripke.
6. **The in-flight design-basis refresh** (`2026-10-01-design-basis-refresh-brief.md`) is where
   the seat's wording lands:
   - DB-04 ("Elgot pedigree"): say Kleene chain of the least fixed point; ALG-08.
   - DB-05: ALG-10.
   - DB-16: it lists the frame judgment among "settled by rows … 48 …" (model-probe
     synthesis `:834`). It must not record the one-world frame judgment as settled.
7. **Prior proofs not cited.**
   - C4's generic half: `inr_iff`, `typed_along`, `c4_iff` in the model probe's pedigree folder.
   - `interpret_along`.
   - The frozen `cleanup_boundary_distinct`.
   - lit-papers Q2's bracket reading.
   - DESIGN-BASIS's "divergence adequacy pending".
   - The model probe's `build_total` small fix.

   These make ALG-05, and parts of ALG-06, ALG-12, ALG-13 and ALG-14, restatements of known
   items.
8. **ALG-04's option (a) is false; option (b) is proved for the main construct.** The bind lemma
   M5 can use is the `seqR` compatibility lemma (`seq_typed`). It rests on one fact: closing with
   `unguard` keeps a program's type (`close_typed`, one induction, every arm a constructor).
9. **Erasure versus machine** (ALG-12): erasure agrees with the machine only for continuations
   that pass skipped exits through. `denoteR` builds only such continuations (`seqR`), and
   `denoteR_straight` silently relies on it. It deserves a stated lemma or a census line.
10. **Stale texts found on the way**, all reading:
    - `Provision.lean:119-122` ("join associativity owed"; `Ty.join_assoc` is proved).
    - `guard_inv`'s "exactly" (`Residual.lean:231-232`).
    - The model-probe synthesis's "machine as runner" (`:730`).
    - That synthesis's "adjunction" (`:318`, `:949`).

## Probes and commands

| Probe | Question | Result | Axioms | Log |
| --- | --- | --- | --- | --- |
| seat `probes/P1`-`P7` | Do the seat's probes reproduce? | All seven exit 0; logs byte-identical to the seat's | as the seat's | `verify-logs/rerun-*.log` |
| `verify-StepLoop.lean` | Is ALG-01 a false declared obligation, and for which command? | `step_loop_refuted` (red); `step_loop_good` (green); `evaluate_keeps`; `bad_not_kripke_initial`; `typed_mBad`, `valid_w1g`, `typed_afterGood` | all `[propext, Quot.sound]` | `verify-logs/verify-StepLoop.log` |
| `verify-WrapWalk.lean` | Does wrapping the hook premises survive the walk? | `hookLawsX`; `walk_typed_one_world`; `output_not_kripke` (red) | all `[propext, Quot.sound]` | `verify-logs/verify-WrapWalk.log` |
| `verify-BindGuard.lean` | Is ALG-04's option (a) enough; does option (b) work? | `bind_not_typed` and `guard_bind_not_closed` (red); `close_typed`, `seq_typed` (green) | all `[propext, Quot.sound]` | `verify-logs/verify-BindGuard.log` |
| `verify-ProvideMerge.lean` | Is `provideMerge` regrouping free, and is the row law's error column really owed? | `provideMerge_assoc_rows`, `provideMerge_assoc`, `provide_provide` | all `[propext, Quot.sound]` | `verify-logs/verify-ProvideMerge.log` |

Commands, each run alone through the lock, exit 0 on the final run:

```
bash <scratchpad>/serial.sh lake env lean -M6144 -DwarningAsError=true <absolute probe path>
bash docs/research/2026-10-01-formal-pass/algebra/verify-rerun.sh   # all eleven, with the diff
```

`<scratchpad>` is `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad`.
Drafts were iterated in that scratchpad; the final files above were recompiled from this folder.
Two fixes were needed on the way: an `omega` that did not see a bound after `cases`, and an unused
`simp` argument. No evidence is bounded or host-only: every claim above is a kernel theorem or a
reading.
