# Formal pass, synthesis (2026-10-01): the formal account of Effect4, its gaps, and the landing plan

The entry document of the formal pass. It reads the four seat notes (algebra, proofs, types,
organization) and their four verifications, reruns the probes the conclusions rest on, ports the
ones the merge broke to the tree as it now stands, and checks the decisions rows and the landing
plan the coordinator wrote from the seats' verdicts. Research only: nothing here is a ruling until
it is written into `docs/core/decisions.md` or another tracked file.

**Base and head.** The seats worked at `ea5b28b5`. While this seat worked, the coordinator merged
Codex's branch (`0c534f06`: G, H1, H2 part one and row 39's Schema wipe), rebuilt the library
(07:27), recorded the landing (`dceae006`), wrote decisions rows 134–148, a landing plan and briefs
for seats A–H (`bb269fde`, `c9f273a2`, `f6786859`), and tracked this seat's ports
(`1c6f9c92`, `docs/research/2026-10-01-landing/ports-at-dceae006/`, byte-identical to the files
compiled here, tested by `cmp`). Every rerun and every new proof below was compiled against the
rebuilt tree; no Lean source under `src/`, `Test/` or `tools/` changed between `dceae006` and
`1c6f9c92` (tested, `git diff --name-only`), so the evidence holds at both. Line numbers are at
`dceae006` unless marked `@ea5b28b5`. Short paths drop `src/Effect4/`.

**Evidence words.** **proved**: a kernel theorem this seat compiled, axioms printed at
`[propext, Quot.sound]` or fewer. **tested**: a finite check this seat ran. **reading**: code or
notes read, not run. **assumed**: not checked. "Proved by seat X at `ea5b28b5`" means the seat's
kernel theorem, rerun then by its verifier, that this seat could not rerun after the rebuild.
Literature carries the mark of the note that cites it: **read** (with the note that read it),
**by name**, or **assumed**. This seat opened no paper.

**Counting rule.** A seat finding counts only if its verifier confirmed or partly confirmed it;
"(partly)" says which part stands. A verifier's own finding is cited as "verifier". Refuted
findings (ALG-19, ORG-19) are not counted.

**Rows and ids.** This note uses the coordinator's numbering: rows 134–148 (written 2026-10-01)
and the register ids `E4-TYPED-CE-009`–`015` of the plan's §2. It proposes one new row, 149.

## The one thing

**Four declared M5–M6 obligations are false at the merged head, proved there, and each has a
small statement-level amendment that changes no ruled design; rows 134–137 already carry them.**
They are the only fundamental gaps; everything else is rigor or tidiness, and the model can be
described end to end in the literature's terms once twelve loose names are corrected (§1, §5).

1. **Value typing compares declared handle types in a different order than the checker** (TY-01;
   row 137; `E4-TYPED-CE-009`). M5 and M6's capstone are false for a checked, closed, admitted,
   host-free program (`HeadM5Fits.m5_false`, `capstone_false`).
2. **Protocol postconditions are not fulfilled by their handlers** (G6; row 136; `-010`, `-013`).
   The await-by-value post alone makes M5 false for the typed corpus's own `awaitFiber.value`
   (`HeadAwaitLoad.typedState_load_false`).
3. **Saved frames and hook protocols are typed at one world** (ALG-01; row 135; `-012`). The merged
   `M6Ledger.step_loop` proposition is false at a concrete typed state
   (`HeadStepLoop.step_loop_refuted`).
4. **The capstone and `decision_preserves` read the typed state at a budget cut, where the queue
   is gone** (G1; row 134; `-011`). H1's landed rule repairs the finished run but not the cut
   (`HeadCut.window_untyped`, `capstone_false_window`, `ledger_jointly_false_window`;
   `m9_root_inert`).

Seats A, B, E, F and H are already at work on their branches (read from the refs: A has
committed row 137 (a), B has re-established `-010`, `-012` and `-013` as batteries; C has not
started). Of the ten one-line corrections in §4.5, three matter now: `E4-TYPED-CE-011`'s
finished-run half no longer holds at the merged head, so its claim and brief C's list narrow to
the cut; plan §2's witnesses no longer elaborate, and the tracked ports replace them; row 122's
write-up has no seat. One new owner row: 149, because brief A renames a frozen refusal.

## 1. For the owner

**Are there fundamental theoretical gaps in the plan for M5–M7?** Yes, four, and all four sit in
how the typed-state guarantee is *stated*, not in what it is meant to say. None asks for a change
to the machine, the program representation, the checker, or any ruled design. Each is proved at
the merged head, not only read, and each has a small amendment that the coordinator has already
written as a row:

| Gap | What it blocks | Smallest amendment | Row |
| --- | --- | --- | --- |
| F1. `Fits` compares a declared handle type in the raw order; the checker uses the normalized order (TY-01) | M5 (`typedState_load`) and M6's capstone are false for a checked, closed, admitted, host-free program; every M6 step that joins answers or enters an annotated loop meets the same mismatch | compare declarations in the checker's order `subN` inside `Fits`'s fiber, cell and deferred arms; prove `fits_normalize`, `fits_subN`, `fits_join_left/right` | 137 (owner; ratification owed): it amends row 96 D1 and re-reads host-boundary §4.4 |
| F2. Eight protocol rows' posts contradict their handlers; no obligation says a handler answers within its protocol (G6, partly, with the verifier's three extra rows) | M5 for every program that awaits a forked fiber by value; every `loop` arm of M6 rests on the posts | each post states the checker's rule for the operation; one adequacy obligation per row, the store frontier included | 136 (written; it follows row 106 and post-Phase C §5.3) |
| F3. Frames and hook protocols are typed at one world (ALG-01, with the verifier's corrections) | `step_loop` (and, by reading, `deliver`, `launch` and `decision_preserves`): no step that allocates can keep another frame typed | Kripke-close the frame judgment and the iterator, loop and async-finalizer protocols in their definitions; restate the walk lemmas over Kripke stacks | 135 (written; it answers row 87 and strengthens row 48) |
| F4. The machine-level statements read the typed state at a budget cut with the queue dropped (G1, partly: the verifier's repair) | `decision_preserves` and the capstone at any program whose command budget ends between a fiber's last walk and its `finish` | the split keyed on `running`: the machine-only predicate types the code of fibers neither exited nor running; the generic lift is unchanged | 134 (owner; ratification owed); it supersedes row 133's halt extension (plan O4) |

**Rigor, not fundamental** (a law or declaration the plan needs is missing; no declared statement
is false because of it), each with its row: M5's real content is undeclared, the denotation's
fundamental property and term soundness at `Fits` (row 148); `TypedProg` is not closed under bind,
so M5 needs the `seqR` compatibility lemma instead, proved (row 148); "never halts" does not follow
from the typed state, whose scopes carry no liveness, and H1's halt extension tolerates halts by
design, its own witness `E4-SCHED-CE-020` being a typed state that holds a dangling scope (row
139); M7 is undeclared, and its only bridge holds at the empty row table while R1 asks every
milestone for Σ_app (row 138, with R1's exception); the world-weakening law `typedProg_mono` is open
in the ledger and proved here (row 135); Σ_app is absent from the M5–M7 statements (rows 111–116);
row 117's contract is a presence (coeffect) fact (row 117 as amended); refused source positions
are consumed as `True` (row 140); the census cannot measure "every traversal is a fold" (row 143);
K2 exactness needs its normalisers named as functions (row 128); inhabitance has no fold yet (row
127), and brief A's renaming of the `int` refusal touches a frozen contract (row 149, new).

**Tidiness** (a text claims what the tree does not, or a cheap law or name is missing): the
vocabulary still calls two retractions exact (row 128); "K1–K5" means two things; the register's
header is stale; several docstrings and documents restate facts their owners hold and disagree
with them; five names resolve two ways (row 141); seven Guard inductions re-prove a lift; twelve
ledger ceilings carry slack; the core root still imports the `Effects` package through one unused
model in `Machine/Context.lean`.

**Can the model be described in the literature's terms end to end?** Yes (section 2): programs are
an initial algebra elaborated into a free monad over a sum of signatures; scopes are bracket
markers; loops are the Kleene chain of a least fixed point; the store is a lawful comodel of state
on its live cells; the machine is a deterministic abstract machine labelled by decisions, with the
tape as its oracle; typing is a protocol-typed weakest precondition over Kripke worlds whose value
part is a store typing; the typed state is meant to be an inductive invariant with a ghost world;
the row calculus is a free semilattice grading; the faces are folds, partial isomorphisms,
simulations, located refusals and a free monoid action. The description is loose in twelve
places, each corrected in the glossary (section 5):

1. "Kripke" fits `Fits`, `TypedProg` and the amended stacks, not the typed state, whose world
   validity has exact support and is not upward closed (`worldValid_not_upward_closed`, proved by the
   proofs verifier at `ea5b28b5`; at the merged head it still elaborates without `sorryAx` in that
   verifier's file, whose other theorems fail on the merge's statement changes, tested).
2. The machine is a runner (the run of a free model against a comodel) only on the straight and
   looped fragments; past the first fiber operation it is an abstract machine related to the
   reference by a lock-step simulation, at the empty host table (ALG-10).
3. The vocabulary's "simulation" examples are equal-observation statements: computational
   adequacy or semantic preservation. The simulation relation itself is the book's `ReplayRel`/`BMeans`.
4. `Ty → Representation` is not an ornament: the read-back is partial; it is a partial isomorphism
   onto the image, and a retraction until exactness lands (row 128).
5. "Finality" for "equal observations imply equal runs" names injectivity of the behaviour map,
   which is neither claimed nor needed; `behaviour_unique` is the uniqueness half of finality for
   the session runner.
6. Elgot's fixpoint law holds only at the limit of the budget chain, never at one budget.
7. `TypedProg` is its own inductive since slice 5; it shares the protocol shape of de Vilhena's
   `Typed` but is not an instance of it.
8. `TypedProg` is not closed under bind; the cause is the non-local exit of a scope marker, not a
   handler frame in the context.
9. Growing Σ_core is hierarchy-consistent, not a persistent extension: a new constructor adds
   elements to an old sort, which is why functions with catch-all arms can change.
10. `CTy` is a bounded join-semilattice; "not a lattice" is unsupported (meets are not claimed).
11. The guard as "exclusive ghost tokens" and "Schema and program" as a graded Freyd category are
    analogies, not theorems (system map §6 says the second is a proposed organization).
12. Budgets plus `Suffices` are not CompCert's stuttering measure: a measure preserves
    divergence, and budgets claim nothing about it.

**What this means for M5–M7 and beyond.** The four fundamental gaps share one shape: a clause is
established at one point and read at another, and the two points differ by an operation the
statement did not account for (normalization, the handler's actual answer, world growth, a budget
cut). The amendments make each clause stable under that operation. Two cheap guards would catch
the next one before a proof does: declare world-monotonicity of every owner predicate of `preds`
as `M3bWorld` goals (the algebra verifier's proposal), and keep the corpus fuel-frontier scan
(tested here: 0 of 64,142 settled results hold a running fiber) as a standing check that the
machine-only clauses survive cuts. Beyond M7, the plan needs carriers it does not have yet:
infinite decision streams for divergence and fairness (R12), a stuttering simulation for
composed modules (R10), and per-form equations whose state laws the store comodel already
satisfies on live cells (proved here).

## 2. The formal account of Effect4

> Note added 2026-10-01 by the coordinator (seat H's receipt): `guardR_bind` was in the tree before this
> pass (`src/Effect4/Laws/Program/Intro/Prepare.lean:44`); P5 re-proved it. The table below keeps its
> attribution to P5; the basis and system map §9 cite the tree.

One row per object. "In tree" laws are read in the tree (the trust gate audits them; this seat did
not run the gate). "This pass" laws were compiled by this seat at `dceae006` (rerun or ported; the
receipt names the file). Severity: **fundamental** (a declared statement is false, or a misnaming
misleads the plan), **rigor** (a law the plan needs is absent or owed), **tidiness** (a cheap law or
a correct name is missing), **none**.

| Object | Formal notion | Literature | Definition site | Laws proved | Laws owed | Severity |
| --- | --- | --- | --- | --- | --- | --- |
| Programs: `Eff`, the proof carrier `Program S`, `denote` | `Eff` is the initial algebra (term algebra: syntax with no equations, from which every algebra receives exactly one structure-preserving map) of a first-order, many-sorted signature whose variables are positions in the environment (de Bruijn levels). `Program S` is the free monad over a signature. `denote` is the fold from the first into `Program StoreSig`. `Eff` has no monad structure: bind is a constructor, and raw reassociation changes values | Goguen, Thatcher, Wagner, Wright 1977 (by name, coherence principle); Plotkin and Pretnar 2013 §1, §5 (read, lit-papers Q11); Swierstra 2008 §2, §6 (read, model-probe pedigree seat); Hyland, Plotkin, Power 2006 (by name, never read in the tree) | `Program/Eff.lean:264`; `cata_eff` `Program/Fold.lean:1104`; `Program` in the pinned package `Algebra/Program.lean:33`; `denote` `Laws/Program/Denote.lean:66` | in tree: `hom_eq_cata_eff` (`Program/Fold.lean:1270`), `program_is_free` (package `Algebra/Universal.lean:98`), `denote.eq_cata`; this pass (P1): the signature sum is the coproduct of the free monads (`sum_is_coproduct`), restriction for any handler of a sum, injections are monad morphisms, red control `sum_not_tensor` | `composeAt` identity and associativity at a named meaning (system map §6; no milestone needs it) | tidiness |
| Scoped constructs and `denoteR` | Scoped operations elaborated into algebraic ones with bracket markers (`guard_` opens, `unguard` closes), well bracketed by construction (`guardR` is the only producer of `guard_`); an elaboration in the hefty-algebra sense, written by fuel recursion. A scope is not an algebraic operation (a continuation cannot be moved inside it). Control erasure is a handler, hence a monad morphism | Wu, Schrijvers, Hinze 2014 §9–10; Piróg et al. 2018 §1.3; van den Berg et al. 2021 §2.2; Bach Poulsen and van der Rest 2023 §1.2, §2.6.4, §3.4 (all read, lit-papers Q2); Plotkin and Power 2002 on algebraicity (by name, core math §6) | `guardR` `Laws/Program/DenoteR.lean:69`; `denoteR` `:799`; `eraseControl` `:114` | in tree: 38 unfolding equations, `eraseControl_bind`, `eraseControl_guardR`, `denoteR_straight` (`:1380`); this pass (P5): `guardR_bind`, red control `guardR_not_algebraic`, `eraseControl_guardR_bind` | the invariant `denoteR_straight` relies on and does not state: erasure agrees with the machine only for continuations that pass skipped exits through, as `seqR` does (verifier, reading `DenoteR.lean:105-111`, `:47-49`); per-form behaviour laws (R10) | rigor |
| The budgeted meaning: `iter`, `denoteB`, `meaningB` | The k-th approximants of the least fixed point of a loop's unfolding equation (a Kleene chain) in partiality with state; a loop means the answer some budget finishes with. Not an Elgot algebra: `Program` is well founded and has no iteration operator. `meaningB_unique` is single-valuedness of the limit (Capretta's termination relation) | Elgot 1975; Adámek, Milius, Velebil 2006 (by name, coherence principle); Capretta 2005 (by name, core math §3); Jacobs Thm 5.3.4, Prop 5.3.3 (read, papers review §1.4) | `Laws/Program/Iter.lean:30`; `Laws/Program/DenoteB.lean:208`, `:241` | in tree: `iter_zero`, `iter_succ`, `iter_uniform`, `denoteB_straight`, `denoteB_mono`, `meaningB_unique` (`:496`), `loopAgreement` (`Agreement/Loop.lean:839`); this pass (P4): Elgot's fixpoint law for the limit `conv_fixpoint`, leastness `conv_least`, `conv_unique`; red control `budget_not_fixpoint` | naturality, dinaturality, codiagonal: only when a loop rewrite is declared (R10) | tidiness (verifier ALG-08) |
| The store handler and `meaning` | A comodel of the store signature (one co-operation `Stores → Val × Stores` per operation); `meaning` runs the free model against it (the runner shape, without exceptions). Lawful for state on live cells; on an unallocated cell the fallback breaks put-get (`E4-DEN-CE-002`) | Plotkin and Power 2008; Ahman and Bauer 2020 (by name, core math §7) | `Laws/Program/Denote.lean:124`, `:130` | in tree: `refPeek_poke_self` (`Machine/Stores.lean:962`), `refStep_get_after_set` (`:968`), arena laws (`Laws/Machine/Arena.lean:18-32`), `run_eq_meaning` on `Straight` (`Agreement/Machine.lean:1922`); this pass (P4): `put_get`, `get_get`, `put_put` on live cells; red control `put_get_dead_fails` | get-put and cross-cell commutation as handler laws, only when a form declares a state equation | tidiness (verifier ALG-09) |
| The fiber machine (native and reference) | A deterministic labelled transition system. Decisions are the labels. The command residue `Cmd` is the defunctionalized continuation (each higher-order continuation replaced by a first-order constructor with an `apply`) of rc.112's synchronous call stack, `driveStep` its apply. A fiber's saved frame is a K-machine state `k ▷ e`: code at an intermediate type and a stack to the answer type. Not a runner past the first fiber operation: the fiber signature has no handler by design (`fiberRefusal` "is not a semantics", `Laws/Program/Sched.lean:216-218`) | Danvy and Nielsen 2001 §1, §3 (read, lit-papers Q12); Harper, PFPL ch. 28 (by name); Felleisen and Friedman's CK machine (by name); Lynch and Vaandrager 1995 (by name; core math §8 read); Leroy 2009 (by name) | `RunMachine` `Machine/Fibers.lean:438`; `Cmd` `:727`; `driveStep` `:1846`; `stepDecisionState` `:2111`; reference `Laws/Program/RuntimeR.lean` | in tree: `run_eq_ref` (`RuntimeR.lean:211`) through `replay_rel` (`:162`), a lock-step simulation (`BMeans`) at the empty host table and empty oracle; `run_eq_meaning`, `loopAgreement` on their fragments | the table-aware agreement (DI-57, parked under R6); the OCaml engine by differential runs only (finite) | rigor (ALG-10: the model-probe synthesis's "machine as runner … holds as a reading", `synthesis.md:730`, is wrong past the fragments) |
| Behaviour and the tape | With `obs`, the machine at a fixed budget is a deterministic Moore machine over the decision alphabet; `Beh` is its behaviour on a tape (a finite word). The tape is the oracle: every nondeterministic choice is a decision. Tapes act on machines (a monoid action, fuel exhaustion absorbing). The session runner is a Mealy machine and `behaviour` its map out, unique by its unfolding. A journal is a word of the free monoid on commands, acting on runs | Jacobs, *Introduction to Coalgebra* ch. 2 (read, papers review §1.4), ch. 3 Thm 3.4.1 for bisimulation (read via the 2026-09-05 review, per the proofs verifier); Xia et al. 2020 §7, Def. 1–2; Chappe et al. 2023 §2.2, §7.2 (read, lit-papers Q7); Rutten 2000 (by name) | `replayEval` `Machine/Fibers.lean:2188`; `Beh` `Laws/Machine/Behaviour.lean:74`; `Runner` `Api/Runner.lean:70`; `behaviour` `Laws/Api/Runner.lean:168` | in tree: `Beh_fuel_irrelevant`, `replay_stable`, `replay_obs_mono`, `replay_colimit`, `replayEval_trace_extends`, `replay_append`, `replay_unique`, `behaviour_cons`, `journal_replays`; this pass (P3): `replayEval_append` and corollaries, `behaviour_unique` | infinite tapes, divergence by compatible prefixes (DB-03), liveness under fairness (`FairTape` has no consuming theorem), frontiers naming armed work: all R12, after M7 | rigor (beyond M7) |
| Typing as protocols over a world: `TypedProg`, generic `Typed`, `World`, `leHost` | A protocol-typed weakest precondition on free-monad trees with first-order protocols: each operation's demand holds now, and its continuation is typed at every later world in which the handler answers within the protocol. Worlds are ghost tables over the store (store typings for fibers, deferreds, cells, tokens), ordered by extension. `TypedProg` is world-monotone. It is not closed under bind: a scope's skipped exit bypasses the continuation (a non-local exit) | de Vilhena thesis 2022, Def. 2.2, 2.4–2.8, rules Bind and Monotonicity (read, papers review §1.3, model-probe pedigree seat); Timany and Birkedal's "non-local control breaks the bind rule", as de Vilhena §2.4 cites it (read via papers review G8); TAPL §13.4–13.5 (by name) | `TypedProg` `Laws/Program/Typed/Residual.lean:186`; `Typed` `Laws/Effects/Protocol.lean:45`; `World` `Typed/World.lean:52`, `World.le` `:131`; `leHost` `Typed/Validity.lean:38` | in tree: `Typed.mono`, `bind`, `widen`, `inl`, `inl_inv`, `inr_inv`; world order laws; this pass: `typedProg_mono` in the ledger's binder order (closes `M3bWorld.typedProg_mono`), `storePre_mono`, `fiberPre_mono`; red control `bind_not_typed`; `seq_typed` with `close_typed`; P6's `Typed.inr`, `Typed.refine` (no axioms; the pedigree's `inr_iff`, `typed_along`, `c4_iff` already prove them) | handler adequacy per protocol row (F2); the fundamental property `denoteR_typed` (M5's content); `fiber_inv` (in a probe only); concrete C4 | fundamental (F2); rigor |
| Value typing: `Fits`, `FitsExit`, `ExitOk` | The world-indexed value interpretation `V⟦τ⟧(W)` of a Kripke model for first-order references: a predicate per type, monotone in the world, by structural recursion on `Ty`, with handle leaves read from the world's declarations. With no arrow clause it is a store typing in TAPL's sense rather than a full logical relation; no step indexing is needed because worlds hold syntactic types read as declarations. `fits_hasTy` is type erasure to the executable check. `ExitOk` adds the shape-defect exclusion (H2 part one) | TAPL ch. 13 (by name); Ahmed 2004; Ahmed, Dreyer, Rossberg 2009; Appel and McAllester 2001 (by name); Reynolds 2000, extrinsic typing (by name) | `Laws/Program/Typed/Membership.lean:87`, `:152`; `ExitOk` `Typed/Admission.lean:30` | in tree: `fits_mono` (`:829`), `fits_map` (`:729`), raw `fits_sub` (`:837`), `fits_hasTy` (`:269`), `fits_live` (`:520`), exit and cause lemmas, `Fits.eq_cata`; this pass: red controls `not_fits_fiber_normal`, `not_fits_cell_raw`, `not_fits_join`, `T_not_sub_normal`; on the amended copy `fitsN_normalize`, `fitsN_subN`, `fitsN_join_left/right`, `amended_join_holds`, red control `tree_join_fails` | `fits_normalize`, `fits_subN`, `fits_join_*` in the tree (F1); term soundness `evalTerm_fits` (TY-07); the reply bridge (parked); `ServicesFit` at `w.serviceTy` (row 112) | fundamental (F1) |
| The typed state, the lifts, the book | The intended inductive invariant (Init ⇒ Inv, Inv ∧ Next ⇒ Inv′ up to world extension, so Inv on every reachable state), with the world as a monotone ghost component and relative induction (`Guarded J I O`). Stacks form the free category on frame typings (existential middles). The lifts are the invariance rule for a transition system, composed through each decision; replay adds a rely condition on the environment's decisions; `driveStep_append` is locality of a command (a frame law). `Projects`/`Refines` are a refinement mapping and a forward simulation; the book is a lock-step simulation lifted to tapes. The typed state is not upward closed (exact support), like TAPL's well-typed store | Manna and Pnueli's invariance rule; Owicki and Gries; Abadi and Lamport 1991 (history variables) and 1995 (assume-guarantee); Jones 1983; O'Hearn, Reynolds, Yang 2001; Hoare 1972 (all by name); Jacobs ch. 6 invariants (read via the 2026-09-05 review) | `TypedState` `Typed/Assembly.lean:123`; `CodeInert` `:84`; `StepPreserves` `:180`; `RReachable` `:145`; `FrameAccepts`/`StackAccepts`/`SavedOk` `Typed/Contracts.lean:32`, `:51`, `:67`; `Laws/Machine/Lift.lean:48`, `:278`, `:308`, `:638`; `Laws/Machine/Book.lean:196`; `Laws/Machine/Refinement.lean:20`, `:31` | in tree: `driveState_lift`, `stepDecisionState_lift`, `replayEval_lift`, `driveStep_append`, `projects_compose`, `book_replayEval` (`Book.lean:1215`), `bookMeans_obs` (`:1283`), `popR_typed` (`Typed/Stack.lean:133`), `deliver_active` (`:390`), the H1 adapters; this pass: `stackAccepts_append`, `_split`, `_id`, `_push` (FrameCategory); `stackAcceptsK_mono`, `stackAcceptsK_now` for the Kripke-closed judgment | M5, M6's 20 goals, M7: all open, and false as declared (F1–F4); stack monotonicity; the decision lift's edits as declared obligations; "never halts"; a stuttering simulation (R10) | fundamental (F3, F4) |
| The row calculus: `Row`, `LayerTy`, `provide`, requirement rows | Requirement rows are the free bounded join-semilattice on service keys, with relative complement (canonical spelling makes the laws equalities). `provide` is the free-variable law of substitution. A program's requirement row is the grade of a graded effect system or, closer, a flat coeffect: what the context must provide. Associative only up to `provideMerge`; context merge is right-biased. Satisfaction is inclusion into the context's key row, a representability fact, not an adjunction | Katsumata 2014, Orchard et al. 2014 (by name, coherence principle §4b); Petricek, Orchard, Mycroft 2014 (by name); Bauer and Pretnar 2014 (by name); Leijen 2017 §3 (read, lit-papers Q4); de Vilhena's Tes §7.3 (read, papers review) | `Data/Row.lean:30`; `Program/Typing/Rules.lean:240-270`; `Program/Provision.lean:97-168`, `build` `:297` | in tree: union and difference laws (`Row.lean:464-650`), `provide_closed`, `provide_provide_rows` (`:122`), `merge_rows_comm` (`:137`), `satisfies_iff_subset_keysRow` (`:168`); this pass: red control `provide_not_assoc` (P7); `provideMerge_assoc` on the whole layer type and `provide_provide` with the error column (verifier) | effect soundness of the grading (a program at row r under a context satisfying r never dies `missingService`): row 117; `build_total`'s restoration and `lower_refines_build` (R5) | rigor |
| Types and signatures: `Ty`, `sub`, `normalize`/`CTy`, `subN`, `Signature Op`, Σ, `inhabited` | `Ty` is the initial algebra of a ground first-order signature; `sub` is algorithmic structural subtyping with unions, literals, a top and a bottom: sound, deliberately incomplete. `subN a b := sub (normalize a) (normalize b)` is a preorder whose kernel is equality of normal forms, so `Ty/≡N ≅ (CTy, sub)`, a bounded join-semilattice. `Signature Op` is the typed presentation of an effect signature; Σ_app is data (the row table: operations by position; the service table: constants sorted by their code). Inhabitance is the emptiness test of a regular tree type, a fold | TAPL ch. 15–16 (by name); Pierce 1991, Dunfield 2014 (by name); Frisch, Castagna, Benzaken 2008 (assumed, type-algebra §5.3); Benke, Dybjer, Jansson 2003 (by name); Ehrig and Mahr 1985 (by name); Delaware, Oliveira, Schrijvers 2013 (by name); Comon et al., TATA; Amadio and Cardelli 1993 (by name) | `Program/Ty.lean:37`, `sub` `:437-456`, `normalize` `:563-753`, `CTy` `:842`; `Program/Typing/Rules.lean:47-66`; `nativeSignature` `Program/Native.lean:316` | in tree: `sub_refl`, `sub_trans`, `sub_antisymm_canonical`, the `CTy` join laws, `hasTy_normalize`, `sub_not_complete`, `check_sound`/`check_complete` over any signature (`Laws/Program/Typing/CheckSound.lean:37`, `:361`); this pass: `subN_trans`, `sub_le_subN`, `subN_equiv_iff`, `ofRaw_eq_iff`; `inhabited_of_fits`, `inhabited_of_hasTy`, `fits_of_inhabited_handleFree`, `inhabited_sub`, the DI-67 red controls; `handle_inhabited` (verifier); `k1`, `k2` (`decide +kernel` evaluates `sub`) | C3 reflection (one generic fold congruence; R2Probe §E proves it on `Looped`), concrete C4, `LawfulSig` (with a third clause shape for required keys), C2 operational, C7, C8; inhabitance amalgamation and invariance under `normalize`; meets of `CTy` (not claimed) | rigor |
| The embeddings (K2) | A lawful prism, that is a partial isomorphism with a total forward map: retraction `read (write a) = some a` plus exactness `read f = some a → N f = N (write a)`. `Canonical`, print/read on the readable domain, the store, node and program byte codecs and `Config.Val` have both laws; `ofSchema` and the JSON codec are retractions only (row 128). Guarding a read by the writer's image makes it exact, but only modulo the named normaliser: at `N = id` the guard refuses key-permuted JSON that the frozen codec contract accepts | Rendel and Ostermann 2010; Pickering, Gibbons, Wu 2017; Foster et al. 2007 (by name, coherence principle); McBride 2011 (by name; the ornament reading is wrong here) | `Store/Domain/Canonical.lean:33`; `Laws/Codegen/ReadPrint.lean:1904`, `Laws/Codegen/Read.lean:887`; `Schema/Bridge.lean:38`, `:79`; `Schema/Codec.lean:230`, `:239`; `Store/Carrier/Val.lean:1040`, `:1045`; `Store/Domain/ProgramWire.lean:51`, `:56`; `Program/ConfigValue.lean:50`, `:64`, `:112` | in tree: `ofVal_toVal`, `ofVal_exact`, `read_print`, `read_exact`, `ofSchema_schema` (`Bridge.lean:140`), `decode_encode`, the byte codecs' `decode_exact`; this pass: `readExact_exact`, `readExact_retract`, `readExact_iff`, `decodeExact_*`, `ofSchemaExact_*`; tested: V1a, V2, and the key-order guard keeping a permuted image while refusing V2 | exactness of `ofSchema` and the codec, with `N_S` and `N_J` named as functions and `read` proved invariant under them (row 128, stage 1's second commit) | rigor |
| The host boundary | A located refusal over completions that keeps the minted-handle invariant (every handle in a state was allocated by the machine): TAPL's well-formed store, capability safety's "no forged references", and a step of the world order at an external allocation. The host is an oracle whose only action is an answer decision | TAPL ch. 13; Miller 2006; Devriese, Birkedal, Piessens 2016; CompCert's external functions and CakeML's oracle (all by name; the last via model-probe synthesis §3.1) | `Program/Admit.lean:59-75`; `Program/Compile.lean:1371-1382`; `Program/Profile.lean:176`, `:196`; `Api/HostSession.lean:84` | in tree: the session's envelope and at-most-once laws; typed failures handle-free by the closed alphabet (`valOfErr_keys`, `causeImage_handleFree`) | parked (R6): the receipt theorem and its bridge `fits_of_hasTy_handleFree`, K4 completeness of `admitAnswer`, DI-57 | rigor (parked) |
| The faces K1–K5 | K1 a catamorphism (unique by initiality; `fold_of`'s pairing gives paramorphisms); K2 a lawful prism; K3 an equal-observation statement on a named fragment, proved through a simulation relation (computational adequacy for machine against meaning, semantic preservation for machine against reference); K4 a sound and complete decision procedure with a located refusal; K5 the action of the free monoid on runs | Meijer, Fokkinga, Paterson 1991; Hutton 1999; Meertens 1992; Plotkin 1977; Lynch and Vaandrager 1995; TAPL ch. 16; Dunfield and Krishnaswami 2021 (all by name) | system map §5; `Program/Checker.lean`; `explain_none_iff` `Program/Typing/Agreement.lean:82`; `admitted_unique`, `admitProgram_certificate` `Laws/Run.lean:207`, `:218` | in tree: `hom_eq_cata_eff`, `explain_none_iff`, `admitProgram_certificate`, `admitted_unique`, `replay_unique`, `journal_replays`, and the K2, K3 laws above | none new; the listing is loose: system map §5's K4 row names a tactic (`authoring_scoped`) and a totality fact (`open_total`) and omits `admitProgram_certificate`; K2 and K3 omit lawful instances (T2) | tidiness |

## 3. The gaps, ranked

Each gap: what it is, the evidence, the theorem it affects, and the smallest amendment that
changes no ruled design (rows 111–133). Theorem names after "proved" are this seat's files compiled at
`dceae006`, tracked at `docs/research/2026-10-01-landing/ports-at-dceae006/` (Appendix A), unless
attributed. Rows and register ids are the coordinator's of 2026-10-01 (rows 134–148; plan §2).

### 3.1 Fundamental

**F1. `Fits` compares a declared handle type in the raw order; the checker uses the normalized
order.** (TY-01, confirmed and strengthened by its verifier.)
- *What.* `Fits`'s handle arms compare a declaration with the asked type by raw `Ty.sub`
  (`FiberDeclared` `Laws/Program/Typed/Membership.lean:36-37`; `Equiv` `:25` for `RefDeclared`
  `:28` and `PromiseDeclared` `:32`). Every subsumption premise of the checker compares `sub` after
  `normalize`, and every answer join is `Ty.join` (verifier, reading `HasTy.lean:186-187`, `:244`,
  `:388`; `Checker.lean:185-188`, `:222`, `:369`; `Rules.lean:114-117`). Raw `sub` does not
  distribute a product over a union: for `T := prod (nat | string) unit`, `sub (normalize T) T`
  holds and `sub T (normalize T)` does not (proved, `T_not_sub_normal`, `normal_sub_T`, probe A
  rerun).
- *Evidence.* Proved: `HeadM5Fits.m5_false` (no world types the load state of `prog3`, which forks
  a closed child whose certificate is the raw `T` and returns the fiber handle through a `select`
  whose checked answer is the canonical form), `typedState_load_false`, `capstone_false` (the
  empty tape reaches the load state). The premises are kernel evaluations (`prog3_typed`,
  `rootTy3_closed`, `child_cert`); admission accepts the program (tested, `#guard`). Only the fiber
  arm is reachable today: native cells and deferreds are handle spellings declared at `nat`, and
  no checker rule produces `refOf` or `deferredOf` (verifier, reading `Program/Native.lean:90-99`).
- *Affects.* `M3bAssembly.typedState_load` (`Typed/Assembly.lean:262`) and
  `M6Ledger.typedState_reachable` (`:350`), proved false; by reading, every M6 step that joins
  answers or enters an annotated loop cursor (`select`, `catchCause`, `catchIf`, `matchCause`,
  races, generator joins, `iterate`).
- *Amendment.* In `Membership.lean`, compare declarations in the checker's order `subN` (`sub`
  after `normalize`) in `FiberDeclared` and `Equiv`; prove `fits_normalize`, `fits_subN` and
  `fits_join_left/right` along `hasTy_normalize`'s and `hasTy_join_*`'s proofs. Proved sufficient on
  a faithful copy of `Fits` (`fitsN_normalize`, `fitsN_subN`, `fitsN_join_left/right`,
  `amended_join_holds`, red control `tree_join_fails`; verifier's probe, rerun identical). Review
  the other comparisons of a declared type and use `subN` where the type is not chosen inside the
  derivation: `CompletionStrong.ofRefGet` (`Typed/Assembly.lean:40`) and its coarse twin
  `CompletionOk.ofRefGet` (`Typed/World.lean:81`), and, new at the merge, `FiberColumnsBelow` and
  `RacePayload` (`Typed/Scheduler.lean:55`, `:67`, `:69`) (reading). `asyncPre`'s deferred arm and
  `fiberPre`'s `awaitAll`/`raceAll` take certificates chosen in the derivation, so with
  `fits_normalize` they need not change (verifier, reading). The checker and the printed faces do
  not change; normalizing every checker type instead would change both (`NativeAtom.lean:21-25`).
  Positive control owed: `prog3` loads under the amendment, which reduces to one `TypedProg`
  derivation through `typedStateF_load`
  (`Test/Counterexamples/Machine/Semantics/ValueMembership.lean:984`; verifier, reading).
- *Which sites, which seat.* `Membership.lean`'s arms and `World.lean:81` are seat A's;
  `Residual.lean`'s entries seat B's; `Assembly.lean:40` and `Scheduler.lean:55`, `:67`, `:69`
  seat C's. Brief B's step 4 names "the completion entries", which sit in A's and C's files, and no
  brief names the three `Scheduler.lean` sites (§4.5).
- *Ruling and register.* Row 137 (owner; written 2026-10-01, ratification owed), which amends row
  96 D1 and re-reads host-boundary §4.4; `E4-TYPED-CE-009`. Seat A, with the Σ_app definitions
  that edit the same module.

**F2. Protocol postconditions are not fulfilled by their handlers.** (G6a confirmed; G6b
confirmed; G6c partly, with the verifier's three further rows and the frontier arm.)
- *What and evidence.* Each row below is proved at `dceae006` by a port of the seat's or the
  verifier's probe:
  1. Await by value (`Typed/Residual.lean:155`): the post reads the target's *answer* column; the
     checker types `awaitFiber t .awaitValue` at `pure (exitOf a e)` and the reference delivers the
     encoded exit (`HeadAwaitValuePost.post_excludes_delivered`, `await_code_refused`). Program
     level: `HeadAwaitLoad.typedState_load_false`, M5 false for the typed corpus's own
     `awaitFiber.value` (`Test/Program/TypedCorpus.lean:62`).
  2. `closeScope` (`:160`, "the answer is the argument exit"): with no finalizer the close
     program answers `success unit` (`HeadCloseScopePost.close_no_finalizer`,
     `post_excludes_answer`, `close_code_refused`).
  3. `closeIter` (`:160`): the walk answers its own merged exit (`HeadVerifyPosts.closeSeq_done`,
     `closeIter_post_excludes`).
  4. `scopeAdd`, `scopeRemove` (`:74`) and `deferredAwaitCleanup` (`:70`): the posts say `bool`,
     the store answers `unit` (`HeadStorePostAdequacy.*_post_excludes`, `admitted`,
     `next_untyped`, `store_step_leaves_typing`).
  5. `memoRelease` (`:81`): the post says `unit`, the last release answers the layer's scope handle
     (`HeadVerifyPosts.memoRelease_answers_scope`, `memoRelease_post_excludes`, `memo_admitted`,
     `memo_next_untyped`).
  6. `refModify`, `refModifySome`: the pre admits a cell at any type (`:43`), the post says `nat`
     (`:66`), and on a `bool` cell the machine answers a `bool` (`HeadVerifyPosts.adequacy_false_refModify`;
     tested, `VerifyScout2` rerun).
  7. The store frontier: when `syncOpStep` answers `none` the evaluator answers `unit`
     (`Laws/Program/EvaluateR.lean:304`), while the scope rows' pre is `True` (`:49`)
     (`HeadVerifyPosts.scopeIsClosed_unknown`, `scopeIsClosed_pre`, `scopeIsClosed_post_excludes_unit`).
- *The missing law.* Handler adequacy: the handler answers within each operation's post, the
  premise of Hazel's handler rule (de Vilhena 2022, read via the papers review §1.3). The
  2026-09-05 papers review proposed it as `Implements` (A2) and it never landed (proofs verifier,
  read). Post-Phase C §5.3 already requires "a postcondition must relate the actual operation to
  the actual answer" (reading). The admission census walked these rows on the post's answer, not
  the machine's (`Test/Program/AdmissionCensus.lean:112`, reading), so it could not see them.
- *Affects.* `typedState_load` (proved false through row 1); by reading, every `loop`/`deliver`
  arm of M6 that consumes these posts.
- *Amendment.* (a) Each post states the checker's rule for the operation's answer: await by value
  `∃ ty, w'.Γ target = some ty ∧ Fits w' ans (.exitOf ty.answer ty.error)` (the token rule row 106
  already rules); `closeScope` and `closeIter` `ExitOk w' (EffTy.pure .unit) ans` (an exit at
  `⟨unit, never⟩`, which is the proofs seat's "success or clean failure"); `scopeRemove` and
  `deferredAwaitCleanup` `ans = Val.unit`; `scopeAdd` `ans = Val.unit` or the reified closing exit
  typed as in R8; `memoRelease` what the store answers; `refModify`/`refModifySome`'s pre at the
  native row's declared cell type. (b) One adequacy obligation per row, store and fiber, declared
  beside the 18 command goals, stated once as a generic `Implements` for the protocol layer and
  instantiated per row, with the frontier arm excluded by the pre (scope liveness, R3) or covered
  by the post. The ported probes stay as red controls.
- *Ruling and register.* Row 136 (written; the posts follow the checker and row 106's token rule,
  so no new design); `E4-TYPED-CE-010` (M5 through await by value) and `E4-TYPED-CE-013` (the
  adequacy family). Seat B states the posts and the generic theorem; wave 2 proves the instances.

**F3. Saved frames and hook protocols are typed at one world, so an allocating step cannot keep
them typed.** (ALG-01, confirmed and strengthened; G2 partly, a duplicate.)
- *What.* `FrameAccepts` (`Typed/Contracts.lean:32-48`) types a frame's `run`, `skip` and `answer`
  clauses and its three hook premises at the one world the stack is checked at; so do
  `IteratorProtocol`, `LoopProtocol` and the async-finalizer clause (`Typed/Residual.lean:268-310`).
  World validity declares every heap cell, so an allocating step must move to a later world, and an
  exit that mentions the new handle falls outside the old clause. H1 and H2 left the stack clause as
  it was: `SavedPosition` keeps `StackAccepts` at one world (`Typed/Assembly.lean:89-93`, reading).
- *Evidence.* Proved: `HeadStepLoop.step_loop_refuted` refutes the merged `StepPreserves` for
  `.loop root false` at a concrete state: one running root fiber whose code is the denoted
  `Ref.make(5)` and whose stack is `.answer badNext` (answering `"x"` on every success), at the
  initial world, with `[loop root]` queued. Its premises are proved: the full merged `TypedState`
  with H1's scheduler, observer and registration conjuncts (`typed`), the nine-field `QueueOk`
  (`queue`), and `stuck = none`. After the step the root is not inert (`result_not_inert`) and no
  world types the machine (`post_untyped`). The seat's example command was wrong: `evaluate`
  allocates nothing (verifier's `evaluate_keeps`, proved at `ea5b28b5`). Wrapping the hook premises
  at the frame does not survive an iterator resume (`HeadKripkeWalk.output_not_kripke`).
- *Why no gate caught it.* The typed-state vocabulary has a Kripke `continuation` source
  (`Typed/Vocabulary.lean:32`) that no row of `Typed/Sources.lean` uses; the saved state is an
  opaque `.owner "SavedOk"` (`Sources.lean:31`); `guard_inv`'s docstring says a guard's typing is
  "exactly" `FrameAccepts.resume` (`Residual.lean:231-232`) though the guard arm quantifies over
  later worlds and the frame arm does not (verifier, reading).
- *Affects.* `M6Ledger.step_loop` (`Typed/Assembly.lean:278`), proved false; by reading, every step
  that grows a table `Fits` reads: `deliver` (fork and store operations), `launch` (race
  entrants), and `decision_preserves`. A park grows only the token table, which is
  `E4-SCHED-CE-016`'s family instead.
- *Amendment (statements; no runtime code).* (1) Quantify `FrameAccepts`'s `resume.run`,
  `resume.skip` and `answer.run` over later worlds: the Kripke-closed judgment is monotone with no
  premise and gives today's judgment at the current world (proved: `stackAcceptsK_mono`,
  `stackAcceptsK_now`) and refuses the bad frame (`bad_not_kripke_initial`). (2) Close
  `IteratorProtocol.step.next`, `LoopProtocol.step.next` and the async-finalizer cancellation
  clause under later worlds in their own definitions. (3) Restate `HookLaws`, `popR_typed`,
  `saveAnswerR_typed` and `deliver_active` over Kripke stacks (`popR_typed` concludes the one-world
  saved judgment today, `Typed/Stack.lean:133`, so the walk is re-proved; its arms are the same).
  (4) Declare `savedOk_mono` and `stackAccepts_mono` in `M3bWorld`, and world-monotonicity of each
  owner predicate of `preds` with freshness premises on the conditional lookups (`ResumeOk`, due
  completions, `HeapCell`). This strengthens row 48's contract (existential middles unchanged), is
  row 87's open question, and edits the same frame contract as row 117's pending amendment, so the
  two are written once.
- *Ruling and register.* Row 135 (written; it answers row 87 for frames); `E4-TYPED-CE-012`. Seat B.

**F4. The machine-level statements read the typed state at a budget cut, where the queue is
gone.** (G1 partly: the refutation stands, the seat's repair fails; the verifier's repair is
recommended.)
- *What.* `decision_preserves` (`Typed/Assembly.lean:332`) and `typedState_reachable` (`:350`)
  read `TypedState` at its default empty queue. `RReachable` (`:145`) includes the machine at a
  command-budget cut, where `stepDecisionState` drops the unfinished residue (`advanceState`'s
  `(d.1, false)`, `Machine/Fibers.lean:2080`; the loop at `:2139-2140`). H1's `CodeInert`
  (`Typed/Assembly.lean:84`) makes current code inert on a halted machine, when a `finish` is
  queued, or when the exit is published; at the cut none of these holds.
- *Evidence.* Proved (port of `StaleCode` and `VerifySplit`): on `E4-SCHED-CE-008`'s preempted
  catch with a timer (a host-free tape), at budget 6 the root is running, not exited, not halted,
  with an empty stack and a stale `Fail` in its code slot (`m6_root_running`, `m6_stuck_none`), so
  it is not inert (`m6_not_inert`) and no world types the machine (`window_untyped`); the capstone's
  proposition fails (`capstone_false_window`), and through the tree's replay lift `typedState_load`
  and `decision_preserves` cannot both hold at this program (`ledger_jointly_false_window`). H1's
  published-exit disjunct does cover the finished run at budget 9 (`m9_root_inert`), so the
  earlier finished-run refutation (verifier's `capstone_false_finished9` at `ea5b28b5`) is closed by
  the merge. The seat's split (no code typing in the machine predicate, row 133's clause in the
  configuration predicate) fails the tree's `DecisionLift.evaluate`, which derives the
  configuration predicate at the fresh queue `[evaluate id, drainDue]`
  (`seat_split_not_decisionLift`).
- *How narrow.* Tested at `dceae006` (`VerifyScout2`, `VerifyScout2Pairs`, `VerifyScout3`,
  `VerifyScout4` reruns): no settled replay result holds a running fiber (0 of 13,078 corpus, 0 of
  51,064 pair results); 0 untypable root windows among 4,640 at 105,051 corpus fuel frontiers;
  among 5,180 finished runs the root code-slot categories are `[3394, 5, 0, 1781, 0]` and every
  marker payload passes. The reachable stale slot needs U-01 plus a catch that removes the error
  column.
- *Amendment.* Row 134's split keyed on `running`: the machine-only predicate types the code of
  every fiber that is neither exited nor running; the configuration predicate types a running
  fiber by the queued command that continues it. In the merged vocabulary this is one more
  disjunct of `CodeInert` read at the empty queue: a running fiber that no queued `loop` or
  `deliver` continues is inert. At a decision boundary it exempts exactly the stranded fiber of a
  cut; inside the command loop a fiber whose `loop` or `deliver` is queued stays typed. Proved at
  the window: `running_exempt_at_m6` (and the verifier's `running_clause_vacuous_at_m6`). The
  generic lift needs no change: no settled result holds a running fiber (tested above), and `evaluate` on a running fiber
  is a no-op (`Machine/Fibers.lean:1849-1856`, reading), so a stranded fiber's code never runs
  again. That the whole decision-lift instance then goes through is reading; it is the M6 proof.
- *Alternatives.* A receipt-dependent lift (strong predicate at true receipts, weak at cuts;
  changes `Laws/Machine/Lift.lean`); or a capstone over replays that end at a true receipt (fuel
  frontiers excluded, so M7 would speak only of settled runs).
- *Ruling and register.* Row 134 (owner; written, ratification owed). It supersedes row 133's halt
  extension (plan O4): a halted machine is outside the machine-only predicate once row 139 puts
  `stuck = none` there. One supporting fact: the extension's own witness (`E4-SCHED-CE-020`) is a
  typed state holding a dangling scope (reading, `M6Capstone.lean:1582-1640`), which row 139's
  scope liveness excludes. `E4-TYPED-CE-011`, whose claim narrows to the cut: at the merged head
  the finished run is covered by H1's published-exit disjunct (`m9_root_inert`). Seat C.

### 3.2 Rigor

| Id | Gap | Evidence | Affects | Smallest amendment |
| --- | --- | --- | --- | --- |
| R1 | M5's real content is undeclared: the fundamental property `denoteR_typed` (every checker-typed point elaborates to a protocol-typed program) and term soundness `evalTerm_fits` | reading: no such declaration under `src/` or `Test/` (ALG-03, TY-07 confirmed); M5 is one `#proof_wanted` (`Typed/Assembly.lean:262`); the coarse twin `evalTerm_hasTy` exists (`Laws/Program/Typed.lean:971`) | M5 | row 148: declare both by name in the M5 ledger; land `fiber_inv` (proved in the types probes; the tree has `guard_inv`, `store_inv` only) |
| R2 | `TypedProg` is not closed under bind; a bind lemma with "no closing marker outside a guard body" is false | proved: `HeadBindGuard.bind_not_typed`, `guard_bind_not_closed`; the working tool is proved: `seq_typed` with `close_typed` (ALG-04 partly) | M5's induction | row 148: the per-construct compatibility family (`seqR` first) is the sequencing tool (seat E lands `seq_typed` from the port) |
| R3 | "Never halts" does not follow from the typed state: it holds no scope liveness, no race-id liveness, no typed scope on a queued `link`; H1's halt extension makes a halted machine's current code inert, so halting does not break the typed state, and its own witness (`E4-SCHED-CE-020`) is a typed state with a dangling scope | reading: `HandleFits`'s scope arm checks only the spelling (`Membership.lean:52-58`); `fiberPre` is `True` at `raceRegister`/`cancelRace` (`Residual.lean:133`); scope rows' pre `True` (`:49`); `CodeInert`'s halt disjunct (`Assembly.lean:84-85`); `StepPreserves` takes `stuck = none` only as a premise (`:180-182`); the witness `M6Capstone.lean:1582-1640`. G4 (partly: already a plan requirement, post-Phase C §6 I) | row 52's corollary; M7 | row 139: the typed state carries scope liveness (the scope arm reads the scope store), race-id liveness where a code names a race, and a typed scope on queued `link`; `StepPreserves`' conclusion adds `r.1.stuck = none` (each command proof shows its halting arms unreachable), or separate no-halt goals; the no-halt conclusion declared (row 138) |
| R4 | M7 is undeclared; its only bridge (`replay_rel`, `run_eq_ref`) holds at the empty host table and empty oracle, while R1 asks every milestone statement to take Σ_app; the table-aware statement (DI-57) is filed without proof and parked | reading: `RuntimeR.lean:197-216`; `Test/contracts/machine-scheduler-core.contract.md:87`; system map §8 R1, R6; proofs R1 and the organization verifier's M3 | M7 | declare M7a (every recorded exit `ExitOk` at Γ, through `replay_rel` and `BMeans.exitOf`), M7b (never halts), M7c (no shape defect, part one) now, on answer-free tapes, observation `obs`, "the frame machine", with row 138's table premise (R1's exception); one bridge lemma from `replayR` machines to `Guard.Reachable` native machines at the empty table so the guard's code-free facts transport through `BMeans` (proofs R4, reading) |
| R5 | `M3bWorld.typedProg_mono` is open and holds | proved: `HeadTypedProgMono.typedProg_mono_ledger` (the ledger's binder order), with `storePre_mono` (all 31 store rows) and `fiberPre_mono` (all 40 fiber rows) (ALG-02 confirmed) | M5, M6 | row 135: land it, replacing the `#proof_wanted` at `Residual.lean:455` |
| R6 | Σ_app and lawful sources are absent from the M5–M7 statements | reading: `ProgramSource` has only program and table (`Typed/Admission.lean`); proofs verifier's missed item 9 (rows 111–112) | M5–M7 | the Σ_app slice as ruled (rows 111–116); M5–M7 quantify over lawful sources; `TypedState` ties `w.serviceTy` to the source |
| R7 | The ledger does not mirror the decision lift's thirteen fields | reading: `Laws/Machine/Lift.lean:308-355`; the lift seat's `M6Edits` (proofs R3 confirmed) | M6b | row 140: declare the outside-loop edits and the snapshot fact as obligations, over the amended machine predicate (F4), not today's |
| R8 | Refused source positions are consumed as `True` | reading: `Typed/Sources.lean:29`, `:53-54`; `StoresOk.c5 : True`; `capture_lookup`'s exit premise (proofs R2 confirmed; post-Phase C §5.1 item 5) | `loop` at `scopeAdd` on a closed scope | row 140: un-refuse the closed-scope exit position with `Fits … (exitOf unknown unknown)`; keep `externals` refused while the host lane is parked |
| R9 | Row 117's contract is coeffect soundness, not transport | proved at `ea5b28b5` and rerun here: `FrameCategory.exitOk2_transport`, `exitOk2_transport_refuted`, `requirement_condition_fails` (G5 partly: not new; a design input) | H2 part two | row 117 as amended 2026-10-01 (owner): a presence clause per position (the context provides the position's requirement row); a requires-monotone side condition on non-discharging frames; the restored context at `scopeExit`/`release` provides the outer row; positive controls for `.scoped` and provision; `E4-TYPED-CE-008` stays the red control |
| R10 | Two exit judgments under one name: the meaning-level `Denote.ExitOk` (`Laws/Program/MeaningSound.lean:324`) and the typed state's `ExitOk` (`Typed/Admission.lean:30`) | proved (rerun): the connector `exitOk_of_fitsExit` holds under two premises, each necessary (`redA_scope`, `redB_external`) (ORG-11 confirmed); the two coexist by overload resolution (tested on stand-ins, `verify-ExitOkOverload` rerun; the merged library, built by the coordinator, holds both, reading) | coherence of the exit judgment; M7 on the straight fragment | row 141: rename the meaning-level one to `Denote.ExitHasTy` (no deadline: H2 landed); land the connector; its scope premise is R3 |
| R11 | Inhabitance has no fold, no agreement theorem, no admission clause | proved (rerun): `inhabited_of_fits`, `inhabited_of_hasTy`, `fits_of_inhabited_handleFree`, `inhabited_sub`, the three handle witnesses, `handle_inhabited` (verifier); the DI-67 red controls (TY-03 confirmed; TY-13, TY-14 partly) | row 127; DI-67 | row 127 as amended: `inhabited` as a `TyAlgebra` fold; amalgamation and invariance under `normalize` owed; `admitColumn` at every answer, error, request and table column with its own refusal name (for example `emptyColumn at`), keeping the frozen `AdmitRefusal.uninhabited` for the `int` scan (`Test/contracts/foundation-wave2.contract.md:217-219`); brief A renames it instead, which changes DI-67's ruled text and a frozen contract: row 149 |
| R12 | K2 exactness of `ofSchema` and the JSON codec: false today, and their normalisers are not functions | tested (rerun): V1a, V2; proved generically: `readExact_*`; tested: the guard at `N = id` refuses a key-permuted image that the frozen codec contract requires (`Test/contracts/schema-codec.contract.md:26`), the key-order guard keeps it and refuses V2 (TY-09 confirmed, TY-18 partly) | row 128; row 123 | name `N_S` and `N_J` as functions and prove `read` invariant under each; any guard is taken modulo `N_J` (key order), never `id`; or exactness by construction (the decoder selects the encoder's canonical branch; `ofSchema` compares whole checks and refuses `TypeParameter`) |
| R13 | The signature-extension definitions are missing | reading: `SigExtends`, `SigProgram`, `LawfulSig`, `π` absent; `admitProgram`'s last arm invents a key (`Program/Admission.lean:169`) (TY-04, TY-05, TY-20 partly) | R2 (C3, C4, C6) | define them in `Laws`; `LawfulSig` as `Forall Local ∧ Pairwise Compatible` plus a third clause shape for "every required key typed"; C3 reflection by one generic fold congruence (R2Probe §E already proves it on `Looped`); prove `Table.lawful t = false → Table.checkLawful t ≠ none` and delete the invented key; `typedProg_rows_append` as row 116's positive control |
| R14 | The traversal census cannot measure its own rule | tested (rerun at `dceae006`): it misses well-founded definitions (`Ty.sub`), private ones (`Codegen.Types.ofNormalized`, `Representation.beq`, `Check.beq`) and one-level matches compiled through shared sparse `casesOn` helpers (for `Ty`: 2 counted, 12 missed) (ORG-04 partly; verifier M1) | AGENTS.md's "a hand match is an exemption the census lists by name" | about fifteen lines in `Laws/Auto/Traversals.lean` (follow compiler helpers, accept `WellFounded.Nat.fix`, admit private names, recognise sparse `casesOn`); row 143: the census document's §1 decides whether a one-level match counts (recommendation in §6) |
| R15 | Erasure agrees with the machine only for continuations that pass skipped exits through, and `denoteR_straight` relies on it silently | reading: `DenoteR.lean:105-111`, `:47-49` (verifier ALG-12) | `denoteR_straight` | state the invariant as a lemma, or list it in the census |
| R16 | Beyond M7: no carrier for divergence and fairness; no per-form behaviour law; no stuttering simulation | reading (ALG-13, ALG-10; system map R10, R12) | R10–R12 | when R12 opens: a run of a decision stream as the chain of its prefixes through `replayEval_append`, divergence as every prefix ending at a frontier with work runnable, fairness on streams with `FairTape` its finite restriction; per-form laws as equations of the form's theory |

### 3.3 Tidiness

Each is a few lines and changes no statement. The landing seat that owns it is in brackets (§7).
- **Vocabulary (row 128).** `AGENTS.md:73-80` still lists `Ty.schema`/`ofSchema` and the JSON codec
  as exact embeddings, lists "the Conform rungs, the truth lane" as simulations (both are finite
  differential checks of a simulation statement), and omits `run_eq_ref` (ORG-05, ORG-06
  confirmed). [coordinator: `AGENTS.md` is coordinator-only in plan §4; row 128 says "now", the
  plan says wave 3]
- **Faces in the system map.** §5's K4 row names the tactic `authoring_scoped` and the totality fact
  `open_total` and omits `admitProgram_certificate`/`admitted_unique`; K2 omits the byte codecs and
  `Config.Val`; K3 omits `Refines`/`Projects` and the book; K4 has three labels (ORG-07, ORG-08
  confirmed). [coordinator]
- **Glossary** (§5 of this note) into the system map as §9; the three senses of "signature" named
  (ORG-13). [coordinator]
- **"K1–K5" collision.** `docs/DESIGN-ISSUES.md:51-66` uses K1–K6 for obligation kinds; rename them
  O1–O6 (ORG-09). [seat F]
- **Register.** Header says 138 live and 260 archived rows; the tree has 146 and 281 (tested); define
  REPAIRED and RETIRED; register row 127's DI-67 counterexample; row 2's status after row 119.
  [seat F; row 2 is the coordinator's]
- **Stale texts** (ORG-22–26 confirmed, ORG-24 partly; tested at `dceae006` where marked):
  `Test/Audit/AxiomGate.lean:29-31` (the warning sentence; tested still present);
  `Program/Provision.lean:120` ("join associativity owed"; `Ty.join_assoc` is proved) and `:162`
  ("adjunction"); `Machine/Context.lean:7-12` ("Deep spike … `Deep.Context`"); `AGENTS.md:21` (the
  baseline as a compatibility gate's input; the comparator was deleted at `243ca0dd`) and the
  gate sentence ("declaration" should read "module"); `Test/Schema/SubAlphabetContract.lean:97-98`;
  contract packets citing deleted falsifiers (`environment-context-key.contract.md:517`, `:525`;
  `faces.contract.md:28`; `schema-payload.contract.md:89`, `:180`, `:404`; the row-39 fallout in
  `schema-codec` and `schema-recursor`, the three effectful-field packets already retired at
  `dceae006`); `docs/core/traversal-census.md:72` ("16 constructors"; `Ty` has 20);
  `docs/core/coherence-principle.md:63` and its rows 12, 15, 16, 18 and literature names at
  `:76-84`, `:144`; `docs/GENERATED.md` (the groups table and "the compatibility snapshot");
  `docs/STATE.md` lines the organization seat lists; `decisions.md:1`, `:75`, `:263-266`. README
  lines are the owner's (AGENTS.md). [seats F and E; `AGENTS.md`, STATE and decisions to the
  coordinator; `GENERATED.md` is seat F's item 7]
- **Names that resolve two ways** (ORG-12 partly): `Program.Fits` (environment fits) against
  `Typed.Fits`; `Ty.Canonical` against the `Canonical` class; `Api.Typed` against
  `Laws.Effects.Typed`; `Denote.ExitOk` against `Typed.ExitOk` (R10). `Typed.World` *extends*
  `Machine.World`: row 141 renames the parent `HandleWorld` in wave 3, and the glossary names the
  extension either way. [row 141: seat F for `ExitOk`; wave 3 for the rest]
- **The census document** names five `Ty` traversals that came with the template calculus
  (`Ty.closed`, `Ty.instantiate`, `Ty.infer`, `Ty.varsOf`, `Ty.templateAdmissible`), `Ty.sub` and
  the three private ones; counts at the landing commit (ORG-03 partly). [seat F]
- **Guard lift redundancy.** `SingleGuard.held_driveState` is one application of
  `driveState_lift_unit` (proved, rerun); the six decision-level inductions need a narrower lift
  first (ORG-18 partly). [seat F]
- **Ledger slack.** Twelve `#typed_state_obligations` commands carry a ceiling above their open
  count, 28 slots (ORG-20 confirmed). [seat F]
- **The core root and the `Effects` package.** At `dceae006` only `Machine/Context.lean` in the core
  root imports it (tested), for a service-program model nothing references (ORG-17 confirmed). [seat F]
- **Provision laws.** Land `provideMerge_assoc` and the error column of `provide_provide` (proved,
  verifier). [seat E]
- **Laws the basis can cite** (optional): P1's coproduct, P3's tape action and `behaviour_unique`,
  P4's limit and comodel laws; promote the pedigree's `inr_iff`, `typed_along`, `c4_iff` rather
  than P6's copies (ALG-05 partly). [seat E]
- **Controls in the library.** `World.lean`'s `worldGood`/`worldBad`/`heapNotMonotone` and
  `Contracts.Example` belong under `Test/` (proofs T3). [seat C, with A and B listing theirs]
- **Smaller.** Two heap typings (`WorldValid.cells` coarse, `preds.HeapCell` strong; the deferred
  table likewise) (TY-08); the comment at `Laws/Program/Template.lean:332-333` (`decide +kernel` does
  evaluate `sub`; the tree already does it) (TY-15); name `subN` and record that atom arguments use
  raw `sub` (TY-02 partly); `Codec.layout`'s identity catch-all gets a record arm in row 119's
  checklist (ORG-31 partly); the host generated groups have had no fixed-point run since slice 6:
  the next sweep runs `make check-gen-full` (ORG-15).

## 4. What changes in the briefs

Nothing here redesigns. Each item is an amendment to a brief that exists or is about to be
written, in the order the briefs will meet them.

### 4.1 The M5–M7 brief (seats A, B, C, then wave 2)

**Statements.** The statement changes land in wave 1b, before any M5 or M6 proof: seat A (values,
the signature, inhabitance), seat B (frames, posts, the walk), seat C (the assembled state, M7,
the ledger). Their declarations, in the tree's own vocabulary, with the row that rules each:

```text
-- F1, row 137 (seat A; the entries in other seats' files as F1 lists)
FiberDeclared w id a e := ∃ fty, w.Γ id = some fty ∧ subN fty.answer a ∧ subN fty.error e
Equiv d t := subN d t ∧ subN t d                       -- RefDeclared, PromiseDeclared
fits_normalize : Fits w v (normalize t) ↔ Fits w v t
fits_subN      : subN a b → Fits w v a → Fits w v b
fits_join_left : Fits w v a → Fits w v (Ty.join a b)   -- and fits_join_right

-- F2, row 136 (seat B states; wave 2 proves the instances)
fiberPost w' (.await t .awaitValue) _ ans := ∃ ty, w'.Γ t = some ty ∧ Fits w' ans (.exitOf ty.answer ty.error)
fiberPost w' (.closeScope _ _) _ ans      := ExitOk w' (EffTy.pure .unit) ans     -- closeIter likewise
storePost w' (.scopeRemove _ _) _ ans     := ans = Val.unit                       -- deferredAwaitCleanup likewise
Implements Ψ step := ∀ w op cert st st' ans, Ψ.pre w op cert → step op st = some (st', ans) →
                       ∃ w', w.leHost w' ∧ Ψ.post w' op cert ans                  -- plus the `none` arm
#proof_wanted storeRows_adequate, fiberRows_adequate (one goal per row)

-- F3, row 135, answering row 87 (seat B): frames and hook protocols at every later world
FrameAccepts w tin tout (.answer next) needs ∀ w', w.leHost w' → ∀ ex, ExitOk w' tin ex → TypedProg w' tout (next ex)
IteratorProtocol, LoopProtocol, asyncFinalizer: their `next`/cancellation clauses ∀ w' ≥ w
stackAccepts_mono, savedOk_mono : in M3bWorld; popR_typed, saveAnswerR_typed, deliver_active over Kripke stacks

-- F4, row 134 (seat C): the split keyed on `running`, written as inertness at the empty queue
CodeInert m q p := TerminalPosition m q p ∨
                   (p names a running fiber ∧ no `loop`/`deliver` for it in q)
-- the halt disjunct goes (row 134, plan O4): `stuck = none` is in the machine-only predicate (row 139)

-- R3, rows 139 and 52 (seat C): never halts
StepPreserves … concludes also  r.1.stuck = none
TypedState carries scope liveness (HandleFits' scope arm reads the scope store), race-id liveness,
  a typed scope on queued `link`

-- R1, row 148 (seat C declares; seat A proves `evalTerm_fits`)
#proof_wanted denoteR_typed : PointTyped src w p ty → TypedProg src w ty (denoteR src.program src.program p)
#proof_wanted evalTerm_fits : EnvTyped w env vals → termTy sig env t = some ty → evalTerm vals t = some v → Fits w v ty
fiber_inv (landed from the types probes); typedProg_mono (landed, R5)

-- R4, row 138 (seat C): M7 declared now, with R1's row-table exception
M7a : root.table = [] → typeOf … = some rootTy → ClosedEff rootTy → ∀ k tape, (∀ d ∈ tape, NoHostAnswer d) →
      ∃ w, ∀ id ex, exitOf (Api.replay root.program k tape) id = some ex → ∃ ty, w.Γ id = some ty ∧ ExitOk w ty ex
M7b : … → (Api.replay root.program k tape).outcome ≠ .stuck _
-- observation `obs`; "the frame machine", not the OCaml engine (row 28 decides that stage)

-- R7, row 140 (seat C): the decision lift's outside-loop edits and its snapshot fact, as
--     declared goals over the amended machine predicate
```

**Proof route** (the proofs seat's §4, as its verifier corrected it):
1. The induction principle is the lift family: each command is `StepKeeps` over the configuration
   predicate (the H1 adapters already state this, `Typed/Assembly.lean`); each decision is
   `stepDecisionState_lift` over `DecisionLift`; the capstone is `replayEval_lift` from M5. The
   frame law `driveStep_append` handles every residue suffix. No hand induction over fuel, rounds
   or tasks.
2. Handler adequacy per protocol row first: it feeds every `loop` arm.
3. Values only through `Fits` lemmas (the guard sentence below). Stacks only through the category
   laws (`stackAccepts_append`, `stackAccepts_split`) and the Kripke closure.
4. Bookkeeping by relative induction: the guard family's facts about tokens, owners, races and
   registrations are proved once on native reachable machines and transported to the reference
   through `BMeans` by one bridge lemma (R4), not re-proved on the reference.
5. M5's `denoteR_typed` by induction on the addressed source with the checker's inversion lemmas;
   sequencing by the `seqR` compatibility lemma (`seq_typed`), never by a general bind (R2).
6. Red controls stay as fixtures: every probe this pass ported (Appendix A; tracked) refutes today's
   statement, is kept as an `Old*` fixture the way `M6Capstone.lean` keeps H1's, and none may
   refute the amended statement.

**The guard sentence (row 132).** "No case analysis on `Ty` outside
`Laws/Program/Typed/Membership.lean`: a value fact in the typed state goes through a `Fits` lemma
(`fits_mono`, `fits_subN`, `fits_join_left/right`, `fits_normalize`, `fitsExit_*`, `await_fits`),
never through raw `Ty.sub` or a `match` on `Ty`. It is checked by an environment probe that
follows compiler-made helpers transitively (red controls `Typed.Fits` and `Ty.isFactor`), not by
grep." The rule holds at `dceae006` (tested, `verify-TyCasesDeep` rerun: under
`Laws/Program/Typed/` person-written `Ty` case analysis is in `Membership` only; the new
`Scheduler.lean` has none). The check must use the transitive probe: the simpler one misses a
`match` compiled through a sparse `casesOn` helper of another module (organization verifier).
The sentence's second half, "never raw `Ty.sub`", needs row 137 first; until then the typed state
compares declared types raw at the sites F1 lists.

**Order** (the plan's waves, which this note confirms, with the corrections of §4.5).
1. Ratifications owed: rows 134, 137, 138 (the row-table exception), and 135, 136, 139 as the plan
   records them; row 149 (§6) before seat A's step 6.
2. Wave 1 (seats E, F, H): the lemma landings, the instrument and registers, the basis. Seat F's
   register rows cite the tracked ports, which elaborate at the merged head (§4.5).
3. Wave 1b (seats A, B, C, in parallel by file ownership): each first re-establishes its
   counterexamples on the merged tree as an `Old*` battery (the ports are ready), then lands its
   statements. Seat B's `Residual.lean` entries wait for seat A's `Ty.subN`.
4. Wave 2: per-row adequacy; stack monotonicity (`typedProg_mono` is already proved); M5's
   `denoteR_typed`, then M5; the easy commands (`evaluate`, `trackChild`, `exitDone`, `wake`,
   `drainDue`, `resume`); `finish` and `observe`; the race commands; `deliver` and `loop` arm by
   arm in post-Phase C's family order; the decision edits; the capstone by `replayEval_lift`; M7a,
   M7b; part two after row 117.

### 4.2 The Σ_app slice (rows 111–116; seat A)

- Land F1 (row 137) in the same edit of `Membership.lean`, which both touch (the types seat's
  recommendation), with the `subN` review of the raw comparisons of a declared type that F1 lists.
- Measure the audit's 27-site inventory first (audit §3), as its first check.
- `LawfulSig` as `(∀ e ∈ Σ, Local e) ∧ Σ.Pairwise Compatible` plus a third clause shape for "every
  required key is typed", which points from rows to services and is monotone under append (TY-05
  partly). Prove `Table.lawful t = false → Table.checkLawful t ≠ none` and delete the invented key
  (`Program/Admission.lean:169`).
- `SigExtends`, `SigProgram` (the reads the checker's algebra makes of the signature) and `π`
  (restriction of the static service table) in `Laws`; C3 reflection by one generic fold
  congruence, citing R2Probe §E, which already proves it on `Looped`; `typedProg_rows_append` as row
  116's positive control.
- Red controls kept: `prepend_not_extends`, `shadow_not_extends`, `typedProg_not_table_monotone`,
  `one_code_two_carriers`, `not_fits_join` (it flips to its positive form under row 137), and
  `HeadM5Fits.m5_false` kept as an `Old*` fixture against the raw-order `Fits`.
- Positive control: `prog3` loads into a typed state under row 137 (one `TypedProg` derivation
  through `typedStateF_load`; owed).
- Wording for DB-01: C1 is the identity for Σ_app (rows and keys are data); the free-monad
  injection laws are C1 for Σ_core's denotation signatures, not for Σ_app.

### 4.3 The data brief (rows 119–128)

- **Row 119, records (stage 1).** Acceptance items: raw `sub` at records compares canonical name
  lists, with the positive control "a permuted record is raw-below its normal form"; a theorem
  `record_sub_not_complete` beside `sub_not_complete` (records are not distributed over union
  fields); the record arms of `inhabitedAlg` and `Fits` after row 137 (with records, F1 gains a
  second entrance through field permutation: `raw_not_invariant`, proved on the types seat's
  model); one field-order normaliser shared by `normalize`, `N_S`, `N_J` and `Shape.struct`;
  `Codec.layout` gains a record arm; the width projection's law stated at the adapter
  (`fits_coerce`'s shape) and width refused by name inside a program, with a red control.
- **Row 128, exactness (stage 1's second commit).** `N_S` and `N_J` as functions; `read` proved
  invariant under each; a guard, if chosen, is taken modulo `N_J` (key order), never `id`, because
  the frozen codec contract accepts key-permuted objects (tested). Or exactness by construction.
- **Row 127, inhabitance (seat A).** The fold and its theorems as R11 says; `admitColumn` with its own
  refusal name; the frozen `AdmitRefusal.uninhabited` stays the `int` scan's (row 149's
  recommendation); `Row.wellScoped` for supplied rows joins C6's local clauses.
- **Row 122, the boundary route (no seat in the plan; §4.5, §7).** host-boundary §4.4's "exactly
  the declared type" becomes "equal normal forms" once row 137 is ratified; the reply-to-`Fits`
  bridge stays parked with the host lane.
- **Row 123, the in-program decode.** It needs row 128's exactness first: with an inexact decoder
  the program-facing operation is an observable face divergence (V2: rc.112 reads one image as an
  `Exit` success, Lean re-encodes the value as a `Result` failure).
- **Row 124, recursive types.** Subtyping coinductive or nominal, inhabitance a least fixed point
  (Amadio and Cardelli 1993; TATA; by name). Nothing now.

### 4.4 The DESIGN-BASIS refresh brief (`docs/research/2026-10-01-design-basis-refresh-brief.md`; seat H)

- **Inputs:** add rows 119–133 (ruled 2026-10-01), rows 134–148 (written 2026-10-01; each marked
  as its status cell says), and this note's §2 and §5. The glossary's home is system map §9; DB-16
  and DB-17 link to it.
- **DB-01:** C1 is vacuous for Σ_app; growing Σ_core is hierarchy-consistent, not a persistent
  extension (a new constructor adds elements to an old sort), so DI-47's finite gate is the chosen
  form of the statement, not the only possible one; free sums are coproducts of free monads
  (`sum_is_coproduct`, a probe, not in the tree until seat E lands it); sums of theories with
  equations are Hyland, Plotkin and Power 2006, by name only.
- **DB-03:** tapes act on machines (`replayEval_append`, a probe); `behaviour_unique` is the
  uniqueness half of finality; "equal observations imply equal runs" is injectivity and is not
  claimed; divergence by compatible prefixes has no carrier yet (R12).
- **DB-04:** say "the Kleene chain of the least fixed point", not "Elgot pedigree": Elgot's
  fixpoint law, leastness and single-valuedness hold at the limit (`conv_*`), never at one budget
  (`budget_not_fixpoint`); budgets are not CompCert's measure.
- **DB-05:** the honest boundary in formal terms: the store is a lawful comodel of state on live
  cells; the machine is not a runner past the first fiber operation; correct the model-probe
  synthesis's level-3 row.
- **DB-16:** must not record the one-world frame judgment as settled (F3). Record: `TypedProg` is
  world-monotone (proved; lands as R5), its own inductive sharing the protocol shape; `Fits` is the
  value interpretation of a Kripke model for first-order references; the typed state is not upward
  closed; `TypedProg` is not bind-closed (non-local exits); handler adequacy (F2) is the missing
  half of the handler rule; cut tolerance (F4).
- **DB-17:** the free bounded join-semilattice with relative complement; `provide` as
  substitution; requirement rows as a grading, worded as a flat coeffect (what the context must
  provide); satisfaction is inclusion into the key row, not an adjunction; `provideMerge`
  associativity proved; `build_total`'s cut and its restoration under R5 (G removed the stale
  header at `0c534f06`).
- **DB-15:** records row 119's ruled design and row 127's repair; the slice still waits for M5–M7
  (ORG-30 confirmed).
- **DB-11:** value typing is rows 44, 96 and, once ratified, 137.
- **Bibliography:** carry the corrections of §1's list (ornament, finality, Jacobs ch. 3 for
  bisimulation, the CompCert measure, persistency, the lattice claim, "Kripke" for the typed
  state, Freyd and ghost tokens as analogies). A theorem from this pass is a probe, not a tree
  witness, until a landing seat lands it.
- **Brief H's addendum, one line:** "no step-indexing because values carry no code" gives the
  looser reason; the one that matters is that worlds hold syntactic types which the handle arms
  read as declarations, so the world is not defined through `Fits` (types verifier, TY-19 (c)).

### 4.5 Corrections to the landing plan and briefs (`docs/research/2026-10-01-landing/`)

The coordinator wrote rows 134–148, a plan and briefs A–H while this synthesis was in progress,
and seats A, B, E, F and H have started (their branches, read by `git log` from the main checkout:
`seat/A` at `bbed898d`, `seat/B` at `eb3ab9a9`, `seat/E` at `d106073e`, `seat/F` at `709181d0`,
`seat/H` at `1efb963e`; `seat/C` still at `bb269fde`). They agree with this note on every
fundamental finding. These are the places where they need one line each, checked against the
merged tree; each is addressed to the seat that owns the step:

1. **`E4-TYPED-CE-011` and brief C step 1: the finished-run refutation does not survive the
   merge.** At budget 9 the root has exited, so H1's published-exit disjunct makes its stale code
   inert (proved, `HeadCut.m9_root_inert`); `capstone_false_finished9` cannot be restated by the
   stale-code route. Only the cut (budget 6) is a live refutation (`HeadCut.window_untyped`,
   `capstone_false_window`, `ledger_jointly_false_window`). The register row's claim should say "at
   a budget cut", and brief C's list should drop `capstone_false_finished9` (it stays as history at
   `ea5b28b5`).
2. **Plan §2's witness paths are probes that no longer elaborate** (the coordinator's own rerun
   note, `formal-pass/rerun-on-0c534f06/README.md`). Seat F's register rows should cite the tracked
   ports, which elaborate at the merged head: `HeadM5Fits` (`-009`), `HeadAwaitLoad` and
   `HeadAwaitValuePost` (`-010`), `HeadCut` (`-011`), `HeadStepLoop` and `HeadKripkeWalk` (`-012`),
   `HeadStorePostAdequacy`, `HeadCloseScopePost`, `HeadVerifyPosts` (`-013`), and for `-015` the
   tracked data-probe `pedigree/verify-Probe.lean` V3 with `types/InhabitedProbe.lean` (both
   elaborate at the merged head, tested). Seats A, B and C can start their step 1 from the same
   ports.
3. **Raw-order sites no brief owns.** Row 137's comparisons in `Typed/Scheduler.lean:55`, `:67`,
   `:69` (new at the merge) and `Typed/Assembly.lean:40` are in seat C's files; `Typed/World.lean:81`
   is seat A's. Brief B's step 4 assigns "the completion entries" to seat B, whose files do not hold
   them. Add the four C sites to brief C and the World site to brief A.
4. **Row 122 has no seat.** Writing Decision 12 and the 2026-09-10 boundary rule into
   `docs/core/host-boundary.md`, force-adding the two 2026-09-10 notes, and moving DI-08 to ruled
   appear in no brief. Seat F already owns `docs/DESIGN-ISSUES.md` and force-adds untracked
   rulings; add host-boundary.md to its scope, or the coordinator writes it.
5. **Row 128 says "amend the vocabulary now"; the plan puts it in wave 3.** `AGENTS.md:73-80` is the
   coordinator's file (plan §4); its text is §3.3's vocabulary item with §5's K1–K5 and embedding
   rows, and it can land now: it changes no statement.
6. **Brief A step 6 renames a frozen refusal.** The `int` scan's `AdmitRefusal.uninhabited` is named
   in DI-67's ruled text and in `Test/contracts/foundation-wave2.contract.md:217-219`. Renaming it
   needs the owner and a contract revision; naming the new emptiness check differently (for example
   `emptyColumn at`) needs neither (types verifier, TY-13). Row 149 (§6).
7. **Brief B's close-scope post, made exact.** "A success or a clean failure" is
   `ExitOk w' (EffTy.pure .unit) ans`, the checker's type for the close program; whether a
   finalizer can fail with a typed reason is what the adequacy instance must show (proofs verifier,
   G6b).
8. **Brief E item 1's red control does not elaborate at the merged head.** P6's
   `typedProg_not_bind_closed` fails on the `ExitOk` change (rerun, exit 1); the same fact, restated,
   is `HeadBindGuard.bind_not_typed` and `guard_bind_not_closed` (proved), which item 7 lands.
9. **Brief E item 8's header is already half done.** G removed the `build_total` sentence from
   `Program/Provision.lean`'s header at `0c534f06`; "owed under R5" may still be added, and the
   "owed" at `:120` and the "adjunction" at `:162` remain.
10. **Seat C's reachability bridge and halting.** With row 139's `stuck = none` in the machine-only
    predicate, the `HaltTyped` facts flip as brief C says; at the merged head they hold by design
    (`CodeInert`'s halt disjunct), so the battery records the old and new statements side by side.

## 5. The glossary

The organization seat's table (its §5), corrected by its verifier and by the other seats'
verifiers, sites at `dceae006`. **Home: a new §9 of `docs/core/system-map.md`** (row 142; the map owns
the vocabulary's definitions, `AGENTS.md:60-61`); DB-16 and DB-17 link to it rather than copy it.
The coordinator carries it (the system map is the coordinator's file, plan §4), with the marks
kept, and checks every site with a probe like the organization seat's `GlossarySites.lean` at the
landing commit.

| Tree name (site) | Literature name, in one line | Mark | The law that makes it that thing | Correction applied |
| --- | --- | --- | --- | --- |
| `Eff` (`Program/Eff.lean:264`) | initial algebra (term algebra) of a binding signature; variables are positions | by name (coherence principle: GTWW 1977; Fiore, Plotkin, Turi 1999) | `hom_eq_cata_eff` (`Program/Fold.lean:1270`), `cata_build`, `build_view` | — |
| `cataFam`, `cata_eff` (`Program/LayerView.lean:414`; `Fold.lean:1104`) | catamorphism, the unique algebra map out | by name (MFP 1991; Hutton 1999) | `hom_eq_cata_eff` | `fold_of`'s pairing is a paramorphism (Meertens 1992, by name) |
| `Program S` (package `Algebra/Program.lean:33`) | free monad on a signature | read (Plotkin and Pretnar §1, §5, lit-papers Q11) | `program_is_free` (`Algebra/Universal.lean:98`) | — |
| `Signature Op` (`Program/Typing/Rules.lean:47`) | the typed presentation of an effect signature: arities and coarities, atom types, service carriers, domain | by name (operation signatures, Plotkin and Pretnar, read via Q11) | `check_sound`, `check_complete` over every signature (`Laws/Program/Typing/CheckSound.lean:37`, `:361`) | "signature" names three things: the syntax signature (`binders.json`), the language signature Σ = Σ_core ⊕ Σ_app (§1.1), and this typing view built by `nativeSignature` (`Program/Native.lean:316`) |
| Σ_app, `RowTable` (`Program/Native.lean:82`) | the application's signature as data: operations by position, service constants sorted by their code | by name | owed: C1–C8 (rows 111–116) | C1 is the identity for Σ_app |
| `Ty` (`Program/Ty.lean:37`) | initial algebra of a ground signature: first-order types with unions, literals, a top and a bottom | by name (TAPL ch. 15–16) | `sub_refl`, `sub_trans`, `sub_antisymm_canonical`, `normalize_idem`, `sub_not_complete` | — |
| `subN` (not yet named; read at `Typing/Rules.lean:114-117`, `HasTy.lean:186-187`) | the checker's order: `sub` after `normalize`; its kernel is equality of normal forms, so `Ty/≡N ≅ CTy` | standard | `subN_equiv_iff` (probe) | name it; atom arguments use raw `sub` (TY-02 partly) |
| `CTy` (`Program/Ty.lean:842`) | bounded join-semilattice; `join` is the least upper bound | by name (TAPL §16.3) | `instIsPartialOrder`, `instLawfulOrderSup`, the join laws (`Laws/Program/TypeAlgebra.lean:1096-1121`) | meets are not claimed; "not a lattice" dropped (TY-17 partly) |
| `inhabited` (owed, row 127) | the emptiness test of a regular tree type, a fold | by name (TATA) | `inhabited_of_fits`, `inhabited_of_hasTy` (probe) | — |
| `Fits` (`Laws/Program/Typed/Membership.lean:87`) | the world-indexed value interpretation `V⟦τ⟧(W)` of a Kripke model for first-order references; a store typing | by name (TAPL §13.4; Ahmed 2004; Ahmed, Dreyer, Rossberg 2009) | `Fits.eq_cata`, `fits_mono`, `fits_sub`, `fits_hasTy` (type erasure to `Val.hasTy`), `fits_live` | "logical relation" is loose (no arrow clause); no step indexing because worlds hold syntactic types read as declarations; `Effect4.Program.Fits` (`Laws/Program/Typed.lean:309`) is a different judgment (an environment fits pointwise): rename it `EnvFits` |
| `World` (`Laws/Program/Typed/World.lean:52`) | a Kripke world, here a store typing: Γ fibers, Π deferreds, Ρ cells, Θ tokens, ordered by extension | read (de Vilhena §4.3, Jacobs Prop. 6.2.4, papers review A3) | `World.le` order laws; `Typed.mono` (`Laws/Effects/Protocol.lean:57`) | `Typed.World` extends `Machine.World` (`Laws/Machine/Handles.lean:868`): a parent and its extension, not two names for one thing; row 141 renames the parent `HandleWorld` in wave 3, and the glossary states the extension either way |
| `TypedProg` (`Typed/Residual.lean:186`) | protocol-typed weakest precondition on free-monad programs at a world | read (de Vilhena Def. 2.2, 2.4–2.8, papers review §1.3; Xia et al. §3.2, §7, lit-papers Q7, Q10) | `guard_inv`; `typedProg_mono` (probe; R5) | its own inductive since slice 5, sharing the protocol shape of the generic `Typed`, not an instance of it; not closed under bind |
| `ExitOk`, `NoShapeDefect` (`Typed/Admission.lean:30`, `:23`) | exit typing with the "does not go wrong" clause over the closed `Defect` alphabet | by name (Milner 1978) | part one landed (`abc7b124`); part two is row 117 | the meaning-level `Denote.ExitOk` (`Laws/Program/MeaningSound.lean:324`) is a second judgment, renamed `Denote.ExitHasTy` by row 141; the connector holds under two premises (proved) |
| `FrameAccepts`, `StackAccepts`, `SavedOk` (`Typed/Contracts.lean:32`, `:51`, `:67`) | the typing of a K-machine state `k ▷ e`; stacks are the free category on frame typings | by name (Harper, PFPL ch. 28) | `popR_typed` (`Typed/Stack.lean:133`); `stackAccepts_append`, `_split` (probe) | typed at one world today; Kripke closure owed (F3) |
| `TypedState` (`Typed/Assembly.lean:123`) | configuration typing: the invariant of a type-safety proof by initiation, consecution and transfer | by name (Wright and Felleisen 1994) | owed: M5, M6's 20 goals, M7 | not upward closed (exact support); "Kripke" applies to `Fits`, `TypedProg` and the amended stacks only |
| `CodeInert` (`Typed/Assembly.lean:84`) | a position is typed by what it will deliver: code is inert on a halted machine, with a queued `finish`, or a published exit | — (row 133) | `m9_root_inert` (probe) | row 134 replaces the halt disjunct by the split keyed on `running`: a running fiber is typed by its queued continuing command, or inert if there is none (`running_exempt_at_m6`, probe) |
| `denote` (`Laws/Program/Denote.lean:66`) | initial-algebra semantics into the free monad on the store signature | read (Plotkin and Pretnar §1, §5) | `denote.eq_cata`; `meaning_never_wrong` | — |
| `storeHandler`, `meaning` (`Denote.lean:124`, `:130`) | a comodel of state; `meaning` runs the free model against it | by name (Plotkin and Power 2008; Ahman and Bauer 2020) | `put_get`, `get_get`, `put_put` on live cells (probe) | lawful on live cells only (`E4-DEN-CE-002`) |
| `denoteR` (`Laws/Program/DenoteR.lean:799`) | elaboration of scoped syntax into first-order effects with bracket markers | read (Wu, Schrijvers, Hinze §9–10; Bach Poulsen and van der Rest, lit-papers Q2) | `denoteR_straight` (`:1380`); `guardR_bind` (probe) | not "a defunctionalized continuation semantics": the defunctionalized continuations are `Cmd` and `ScopeFrame` |
| `iter`, `denoteB` (`Laws/Program/Iter.lean:30`; `DenoteB.lean:208`) | the Kleene chain of the least fixed point; a budget is an approximant | by name (Capretta 2005; Elgot 1975); read (Jacobs Thm 5.3.4) | `denoteB_mono`, `meaningB_unique`; `conv_*` (probe) | Elgot's laws hold at the limit only; `Iter.lean`'s "Elgot iteration cut at a budget" is the approximant, not the law |
| `RunMachine`, `Cmd`, `driveStep` (`Machine/Fibers.lean:438`, `:727`, `:1846`) | an abstract machine with a defunctionalized continuation (rc.112's synchronous call stack) | by name (Felleisen and Friedman 1986); read (Danvy and Nielsen 2001, lit-papers Q12) | `driveState_lift`; `run_eq_ref` | not a runner past the first fiber operation |
| `Beh`, `Obs` (`Laws/Machine/Behaviour.lean:74`, `:30`) | behaviour of a deterministic Moore machine on a tape word | read (Jacobs ch. 2, papers review §1.4) | `Beh_fuel_irrelevant`; `behaviour_unique` for the Runner (probe) | "equal observations imply equal runs" is injectivity of the behaviour map: not claimed, not needed (the coherence principle's census row 38 says "finality") |
| `replay` (`Api/Runner.lean:75`) and the journal (`List Command`, `Command` at `:35`) | the free monoid action; a journal is a word, an event-sourced log | standard; by name | `replay_unique`, `replay_append`, `journal_replays` (`Laws/Run.lean:184`) | four functions named `replay`; row 98 owns the public typed route |
| `FairTape` (`Laws/Machine/Scheduling.lean:432`) | the finite restriction of weak fairness | by name (Lee et al. 2023, core math §9) | `flush_fair_prefix` | no consuming theorem; liveness owed (R12) |
| the lifts (`Laws/Machine/Lift.lean:48`, `:278`, `:308`, `:638`) | the invariance rule for a transition system, with a monotone ghost world and relative induction | by name (Manna and Pnueli; Owicki and Gries) | `driveState_lift`, `stepDecisionState_lift`, `replayEval_lift`, `driveStep_append` (a frame law) | — |
| the book (`Laws/Machine/Book.lean:196`) | a lock-step forward simulation lifted to tapes | by name (Lynch and Vaandrager 1995) | `book_replayEval`, `bookMeans_obs`; `replay_rel` (`Laws/Program/RuntimeR.lean:162`) | this, not `run_eq_meaning`, is the vocabulary's "simulation" relation |
| `Projects`, `Refines` (`Laws/Machine/Refinement.lean:20`, `:31`) | a refinement mapping and a forward simulation that also matches frontiers | by name (Abadi and Lamport 1991; Hoare 1972) | `projects_compose`, `projects_induces_refines` | — |
| the guard (`Laws/Program/Guard/Core.lean`; `Guard.Reachable` `:32`) | an inductive invariant of the native machine about who owns resume keys and tokens | by name | `driverContract`; `parkHandshake_reachable` owed | "exclusive ghost tokens" is an analogy: the tokens are machine state |
| the fork ledger (`ForkRecord`, `Machine/Fibers.lean:236`) | an append-only history variable written by one transition | by name (Abadi and Lamport 1991) | `step_agrees`, `reachable_agrees` | one observation reads it (`originOf`, used by `Api/Supervision.lean:226`); no transition does |
| `Canonical` (`Store/Domain/Canonical.lean:33`) | a lawful prism into the value sort | by name (Pickering, Gibbons, Wu 2017) | class fields `ofVal_toVal`, `ofVal_exact`; `decode_exact` (`:82`) | `Ty.Canonical` (`Program/Ty.lean:810`) is the normal-form predicate: write `Ty.Normal` there |
| `printT`, `read` (`Codegen/Templates.lean:438`; `Codegen/Read.lean`) | a partial isomorphism (invertible syntax description) on the readable domain | by name (Rendel and Ostermann 2010) | `read_print` (`Laws/Codegen/ReadPrint.lean:1904`), `read_exact` (`Laws/Codegen/Read.lean:887`) | the readable domain excludes annotated loops (DI-91) |
| `Representation`, `Ty.schema`/`ofSchema` (`Schema/Bridge.lean:38`, `:79`) | the free algebra of rc.112's Schema AST signature; `Ty` reaches it by a section with a partial left inverse | by name (Rendel and Ostermann) | `ofSchema_schema` (`:140`); exactness owed (row 128) | not an ornament (McBride 2011): an ornament's forgetful map is total; a partial isomorphism onto the image, a retraction until exactness lands |
| the JSON codec (`Schema/Codec.lean:230`, `:239`) | a retraction on the codec domain; exact modulo key order once proved | by name (Foster et al. 2007) | `decode_encode`, `decode_of_encode` | row 128; the normaliser is key order, not identity |
| provision and layers (`LayerTerm` `Program/Eff.lean:383`; `build` `Program/Provision.lean:297`) | a requirement row calculus; requirement rows grade programs (a flat coeffect: what the context must provide) | by name (Katsumata 2014; Petricek, Orchard, Mycroft 2014) | `provide_closed`, `merge_rows_comm`, `satisfies_iff_subset_keysRow` (`:168`) | satisfaction is inclusion into the key row, not an adjunction; grading soundness is row 117; `build_total`'s restoration and `lower_refines_build` owed (R5) |
| `HostSpec`, `LawfulHostSpec` (`Program/Profile.lean:176`, `:196`) | an environment specification for external calls | by name (CompCert's external functions; CakeML's oracle, model-probe synthesis §3.1) | the `LawfulHostSpec` fields; the rest parked (R6) | — |
| `Session` (`Api/HostSession.lean:84`) | a protocol automaton with capability ledgers (call ids, tokens) | by name | `advance_step` (`Laws/Run.lean:791`) | `open_total` (`:230`) is a totality fact, not a K4 law |
| `HasTy` (`Laws/Program/Typing/HasTy.lean:64`) | the declarative typing judgment; the checker is its sound and complete decision procedure | by name (TAPL ch. 16; Dunfield and Krishnaswami 2021) | `check_sound`, `check_complete`, `hasTy_unique` | its namespace `Conform.Effect4.Typing` is a tool root's (legacy) |
| `Straight`, `Looped` (`Program/Fragment.lean:22`; `Laws/Program/DenoteB.lean:125`) | fragments named by exclusion: a simulation's domain | — | `Straight.eq_cata`, `Looped.eq_cata` | — |
| K1–K5 (system map §5) | catamorphism; lawful prism; an equal-observation statement (adequacy, semantic preservation) proved through a simulation relation; a sound and complete decision procedure with a located refusal; a free monoid action | by name (as above; Plotkin 1977 for adequacy) | as in §2's last row | `docs/DESIGN-ISSUES.md`'s K1–K6 are obligation kinds: rename them O1–O6 |
| "Schema and program" (`AGENTS.md` vocabulary) | data descriptions as objects, programs as arrows, graded by error and requirement columns | by name (Power and Robinson 1997; Levy, Power, Thielecke 2003; Katsumata 2014) | — | an analogy (system map §6: "a proposed organization"); no carrier holds a refused foreign name (data probe NS0) |

## 6. Decision rows

The coordinator wrote rows 134–148 on 2026-10-01 from the seats' verdicts (`c9f273a2`) and amended
rows 2, 87, 96, 111–117, 127 and 133. This section checks each against the merged tree. Every
ruling this synthesis found needed is in those rows; it proposes **one new row (149)** and four
one-line amendments to row texts.

| Row | Who | This synthesis | Evidence at the merged head |
| --- | --- | --- | --- |
| 134, the typed state at a budget cut (F4) | owner; ratification owed | agrees. Amend the text: `E4-TYPED-CE-011`'s claim is "at a budget cut"; the finished run is covered by H1's published-exit disjunct. Supporting fact for superseding row 133's halt extension: its witness `E4-SCHED-CE-020` is a typed state holding a dangling scope, which row 139's scope liveness excludes | proved: `HeadCut.window_untyped`, `capstone_false_window`, `ledger_jointly_false_window`, `seat_split_not_decisionLift`, `running_exempt_at_m6`, `m9_root_inert`; tested: 0 of 64,142 settled results hold a running fiber |
| 135, frames and hook protocols Kripke-closed (F3) | owner | agrees | proved: `HeadStepLoop.step_loop_refuted`, `bad_not_kripke_initial`; `HeadKripkeWalk.output_not_kripke`, `stackAcceptsK_mono`, `stackAcceptsK_now`; `HeadTypedProgMono.typedProg_mono_ledger` |
| 136, every protocol row fulfilled by its handler (F2) | owner | agrees. Amend: the close-scope and `closeIter` posts are `ExitOk w' (EffTy.pure .unit) ans` (the precise form of "a success or a clean failure"); `refModify`/`refModifySome`'s pre at the native row's declared cell type | proved: `HeadAwaitLoad.typedState_load_false`; `HeadAwaitValuePost.*`; `HeadCloseScopePost.*`; `HeadStorePostAdequacy.*`; `HeadVerifyPosts.*` |
| 137, `Fits` in the checker's order (F1) | owner; ratification owed | agrees. Amend: name the sites by owner (seat A: `Membership.lean`, `World.lean:81`; seat B: `Residual.lean`'s entries; seat C: `Assembly.lean:40`, `Scheduler.lean:55`, `:67`, `:69`) | proved: `HeadM5Fits.m5_false`, `typedState_load_false`, `capstone_false`; rerun identical: `TypesOrderProbe`'s red controls, `verify-AmendedFitsProbe`'s sufficiency theorems |
| 138, M7 declared; R1's row-table exception | owner; ratification owed for the exception | agrees | reading: `Laws/Program/RuntimeR.lean:197-216`; DI-57 parked under R6 |
| 139, halting-freedom and liveness | owner | agrees | reading: `Typed/Assembly.lean:84-85`, `:180-182`; `Membership.lean:52-58`; `Residual.lean:49`, `:133`; the witness `M6Capstone.lean:1582-1640` |
| 140, the ledger as the one list | owner | agrees | reading: `Laws/Machine/Lift.lean:308-355`; `Typed/Sources.lean:29`, `:53-54` |
| 141, the two-way names | owner | agrees; the glossary states that `Typed.World` extends `Machine.World` whichever name the parent keeps | proved (rerun): `verify-ExitOkConnector`'s connector under two premises with its two red controls; tested (rerun): `verify-ExitOkOverload` |
| 142, the glossary and the senses of "signature" | coordinator | agrees; §5 is ready to carry | tested: the corrected sites located by `grep -n` at `dceae006`; the rest carried from the organization seat's `GlossarySites` (rerun by its verifier at `ea5b28b5`) |
| 143, the census instrument | coordinator | agrees. Input for its counting sentence: the census counts recursive traversals (structural or well-founded, private included); a one-level case analysis is a classifier, governed by row 56 and the case-site policy, not a census row; the instrument reports one-level matches in their own column | tested (rerun): `CensusWfBlindSpot`, `verify-CensusPrivate`, `verify-SparseShape`, `verify-CensusConsistency`, `CensusNow` |
| 144–147 | owner; coordinator for 146 | agree | reading (organization seat and verifier) |
| 148, M5's denotation lemma by name | coordinator | agrees | proved: `HeadBindGuard.bind_not_typed`, `guard_bind_not_closed`, `close_typed`, `seq_typed` |
| 87, 96, 117, 127, 133 (amended) | as written | agree; row 127's "distinct names" needs row 149 | as above |

**Row 149 (new; owner).** *The two admission refusals' names (DI-67, row 127).*
- **Question.** DI-67's ruled text and the frozen `Test/contracts/foundation-wave2.contract.md:217-219`
  name the `int` scan's refusal `AdmitRefusal.uninhabited (at : Path)`. Row 127's repair adds an
  emptiness check, and brief A step 6 renames the `int` refusal `intType at` so that `uninhabited
  at` names the new check.
- **Options.** (a) Keep the frozen `uninhabited` for the `int` scan and give the new check its own
  name (for example `emptyColumn at`): no contract revision, and the frozen name already fits what
  it points at, an `int` occurrence that is itself empty (types verifier, TY-13). (b) Brief A's
  rename, with DI-67's ruled text and the frozen contract revised by the owner.
- **Recommendation.** (a). If the owner prefers (b) for the clearer names, rule it explicitly
  before seat A's step 6, since a frozen contract changes.
- **Evidence.** Tested (rerun at the merged head): `admitColumn` admits `list int`, which `findInt`
  refuses (`types/InhabitedProbe.lean`); the data probe's V3 witnesses elaborate
  (`pedigree/verify-Probe.lean`, exit 0 at `1c6f9c92`).

## 7. The landing plan for the coordinator's seats

The coordinator's plan (`docs/research/2026-10-01-landing/plan.md`, waves 1, 1b, 2, 3; seats A–H in
their own worktrees, branches `seat/<X>`) is the landing plan. This section checks it against the
gap list: every finding of §3 has a seat, the file ownership has one writer per file except the
root-import anchors, and the additions below close what it misses (§4.5 gives the reasons).

| Seat | Scope (as briefed, with this note's additions) | Files | Acceptance | Depends on |
| --- | --- | --- | --- | --- |
| H (wave 1): the DESIGN-BASIS refresh | the refresh brief, its addendum, and §4.4 here; add the step-indexing reason (worlds hold syntactic types) | `docs/DESIGN-BASIS.md`; the eight notes it force-adds; `docs/research/2026-10-01-design-basis-refresh/` | the brief's steps 1–7; DB-16 does not record the one-world frame judgment as settled; a theorem from this pass cited as a probe until it lands; the citation check at the stated commit | none |
| E (wave 1): algebra lemma landings | brief E; item 1's red control taken from `HeadBindGuard` (P6's no longer elaborates); item 8's header already half done by G | `Laws/Effects/{Protocol,Sum}.lean`; `Laws/Machine/{Approximation,StoresLaws}.lean`; `Laws/Api/Runner.lean`; a limit module beside `Iter.lean`; `Laws/Program/DenoteR.lean` or a scope-marker module; `Laws/Program/Typed/Seq.lean`; `Program/Provision.lean`; fixtures under `Test/` | every landed theorem prints `[propext, Quot.sound]` or fewer; each fixture by `lake env lean -DwarningAsError=true` | none |
| F (wave 1): instrument, registers, imports, record | brief F, plus: register witnesses are the tracked ports; `E4-TYPED-CE-011` claims the cut only; `E4-TYPED-CE-015` cites the data probe's V3 (tracked) and `types/InhabitedProbe.lean`; **row 122's write-up** (Decision 12 and the boundary rule into `docs/core/host-boundary.md`, the two 2026-09-10 notes force-added, DI-08 to ruled), unless the coordinator writes it; the census counting sentence per row 143's input (§6) | brief F's files; `docs/core/host-boundary.md`; `docs/research/2026-09-10-schema-at-boundaries.md`, `2026-09-10-boundary-decisions.md` (force-added) | brief F's checks; the seven register rows cite files that elaborate at the merged head; host-boundary names route A as the one boundary decode route and says "Decision 12", never "D12" | none |
| A (wave 1b): values in the checker's order, the signature, inhabitance | brief A, plus `World.lean:81`'s comparison under row 137; step 6 waits for row 149 | brief A's files | brief A's checks; `HeadM5Fits` restated as an `Old*` battery; `fits_normalize`, `fits_subN`, `fits_join_*` in the tree; `prog3` loads typed | rows 137 and 149 for step 6; wave 1 merged |
| B (wave 1b): frames, posts, the walk | brief B; the close-scope post as `ExitOk w' (EffTy.pure .unit) ans`; "the completion entries" belong to A (`World.lean:81`) and C (`Assembly.lean:40`), not B | brief B's files | brief B's checks; `HeadStepLoop`, `HeadKripkeWalk` and the post ports restated as `Old*` batteries; none refutes the new statements | seat A's `Ty.subN` for `Residual.lean`'s entries |
| C (wave 1b): the assembled state, M7, the ledger | brief C, plus `Scheduler.lean:55`, `:67`, `:69` and `Assembly.lean:40` under row 137; step 1 starts from `HeadCut` and drops `capstone_false_finished9` (it does not hold at the merged head); `running_exempt_at_m6` beside `running_clause_vacuous_at_m6` as the positive control | brief C's files | brief C's checks; the split's entry premises shown for `DecisionLift` unchanged; M7a–c declared with R1's exception in the docstring | seat A's `Ty.subN`; seat B's frame statements for stack monotonicity |
| D (wave 2): row 117's contract and part two | the presence clause, the requires-monotone side condition, the restored context; positive controls for `.scoped` and provision | `Typed/Contracts.lean` and the files B and C left | `E4-TYPED-CE-008` refutes the old statement and not the new | B and C merged (the same frame contract as row 135) |
| Wave 2 proof seats | per-row adequacy; M5 (`denoteR_typed`, `evalTerm_fits`); the eighteen commands; the edits; the capstone; M7 | as the plan names | each `#proof_wanted` closed by `#obligation_proved` | wave 1b merged |
| Coordinator, now | row 128's vocabulary edit (`AGENTS.md:73-80`, "now" by its ruling), the glossary as system map §9 (row 142), R1's exception in §8 (row 138), and the lines the seats propose for `STATE.md`, `README.md`, `decisions.md` (`GENERATED.md` is seat F's item 7) | `AGENTS.md`; `docs/core/system-map.md`; the registers | the K2 list names the lawful instances and calls `ofSchema` and the JSON codec retractions; the simulation entry names the statements and the relation; every glossary site resolves at the landing commit | row 138's ratification for the §8 sentence |
| Required item: DESIGN-BASIS refresh | seat H | — | — | — |
| Required item: the vocabulary amendment (row 128) | the coordinator, now (above) | — | — | — |
| Required item: register and tracked-text repairs (row 129) | seat F (items 5–10) | — | — | — |
| Required item: the boundary route write-up (row 122) | seat F, added (above) | — | — | — |
| Required item: the inhabitance counterexample registration (row 127) | seat F (`E4-TYPED-CE-015`), witness tested at the merged head | — | — | — |
| Required item: the glossary (row 142) | the coordinator (system map §9); §5 here is the text | — | — | — |
| Required item: the Schema wipe (row 39) | none: landed at `0c534f06` (Codex's four slices, verified `bd142695`); three packets retired at `dceae006`; the rest of its fallout is seat F's item 6 | — | — | — |

**Sequential.** Wave 1 (E, F, H) runs in parallel now. Wave 1b's A, B and C run in parallel by file
ownership, but B's `Residual.lean` entries and C's `Scheduler.lean`/`Assembly.lean` entries wait for
A's `Ty.subN`, and C's stack-monotonicity declarations wait for B. Seat F's register rows land
before A, B and C turn their witnesses into `Old*` fixtures. Seat D follows B and C (the same frame
contract). Wave 2 follows wave 1b's merge. Row 149 is ruled before seat A's step 6. The
root-import anchors (`src/Effect4/Laws.lean`, `Test/All.lean`) are shared by E, F, A, B, C: the
coordinator names one anchor per seat so the branches merge clean.

## 8. Open questions, each with a proposed owner decision

1. **Ratify rows 134, 137 and 138's row-table exception.** Proposed: ratify as written; each rests
   on a refutation proved at the merged head and an amendment that changes no ruled design.
2. **Row 149, the two refusals' names.** Proposed: (a), keep the frozen name for the `int` scan.
3. **Row 128's timing.** Ruled "amend the vocabulary now"; the plan says wave 3. Proposed: now, by
   the coordinator; two sentences, no statement changes.
4. **Row 143's counting sentence.** Proposed: the census counts recursive traversals only, private
   and well-founded included; one-level classifiers are row 56's.
5. **Row 117's contract and row 135's frame restatement touch the same `FrameAccepts`.** Proposed:
   seat D after seat B, as the plan orders, with seat B's receipt naming the frame clauses seat D
   will extend.
6. **A standing check for cut tolerance.** The corpus fuel-frontier scan (`VerifyScout2`,
   `VerifyScout2Pairs`, `VerifyScout4` rerun here; `VerifyScout4Pairs` by the proofs verifier) caught nothing new but would catch a
   machine-only clause that fails at a cut. Proposed: run it as a probe whenever the typed state's
   statements change, not as a gate (the owner's gate-removal steer).
7. **`CTy`'s meets.** Proposed: not claimed until a consumer needs one (TY-17 is an argument, not
   a proof).
8. **Tracking the formal pass.** Its folder is 2 MB (notes, verifications, probes, logs). Proposed:
   force-add the synthesis, the four notes and verifications and the probe sources as cited history
   (the owner's rule that the last design push lands tracked); logs optional.
9. **The six decision-level Guard inductions.** Proposed: seat F probes a narrower lift once (brief
   F's M2) and replaces them only if it closes; otherwise the obstacle is recorded.
10. **A configuration capstone over the full predicate.** Proposed: only if a consumer appears (row
    134 says so); M7 needs only the machine-only predicate.
11. **Beyond M7.** Proposed: open R12's carriers (decision streams through `replayEval_append`,
    divergence by compatible prefixes, fairness on streams) when R12 is scheduled, and R10's
    per-form laws as equations of each form's theory, using the store comodel's state laws already
    proved on live cells.

## 9. Receipt

**The one thing first.** Four declared M5–M6 obligations are false at the merged head (proved
there); rows 134–137 carry their repairs; three corrections to the landing plan matter before wave
1b (§4.5 items 1–4), and one new owner row (149) is proposed.

**Base and head.** Seats at `ea5b28b5`; this seat's compiles began at `0c534f06` (the merge) and,
after the coordinator's rebuild at 07:27, ran against the rebuilt library; heads recorded in the
logs are `0c534f06`, `dceae006` and `1c6f9c92`, which share every Lean source under `src/`,
`Test/` and `tools/` but one (`tools/Tools/ArchitectureRoles.lean`, changed at `dceae006`, imported
by no probe) (tested, `git diff --name-only`). No library build was run by this seat; the build
products were the coordinator's (`.lake/build`, 07:27).

**Files written.** In the tree: this note only. Scratch (session scratchpad, not tracked):
`synthesis-reruns/rerun.sh`, `synthesis-reruns/*.log` (every rerun and port log),
`synthesis-reruns/port/*.lean` (the eleven ports, which the coordinator tracked byte-identical at
`docs/research/2026-10-01-landing/ports-at-dceae006/` in `1c6f9c92`; tested by `cmp`), and
`synthesis-draft1.md` (this note before the reconciliation with rows 134–148). No tracked file was
edited by this seat; no `lake build`, `make`, generator, `git add` or `git commit` was run; the
Codex worktree was not touched.

**Commands.** Every Lean run was one probe at a time through the lock:
`bash <scratchpad>/serial.sh lake env lean -M6144 -DwarningAsError=true <absolute probe path>`,
wrapped by `synthesis-reruns/rerun.sh`, which records the probe's sha256, the head, the exit code
and the wall time. Non-Lean commands: `git log`, `git show --stat`, `git diff --name-only`,
`git grep`, `grep -n`, `cmp`, `shasum -a 256`, short Python text checks; outputs cited where used.
Fifty-six logs in all; Appendix B lists them.

**Axiom output.** Every theorem this note calls proved printed `[propext, Quot.sound]` or fewer;
`sorryAx` appears only in the failed reruns of probes the merge broke (their errors are API drift,
`FitsExit` to `ExitOk` and `SavedOk` to `SavedPosition`), which carry no claim; no
`Classical.choice` anywhere.

**Read.** The four seat notes and verifications in full; `AGENTS.md`; `docs/core/system-map.md`
(§§1.1, 2–8, at `ea5b28b5` and `dceae006`); `docs/core/decisions.md` rows 2, 28, 39, 40, 48, 52,
56, 61, 79, 87, 95–97, 99, 105–108, 110–148; brief addendum 6; Codex's receipt "After addendum 6" (by
`git show` on its branch); the model-probe synthesis §3.1–§4.3; Codex's audit in full; the data
probe's synthesis (opening, §5 headers) and its tracked `pedigree/verify-Probe.lean` V2–V3; the pass
synthesis §2.4; the DESIGN-BASIS refresh brief; `docs/core/coherence-principle.md:60-90`;
`docs/core/host-boundary.md` §4.4; the frozen `foundation-wave2.contract.md:212-222`; DI-67; the
landing plan and briefs A, B, C, E, F and H's addendum; the coordinator's rerun note; and the source
at every `file:line` cited (merged definitions of `TypedState`, `CodeInert`, `SavedPosition`,
`StepPreserves`, `QueueOk`, the scheduler facts, `fiberPost`/`storePost`, `HandleFits`,
`driveStep`, `advanceState`, the evaluator's frontier arm, `run_eq_ref`, the `M6Capstone`
H1 controls).

**What could not be settled.**
- The seats' probes could not be rerun at `ea5b28b5` after the rebuild; their evidence at that
  commit rests on their verifiers' reruns. At the merged head eleven of them were ported and
  proved; the rest that broke are covered by those ports or are by-design now (`HaltTyped`: halting
  is tolerated by `CodeInert`'s halt disjunct, reading).
- Not proved here: that the split keyed on `running` satisfies every field of `DecisionLift`
  (reading; it is M6's proof); the Kripke-restated walk; any adequacy instance; `prog3`'s positive
  load under row 137; the green control `step_loop_good` at the merged head; amalgamation and
  `inhabited (normalize t) = inhabited t`; `readExact_iff`'s premise for `N_J` and `N_S`; meets of
  `CTy`.
- Literature: no paper was opened; every mark is the citing note's.
- Whether `TypedState` holds at the finished run `m9` at the merged head: only the stale-code
  obstruction is shown absent (`m9_root_inert`).

## Appendix A. The ports to the merged head (tracked)

Each file is tracked at `docs/research/2026-10-01-landing/ports-at-dceae006/` (`1c6f9c92`), byte
identical to the file this seat compiled. Every theorem listed prints `[propext, Quot.sound]` or
fewer at `dceae006`.

| Port (sha256 prefix) | From (sha256 prefix) | What changed | Theorems (proved) |
| --- | --- | --- | --- |
| `HeadM5Fits.lean` (`08d0e574`) | `types/M5CounterProbe.lean` (`627b12f2`) and `types/verify-CapstoneProbe.lean` §2 | `load_not_inert` added (the loaded root is not halted, has no queued finish, no published exit); the stack and leaf read `ExitOk` (`.1` for its `FitsExit` part) | `load_not_inert`, `m5_false`, `typedState_load_false`, `capstone_false` |
| `HeadAwaitLoad.lean` (`8f0df798`) | `proofs/verify-probes/VerifyAwaitLoad.lean` (`7f9902a8`) | `ExitOk` at the payload and leaf; `load_not_inert` before the code clause | `typed_source`, `code_eq`, `cert_of_bodyTyped`, `root_code_refused`, `one_not_loaded`, `typedState_load_false`, `load_not_inert` |
| `HeadCut.lean` (`83470e6c`) | `proofs/probes/StaleCode.lean` (`a707805b`) and `proofs/verify-probes/VerifySplit.lean` (`74483e0a`) | the code clause conditional on `¬ CodeInert`; `m6_not_inert` added; the finished run checked against H1's published-exit disjunct; the seat's split restated with `ExitOk`; a positive control in the merged vocabulary | `m6_stuck_none`, `m6_root_running`, `m6_not_inert`, `window_untyped`, `capstone_false_window`, `ledger_jointly_false_window`, `m9_root_inert`, `seat_split_not_decisionLift`, `running_exempt_at_m6` |
| `HeadStepLoop.lean` (`5d9149d3`) | `algebra/verify-StepLoop.lean` (`5bd7ffd9`), new construction | the state built the way `M6Capstone.H1TerminalAmendment` builds its controls: one running root fiber, the merged `TypedState` with H1's conjuncts, the nine-field `QueueOk`, `stuck = none` | `typed`, `queue`, `result_not_inert`, `post_untyped`, `step_loop_refuted`, `bad_not_kripke_initial` |
| `HeadKripkeWalk.lean` (`28f0687b`) | `algebra/verify-WrapWalk.lean` (`c722256c`) and P2 §3 | `ExitOk` in the hooks and inputs; P2's generic Kripke laws added | `hookLawsX`, `w0_le_w1`, `input_kripke`, `walk_output`, `walk_typed_one_world`, `output_not_kripke`, `stackAcceptsK_mono`, `stackAcceptsK_now` |
| `HeadTypedProgMono.lean` (`82f9277b`) | `algebra/probes/P2KripkeTyping.lean` §1 (`8ac3ae15`) | `fitsExit_mono` replaced by the merged `strongExit_mono`; a wrapper in the ledger's binder order | `storePre_mono`, `fiberPre_mono`, `typedProg_mono`, `typedProg_mono_ledger` |
| `HeadBindGuard.lean` (`dbcc8317`) | `algebra/verify-BindGuard.lean` (`9f9e9e9b`) | `ExitOk` at the payloads, the skip clause and the continuation premise | `p_typed`, `k_typed`, `bind_not_typed`, `guard_bind_not_closed`, `close_typed`, `seq_typed` |
| `HeadCloseScopePost.lean` (`0ab32da0`) | `proofs/probes/CloseScopePost.lean` (`364d1ef5`) | `.1` of `ExitOk` | `close_no_finalizer`, `post_excludes_answer`, `close_code_refused` |
| `HeadStorePostAdequacy.lean` (`027c289f`) | `proofs/probes/StorePostAdequacy.lean` (`84e87a53`) | `ExitOk` at `TypedProg.pure` | the nine of the seat, `store_step_leaves_typing` among them |
| `HeadAwaitValuePost.lean` (`1fb79288`) | `proofs/probes/AwaitValuePost.lean` (`fa6fc402`) | `.1` of `ExitOk` | `target_declared`, `exitValue_delivers`, `delivered_fits_checked`, `post_excludes_delivered`, `await_code_refused` |
| `HeadVerifyPosts.lean` (`48f58c19`) | `proofs/verify-probes/VerifyPosts.lean` (`c9fa4241`) | `ExitOk` at `TypedProg.pure` | the thirteen of the verifier, `adequacy_false_refModify`, `closeIter_post_excludes`, `scopeIsClosed_post_excludes_unit` among them |

## Appendix B. Reruns at the merged head

Each probe compiled alone through the lock. "Same" means its axiom lines equal the seat's or
verifier's log line for line. "Drift" means it failed on the merge's statement changes (`FitsExit`
to `ExitOk`, `SavedOk` to `SavedPosition`), with no claim taken; the port that replaces it is named.

| Probe | Exit | Axiom lines | Result |
| --- | --- | --- | --- |
| `types/TypesOrderProbe.lean` | 0 | 23 | same |
| `types/verify-AmendedFitsProbe.lean` | 0 | 10 | same |
| `types/InhabitedProbe.lean` | 0 | 15 | same |
| `types/verify-HandleInhabitedProbe.lean` | 0 | 6 | same |
| `types/ExactByImageProbe.lean` | 0 | 9 | same |
| `types/verify-ExactNormaliserProbe.lean` | 0 | 0 (guards) | every guard holds |
| `types/KernelEvalProbe.lean` | 0 | 3 | same |
| `types/RecordWorldProbe.lean` | 0 | 6 | same |
| `types/M5CounterProbe.lean`, `types/verify-CapstoneProbe.lean` | 1, 1 | — | drift; `HeadM5Fits` |
| `proofs/probes/FrameCategory.lean` | 0 | 9 | same |
| `proofs/probes/StaleCode.lean`, `proofs/verify-probes/VerifySplit.lean` | 1, 1 | — | drift; `HeadCut` |
| `proofs/verify-probes/VerifyAwaitLoad.lean` | 1 | — | drift; `HeadAwaitLoad` |
| `proofs/probes/{CloseScopePost,StorePostAdequacy,AwaitValuePost}.lean`, `proofs/verify-probes/VerifyPosts.lean` | 1 each | — | drift; the four post ports |
| `proofs/probes/HaltTyped.lean` | 1 | — | drift; by design at the merged head (`CodeInert`'s halt disjunct), not ported |
| `proofs/verify-probes/VerifyScout2.lean`, `VerifyScout2Pairs.lean` | 0, 0 | 0 | 0 of 13,078 and 0 of 51,064 settled results hold a running fiber |
| `proofs/verify-probes/VerifyScout3.lean`, `VerifyScout4.lean` | 0, 0 | 0 | finished runs `[3394, 5, 0, 1781, 0]`; windows 0 of 4,640 untypable at 105,051 frontiers |
| `algebra/probes/P1Coproduct.lean`, `P3TapeAction.lean`, `P4ComodelIteration.lean`, `P5ScopeMarkers.lean`, `P7ProvideRows.lean` | 0 each | 7, 5, 13, 3, 3 | same |
| `algebra/probes/P6ProtocolLaws.lean` | 1 | 3 | `Typed.inr`, `Typed.refine` (no axioms) elaborate; its red control drifts; `HeadBindGuard` |
| `algebra/probes/P2KripkeTyping.lean` | 1 | — | drift; `HeadTypedProgMono`, `HeadKripkeWalk` |
| `algebra/verify-StepLoop.lean`, `verify-WrapWalk.lean`, `verify-BindGuard.lean` | 1 each | — | drift; `HeadStepLoop`, `HeadKripkeWalk`, `HeadBindGuard` |
| `algebra/verify-ProvideMerge.lean` | 0 | 3 | same |
| `organization/probes/{GuardLiftRedundancy,CensusWfBlindSpot,CensusNow,LedgerNow}.lean` | 0 each | 1, 0, 0, 0 | `GuardLiftRedundancy`'s axiom line same; the blind spot reproduces; the ledger at the merged head is 358 declared, 335 proved, 23 open, as at `ea5b28b5`; the census's structural counts unchanged (`Ty` 23, 17 with a fold), its totals lower after row 39 (`Ty` 112 takers against 117) |
| `organization/verify-{CensusPrivate,SparseShape,CensusConsistency,TyCasesDeep,ExitOkConnector,ExitOkOverload}.lean` | 0 each | 0, 0, 0, 0, 3, 0 | the verifier's findings reproduce (the private and sparse blind spots; for `Ty` 2 one-level matches counted, 12 missed); the connector's axiom lines same; under `Laws/Program/Typed/` person-written `Ty` case analysis is in `Membership` only, `Scheduler.lean` included |
| `docs/research/2026-10-01-data-probe/pedigree/verify-Probe.lean` | 0 | 3 | V2 and V3 guards hold at `1c6f9c92` |
| the eleven ports (Appendix A) | 0 each | 4, 7, 9, 6, 8, 4, 6, 3, 9, 5, 13 | proved |
