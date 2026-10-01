# Formal pass, seat ALGEBRA: what each semantic object is, and which laws it owes

Status: research note, 2026-10-01, seat ALGEBRA of the formal pass. Base: `refactor/phase1-phase3`
at `efd67af1`; at the end the head was `ea5b28b5`, a docs-only commit (`docs/STATE.md`,
`docs/core/decisions.md` rows 119-133 as read here, brief addendum 6), so every source citation
holds at both. Nothing tracked was edited; no `lake build`, `make`,
generator, `git add` or `git commit` was run. Seven probes and their logs are beside this note
(`probes/`, `logs/`), each compiled alone through the one-compiler lock with
`lake env lean -M6144 -DwarningAsError=true`; every theorem named "proved" below printed its
axioms at `[propext, Quot.sound]` or fewer.

Evidence words: **proved** (a kernel theorem run here, axioms printed), **tested** (a finite check
run here), **reading** (code or notes read, not run), **assumed** (not checked). Literature is
marked **read (note)** when a tracked or research note records reading the section, **by name**
when only cited, **assumed** for a claim about a paper's content that nobody in the tree has read.
No paper text was opened in this pass. Short paths: `Program/…`, `Machine/…`, `Laws/…` are under
`src/Effect4/`; `Algebra/…` is `.lake/packages/effects/Effects/Algebra/`.

## The one thing

**The saved-stack judgment is not Kripke-closed, so world weakening fails for it, and M6's
per-command preservation cannot be proved as declared.** `FrameAccepts`
(`Laws/Program/Typed/Contracts.lean:32-48`) types a frame's continuation only on exits that fit at
the one world the stack is checked at. A step that allocates must move to a later world (world
validity makes every heap cell declared, `Typed/Validity.lean:22`), and an exit that mentions the
new handle falls outside the old clause. So `StackAccepts`, and with it `SavedOk`, which every
fiber's frame owes in `TypedState` (`Typed/Assembly.lean:67-73`, `Typed/Sources.lean:22`, `:31`), does
not transport. **Proved** (P2, red control): `stackAccepts_not_mono`, a frame accepted at a world
and refused at a later one. The smallest amendment is the closure the tree already uses everywhere
else: quantify the frame's `run`/`skip` clauses and its three hook premises over later worlds, as
`TypedProg`'s clauses (`Typed/Residual.lean:189-216`) and the typed-state vocabulary's
`continuation` source (`Typed/Vocabulary.lean:31-32`: "`∀ w' ≥ w, ∀ ex, ExitOk e ex → TypedProg w'
e' (next ex)`") already do. **Proved** (P2): the closed judgment is world-monotone with no premise
(`stackAcceptsK_mono`), gives today's judgment at the current world so `popR_typed` applies
unchanged (`stackAcceptsK_now`), and refuses the counterexample frame (`bad_not_kripke`). Proved
in the same probe: the open obligation `M3bWorld.typedProg_mono` holds (`typedProg_mono`).

## 1. The objects, one row each

Severity: **fundamental** (a milestone statement cannot be proved as declared, or the formal
object is misnamed in a way that misleads the plan), **rigor** (a law the plan relies on, or a
milestone will need, is absent or owed), **tidiness** (a law that holds and is cheap is missing, or
a text claims what the tree does not prove).

| # | Object | Formal notion | Literature | The tree's definition | Laws proved | Laws expected but absent or owed | Severity |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | Programs | Two free objects. `Eff`: the initial algebra of a first-order, many-sorted signature whose variables are absolute positions (de Bruijn levels). `Program S`: the free monad over a signature (well-founded operation trees). `denote`/`denoteR` map the first into the second | Hyland, Plotkin, Power 2006 (by name; never read in the tree, model probe P14); Swierstra 2008 §2, §6 (read, pedigree seat via model probe §3.1); Plotkin and Pretnar 2013 (read, lit-papers Q11); Goguen et al. 1977, Fiore, Plotkin, Turi 1999 (by name, coherence principle) | `Eff` `Program/Eff.lean:263-412`; `EffAlgebra`/`cata_eff`/`EffHom` `Program/Fold.lean:1038`, `:1104`, `:1197`; `Program` `Algebra/Program.lean:33-38`; `interpret` `Algebra/Handler.lean:45`; `Signature.sum` `Algebra/Signature.lean:35` | initiality of `Eff`: `hom_eq_cata_eff` (`Fold.lean:1270`); free monad: `LawfulMonad` (`Algebra/Laws.lean:45`), `interpret_bind`, `program_is_free`, `program_is_initial_in_models_eq` (`Algebra/Universal.lean:98`, `:215`), `eq_of_all_interpretations` (`Algebra/Laws.lean:116`); handler category `through_assoc` and units (`Algebra/Handler/Category.lean:26-45`); sum: `Handler.sum_unique`, `interpret_inl`, `inl_bind`, `inl_injective`, `inl_unique` (`Algebra/Sum.lean:36`, `:48`, `:72`, `:92`, `:186`); `denote` is a fold (`Laws/Program/Folds/Denote.lean:21`) | **now proved (P1):** the sum is the coproduct of the free monads (`sum_is_coproduct`), the restriction law for any handler of a sum (`interpret_inl_restrict`), the sum is not a tensor (`sum_not_tensor`). Absent: maps along general signature morphisms (pedigree probe only); `Eff` has no monad structure, `composeAt`'s identity and associativity are future work (`system-map.md` §6) | tidiness |
| 2 | Scoped constructs and `denoteR` | Scoped operations elaborated into algebraic ones with bracket markers (`guard_`/`unguard`), well-bracketed by construction; an elaboration in the hefty-algebra sense, by fuel recursion rather than a fold; control erasure is a handler, hence a monad morphism | Wu, Schrijvers, Hinze 2014 §9-10; Piróg et al. 2018 §1.3; van den Berg et al. 2021 §2.2; Bach Poulsen and van der Rest 2023 §1.2, §2.6.4, §3.4 (all read, lit-papers Q2); Plotkin and Power 2002 on algebraicity (by name, core math §6) | `RSig` `Laws/Program/Sched.lean:197`; `guardR` `Laws/Program/DenoteR.lean:69`; `denoteEffBody` `:581`; `denoteRWith`/`denoteR` `:785`, `:799`; `eraseControl` `:114` | 38 unfolding equations (`denoteR_zero` … `denoteLayer_ref_succ`, `DenoteR.lean:825-1190`); `eraseControl_bind` (`:120`), `eraseControl_guardR` (`:125`), `eraseControl_onExitR`; `denoteR_straight` (`:1380`): after erasure, on `Straight`, with budget for its depth, `denoteR` is `inl ∘ denote`; `meaning_via_rsig` (`Sched.lean:237`) | **now proved (P5):** the scope law (`guardR_bind`: the continuation runs after the closing marker), non-algebraicity (`guardR_not_algebraic`, red control), the erasure law (`eraseControl_guardR_bind`). Absent: any law of the scoped constructs at the machine meaning (catch, mask, scope, provide laws with interruption); R10's per-form behaviour laws; the fiber half has no handler by design (`Sched.lean:32-39`, `E4-SCHED-CE-001`) | rigor |
| 3 | The budgeted meaning | A fuel-indexed approximation (the Kleene chain) of the least fixed point of the loop's unfolding equation, in partiality with state; not an Elgot algebra (well-founded `Program` has no iteration operator); `meaningB_unique` is functionality of the limit, Capretta's termination relation being single-valued | Elgot 1975, Adámek, Milius, Velebil 2006 (by name, coherence principle); Capretta 2005 (by name, core math §3); Jacobs Thm 5.3.4, Prop 5.3.3 (read, papers review §1.4); Xia et al. 2020 `iter` laws (by name, core math §4) | `iter` `Laws/Program/Iter.lean:30`; `denoteB` `Laws/Program/DenoteB.lean:208`; `meaningB` `:241`; `LoopAgreement` `Laws/Program/LoopAgreement.lean:27` | unfolding `iter_zero`/`iter_succ`, uniformity for pure maps `iter_uniform` (`Iter.lean:34-49`); `denoteB_straight` (`DenoteB.lean:285`), `iter_mono` (`:355`), `denoteB_mono` (`:386`), `meaningB_unique` (`:496`); `loopAgreement` (`Agreement/Loop.lean:839`); `soundB`, `meaningB_typed` (`LoopSound.lean:306`, `:535`) | **now proved (P4):** for any step over the store signature, Elgot's fixpoint law for the limit (`conv_fixpoint`), leastness (`conv_least`), single-valuedness (`conv_unique`); red control: no fixed budget solves the fixpoint equation (`budget_not_fixpoint`). Absent: naturality, dinaturality, codiagonal at the limit (needed only for a declared loop rewrite, R10) | rigor |
| 4 | The store and the machine | The store handler is a comodel of the store signature (one co-operation `Stores → Val × Stores` per operation); `meaning` is the run of the free model against that comodel (Plotkin-Power's tensor; a runner without exceptions). The fiber machine is not a runner: it is a deterministic transition system labelled by decisions, an abstract machine whose fibers hold `RSig` trees (resumptions) | Plotkin and Power 2008; Ahman and Bauer 2020 (by name, core math §7); Plotkin and Power 2002 (by name, core math §6; that it presents state by lookup and update with four equations is assumed); Piróg and Gibbons 2014, Harrison 2006, resumptions (by name, core math §5) | `storeHandler` `Laws/Program/Denote.lean:124`; `meaning` `:130`; `syncOpStep` `Machine/Stores.lean:1938`; `RunMachine` `Machine/Fibers.lean:415`; the reference machine `Laws/Program/RuntimeR.lean` | heap read-over-write `refPeek_poke_self` (`Machine/Stores.lean:962`); arena laws (`Laws/Machine/Arena.lean:18-32`); `refStep_eq_refStepOf` (`Laws/Machine/RefKernel.lean:67`); the runner theorem on `Straight`: `run_eq_meaning` (`Agreement/Machine.lean:1922`); on `Looped`: `loopAgreement`; machine against reference, empty host table: `run_eq_ref` (`RuntimeR.lean:211`) | **now proved (P4):** the handler satisfies put-get, get-get, put-put on live cells (`put_get`, `get_get`, `put_put`); red control: put-get fails on an unallocated cell (`put_get_dead_fails`, the fallback of `E4-DEN-CE-002`). Absent: get-put, and the commutation of different cells, as handler-level laws; any runner theorem past the first fiber operation (by design) | rigor |
| 5 | Behaviour and the tape | The machine with `stepDecisionState` is a coalgebra for `X ↦ X^D` (deterministic, labelled by decisions); with `obs` a Moore machine whose behaviour is `Beh`. The session runner is a Mealy machine; `behaviour` is its map to the final Mealy machine. The tape is the interaction tree's oracle: every visible node is answered by a decision (INV-TAPE-1) | Xia et al. 2020 §7, Def. 1-2; Chappe et al. 2023 §2.2, §7.2 (read, lit-papers Q7); Jacobs §3.4 (read, papers review §1.4) and ch. 2 on Moore machines (by name, core math §2); Lee, Cho, Song, Hur et al. 2023 (by name, core math §9) | `replayEval` `Machine/Fibers.lean:2188`; `Beh` `Laws/Machine/Behaviour.lean:74`; `Runner.step`/`behaviour` `Api/Runner.lean:70`, `Laws/Api/Runner.lean:168`; `FairTape` `Laws/Machine/Scheduling.lean:432` | `Beh_fuel_irrelevant` (`Behaviour.lean:92`); fuel laws `replay_stable`, `replay_obs_mono`, `replay_colimit` (`Laws/Machine/Approximation.lean:1237`, `:1403`, `:1662`); trace extension `replayEval_trace_extends` (`:756`); journal action `replay_append`, `replay_unique`, `behaviour_cons` (`Laws/Api/Runner.lean:81`, `:157`, `:174`); `journal_replays` (`Laws/Run.lean:184`); `flush_fair` (`Scheduling.lean:413`) | **now proved (P3):** the decision tape acts on machines with fuel exhaustion absorbing (`replayEval_append`), and `behaviour` is the unique map satisfying its unfolding (`behaviour_unique`). Absent: infinite tapes, divergence by compatible prefixes (DB-03), any liveness statement; `FairTape` is a finite-tape definition with no consuming theorem; frontiers do not name armed work (`awaitDecision_iff`, R12) | rigor |
| 6 | Typing | A protocol-typed weakest precondition on free-monad trees (Hazel's `ewp` with first-order protocols) over a Kripke world; the world is ghost tables over the store, ordered by extension and cell compatibility; `Fits` is a unary Kripke logical predicate on first-order values. No step indexing: values carry no code, so the predicate is structural on `Ty`, and divergence is fuel and frontiers, not a later modality. M6's typed state is meant as an inductive invariant with world growth | de Vilhena 2022 Def. 2.2, 2.4-2.8, rules Bind and Monotonicity (read, papers review §1.3; pedigree verify §2 item 7); Ahmed 2006, Iris (by name, foundations review §4.1); Dreyer et al.; Wright and Felleisen 1994 and store typing (by name, this note) | `Typed` `Laws/Effects/Protocol.lean:45`; `World`/`World.le` `Typed/World.lean:52`, `:131`; `World.leHost` `Typed/Validity.lean:38`; `Fits` `Typed/Membership.lean:87`; `TypedProg` `Typed/Residual.lean:186`; `FrameAccepts`/`StackAccepts` `Typed/Contracts.lean:32`, `:51`; `TypedState`/`StepPreserves` `Typed/Assembly.lean:67`, `:99` | generic: `Typed.mono`, `bind`, `widen`, `inl`, `inl_inv`, `inr_inv`, `plain_iff` (`Protocol.lean:57-165`); world: `order_refl`/`trans`, `leHost_refl`/`trans`, the five allocation extensions (`World.lean:394-710`, `Validity.lean:112-121`); values: `fits_map`, `fits_mono`, `fits_sub`, `fitsExit_mono`, `fitsExit_sub` (`Membership.lean:729-960`); stacks at one world: `popR_typed`, `saveAnswerR_typed`, `deliver_active` (`Stack.lean:105`, `:339`, `:358`) | **now proved (P2, P6):** `typedProg_mono` (closes `M3bWorld.typedProg_mono`), `Typed.inr`, `Typed.refine` (protocol order). **False as defined (P2):** world weakening of `StackAccepts`. Absent: the Kripke closure of frames and hook protocols; the elaboration lemma `denoteR_typed` (M5's S1, not declared as an obligation) and its value half at `Fits` (term evaluation; only coarse `evalTerm_hasTy`, `Laws/Program/Typed.lean:971`); a bind lemma for `TypedProg`, which is not bind-closed (P6 red control) | **fundamental** (frames); rigor (the rest) |
| 7 | The generic lifts | The inductive-invariant (invariance) rule for a transition system, with a monotone ghost component (an auxiliary, history-like variable); the decision lift composes it through each decision's sub-steps; replay adds rely conditions on the environment's decisions; the frame law is locality of a command over the pending queue; `Projects`/`Refines` are a refinement mapping and a forward simulation, both without stuttering | Manna and Pnueli, rule INV; Owicki and Gries; Abadi and Lamport 1991; Jones 1983; O'Hearn, Reynolds, Yang 2001; Lynch and Vaandrager 1995 (all by name; not read in the tree) | `StepKeeps` `Laws/Machine/Lift.lean:48`; `DecisionLift` `:308`; `AdmittedReplay` `:619`; `Framed` `:142`; `Projects`/`Refines` `Laws/Machine/Refinement.lean:20`, `:31` | `driveState_lift` (`:56`), `driveState_keeps` (`:105`), `driveStep_append` (`:170`), `stepDecisionState_lift` (`:564`), `replayEval_lift` (`:638`), `machineFact_stepDecision` (`:692`); `projects_compose`, `projects_induces_refines` (`Refinement.lean:72`, `:98`) | none fundamental. The lift needs preservation from every state satisfying the invariant (that is what makes it inductive), which is why row 6's frames must be closed under world growth. Stuttering simulation is not provided (`machine-state.md` §7) | tidiness |
| 8 | Provision rows | Requirement rows are the free bounded join-semilattice on service keys (finite sets, canonical spelling) with relative complement; `provide` is the substitution rule for free variables (rows minus outputs, plus the dependency's rows); a program's requirement row is the grade of a graded effect system, removed at provision as a handler removes operations; contexts merge right-biased (not commutative) | Katsumata 2014, Orchard et al. 2014 graded monads (by name, coherence principle §4b); Bauer and Pretnar 2014 effect system (by name, this note); Leijen 2017 §3 and Hillerström and Lindley (read, lit-papers Q4); de Vilhena Tes §7.3 (read, papers review §1.3); Rémy (assumed, type algebra §8) | `Row` `Data/Row.lean:30`; `LayerTy` and its operations `Program/Typing/Rules.lean:240-270`; laws `Program/Provision.lean:70-160`; `satisfies_iff_subset_keysRow` `:169`; `build` `:298` | `union_assoc`/`comm`/`idem`/`empty_left`/`right`, the `diff` laws (`Row.lean:464-650`); `provide_closed` and its converse, `provide_provide_rows`, `merge_rows_comm`, `provide_requires_antitone_out`, `appTy_closed_iff` (`Provision.lean:98-247`); `satisfies_iff_subset_keysRow`; context merge non-commutative (`#guard`s `:610-614`, tested by the tree); **now proved (P7):** `provide` is not associative on rows (`provide_not_assoc`, red control), which is why the tree's law is associativity up to `provideMerge` | the semantic soundness of the grading (a program at row `r` under a context satisfying `r` never dies `missingService`): open as row 117, with a proposed counterexample; `build_total` cut (`b08f3b58`) while the docstring still claims it (`Provision.lean:35-41`); `lower_refines_build` owed (R5) | rigor |

## 2. Object by object

### 2.1 Programs: two free objects, and the sum

**What each is.** The tree has two free objects for programs and they are not the same kind
(reading). `Eff` (`Program/Eff.lean:263-412`) is first-order syntax: seven mutually inductive
sorts, every constructor a symbol of a many-sorted signature, with variables as absolute
positions in the environment ("every node passes its whole scope forward and an answer is
appended", `:12-15`). Its universal property is initiality: `EffAlgebra` gives one field per
constructor (`Program/Fold.lean:1038-1102`), `cata_eff` is the map out (`:1104`), and
`hom_eq_cata_eff` (`:1270`) proves every homomorphism equals it (proved in the tree, generated).
`Program S` (`Algebra/Program.lean:33-38`) is the free monad over a signature: well-founded trees
with Lean continuations, the higher-order proof carrier of DB-01. Its universal property is
freeness: for a lawful target monad, a handler's interpretation is the unique monad morphism that
agrees with the handler on single operations (`program_is_free`, `program_is_initial_in_models_eq`,
`Algebra/Universal.lean:98`, `:215`; proved in the package). `denote` is a fold from `Eff` into
`Program StoreSig` (`denote.eq_cata`, `Laws/Program/Folds/Denote.lean:21`), and `denoteR` an
elaboration into `Program RSig` by fuel recursion (`DenoteR.lean:785-800`), a census exemption
(`traversal-census.md` line 57).

**What `Eff` is not.** `Eff` has no monad structure: its `bind` is a constructor, and with
positional variables raw reassociation changes values (`system-map.md` §6, citing
`2026-09-19-critique-response.md` §2; reading). "Programs as the free monad" is true of the image
in `Program`, not of `Eff`. The categorical composition `composeAt` and its identity and
associativity laws are recorded as future work; this pass agrees that nothing in M5-M7 needs them.

**The sum.** `Signature.sum` (`Algebra/Signature.lean:35`) with `Handler.sum`, its uniqueness
(`Handler.sum_unique`, `Algebra/Sum.lean:36`) and the injection laws gives every ingredient of a
coproduct, but the package never states that `Program (S ⊕ₛ T)` is the coproduct of `Program S`
and `Program T` in the category of monads, which is the content of Hyland, Plotkin and Power's sum
of theories for free theories (by name; that the sum of theories is the coproduct is assumed from
the paper's title and the coherence principle's description, not read). **Proved** (P1,
`sum_is_coproduct`): for monad morphisms `f`, `g` out of the two free monads into a lawful monad,
the copairing is a monad morphism, restricts to `f` and `g`, and is the only such morphism. Also
**proved**: the restriction law for an arbitrary handler of a sum, not only a copaired one
(`interpret_inl_restrict`, `interpret_inr_restrict`), and that the injections are monad morphisms
(`inl_isMonadMorphism`). **Proved** (red control, `sum_not_tensor`, no axioms): a left operation
followed by a right one is a different tree from the reverse; the sum carries no commutation
equations. `RSig = StoreSig ⊕ₛ FiberSig` is therefore a sum, not a tensor, which is correct: fiber
operations read and write the stores, so they do not commute with store operations (reading,
`Machine/Fibers.lean`). Conservativity of the sum (C1) holds because the theories are free
(`inl_injective`); if the fiber layer ever gains equations, conservativity of a sum of theories
with equations becomes HPP's question (assumed, as the model probe §2.2 says).

### 2.2 Scoped constructs: bracket markers, elaborated

**What it is.** `denoteR` sends the scoped constructs (`bind`'s success frame, `catchCause`,
`catchIf`, `matchCause`, `onExit`, `exit`, the service and layer regions) to `RSig` programs in
which the scope is delimited by a `guard_` node and closed by an `unguard` node
(`guardR`, `DenoteR.lean:69-73`). This is the bracket encoding of scoped effects that Wu,
Schrijvers and Hinze describe and set aside because nothing guarantees that brackets pair
(lit-papers Q2 records both §9 and Piróg et al. §1.3; read there). Here the pairing holds by
construction: `guardR` is the only producer of `guard_` (reading, `DenoteR.lean`), the frame
stack enforces it at run time, and `TypedProg`'s `guard` arm types the pair (`Residual.lean:199-209`).
In hefty-algebra terms `denoteR` is an elaboration of higher-order syntax into first-order effects;
it is written by fuel recursion, not as a fold, because a layer reference hops to another path of
the root (`DenoteR.lean:733-737`) and the budget mirrors `compileEff`'s (reading). DB-05's "no
`HHandler` for first-order children" holds: scoped bodies are addressed by `Point`s.

**What is proved.** The unfolding equations (`denoteR_zero` and 37 siblings, `DenoteR.lean:825-1190`);
control erasure is `interpret` of a handler (`controlErasure`, `:105`), so `eraseControl_bind`
(`:120`) is the monad-morphism law; erasing a scope gives its body (`eraseControl_guardR`, `:125`);
and on `Straight`, with budget for the depth, the erased elaboration is the straight denotation
injected on the left (`denoteR_straight`, `:1380`). **Proved** (P5): the scope law
`guardR_bind` (sequencing after a scope enters its normal branch only after the closing marker,
and is the whole of the saved branch); the red control `guardR_not_algebraic` (moving the
continuation inside the scope changes the program: a scope is not an algebraic operation in
Plotkin and Power's sense); the erasure law `eraseControl_guardR_bind` (on one fiber a scope is
plain sequencing, which is core math §6's remark "on one fiber a scope is just a continuation"
made a theorem).

**What is not.** No law of a scoped construct holds at the machine meaning in the tree: no
catch law with interruption, no mask law, no scope-close law (reading). The straight meaning's
equations (`meaning_catchCause`, `meaning_matchCause`, `meaning_onExit`, `Denote.lean:283-319`)
are the only algebraic laws of scoped constructs, and only on one fiber. The congruence of a
program equivalence across the fiber layer is impossible in principle (Chappe et al. §7.2, read,
lit-papers §0 item 1). R10 already rules that each form owes one behaviour law (DI-89, row 79);
this pass adds only that such a law should be declared as an equation of the form's theory and
discharged per clause (Plotkin and Pretnar §5, read, lit-papers Q11).

### 2.3 The budgeted meaning: a Kleene chain, not an Elgot algebra

**What it is.** `iter f k x` (`Iter.lean:30-32`) is the `k`-th approximant of the loop's unfolding
equation; `denoteB` (`DenoteB.lean:208`) uses it for `iterate`. `Program S` is well founded, so it
has no iteration operator and no Elgot structure of its own (reading; Jacobs 5.3.4 is the reason
the algebra cannot be the behaviour carrier, papers review G2, read). The tree's meaning of a loop
is therefore the limit of the chain: the answer some budget finishes with. `meaningB_unique`
(`DenoteB.lean:496`) states exactly that two finishing budgets agree on exit and stores, derived
from `denoteB_mono` (a finished answer survives one more budget); it is functionality of the
limit, Capretta's single-valued termination relation (by name), not a fixpoint law (reading).

**What is proved now.** **Proved** (P4), for any step function over the store signature, of the
convergence relation `Conv f x s y s'` (some budget finishes with `y` and stores `s'`):
- `conv_fixpoint`: Elgot's fixpoint law for the limit: the loop converges exactly when its step
  stops with that answer, or continues to a cursor from which it converges;
- `conv_least`: convergence is contained in every relation closed under the loop's two rules, so
  it is the least fixed point (Kleene);
- `conv_unique`: convergence is single-valued, stores included (the generic form of
  `meaningB_unique`);
- red control `budget_not_fixpoint` (no axioms): at budget 1 a two-round loop is unfinished while
  one unfolding in front of the same budget finishes, so no single approximant solves the equation.

Uniformity holds at every budget (`iter_uniform`, `Iter.lean:40`, proved in the tree). Naturality,
dinaturality and the codiagonal (nested loops as one loop) are absent; the DenoteB header says the
nesting clause is carried "by the answer type, not by a loop law" (`DenoteB.lean:20-25`), and no
milestone needs them. They become owed when a form or a printer step rewrites a loop (R10).

### 2.4 The store is a comodel; the machine is not a runner

**The comodel.** `storeHandler` (`Denote.lean:124-127`) assigns each `SyncOp` a co-operation
`Stores → Val × Stores`, which is a comodel of the store signature in Plotkin and Power's sense
(by name). For the free signature every such family is a comodel; the interesting question is the
theory of state. **Proved** (P4): on a cell the heap holds, the handler satisfies put-get
(`put_get`), get-get (`get_get`, on any cell) and put-put (`put_put`). **Proved** (red control,
`put_get_dead_fails`): on a cell the store never allocated, `refSet` and `refGet` both fall back
to `Val.unit` (`E4-DEN-CE-002`), so writing 7 and reading back answers `unit`. The store is a
lawful comodel of state on its live part, which is exactly the part `Fits` admits (a cell handle
fits only if the world declares it, `Membership.lean:28-29`, `:139-142`). The heap-level read-over-write
law already exists (`refPeek_poke_self`, `Machine/Stores.lean:962`).

**The runner theorem and where it stops.** `meaning e env s = (interpret storeHandler (denote e
env)).run s` (`Denote.lean:130-131`) is the run of the free model against the comodel, the shape
of Plotkin and Power's tensor and of Ahman and Bauer's `using … run` without exceptions (by name).
`run_eq_meaning` (`Agreement/Machine.lean:1922`) proves the machine's run equals it on `Straight`
at the stated budget; `loopAgreement` (`Agreement/Loop.lean:839`) extends it to `Looped` with the
budgeted meaning. It stops at the first fiber operation, async row, generator, mask, scope,
acquire, provision or service form (the exclusions of `Straight`/`Looped`). Past that, the fiber
machine is not a runner: the fiber signature has no handler on purpose (`fiberRefusal` "is not a
semantics", `Sched.lean:216-218`, `E4-SCHED-CE-001`). It is an abstract machine: a deterministic
transition system labelled by decisions (`stepDecisionState`, `Machine/Fibers.lean:2111`), whose
fibers hold `RSig` trees as resumptions. The statement there is a simulation between two machines,
`run_eq_ref` (`RuntimeR.lean:211`), at the empty host table only (reading). Ahman and Bauer's
`finally` corresponds to resource release, R11 (one close proved, the whole run open; system map
§8).

### 2.5 Behaviour as a function of the tape

**What it is.** `stepDecisionState` is a function, so the machine is a deterministic coalgebra
labelled by decisions, and with `obs` (exits and stores, `Behaviour.lean:29-51`) a Moore machine;
`Beh m tape` is its behaviour at a sufficient budget (`Behaviour.lean:74`), and
`Beh_fuel_irrelevant` (`:92`) makes it independent of which sufficient budget (proved in the
tree). Determinism given the tape holds by construction, which is INV-TAPE-1 at the level of the
model (no off-tape choice); as a claim about rc.112 it remains a modelling claim (reading). The
session runner is a Mealy machine (`Laws/Api/Runner.lean:97-109`), and `behaviour` is called its
map into the final Mealy machine, but only the unfolding is proved.

**Proved now (P3).**
- `replayEval_append`: replaying `a ++ b` is replaying `a`, then `b` from the machine `a`
  reached, unless the prefix ran out of fuel, which absorbs the suffix (with `replayEval_of_stuck`,
  `replayEval_append_fuel`, `replayEval_append_machine`). This is the machine-level monoid action
  that K5 states for journals, and the theorem DB-03's "compatible finite prefixes" needs: the
  results along a tape's prefixes form a chain.
- `behaviour_unique`: any map satisfying `behaviour_nil` and `behaviour_cons` is `behaviour`, the
  uniqueness half of finality.

**What is absent.** There is no infinite tape and no notion of an infinite run, so "divergence is
witnessed by compatible finite prefixes" (DB-03) has no statement (reading). `FairTape`
(`Scheduling.lean:432-441`) is a predicate on finite tapes whose only use is one test
(`Test/Machine/Runtime/SchedulingContract.lean:61`); fairness in Lee et al.'s sense lives on
infinite executions (by name, core math §9). Liveness (R12) therefore has no carrier yet. Frontiers
do not name armed dispatcher work (`awaitDecision_iff`, `Laws/Api/Frontier.lean:13`; R12, model
probe D7). None of this is on M5-M7's path.

### 2.6 Typing: a Kripke protocol logic, and the frames that are not Kripke

**What it is.** `Typed o Ψ w Q p` (`Protocol.lean:45-50`) is a protocol-typed weakest precondition
on free-monad trees: each operation's demand holds now, and its continuation is typed at every
later world in which the handler answers within the protocol. This is Hazel's `ewp` with
first-order protocols (de Vilhena Def. 2.2, read via the papers review), with the Kripke clause
built in. `TypedProg` (`Residual.lean:186-216`) is the concrete instance as its own inductive
(slice-5 ruling), with arms for the control markers. The world (`Typed/World.lean:52-57`) is ghost
tables (`Γ`, `Π`, `Ρ`, `Θ`) over the store; `World.le` (`:131-136`) is extension of the tables
plus preservation of old cell typings; `leHost` adds stable external spellings
(`Validity.lean:38`); `WorldValid` (`:19`) ties a world to a machine, in the role Iris gives a
state interpretation (by name). `Fits` (`Membership.lean:87-148`) is a unary logical predicate on
values, defined by structural recursion on `Ty`, with handle leaves read from the world's tables.

**What replaces step indexing.** Two facts of the design (reading). Values are first-order data
(no closures, `AGENTS.md`), so `Fits` at a `refOf t` reads a declaration, never the cell's
contents, and needs no recursion through the world; code lives in fibers and frames and is typed
syntactically by `TypedProg` and `StackAccepts`, not by a semantic relation on values. And
divergence is fuel and frontiers, so safety is an invariant of reachable states, not an adequacy
theorem over infinite executions; no later modality is needed.

**Laws the literature expects, and their state.**
- Value monotonicity and subsumption: proved in the tree (`fits_mono`, `fits_map`, `fits_sub`,
  `fitsExit_mono`, `fitsExit_sub`, `Membership.lean:729-960`).
- Computation monotonicity (the Kripke property of `TypedProg`): an open obligation in the tree
  (`Residual.lean:424`, `#proof_wanted` at `:455`). **Proved** (P2): `typedProg_mono`, from
  `storePre_mono` (all 31 store rows) and `fiberPre_mono` (all 40 fiber rows, with
  `asyncPre_mono`, `pointTyped_mono`, `bodyTyped_mono`, `envTyped_mono`). Only the guard's body
  needs the induction; every other clause already quantifies over later worlds.
- Continuation monotonicity (the evaluation-context relation of a Kripke logical relation, which
  quantifies over future worlds; Ahmed 2006 and Dreyer et al., by name; the shape of their continuation relation is assumed, not read): **false as defined.**
  `FrameAccepts.answer`/`resume` and the hook premises are stated at one world. **Proved** (P2,
  `stackAccepts_not_mono`): the frame `.answer badNext`, whose continuation answers `"x"` on every
  success, is accepted at the empty world `w0` (no success fits `refOf nat` there) and refused at
  `w1`, which declares cell 0 at `nat` (`w0_le_w1`): `badNext (success (cell 0))` must fit `unit`.
- The bind rule: generic `Typed.bind` is proved. **Proved** (P6, red control,
  `typedProg_not_bind_closed`): `TypedProg` is not closed under bind, because an `unguard` carries
  an exit at the current type. This matches Hazel, whose Bind rule holds for neutral contexts only
  (papers review G8, read); it is an expected side condition, not a defect, but M5's elaboration
  lemma cannot use a general bind.
- Protocol monotonicity (Hazel's protocol order) and the right injection: absent from the tree;
  **proved** (P6, no axioms): `Typed.refine`, `Typed.inr`.
- The fundamental property (every checker-typed point elaborates to a protocol-typed program):
  M5's S1, `denoteR_typed` (`2026-09-18-typed-state-plan.md` S1; `2026-09-21-codex-brief-foundations-slices-3-6.md:468`),
  not declared as an obligation in the tree's ledger (reading: the `#proof_wanted` list in
  `Typed/Assembly.lean:251-273` and `Residual.lean:455`). Its value half, term evaluation at
  `Fits`, is absent: only the coarse `evalTerm_hasTy` (`Laws/Program/Typed.lean:971`) exists, with
  `fits_pair` and `fits_fst` (`Membership.lean:965-981`) as its first arms.

**Is the typed state an inductive invariant?** As declared, no. `StepPreserves`
(`Assembly.lean:99-104`) quantifies over every machine satisfying `TypedState`, which is what an
inductive invariant must do (row 7). A fiber whose current code allocates a cell and whose stack
holds `.answer badNext` satisfies `TypedState` at a world without the cell (reading: each clause
of `TypedState` is met, the stack clause vacuously); after `evaluate`, any later world must
declare the cell (`WorldValid.heap`), the exit `success (cell k)` reaches `badNext`, and the
fiber's exit `"x"` cannot fit `unit`. So `step_evaluate` is false as stated (reading; the
judgment-level failure is proved). With frames Kripke-closed the bad frame is excluded from the
start (`bad_not_kripke`, proved), and every stack transports to every later world
(`stackAcceptsK_mono`, proved). The conditional lookups (`ResumeOk`, due completions, `HeapCell`)
transport only with freshness of the new keys, which row 106 and `WorldValid`'s coverage supply;
that is already tracked (`2026-09-21-foundations-monotonicity-and-refinement-review.md` §2.3 item 5).

### 2.7 The lifts: invariance with a ghost world

`StepKeeps` and `driveState_lift` (`Lift.lean:48-81`) are the invariance rule for a transition
system: an assertion preserved by every step from every state that satisfies it holds at every
reachable state (Manna and Pnueli's rule, by name). The world is a ghost component that only grows
along the preorder, the auxiliary-variable pattern (Owicki and Gries; Abadi and Lamport's history
variables; by name), and the lift composes the growth (`o.trans`). `DecisionLift` and
`stepDecisionState_lift` (`:308`, `:564`) carry the invariant through each decision's sub-steps
(the command loop, the dispatcher drain, the clock, the answer's preparation); `replayEval_lift`
(`:638`) adds an admission premise for the environment's decisions, a rely condition in Jones's
sense (by name). `driveStep_append` (`:170`) is locality of a command over the pending suffix, the
frame property in O'Hearn, Reynolds and Yang's sense (by name), with the halting alternative made
explicit. `Projects` and `Refines` (`Refinement.lean:20-37`) are a refinement mapping and a forward
simulation, both with exactly corresponding steps; stuttering is not provided
(`machine-state.md` §7). All proved in the tree; users landed (rows 93, 94, 110). Nothing is
missing for M6 here; the one consequence is the one in §2.6: an inductive invariant must survive
every step from every state it admits, which is why frames must be Kripke-closed.

### 2.8 Provision rows: a semilattice with complement, and an open soundness theorem

`Row` (`Data/Row.lean:30`) is a finite set with one canonical spelling. Union is associative,
commutative and idempotent with the empty row as unit, and difference has its usual laws
(`Row.lean:464-650`, proved in the tree): rows form the free bounded join-semilattice on service
keys, with relative complement. `provide`'s rule, rows minus the dependency's outputs plus the
dependency's rows, is the free-variable law of substitution (papers review A1, read).
`provide_closed`, its converse, `provide_provide_rows` (associativity up to `provideMerge`),
`merge_rows_comm` and antitonicity hold (`Provision.lean:98-160`, proved in the tree). **Proved**
(P7, red control, `provide_not_assoc`): plain associativity of `provide` fails on rows, because a
nested `provide` hides the inner dependency's outputs from the outer dependent; regrouping a
`provide` chain (in a printer step or a form) changes the requirement row, and only the
`provideMerge` grouping is free. At the
context level merge is right-biased and not commutative (the `leftWins`/`rightWins` `#guard`s,
`Provision.lean:607-614`, tested by the tree). `satisfies_iff_subset_keysRow` (`:169`) says a
context satisfies exactly the subrows of its key row; the section header calls it an adjunction (`Provision.lean:163`), but
there is one monotone map (`keysRow`), not two, so it is a representability statement (reading).

A program's requirement row is the grade of a graded effect system, removed at provision as a
handler removes the operations it handles (Katsumata 2014; Bauer and Pretnar 2014; by name). The
law that makes a grade mean something, effect soundness (a program at row `r`, run under a context
that satisfies `r`, never dies with `missingService`), is not proved: it is R9's part two, row 117,
held for a frame-contract design, with the proposed counterexample `E4-TYPED-CE-008` (a saved frame
transports `missingService` across a change of requirement row). `build_total`, which stated the
build-level half, was cut as unused (`traversal-census.md` line 435, `b08f3b58`), and the module
header still claims it is proved (`Provision.lean:35-41`; first flagged by the model probe §3.2
item 7, still present at `efd67af1`, reading).

## 3. The gaps, with their smallest amendments

**A1 (fundamental; M6).** `FrameAccepts`, `StackAccepts`, `SavedOk` and the hook protocols are
stated at one world, so the saved-stack judgment is not world-monotone (proved, P2) and the M6
per-command obligations are not provable over the declared typed state (reading, §2.6).
*Amendment:* quantify the `resume.run`, `resume.skip`, `answer.run` clauses and the three hook
premises of `FrameAccepts` over later worlds (`∀ w', w.leHost w' → …`), exactly as
`FrameAcceptsK` in P2; add `stackAccepts_mono` (one induction, P2) and `frameAccepts_now`. Call
sites: `saveAnswerR_typed`'s `hnext` (`Stack.lean:342`) takes the Kripke form, which `TypedProg`'s
own `next` clause already supplies; `popR_typed` (`Stack.lean:105`) is re-instantiated at the
current world by reflexivity; the hook protocols (`IteratorProtocol`, `LoopProtocol`,
`frameProtocols.asyncFinalizer`, `Residual.lean:266-310`) get the same closure, or are wrapped as in
P2. Register the P2 red control as a counterexample row, of the same family as H1's
`E4-SCHED-CE-019` (a `StepPreserves` statement false over arbitrary typed states). Land it with
Codex's H1 restatement of the typed state (brief addendum 6, item H1), which edits the same
clauses, so the step statements are written once; it changes no runtime code.

**A2 (rigor; M5).** `M3bWorld.typedProg_mono` is open in the tree and holds. *Amendment:* land
P2's `envTyped_mono`, `pointTyped_mono`, `bodyTyped_mono`, `storePre_mono`, `asyncPre_mono`,
`fiberPre_mono`, `typedProg_mono` (about 130 lines) in `Typed/Residual.lean`, replacing the
`#proof_wanted`.

**A3 (rigor; M5).** The fundamental property `denoteR_typed` (S1) is not a declared obligation,
and its value half at `Fits` is absent. *Amendment:* declare both by name in the M5-M7 ledger:
`denoteR_typed : PointTyped src w p ty → … → TypedProg src w ty (denoteR src.program e p)` and
`evalTerm_fits : EnvTyped w tys env → termTy … tys t = some ty → evalTerm env t = some v → Fits w v ty`,
so M5's count is the true one.

**A4 (rigor; M5).** `TypedProg` is not bind-closed (proved, P6), as Hazel's Bind is restricted to
neutral contexts. *Amendment:* state the M5 sequencing tool explicitly: either a bind lemma whose
premise is that the first program has no closing marker outside a guard body, or per-construct
compatibility lemmas for `guardR`, `seqR`, `onExitR`, `finalizerR`; write the choice into the M5
brief.

**A5 (tidiness).** The generic protocol layer lacks `Typed.inr` and monotonicity in the protocol
order. *Amendment:* add P6's `Typed.inr` and `Typed.refine` (with its `Refines` structure) to
`Laws/Effects/Protocol.lean`; both are axiom-free. This is the generic half of C4.

**A6 (tidiness).** The coproduct property of the signature sum and the restriction law are not
stated. *Amendment:* add P1's `sum_is_coproduct`, `interpret_inl_restrict`/`interpret_inr_restrict`,
`inl_isMonadMorphism` and the red control `sum_not_tensor` beside the protocol layer
(`src/Effect4/Laws/Effects/`), not in the pinned package, whose parity gate freezes its shape.
Write DB-01's caveat in these terms: the tree's sums are free, hence conservative; a sum of
theories with equations is HPP's open question.

**A7 (tidiness; K5 and DB-03).** The machine-level tape action and the finality of `behaviour` are
not stated. *Amendment:* land P3's `replayEval_append` (with its corollaries) in
`Laws/Machine/Approximation.lean` and `behaviour_unique` in `Laws/Api/Runner.lean`; restate
DB-03's "compatible finite prefixes" over `replayEval_append`.

**A8 (rigor; R10, DB-04).** The limit of the budgeted meaning has no stated laws. *Amendment:* land
P4's `conv_fixpoint`, `conv_least`, `conv_unique` beside `Iter.lean` and record in DB-04's
amendment: the budgeted meaning is the Kleene chain of the least fixed point; the Elgot laws hold
for the limit, never for one budget (`budget_not_fixpoint`); naturality, dinaturality and the
codiagonal are owed only when a loop rewrite is declared.

**A9 (rigor; R10).** The store comodel's state laws are unstated, and they fail on unallocated
cells. *Amendment:* land P4's `put_get`, `get_get`, `put_put` over `Live` cells with the red control,
and name `E4-DEN-CE-002` in comodel terms (the fallback breaks put-get). Owed in full only when a
form or optimization declares a state equation.

**A10 (rigor; R12).** Divergence and fairness have no carrier. *Amendment:* when R12 opens, define
a run of a decision stream (`Nat → decision`) as the chain of its prefixes through
`replayEval_append`, divergence as every prefix ending at a tape frontier with work runnable, and
fairness on streams; `FairTape` becomes its finite restriction. Not before M5-M7.

**A11 (rigor; R5, R9).** The requirement grading has no soundness theorem, and the module header
claims a cut theorem. *Amendment:* the theorem is row 117's (no new row); now, correct the header
at `Provision.lean:35-41` to say `build_total` was cut at `b08f3b58` and its restoration is owed
under R5, and rename "the adjunction" to "satisfaction is inclusion into `keysRow`".

**A12 (tidiness).** Stale cross-reference: `docs/core/coherence-principle.md`'s literature list
says Jacobs and Lynch-Vaandrager explain "the missing finality law (row 38)"; row 38 is `explain`
onto the fold (`decisions.md:79`). *Amendment:* point it at `behaviour_unique` (A7) when it lands.

## 4. The probes

| Probe | Question it settles | Result | Axioms | Log |
| --- | --- | --- | --- | --- |
| `probes/P1Coproduct.lean` | Is the signature sum the coproduct of the free monads; does the restriction law hold for any handler; is the sum a tensor? | `sum_is_coproduct`, `interpret_inl_restrict`, `interpret_inr_restrict`, `inl_isMonadMorphism`, `inr_isMonadMorphism` proved; `sum_not_tensor` proved (red control) | `[propext, Quot.sound]` or fewer; `sum_not_tensor` none | `logs/P1Coproduct.log` |
| `probes/P2KripkeTyping.lean` | Is `TypedProg` world-monotone; is `StackAccepts`; does a Kripke closure repair it? | `typedProg_mono` (with `storePre_mono`, `fiberPre_mono`) proved; `stackAccepts_not_mono` proved (red control); `stackAcceptsK_mono`, `stackAcceptsK_now`, `bad_not_kripke` proved | `[propext, Quot.sound]` | `logs/P2KripkeTyping.log` |
| `probes/P3TapeAction.lean` | Does the decision tape act on machines; is `behaviour` the final map? | `replayEval_append` and corollaries, `behaviour_unique` proved | `[propext, Quot.sound]` | `logs/P3TapeAction.log` |
| `probes/P4ComodelIteration.lean` | Does the store handler satisfy the state laws; what is the budgeted meaning's limit? | `put_get`, `get_get`, `put_put` proved; `put_get_dead_fails` proved (red control); `conv_fixpoint`, `conv_least`, `conv_unique` proved; `budget_not_fixpoint` proved (red control) | `[propext, Quot.sound]`; `budget_not_fixpoint` none | `logs/P4ComodelIteration.log` |
| `probes/P5ScopeMarkers.lean` | What laws hold of the scope markers? | `guardR_bind`, `eraseControl_guardR_bind` proved; `guardR_not_algebraic` proved (red control) | `[propext, Quot.sound]` | `logs/P5ScopeMarkers.log` |
| `probes/P6ProtocolLaws.lean` | Does the protocol layer have its Hazel laws; is `TypedProg` bind-closed? | `Typed.inr`, `Typed.refine` proved; `typedProg_not_bind_closed` proved (red control) | `Typed.inr`, `Typed.refine` none; the red control `[propext, Quot.sound]` | `logs/P6ProtocolLaws.log` |
| `probes/P7ProvideRows.lean` | Is `provide` associative on requirement rows? | `provide_not_assoc` proved (red control), with `a_needed_nested`, `a_discharged_sequenced` | `[propext, Quot.sound]` | `logs/P7ProvideRows.log` |

Each log holds the final run's full output, which is only `#print axioms` lines, one for every
theorem this note names (helpers included). Earlier failing runs of P1-P5 were fixed in place;
P6 and P7 passed on their first run; P1-P4 and P7 were rerun once more to print the helpers'
axioms. Three helpers of P4 (`syncOp_refSet_live`, `syncOp_refGet_live`, `syncOp_ref_dead`) print
`[propext]` only.

## 5. Receipt

- **First, for the coordinator:** A1. The M6 per-command obligations cannot be proved over the
  typed state as declared, because saved frames are typed at one world; the fix is a Kripke closure
  of `FrameAccepts` (and the hook protocols), proved monotone and conservative over today's walk in
  P2. Dispatch it with H1 (addendum 6), before the first M6 instance.
- **Base and head:** base `efd67af1` on `refactor/phase1-phase3`; head at the end `ea5b28b5`
  (docs only: `docs/STATE.md`, `docs/core/decisions.md`, addendum 6). No source file changed
  between them, so every probe and citation holds at both.
- **Files written:** this note; `probes/P1Coproduct.lean` … `probes/P7ProvideRows.lean`;
  `logs/P1Coproduct.log` … `logs/P7ProvideRows.log`. No tracked file edited.
- **Commands:** for each probe, `bash <scratchpad>/serial.sh lake env lean -M6144
  -DwarningAsError=true <absolute probe path>`, exit 0 on the final run.
- **Axiom output:** as in §4; nothing above `[propext, Quot.sound]`; no `sorryAx`, no
  `Classical.choice`.
- **Bounded or host-only evidence:** none of the probes is a finite check; all are kernel theorems.
  The step-level form of A1 (a concrete typed machine whose `evaluate` breaks `TypedState`) is
  reading, built on the proved judgment-level red control; building it as a kernel term is a good
  witness for the counterexample row.
- **Open obligations created:** none; A1-A12 are proposals.
- **Decisions rows proposed** (the coordinator's register): (1) "Saved frames and hook protocols
  are Kripke-closed (A1), before M6's instances"; (2) "M5's ledger declares `denoteR_typed` and
  `evalTerm_fits` by name, and its sequencing tool (A3, A4)". A2, A5-A9 and A11-A12 need no
  decision: they land proved lemmas or correct text.
