# The runtime's semantics: the core mathematics, a literature review

Companion to `docs/research/2026-09-05-runtime-proof-graph.md` (the plan) and to the
four-paper review `docs/research/2026-09-05-effects-papers-review.md`, which this note
does not repeat: MCA's purity and central morphisms, Mattick's algebraic specification,
de Vilhena's protocols, and Jacobs' Chapters 2, 5 and 6 are read there. This note collects
the mathematics the plan leans on beyond those four, states each result in the form the
tree will use, and says which node of the proof graph it discharges. Theorem numbers are
given only where the earlier review already pinned them; everything else is cited by name
and should be checked against the source before it is quoted in a packet.

The tree, as of tonight (`docs/research/DENOTE-DAG.md`): the straight-line fragment of
`Eff` has a denotation into the algebra (`meaning`) and `Api.run` agrees with it on exit
and stores, with no op-budget hypothesis. The machine replays any program the reader
produces against a decision tape (`replayEval`), with Deferred, scopes, races, interrupts,
yields and async already implemented. The fuel laws over the replay (G2) are landing. What
the plan needs from the literature is the carrier for everything past the straight line:
a behaviour that is a function of the tape, well-defined under fuel, compositional in the
program, and provable by simulation.

## 1. Two carriers: initial algebra, final coalgebra

**Syntax is initial, behaviour is final.** A signature functor `Σ` has an initial algebra
`Σ* 0`, the closed terms (`Eff` is one, with `Term` leaves); a behaviour functor `B` has a
final coalgebra `νB`, the behaviours. An operational semantics is a `B`-coalgebra structure
on terms, `⟨·⟩ : Σ* 0 → B (Σ* 0)`; the behaviour of a term is the unique coalgebra map
`beh : Σ* 0 → νB`.

**Bialgebraic semantics (Turi and Plotkin, "Towards a mathematical operational semantics",
LICS 1997; Klin, "Bialgebras for structural operational semantics: an introduction", TCS
2011).** An abstract GSOS rule is a natural transformation

```
ρ : Σ (Id × B) ⇒ B Σ*
```

("the behaviour of `op(x₁, …, xₙ)` is determined by the `xᵢ` and their one-step behaviours,
and the results are terms over the `xᵢ`"). Such a `ρ` induces a distributive law `λ` of the
free monad `Σ*` over the cofree copointed functor `Id × B`, and `λ`-bialgebras
`(X, a : ΣX → X, c : X → BX)` with the compatibility square. The two results the plan uses:

* the initial `Σ`-algebra carries a unique `λ`-bialgebra structure (the operational model),
  the final `B`-coalgebra carries a unique one (the denotational model), and the unique
  bialgebra morphism between them is both the behaviour map and a `Σ`-algebra homomorphism:
  **adequacy and compositionality in one theorem**;
* `B`-bisimilarity on terms is a congruence for every operation of `Σ`.

**What the tree takes.** Jacobs §5.5 (read in the earlier review) is the same picture. The
plan's Layer R, the reference machine on `Eff` (`docs/research/2026-09-05-runtime-proof-graph.md`
§3), is the operational model; its step is written per constructor of `Eff`, using only the
immediate subterms and their state, which is the GSOS shape. The congruence result is what
lets a rewrite pass on `Eff` be justified once for the whole runtime instead of once per
program, which is the G1 congruence the earlier review asked for. The cost of the shape:
constructs whose step needs to look *inside* a subterm's behaviour past one step (a `catch`
that must know whether the body failed) are not GSOS, and appear in the plan as frames of
the reference machine rather than as rules; §6 below says why.

## 2. Behaviour as a function of the tape: Moore machines and the Kleisli trace

**Moore coalgebras (Jacobs, Ch. 2).** For an input alphabet `D` (the decisions) and an
output set `O` (the observations), the functor `B X = O × X^D` has as final coalgebra the
set of functions `D* → O`, with `beh(x)(d₁ … dₙ)` the output after feeding the word. The
machine's `stepDecision : Decision → Machine → Machine` together with an observation map
`obs : Machine → O` is a `B`-coalgebra; its behaviour `Beh m : List Decision → O` is
`fun tape => obs (replay tape m)`. This is the "meaning is the relation over tapes" of DB-03,
stated as finality: two machines with the same behaviour are indistinguishable by any tape.

**The fuel inside one decision: Kleisli traces (Hasuo, Jacobs, Sokolova, "Generic trace
semantics via coinduction", LMCS 2007; Jacobs §5.3, Theorem 5.3.4 in the earlier review).**
One decision runs the command loop, which may not terminate within the fuel. Let `T` be a
monad for partiality (the lift monad `T X = X + 1`, or the delay monad of §3), and let the
step be `c : X → T (F X)`. When the Kleisli category of `T` is order-enriched with a bottom
and joins of ω-chains, composition is monotone and continuous, and `F` lifts to the Kleisli
category (a distributive law `F T ⇒ T F`), then

* the initial `F`-algebra in Sets, seen in the Kleisli category, is the final coalgebra of
  the lifted functor, and
* the unique coalgebra map `tr_c : X → T A` (the *trace*) is the join of the chain
  `c₀ = ⊥`, `cₙ₊₁ = c ; F̄(cₙ)`.

**What the tree takes.** The chain is fuel. `drive fuel` at fuel `n` is `cₙ`; G2's
`driveState_add` is the statement that the chain is a chain (fuel splits), `drive_stable`
that a settled element is the join, and `replay_colimit` that the join exists and is
computed by the least sufficient fuel. The order on observations is the Kleisli order, and
"a live frontier is below every observation extending its trace" is the bottom being least.
This is why the behaviour object of the plan is defined *after* G2: `Beh m tape` is the
join, and it is a total function on tapes whose decisions all settle.

**Where the tree departs from the theorem, found by G2 at its landing.** The theorem needs
the chain to be a chain along the whole trace map. On this machine it is a chain only
within one unit of work: `fire` refreshes the fuel per task, `flushAll` per round,
`replayEval` per decision, and exhaustion is silent, so the next unit runs on a half-done
machine and `cₙ` and `cₙ₊₁` at the tape level need not be comparable
(`E4-APPROX-CE-003`, `E4-APPROX-CE-004`). Two readings are open. Keep the machine and state
every behaviour under the decidable `Suffices`, in which case the Kleisli picture applies
per unit of work and the tape-level behaviour is the join *on sufficient fuel*. Or make
exhaustion absorbing (a sticky frontier), which restores the chain and the theorem as
stated; since rc.112 has no fuel, exhaustion is the model's artefact and an absorbing
frontier is the reading closer to the theorem. The plan lists this as decision D5.

## 3. Partiality and fuel: the delay monad

**Capretta, "General recursion via coinductive types", LMCS 2005.** The delay monad is the
final coalgebra `D A = νX. A + X`, with `now : A → D A`, `later : D A → D A`. Termination
`x ↓ a` is the least relation with `now a ↓ a` and `later x ↓ a` when `x ↓ a`. Weak
bisimilarity `x ≈ y` is the largest relation with: `now a ≈ now a`; `later x ≈ later y` when
`x ≈ y`; and `x ≈ y` when `x ↓ a` and `y ↓ a`. General recursion is defined into `D`, and
`D` is a monad whose bind is `later`-preserving.

**Chapman, Uustalu, Veltri, "Quotienting the delay monad by weak bisimilarity", ICTAC 2015
and MSCS 2019.** The quotient `D A / ≈` is again a monad in a constructive setting (under
countable choice, or by building the quotient as a higher inductive type); without the
quotient, `≈` is a setoid the bind respects.

**What the tree takes.** Lean has no coinductive types, so `D` is represented by its finite
unfoldings: `replayEval fuel` at each fuel. `ReplayResult.frontier` is `later`; `finished`
and `stuck` are `now`. G2's `Observation.le` is the approximation order whose chains
converge to a `≈`-class, and `replay_stable` is `x ↓ a → x ≈ now a`. The plan never needs
the quotient: every statement is "for all fuel above the sufficient one", which is the
setoid form.

## 4. Programs as trees with visible events: interaction trees and choice trees

**Interaction trees (Xia, Zakowski, He, Hur, Malecha, Pierce, Zdancewic, "Interaction
trees: representing recursive and impure programs in Coq", POPL 2020).**

```
CoInductive itree (E : Type → Type) (R : Type) :=
  | Ret (r : R)
  | Tau (t : itree E R)
  | Vis {X} (e : E X) (k : X → itree E R)
```

`Ret` returns, `Tau` is an internal step (the delay monad's `later`), `Vis e k` performs a
visible event and continues with the answer. `itree E` is a monad; `eutt` ("equivalence up
to Tau", weak bisimulation) is a congruence for `bind`; `interp h` for a handler
`h : E ~> M` is a monad morphism into an iterative monad with the laws `interp_ret`,
`interp_bind`, `interp_vis`; and `iter : (A → itree E (A + B)) → A → itree E B` satisfies
the equations of an iterative (Elgot) structure: the fixpoint law
`iter f a ≈ f a >>= case (iter f) Ret`, naturality, dinaturality and the codiagonal law.

**Choice trees (Chappe, He, Ying, Zakowski, Zdancewic, "Choice trees: representing
nondeterministic, recursive, and impure programs in Coq", POPL 2023).** The same tree with
branching nodes `Br` over a branching signature, in two flavours, visible (a step) and
invisible (a delay); strong bisimulation treats invisible branches as `Tau`, and the paper's
running examples are a cooperative scheduler with `fork` and `yield` and a CCS embedding,
with congruence of the bisimulation proved by up-to techniques (§8 below).

**What the tree takes.** The algebra's `Effects.Program Sig A` is the *finite* interaction
tree without `Tau`: `pure` is `Ret`, `perform op k` is `Vis`. The tape answers the `Vis`
nodes: a store operation is answered by the store (the handler), a fiber operation by the
scheduler, an async by the tape's `answerAsync`. `choose` is a `Br` node whose branch is
decided at compile time by the `choices` list, so no nondeterminism survives into the
machine and the choice-tree machinery is not needed yet; it becomes needed the day the
tape is quantified over (fairness, §9). What is needed now and missing from the algebra is
`iter`: `whileLoop` and `gen` have no image in `Program`. Two representations are open,
both used in the literature: the fuel-indexed approximants of §2 (the loop as its chain,
the meaning as the join), or an explicit `iter` with the Elgot laws as axioms of the
carrier (Adámek, Milius and Velebil, "Elgot algebras", 2006; Bloom and Ésik's iteration
theories). The plan chooses the first for the agreement theorems, because the machine
side is already fuel-indexed, and keeps the second for the equational layer later.

## 5. Concurrency carriers: resumptions, handlers, protocols

**Resumption monads (Cenciarelli and Moggi, "A syntactic approach to modularity in
denotational semantics", 1993; Harrison, "The essence of multitasking", AMAST 2006; Piróg
and Gibbons, "The coinductive resumption monad", MFPS 2014).** For a monad `T`, the
resumption monad `R A = μX. T (A + X)` (finite) or `νX. T (A + X)` (coinductive) is the
type of computations that either return or *suspend* with a continuation. A scheduler is a
function that holds a queue of resumptions and picks which one to advance. With an
interface functor `F` the coinductive resumption monad `νX. T (A + F X)` is the interaction
tree over `F` with `T`-effects at each node. A fiber is a resumption; the fiber machine is
the scheduler.

**Schedulers as effect handlers (Plotkin and Pretnar, "Handlers of algebraic effects",
ESOP 2009 and LMCS 2013; Kammar, Lindley, Oury, "Handlers in action", ICFP 2013; Dolan,
Eliopoulos, Hillerström, Madhavapeddy, Sivaramakrishnan, White, "Concurrent system
programming with effect handlers", TFP 2017; Sivaramakrishnan, Dolan, White, Kelly, Jaffer,
Madhavapeddy, "Retrofitting effect handlers onto OCaml", PLDI 2021).** For a signature of
operations `op : A → B`, the free model is the term algebra `return x | op(a; k)` with
`k : B → term`; a handler assigns to each operation a function of the parameter and the
(already handled) continuation, and `handle` is the unique homomorphism out of the free
algebra:

```
handle (return x)  = v_ret x
handle (op(a; k))  = v_op (a, handle ∘ k)
```

Cooperative concurrency is the handler for `fork` and `yield` whose state is a queue of
continuations: `yield` enqueues the current continuation and dequeues the next; `fork`
enqueues the new thread. Dolan et al. and the OCaml 5 paper are the same handler with
system I/O, which is the OCaml half of this estate.

**Protocols and verified cooperative concurrency (de Vilhena and Pottier, "A separation
logic for effect handlers", POPL 2021; de Vilhena's thesis, read in the earlier review).**
A protocol `Ψ` specifies what an operation may be called with and what its continuation
may assume; a handler is verified against the protocol it implements; the thesis verifies a
cooperative scheduler this way.

**What the tree takes, and the trap.** The reference machine of the plan is the scheduler
handler written out as a state machine: its state is the queue (the machine's `armed` list
and dispatchers), its `yield` is `Myield` and `fire_Myield` from tonight, its `fork` is a
`Task.start`. Two points decide its shape. First, the handler must consume the *same*
decisions the fiber machine does, or the agreement would need a translation of tapes;
so the reference machine copies the machine's scheduling skeleton and differs only in what
a fiber holds (§3 of the plan, challenge C1). Second, `fork` carries a program. In an
algebra `Program Sig A`, an operation whose parameter is itself a `Program` is a nested
occurrence through the signature parameter and is not a positive inductive definition;
interaction-tree libraries meet the same wall. The standard exit, and the plan's, is that
`fork` carries *syntax* (an `Eff` subterm, addressed by a `Point`), and the scheduler
denotes the child when it starts. This is also what the compile does (`WithFiberAction.fork
program` holds a compiled `Prim`), so the correspondence is between two addressings of the
same subterm.

## 6. Scoped operations: catch, finalizers, masks, scopes

**Algebraicity (Plotkin and Power, "Notions of computation determine monads", FoSSaCS
2002).** An operation is algebraic when it commutes with sequencing:
`op(a; k) >>= f = op(a; λb. k b >>= f)`. Every operation of a free model is algebraic. A
construct like `catch body handler` is not: `catch b h >>= f` is not `catch (b >>= f) (…)`;
it *delimits* a scope.

**Scoped effects (Wu, Schrijvers, Hinze, "Effect handlers in scope", Haskell 2014; Piróg,
Schrijvers, Wu, Jaskelioff, "Syntax and semantics for operations with scopes", LICS 2018;
van den Berg, Schrijvers, Poulsen, Wu, "Latent effects for reusable language components",
APLAS 2021).** The syntax gains a second functor `Γ` of scoped operations, with terms
`Return a | Call (Σ (Prog a)) | Enter (Γ (Prog (Prog a)))`: a scoped operation encloses a
program whose result is itself a program (what happens after the scope). Handlers become
"functorial algebras"; the laws distinguish what the scope sees from what comes after.

**What the tree takes.** `catchCause`, `matchCause`, `onExit`, `exit`, `uninterruptible`,
`interruptible`, `scoped`, `acquireRelease` are `Enter`-shaped. The straight-line
denotation `denote` handles the first five at the meta level (a `bind` and a case on the
exit) because on one fiber a scope is just a continuation; that stops being true when an
*interrupt* must see the mask, when a *scope close* must run finalizers registered by other
fibers, and when a *race* must interrupt entrants inside their scopes. The reference machine
of the plan therefore keeps scopes as frames of a continuation stack (the IR-level twins of
`Prim.onExit`, `setInterruptible`, the scope-link frames), which is the operational reading
of `Enter`. The equational laws of scoped operations (what commutes with what) are the
later logic layer, not the agreement.

## 7. Runners and comodels: the machine as a runner, the store as a comodel

**Comodels (Plotkin and Power, "Tensors of comodels and models for operational semantics",
MFPS 2008).** A comodel of a signature is a model in the opposite category: a state set `C`
with co-operations `C → A → B × C`, which is exactly a state machine answering operations.
The tensor of a model (a program) with a comodel (a state) is the operational semantics:
state passing.

**Runners (Ahman and Bauer, "Runners in action", ESOP 2020).** A runner for a signature into
a state `C` is a comodel whose co-operations may also raise exceptions and kill; `using R
@ init run p finally F` runs a program against the runner and, whatever the outcome
(return, exception, kill), runs the finalisation `F` on the final state. Runners are the
top-level effect handlers with resources, and their finalisation is the point.

**What the tree takes.** `storeHandler : Handler StoreSig (StateT Stores Id)` is the
comodel `Stores` with co-operation `syncOpStep`, and `meaning` is the tensor. `Api.run` is a
runner; scope close programs and `onExit` finalizers are its finalisation, and the machine's
exit path (`exitFiber`, the observers, `linkScope`) is the runner's `finally` written out
per fiber. The runner reading is what makes "the same store on both sides" a design
principle in the plan (challenge C1): the reference machine uses the very same comodel.

## 8. The proof method: simulation, bisimulation, up-to techniques

**Bisimulation (Milner, "Communication and Concurrency", 1989; Sangiorgi, "Introduction to
bisimulation and coinduction", CUP 2011).** A relation `R` on states is a bisimulation for a
transition system when related states have matching transitions into related states;
bisimilarity is the largest one and is proved by exhibiting any bisimulation containing the
pair. A *simulation* asks for the match in one direction; a *stuttering* (or weak)
simulation lets one side take several steps, or none, for one step of the other.

**Up-to techniques (Pous, "Coinduction all the way up", LICS 2016; Hur, Neis, Dreyer,
Vafeiadis, "The power of parameterization in coinductive proof", POPL 2013).** For a
monotone `b` on a complete lattice, the companion `t` is the largest compatible function;
"bisimulation up to `f`" is sound whenever `f ≤ t`, and compatible functions (up to
context, up to equivalence, up to transitivity) compose. Parameterized coinduction lets a
coinductive proof be built incrementally, accumulating the pairs already justified.

**What the tree takes.** Tonight's proofs are a stuttering simulation with fuel accounting:
one local step of the frame fiber is one or two commands of the loop, the counts are
carried as `∃ c ≤ 2n`, and the induction is on the length of the sequential run because the
tape is fixed and the fiber is alone. Past the straight line, with several fibers, the
induction can no longer be on one program's structure: the plan's Layer S (§4 of the plan)
is a simulation *relation* on whole machine states, fiber by fiber, and the theorem is that
every decision preserves it. Because the machine has fuel and no coinductive types, the
relation is a plain inductive invariant over decisions and the "up to" content is the fuel
bookkeeping: the number of commands one reference step costs, and the observation that a
yield round spends at least `defaultBudget - 1` steps. The plan records where an up-to
technique will be wanted (up to context, for the congruence of §1; up to fuel, for the
rounds) so that the Lean encoding, an explicit measure in the invariant, is chosen once.

## 9. Fairness, liveness, deadlock

**Fair operational semantics (Lee, Cho, Song, Hur and others, "Fair operational semantics",
PLDI 2023).** Fairness is put into the operational semantics itself: steps that must
eventually happen carry counters, a fair execution is one on which every counter is reset
infinitely often, and a *fairness-preserving simulation* is a simulation that also
maintains the counters, so that liveness properties (every waiting thread is eventually
scheduled) transfer along compilation.

**Deadlock as a greatest fixed point (standard).** A state is deadlocked when no fair tape
advances it: `Deadlocked` is the largest set of states closed under every decision that
does not make progress, modulo the decisions that only interrupt.

**What the tree takes.** Both live on `Beh` over *sets* of tapes and are rows of the plan's
last wave (G6, G7 in the earlier review). The tape is where fairness is stated: a tape is
fair when every armed dispatcher is eventually fired and every parked async is eventually
answered; the machine's `armed` FIFO (R2-15) makes `flush` fair by construction, which is
a theorem to state rather than assume. Fairness-preserving simulation is the reason the
plan's simulation relation carries the `armed` order exactly rather than up to permutation.

## 10. Time and streams

**Discrete relative time (Baeten and Middelburg, "Process Algebra with Timing", Springer
2002).** ACP with discrete relative timing adds a time-slice operator (the tick) and
relative delays `σ^n(x)` with laws for how delays distribute over choice and sequencing;
timers are deadlines counted in slices from the current one.

**Streams (Rutten, "Behavioural differential equations: a coinductive calculus of
streams, automata, and power series", TCS 2003).** A stream is a coalgebra of `X ↦ A × X`
(head and tail); stream equality is bisimilarity; stream functions are defined by
behavioural differential equations (initial value and derivative) and proved equal by
coinduction.

**What the tree takes.** The timer spike (`workshop/Timer`, 41 theorems, four rc.112 clock
findings) is a logical clock with relative steps, which is the discrete-relative-time
reading; joining it to `Stores` and giving the tape a time decision is a wave of the plan
(challenge C11). The WHATWG streams reification is Rutten's calculus in its own package,
and its join to the runtime is through the reader (generators as the loop shape), not
through the fiber machine.

## 11. The reading list, by node of the graph

| Node (plan §) | Result | Source |
| --- | --- | --- |
| BEH/order, BEH/split, BEH/colimit (G2) | trace as join of the fuel chain; approximation order; stability | Hasuo–Jacobs–Sokolova 2007; Jacobs §5.3 (5.3.3, 5.3.4); Capretta 2005; Chapman–Uustalu–Veltri 2015 |
| BEH/tape | behaviour as a function of decision words; finality of Moore coalgebras | Jacobs Ch. 2 |
| REF/machine, REF/denote | scheduler as a handler; resumptions; fork carries syntax | Plotkin–Pretnar 2009/2013; Kammar–Lindley–Oury 2013; Dolan et al. 2017; Piróg–Gibbons 2014; Xia et al. 2020 |
| REF/scoped (frames for catch, finalizers, masks, scopes) | algebraic vs scoped operations; `Enter` | Plotkin–Power 2002; Wu–Schrijvers–Hinze 2014; Piróg et al. 2018 |
| REF/store | comodels and runners; finalisation | Plotkin–Power 2008; Ahman–Bauer 2020 |
| SIM/* | stuttering simulation, up-to techniques, invariants with measures | Milner 1989; Sangiorgi 2011; Pous 2016; Hur et al. 2013 |
| AGR/congruence | GSOS, bialgebras, bisimilarity as a congruence | Turi–Plotkin 1997; Klin 2011; Jacobs §5.5 |
| SIM/loop, the `iter` layer | Elgot iteration laws | Xia et al. 2020 (`iter`); Adámek–Milius–Velebil 2006 |
| LIVE/fair, LIVE/deadlock | fair operational semantics, fairness-preserving simulation | Lee et al. 2023 |
| CLOCK/join | discrete relative time | Baeten–Middelburg 2002 |
| STREAMS/join | stream calculus, coinduction | Rutten 2003 |
| the logic layer (later) | protocols as handler specifications; MCA modalities | de Vilhena–Pottier 2021 and the earlier review |

What is deliberately not taken: process calculi with communication as the carrier (CCS,
the π-calculus); the fibers do not communicate by channels but through the store and the
scheduler, and the tape is the only source of nondeterminism. Probabilistic and weighted
traces (the other instances of the Kleisli theorem) are not this runtime. Coinductive
types: everything is fuel-indexed, per §3.
