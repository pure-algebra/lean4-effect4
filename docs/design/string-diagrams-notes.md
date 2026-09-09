# String diagrams for this runtime — 2026-09-08

Seat: the string-diagram reading, against the tree at `781cfbc`. Sources: Kissinger's *Picturing
Quantum Processes* deck (`docs/research/picturing_quantum_processes.pdf`; the deck is an
incremental build with no printed numbers, so "slide N" here means PDF page N), Coecke &
Kissinger *CQM II* (`docs/research/categorical_quantum_mechanics_2.pdf`; printed page = PDF page), CQM I (arXiv:1510.05468), and the effectful-category line
(Román, arXiv:2205.07664 and arXiv:2305.06075; Jeffrey 1997). Nothing tracked was edited except
this file. This note is an input to `2026-09-08-design-language.md`, written in parallel; it does
not depend on it.

## 0. Summary — five lines

1. **Take the vocabulary.** Wire = system, box = process, diagram = term, `∘` = `bind`, `⊗` =
   independence. It is the right frame and it is already how we talk (PQP slide 14; CQM II §2 p.2).
2. **State the mismatch first.** A run is **not** a monoidal diagram. Our composition is
   *premonoidal*: `⊗` is not a bifunctor because the tape decides the interleaving. The exact
   fix already exists — Jeffrey's **runtime wire**, promoted to a theorem by Román (2205.07664
   Thm 2.14, Cor 2.15). **Our tape is that wire**, and `replay (program, fuel, tape)`
   (`src/Effect4/Api.lean:156-162`) is literally its hom-set.
3. **Spiders are real here.** `DeferredCell` (`src/Effect4/Machine/Stores.lean:1298-1303`) is one
   completion fused to n waiters: a 1→n spider on the classical wire, with a genuine fusion law
   (await-after-done resumes at once). Same node for fiber-exit observers, Latch, PubSub. One
   node type replaces four.
4. **Three wire grades, not two.** Value (`Term`: copy ✓ delete ✓), handle (copy ✓ delete ✗ — a
   drop must be a close), continuation/park token (copy ✗ delete ✗ — one-shot). CQM's
   classical/quantum split gives the *notation*; its doubling construction gives us nothing.
5. **Two diagrams, not one.** The **program** diagram has no runtime wire and genuine `⊗`; the
   **run** diagram has the runtime wire and is totally ordered. Concurrency = the reorderings
   along the runtime wire that the program diagram does not fix. A frontier is the run diagram
   with the runtime wire still dangling — a *monoidal context*, a diagram with a hole.

---

## 1. Process theory as the frame

**What the sources say.** PQP slide 14: "Wires represent *systems*, boxes represent *processes*",
and a process theory is a collection of processes "that make sense to combine into diagrams".
Slide 16: processes with no input are *states*, none out are *effects*, neither are *numbers*.
CQM II §2 (p.2) restates it and adds string diagrams proper (input-to-input and output-to-output
connections, cups and caps, the yanking equation (1)). CQM I Def 2.1 is the formal definition;
its equality principle is that diagrams which deform into each other without changing connections
are equal.

**The mapping.** Read our diagrams top-to-bottom (a program's text order), not bottom-to-top as
the deck does.

| CQM | here | file:line |
| --- | --- | --- |
| wire (system) | a **value in flight at a `Ty`** — the answer of a node, the request of a row | `Program/Eff.lean:187-189` |
| wire, thick | a **handle**: `Val.fiber`, `Val.cell`, `Val.promise`, `Val.scopeHandle` | `Api.lean:66-68` |
| wire, dashed/cut | a **park token**: `(fiber, token)`, a continuation | `Machine/Fibers.lean:361-362` |
| box | an `Eff` node under its interpretation | `Program/Eff.lean:250-333` |
| box on the boundary | a **row**: request wire in, answer wire out, error wire out | `Program/Eff.lean:177-199` |
| `g ∘ f` | `Eff.bind first rest` | `Program/Eff.lean:264` |
| `f ⊗ g` | the *independence* of two fibers between fork and join | `Program/Eff.lean:288, 315` |
| state (no input) | `succeed`, `sync`, a literal | `Program/Eff.lean:254, 260` |
| effect (no output) | discard / interrupt / a finalizer | `Program/Eff.lean:269, 291` |

Three negative rulings, because the obvious readings are wrong:

- **A wire is not a fiber.** A fiber is a *box with a lifetime*; what travels on a wire is its
  handle (`Val.fiber`) and, at the join, its `Exit`. Drawing fibers as wires makes `awaitFiber`
  look like a plain composition, which hides that it may park.
- **A wire is not a scope's lifetime.** A scope is a *region* (a boundary in the plane), not a
  wire. `scoped` (`:289`) and `uninterruptible` (`:272`) are the same shape: a box that contains
  a sub-diagram and changes what deformation is legal inside it. Draw them as rules around a
  region.
- **`fork` is not `⊗`.** `fork` is a box that *creates* a second wire; `⊗` is the fact that,
  between that box and `awaitFiber` (`:286`), the two columns share no wire. The parallelism is
  the negative space, not a generator.

**Where it breaks, and what it is instead.** Two forks do not interchange, because the tape orders
them (`pTwo`, §5). So `(⊗) : C × C → C` is not a functor; it is only functorial in each variable
separately. That is exactly the definition of a **binoidal** category (Román 2205.07664 Def 2.1)
and, with central coherence, a **premonoidal** category (Def 2.2, after Power–Robinson). Adding a
chosen family of central "pure" morphisms gives an **effectful category** = non-cartesian Freyd
category (Def 2.4).

**Answer: an effectful (non-cartesian Freyd) category, symmetric premonoidal, whose centre is the
pure terms.** Not "monoidal with a chosen braiding". Reason: a braiding would make the two fork
orders isomorphic under a canonical map, i.e. the *same* diagram viewed twice; here they are two
different runs with two different traces and (in general) two different exits. A braiding asserts
an equality we can refute from `harness/truth/corpus.json`. The centre is `Term`/`Terms`
(`Program/Eff.lean:223-230`) plus anything reading no store and touching no scheduler; the
effectful part is everything with a store or a fiber leg.

**The construction to adopt.** Jeffrey's technique, promoted to Theorem 2.14 in 2205.07664
("Premonoidal categories are Monoidal categories with a Runtime"): freely add one object `R` to
the input *and* output of every effectful generator (not to pure ones), braided with respect to
everything else, and then

```
Eff(V,G)(A,B)  ≅  MonRun(V,G)(R ⊗ A, R ⊗ B)
```

Corollary 2.15: **you may use ordinary string diagrams, quotiented by ordinary isotopy, provided
you draw the runtime as an extra wire that is an input and output of every effectful box.**

That wire is our tape. `Api.lean:156-162`:

```lean
def replay (program : Program) (fuel : Nat) (tape : List Decision) … : Run
```

is `R ⊗ A → R ⊗ B` with `R` the decision stream and the return `Run` carrying the residual `R`
(`Outcome.frontier`, `Api.lean:146`). This is not an analogy; it is the same shape, and it means
the "the tape orders everything" caveat becomes a *drawing convention* rather than a footnote.

---

## 2. Diagram = term: what "only connectivity matters" does and does not say

**Expresses correctly (with `R` drawn):**

- **Associativity of `∘`.** `bind (bind a b) c` and `bind a (bind b c)` are one diagram. This is
  why we can afford two frame shapes (`bind` and `gen`, `Program/Eff.lean:264, 265`) for one
  meaning.
- **Unit and associativity of `⊗`** for the pure fragment, and **interchange for central boxes**:
  two `Term` computations on disjoint variables may be drawn in either order. This is `Term`'s
  centrality, and it is the *only* interchange we get for free.
- **Independent fibers may be drawn side by side.** In the *program* diagram (no `R`), a forked
  child and the parent's continuation are two columns and their relative height means nothing.

**Would wrongly assert, if `R` is omitted:**

- **Two forks are interchangeable.** They are not. `pTwo` forks 1 then 2 and the schedule is
  `forked 0->1, scheduled, forked 0->2, scheduled, parked 0, ran 0 (→ start 1), ran 0 (→ start 2)`
  — the arming order of the dispatcher (`RunMachine.armed`, `Machine/Fibers.lean:419-423`) is the
  fork order. Swapping the forks swaps the trace. Isotopy in a monoidal diagram would make these
  equal.
- **A park and its resume are one wire.** They are not one wire; they are a wire *cut by the
  environment*. `callback` (`Program/Eff.lean:285`) parks on a row;
  `RunDecision.answerAsync (fiber) (token) (answer)` (`Machine/Fibers.lean:441`) re-enters. Isotopy
  would let a box slide across the cut. Forbidden: everything after the cut depends on a value
  that did not exist before it.
- **Scoped regions are transparent.** `uninterruptible` (`:272`) changes what the *environment*
  may do inside it, so its boundary is load-bearing; a box may not be slid across it.

**Proposed deformation rule (D-DEFORM).** A diagram of a run may be deformed exactly by:

- **D1.** Planar isotopy that does not change the order in which boxes meet the runtime wire `R`.
- **D2.** A box with **no** `R` leg is central and may slide anywhere its data wires permit
  (pure terms, atoms, `branch` tests, `succeed`).
- **D3.** A box **with** an `R` leg may slide only *along* `R`, never past another `R` box.
- **D4.** A **cut** in `R` — a park, a `choose` site (`:293`), a `fire`/`flush` decision
  (`Machine/Fibers.lean:431-434`) — is a hard boundary. Nothing crosses it, in either direction.
  Equivalently: a run diagram deforms freely *inside* the segment between two consecutive tape
  decisions, and not at all across one.

D1–D4 is Corollary 2.15 specialised. Its virtue: "the tape is the total order" stops being a
warning and becomes the one thing the picture makes visible.

---

## 3. Causality

**What the sources say.** PQP slide 44 defines discarding as the unique effect with the property
that it collapses any state; slide 50 states causality as `Φ` followed by discarding equals
discarding, and derives no-signalling. CQM II Def 3.5 (p.10) generalises to hybrid boxes with the
motivating sentence: "if we apply a process to some inputs, but then discard all of its outputs,
its performance has gone to waste, and we could as well have simply discarded its inputs." CQM I
makes this "the tensor unit is terminal".

**(a) Discarding is our interrupt — but ours is not terminal, and that is the finding.**
`RunDecision.interruptFrom (interruptor) (annotations) (target)` (`Machine/Fibers.lean:444`)
discards a fiber's future. CQM's discard is *terminal*: there is exactly one way to throw a wire
away, and it carries no data. Ours carries data twice over: the interruptor and its annotations,
and the finalizer program that runs on the way out (`acquireRelease`, `Program/Eff.lean:291`;
`onExit`, `:269`; `RunEvent.finalizerProgram (fiber) (finalizer) (exit)`,
`Machine/Fibers.lean:368`).

**Ruling to propose: draw discard as a named box, not as a ground symbol.** The causality
equation we can actually state is weaker and is a rewrite rule, not a terminality:

> discarding the output of a scope = running its finalizer on the discarding `Exit`, then
> discarding.

Saying "our runtime is causal in the CQM sense" would be false and would erase finalizers from
the picture. Say the rewrite instead.

**(b) No signalling from the future is real, and it is one-shot continuations.** A park token is
cleared by its `Resume` (hazel notes §1: "one-shot continuation `cont (ℓ, N)` ↔ park token +
`Resume` clearing it"; grill Q3: request identity is `(fiber, token)`). Because a continuation
cannot be resumed twice, no information crosses a cut backwards. That is the content of causality
here, and unlike (a) it is a statable theorem over the machine (one exit per fiber, one completion
per cell — the "torch" theorems already named in the hazel notes §3).

**(c) Is `Cause` the trace of a discard? No.** The runtime `Cause` is rc.112's flat, dedup'd
reason list and *is* the normal form (grill agenda Q15); `CauseTerm`
(`Program/Eff.lean:240-246`) is the tree, whose `causeOf` is a declared lossy quotient. The trace
of a discard is the event sequence — `interruptRecorded`, `interruptDeferred`,
`childrenInterrupted`, `finalizerProgram`, `exited` (`Machine/Fibers.lean:363-376`). `Cause` is
only the *annotation the discard carries*. A design language that draws `Cause` as "the discard's
history" will mis-teach the flat carrier; draw the events as the history and `Cause` as a label
on the discard box.

**(d) The happens-before drawing rule.** CQM's "causal structure is diagram shape" transfers, but
only after the two-diagram split, because `R` threads through *everything* and would say there is
no concurrency at all:

- **Program diagram — no `R`.** An edge is a data dependence. Two nodes with no directed path
  between them are **concurrent**. Forks are genuine `⊗`.
- **Run diagram — with `R`.** Every effectful box is totally ordered along `R`.
- **Concurrency is the difference:** the reorderings along `R` that the program diagram does not
  fix. That is a definition, not a slogan, and it is exactly what "no off-tape choice"
  (INV-TAPE-1, grill §2.11) asserts.

---

## 4. Classical vs quantum wires → pure, handle, continuation

**What the sources say.** CQM II §3 (p.5): "classical single wire / quantum double wires", because
"unlike quantum systems, which can only be used once, classical data can be copied and deleted".
§3.1 Def 3.1 (p.6) defines a spider and its rules: **spider-fusion** (eq. 4), leg-swapping
invariance, conjugation invariance, and "a single wire, cups and caps are spiders". `copy` and
`delete` are the 1→2 and 1→0 spiders. Def 3.2 (p.7, eq. 8): a *classical value* is a state copied
by the copy-spider — copiability **defines** classicality. PQP slides 66 (single vs double wires),
70 (spiders), 71 (the fusion rule), 72 (quantum spiders as doubled classical ones).

**Our three grades.**

| grade | draw | copy | delete | witness |
| --- | --- | --- | --- | --- |
| **value** | thin | ✓ | ✓ | `Term`, positional `Var := Nat` used any number of times, or none (`Program/Eff.lean:217-230`) |
| **handle** | thick | ✓ (the *name*) | ✗ | `Val.fiber/cell/promise/scopeHandle` (`Api.lean:66-68`); dropping a scope handle without `closeScope` (`Program/Eff.lean:330`) leaks |
| **continuation** | dashed, cut | ✗ | ✗ | park token `(fiber, token)` (`Machine/Fibers.lean:361-362`); one-shot |

This is a **three**-way split where CQM has two, and the middle grade is new: a handle is a
classical *name* over a non-classical *resource*. Copy holds, delete does not. CQM has no wire
like that, so do not force it into the classical/quantum frame; just record the third grade.

**Doubling: reject.** Doubling exists in CQM to make discarding definable and numbers positive
(PQP slides 36–44). We have no positivity to enforce and discarding is a primitive with a program
attached (§3a). Take the *presentational* half — wire thickness distinguishes what may be copied —
and drop the construction.

**Spiders: adopt, and they are already in the tree.**

`DeferredCell` (`Machine/Stores.lean:1298-1303`):

```lean
structure DeferredCell where
  completion : Option Program
  waiters    : List (FiberId × Nat)
```

and on completion the whole waiter list moves to the due queue at once
(`Machine/Stores.lean:1365-1369`). That is a spider: **one completion leg fused to n resume legs,
order among the legs irrelevant.** The fusion law is real, not decorative: awaiting a cell that is
already done resumes immediately rather than parking (hazel notes §1, `E4-CHECK-CE-005`), so
"complete then await" and "await then complete" are the same n-legged node.

Same node, three more times: fiber-exit observers (`RunEvent.observerFired`,
`Machine/Fibers.lean:366` — one exit, many observers), Latch, PubSub publish.

**`Ref` is not a spider.** A `Ref` cell is the paradigm *premonoidal generator* — Román's Fig. 2
is `print`, and the point is precisely that two writes do not interchange. Drawing `Ref` as a dot
would suggest a fusion law it does not have. `Ref` is a box with an `R` leg.

**Ruling to propose:** one node type, "spider = a store cell whose only law is *one completion,
any number of waiters, order irrelevant*", drawn as a dot. Deferred, Latch, fiber-exit, PubSub
collapse to it. Everything else with state is a box on `R`.

---

## 5. Measurement and classical control → the tape

**What the sources say.** CQM II §4.1 (p.22): measurement is a *bastard* spider with some legs
classical and some quantum; discarding the quantum output gives a demolition measurement,
discarding the classical output gives decoherence. §4.2 (from p.25) redraws teleportation with a
**classical wire** carrying the outcome to a **controlled unitary**, whose defining equations (27)
say the classical input is *copied* and used to pick the operation. Deleting that classical wire
destroys the protocol (Bob gets the maximal mixture).

**Our analogue is exactly this.** `RunDecision` (`Machine/Fibers.lean:429-448`) is classical data
entering from the environment: `fire (owner)`, `flush`, `evaluate (fiber)`,
`yieldVerdict (fiber) (verdict)`, `answerAsync (fiber) (token) (answer)`, `interruptFrom`,
`installMiddleware`. `choose (site) (left) (right)` (`Program/Eff.lean:293`) is the controlled
branch, answered by `choices : List Bool` threaded through `compile` (`Api.lean:124-125`) —
literally CQM's "classical input copied and used to pick the operation".

### 5.1 `pFork`, as a **program** diagram (no runtime wire; `⊗` is genuine)

`Effect.flatMap(Effect.forkChild(Effect.flatMap(Effect.yieldNowWith(0), a0 => Effect.succeed(7)),
{startImmediately:false, uninterruptible:"inherit"}), a0 => Fiber.await(a0))`

```
                     | ()
              +------+---------+
              |   forkChild    |            withFiber (.fork …)   Eff.lean:288,315
              +--+----------+--+
                 |          #                   # = thick: a handle
    a0 : Fiber<num>         #  child fiber
      (thin: copyable)      #
                 |     +----#-----+
                 |     | yieldNow |                              Eff.lean:282
                 |     +----+-----+
                 |     +----+-----+
                 |     |succeed 7 |
                 |     +----+-----+
                 |          #  exit = success 7
              +--+----------#--+
              |   awaitFiber   |   (the join)                    Eff.lean:286
              +-------+--------+
                      | Exit<number>
```

The two columns share no wire between the fork box and the join box: that is the program's `⊗`,
and their relative height is meaningless.

### 5.2 `pFork`, as a **run** diagram (runtime wire `R`; nothing is parallel any more)

`o` = a tape decision entering from the environment; `run = replay program fuel [evaluate, flush]`
(`Api.lean:171-172`). The trace is `harness/truth/corpus.json`, program `pFork`.

```
 R ==o(evaluate 0)==> [start 0] ==> [fork 0->1] ==> [schedule task owner=0]
                                        #
                                        #  fiber 1: a wire, not yet running
    ==> [park 0 tok=0] - - - - - cut - - - - -
    ==o(flush)==> [ran task owner=0] ==> [start 1] ==> [park 1 tok=1] - - cut - -
    ==> [ran task owner=1] ==> [resume 1 tok=1] ==> [start 1]
    ==> [exit 1 = success 7] ==(*)==> [observerFired 1]
    ==> [resume 0 tok=0] ==> [start 0] ==> [exit 0 = success(success 7)]

    (*) the join spider: one exit leg, n observer legs
```

`pTwo` is the same picture with two forks and two spiders, and it is the refutation of interchange:
its schedule is `forked 0->1, sched, forked 0->2, sched, parked 0, ran 0 → start 1, ran 0 →
start 2, …`, exit `success(success 2)`. Swap the two `forkChild` boxes in the program and the run
diagram changes; a monoidal isotopy would have called them equal.

### 5.3 A scope with a finalizer, in the proposed notation (`pAcquire`)

Double rules are a scope region; `[[ … ]]` is the discard box, which — unlike CQM's ground
symbol — is *named* and carries data.

```
  ================ scope s ================================
  ||        | ()                                         ||
  ||   +----+--------+                                   ||
  ||   |   acquire   |  succeed 7                        ||   Eff.lean:291
  ||   +----+--------+                                   ||
  ||        | a1 : number                                ||
  ||        +-------o------+   copy spider (a1 is a      ||
  ||        |              |   classical value: CQM II   ||
  ||     .. body ..        |   Def 3.2, eq. 8)           ||
  ||        |              v                             ||
  ||        |     +--------+---------+                   ||
  ||        |     | release (a1, exit)|  Ref.set          ||   RunEvent.finalizerProgram
  ||        |     +--------+---------+                   ||   Fibers.lean:368
  ||        |              |                             ||
  ||        |          [[ discard ]]                     ||
  ========= | ==============================================
            | a1
```

Read the boundary as the deformation rule of §2: nothing slides across the double rule, because
the region decides what runs on the way out. `uninterruptible` is drawn the same way with a
different label — same shape, different environment permission.

### 5.4 Is the process diagram the right *primary* picture of a run?

**No — it is the primary picture of a program, and a derived picture of a run.** A run is
`replay (program, fuel, tape)`: a function of two arguments (`Api.lean:156-162`). One run's diagram
is the program's diagram with one tape **plugged into `R`** — in CQM's own vocabulary, a classical
*state* plugged into the runtime wire, exactly as (27)'s classical input picks the operation.

That factoring is what makes the frontier drawable: `Outcome.frontier` (`Api.lean:146`) is the run
diagram with `R` still dangling and one or more dashed continuation wires still open — a diagram
with a hole. That object has a name and a theory: a **monoidal context** (Román, *Monoidal Context
Theory*, arXiv:2404.06192; Earnshaw–Hefford–Román, *The Produoidal Algebra of Process
Decomposition*, arXiv:2301.11867 / CSL 2024), "a process from A to B with a hole admitting a
process from X to Y", with two promonoidal structures for sequential and parallel composition.
Recommend the design language use "context" for the frontier and reserve "diagram" for a closed
run.

---

## 6. Effect handlers as string diagrams — what actually exists

I searched for the "Effect Handlers as String Diagrams" line. **There is no settled diagrammatic
notation for algebraic effects and handlers.** What the search returns is term-based: *Hefty
Algebras* (arXiv:2302.01415), *A Calculus for Scoped Effects & Handlers* (arXiv:2304.09697),
*Abstracting Effect Systems* (arXiv:2404.16381), Lindley et al. *Algebraic effects and handlers for
arrows*, *Generalized monoidal effects and handlers* (JFP 30 e23, 2020). Useful, already in
`2026-09-07-lit-papers.md`, and not pictorial. Piedeleu & Zanasi's *An Introduction to String
Diagrams for Computer Scientists* (CUP, Elements in Applied Category Theory) is the general
conventions reference, not an effect-handler one.

What *does* exist and fits us precisely is the effectful-category line: **Jeffrey (1997)**,
"Premonoidal categories and a graphical view of programs" (the runtime wire, preformally);
**Román, arXiv:2205.07664** §2.1–2.3 (Def 2.1 binoidal, Def 2.2 premonoidal, Def 2.4 effectful
category = non-cartesian Freyd, Def 2.8 the runtime monoidal category, **Thm 2.14** the bijection,
**Cor 2.15** the licence to use ordinary isotopy once `R` is drawn; Fig. 3 fixes the convention
of **two colours, values and computations** — "Hello world is not world hello"); **Román,
arXiv:2305.06075** (the same result as an internal-language theorem); and **arXiv:2404.06192 /
2301.11867** (monoidal contexts, diagrams with holes: our frontier).

**Verdict for the design-language seat.** Their conventions fit the *run* picture better than
CQM's, because they were built for exactly our failure of interchange: a runtime wire, two
colours for pure vs effectful, a centre. CQM's conventions fit the *store* picture better, because
spiders, discard and wire grades are about copy/delete/fan-out, which the effectful line does not
address at all. **Take the frame from Román/Jeffrey and the nodes from Coecke–Kissinger.** That is
the recommendation; it is not a compromise, the two halves are disjoint.

---

## 7. Take / reject, one line each

**Take.**

1. **Wire/box/`∘`/`⊗` vocabulary** (PQP 14, CQM II §2) — it is the right frame and costs nothing.
2. **"Only connectivity matters", with the premonoidal caveat** — as rule D-DEFORM (§2 D1–D4),
   with the runtime wire drawn. Without `R`, the principle asserts falsehoods about fork order.
3. **The runtime wire = the tape** (Román Thm 2.14, Cor 2.15) — the single most useful import;
   it turns our biggest caveat into a drawing convention.
4. **Two colours, pure vs effectful** (Román Fig. 3) — the centre is `Term`; everything with a
   store or scheduler leg is effectful.
5. **Spiders for fan-out/fan-in** (CQM II Def 3.1, eq. 4) — one dot for Deferred, Latch,
   fiber-exit observers, PubSub; the fusion law is real (await-after-done).
6. **Wire grades by thickness** (CQM II §3 p.5) — value / handle / continuation, with the copy and
   delete laws each grade does and does not satisfy.
7. **Discarding as the picture of interrupt/finalize** (PQP 44, 50; CQM II Def 3.5 p.10) — but as
   a *named box with data*, and as a rewrite rule, never as terminality.
8. **Monoidal contexts for the frontier** (arXiv:2404.06192) — a run that stopped is a diagram
   with a hole, and that object already has a theory.

**Reject.**

1. **Doubling** (PQP 36–44, CQM II §2) — it exists to define discarding and force positivity; our
   discard is primitive and carries a program. Keep the thickness convention, drop the construction.
2. **Terminality of discard / causality as stated** — false here: a finalizer runs on the way out.
3. **Hilbert spaces, ONBs, `Mat(C)`, completeness theorems** (CQM II §3.6, Thm 3.18/3.19) — the
   semantic model is not ours.
4. **Phases, phase groups, complementarity** (PQP 78–84; CQM II §5) — no analogue; nothing in our
   runtime is unbiased with respect to anything.
5. **Entanglement, GHZ/W, anti-spiders, SLOCC** (CQM II §4.4–4.5) — no analogue.
6. **Cups, caps and the yanking equation** (CQM II §2, eq. 1) — they need a compact-closed
   structure we do not have; a wire cannot be bent backwards in time here, and pretending it can
   is precisely the no-signalling-from-the-future violation §3b forbids.
7. **Born rule / probabilities** (PQP 16, 44) — our numbers are not probabilities; a tape is
   chosen, not sampled.

---

## 8. Vocabulary crosswalk

| CQM term | our term | transfers, or the caveat |
| --- | --- | --- |
| system / wire | a value at a `Ty` (`Eff.lean:187-189`) | transfers |
| box / process | an `Eff` node (`Eff.lean:250-333`) | transfers |
| diagram | a program term | transfers, modulo D-DEFORM |
| sequential composition `∘` | `bind` (`Eff.lean:264`) | transfers |
| parallel composition `⊗` | fork/join independence (`:288, :286`) | **caveat: not a bifunctor.** Premonoidal; only the centre interchanges |
| "only connectivity matters" | D-DEFORM D1–D4 | transfers **only** with the runtime wire drawn |
| — (absent in CQM) | the runtime wire `R` = the tape | Román Thm 2.14; `replay` is its hom-set (`Api.lean:156`) |
| state (no input) | `succeed` / `sync` (`:254, :260`) | transfers |
| effect (no output) | discard / finalizer (`:269, :291`) | transfers as a *shape*; not terminal |
| number | — | no analogue; reject the Born rule |
| classical wire (single) | value wire: `Term` (`:223-230`) | transfers; copy and delete both hold |
| quantum wire (double) | continuation wire: park token (`Fibers.lean:361`) | transfers in spirit — one-shot, no broadcasting; **not** by doubling |
| — (absent in CQM) | handle wire: `Val.fiber/cell/…` (`Api.lean:66`) | third grade: copy ✓, delete ✗ (a drop must close) |
| spider (Def 3.1) | a completion cell: `DeferredCell` (`Stores.lean:1298`) | transfers; one completion, n waiters |
| spider-fusion (eq. 4) | await-after-done resumes at once (`E4-CHECK-CE-005`) | transfers |
| copy-spider / classical value (eq. 8) | a `Term` bound to a `Var`, used n times | transfers |
| delete-spider | dropping a value | transfers for values; **not** for handles |
| discarding (PQP 44) | `interruptFrom` (`Fibers.lean:444`) | **caveat: not terminal**; carries interruptor + annotations |
| causality (PQP 50, Def 3.5) | discard-a-scope = run finalizer, then discard | **caveat:** a rewrite rule, not terminality |
| no-signalling | one-shot continuations | transfers, and is statable as a theorem |
| measurement (§4.1 p.22) | a `RunDecision` entering `R` (`Fibers.lean:429-448`) | transfers as a *shape* (classical leg out of an effectful box) |
| controlled unitary (eq. 27) | `branch` (`:275`) / `choose` (`:293`) + `choices` (`Api.lean:124`) | transfers; classical input copied to pick the arm |
| decoherence (§3.4 p.15) | — | no analogue; reject |
| — (absent in CQM) | frontier | a **monoidal context**: a diagram with a hole (arXiv:2404.06192) |

---

## 9. What I read and screenshotted

**Read in full (text extractions in the session scratchpad `books\`):** the PQP deck extraction
(19 KB — thin, as warned, which is why the slides were read as images); the CQM II extraction
(65 KB — the prose and equation numbering are usable, the diagrams are not).

**Screenshotted and read as images** (`scratchpad\pqp\`, `scratchpad\cqm2\`, liteparse
`screenshot`, 130–150 dpi). PQP slides 1–12, **14** (wires = systems, boxes = processes),
**16** (states / effects / numbers, Born rule), 22–24, 36, **44** (discarding, the defining
equation), **50** (causality; no-signalling), 56, 60, 63, **66** (single vs double wires;
stochastic maps), 68, **70** (spiders), 71 (fusion rule), **72** (quantum spiders), 76
(measurement). CQM II pages 5, **6** (§3.1 Spiders: `copy`/`delete`, Def 3.1, fusion eq. (4),
leg-swapping, conjugation, "a single wire, cups and caps are spiders"), 7, **10** (Def 3.5,
causality for hybrid boxes), **15** (§3.4 decoherence), 16, **22** (§4.1 measurement, demolition
vs non-demolition), **23** (collapse; von Neumann measurements).

**Fetched:** CQM I (arXiv:1510.05468) for the process-theory definition and the causality
postulate; Román, *Promonads and String Diagrams for Effectful Categories* (arXiv:2205.07664) —
fetched as PDF and parsed locally, §§1–3 read in full including Defs 2.1–2.10, Thm 2.14,
Cor 2.15; abstracts of arXiv:2305.06075, arXiv:2404.06192, arXiv:2301.11867.

**Read in the tree:** `src/Effect4/Program/Eff.lean:170-333`, `src/Effect4/Machine/Fibers.lean:345-454`,
`src/Effect4/Machine/Stores.lean:1297-1400`, `src/Effect4/Api.lean` (whole),
`harness/truth/corpus.json` (all eleven programs; `pFork`, `pTwo`, `pAcquire` used above),
`docs/research/2026-09-07-grill-agenda.md`, `2026-09-07-hazel-design-notes.md`,
`2026-09-07-cas-design.md` §0–1, `2026-09-07-lit-papers.md` §Q2/Q11.

Written 2026-09-08.
