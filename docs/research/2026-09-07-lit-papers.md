# Literature answers to the fifteen open design questions — 2026-09-07

Read-only. Corpus: the 21 PDFs under `docs/research/2026-09-02-web-standards-sources/papers/` plus
the reading map, parsed with `liteparse` and read at the sections cited. Judged against
`2026-09-07-implementation-direction.md` §2 (L1–L10) and `2026-09-07-open-design-questions.md`
(Q1–Q15). Builds on `2026-09-05-effects-papers-review.md` (a **disjoint** four-paper corpus: MCA,
Mattick, de Vilhena, Jacobs) and on `2026-09-07-hazel-design-notes.md` as corrected by
`2026-09-07-manifest-review.md` §B. Nothing was built; no Lean was run.

Every verdict is one of **KEEP** (the direction's default is right and the corpus says why),
**CHANGE** (the corpus shows a concretely better shape), **SHARPEN** (default stands but gains a
named invariant or a cheaper construction), or **NO GUIDANCE**.

## 0. Where this disagrees with the 2026-09-05 review

1. **G1's payoff is smaller than the review priced it.** The review wants
   `replay_eq_interpret` so that Jacobs 5.5.5 gives "bisimilarity on `T(0)` is a congruence".
   Choice Trees §7.1 says the scheduler *cannot* be written as `interp` ("we cannot hope to use
   interp … the combinator cannot be implemented as a simple fold"), and §7.2 states the
   consequence outright: the equivalence "is a congruence for the source language after the
   first stage of interpretation, but **not** after the second stage". So a compile theorem on
   the sequential fragment buys sequential rewriting only; it never becomes a congruence across
   the fiber layer. Keep G1 scoped to the straight fragment and stop advertising the congruence.
2. **The masks item (review A7) is under-sold.** Interaction Trees §7, Definition 1–2: trace
   refinement/equivalence on ITrees *coincides with weak bisimulation* — but only because every
   branch is a `Vis` whose answer comes from the environment. That converts "`run_eq_ref` over
   every tape" from a trace-set statement into a bisimulation-strength one, and makes "no
   scheduler choice is ever made off-tape" a load-bearing invariant rather than vocabulary. See
   Q7.
3. **Row-monomorphism has a cheaper justification than Tes.** The review defends it from de
   Vilhena §7.5 (generalisation unsound over the store). Leijen (17) §3.2 gives the primary
   reason: row polymorphism exists to type *arrow types* (`id(raise "hi")` fails without the
   `open`/`close` rules). `Eff` has no effect-carrying arrow type, so the machinery has no work.
4. **Agreement, strengthened:** the review's "`Program` stays out of the behaviour seat"
   (E4-ALG-CE-008) is independently confirmed by ITrees §7 ("TEnd … corresponds to spin or ⊥, we
   cannot distinguish the two, a problem of using finite traces").

---

## Q1. Where do handlers live? (dictionary passing vs dynamic handler stack)

**Sources.** Xie & Leijen, *Generalized Evidence Passing* (09) §2.3, §2.5, §2.12, §2.12.1;
Leijen, *Type Directed Compilation* (17) §2.5/§5.4; Sivaramakrishnan et al. (19) §5.2.

(a) 09 §2.3 names the two costs a dynamic handler stack pays on every `perform`: **searching**
(linear walk up the frames for the innermost handler) and **capturing** (reify the context as a
resumption). §2.5 replaces search with an evidence vector `w` passed down: `perform op v →
yield m (k. f v k) where (m,h) = w.l`. Two orderings: *insertion order* (a linked list of
handlers on the stack — "exactly how … Windows structured exception handling implements
exception handlers"), and *canonical order* (lexicographic by label, so with a statically known
effect row `w.read` becomes `w[0]`, constant time; "this is the approach used in the Koka
compiler"). §2.12.1 is the load-bearing caveat: **static evidence passing is unsound whenever a
resumption can be resumed under a different handler context**. Their `evil` handler returns the
captured continuation as a value; resumed under a fresh `hread2`, the second `ask` returns 2 and
not the 1 the statically-passed vector predicted. The earlier EPT system "rejects this program at
runtime". Generalized evidence passing recovers full generality only by making the vector
*dynamic* again (a `(m, h, w)` triple per entry plus `under` frames, §2.6).

(b) The direction's (a) — a Layer service's program is a stored capture the perform site jumps
to — **is** canonical-order evidence passing. Its soundness precondition is exactly Q3's default:
no continuation value escapes to the value language, so no `evil`. `Ctx.services` (L2) is the
evidence vector; `ServiceKey` is the label; the reserved keys 0–3 are the fixed prefix. This is a
one-line dependency worth writing into the direction: **L2's `Ctx.services` is only a valid
dictionary because L3's captures are never program values.** If Q3 ever flips, Q1 must flip too.

(c) **KEEP (a).** SHARPEN: state the coupling in L2's note, and store `services` in a canonical
`ServiceKey` order so lookup is positional (09 §2.5 variant 2) rather than a scan — this is free
now and expensive after `Ctx` is imaged (L2 says `Ctx` grows once).

## Q2. Scoped operations: constructors or rows?

**Sources.** van den Berg et al., *Latent Effects* (13) §2.2; Bach Poulsen & van der Rest,
*Hefty Algebras* (14) §1.2, §2.6, §3.1, §3.4, §3.5, §5.2; van den Berg & Schrijvers (15) §3, §4;
Wu/Schrijvers/Hinze, *Effect Handlers in Scope* (10) §9, §10; Piróg et al. (11) §1.2.

(a) 13 §2.2 gives the exact three-way taxonomy the question needs.
- **Algebraic**: `op : D → M a → … → M a` satisfying `op d m₁…mₙ >>= k ≡ op d (m₁>>=k)…`. No
  body needed; encodable as a plain request/answer row (14 §1.2 proves it: `op m₁…mₙ = do x ←
  op₀(); select x`).
- **Scoped**: `op : D → ∀a. M a → … → M a → ∀b. (a → M b) → … → M b`. The `∀a` "restricts data
  flow: it is only the possible continuations `k₁…kₘ` that can inspect values yielded by the
  computations `mᵢ`". `catch` is scoped.
- **Latent**: the body's return type is *not* universally quantified, so execution may be
  deferred past the operation's own continuation (λ-abstraction, thunking, staging). 14 §2.6.4
  proves scoped effects cannot express these: in `enter op (sc : Ret op → Prog Δ γ B) (k : B →
  Prog Δ γ A)` the `B` is existential, "the only way to get a value of this type `B` is by
  running the scoped computation `sc`", so postponing is impossible.

The concrete constructor shapes, all three papers agreeing: 14 §2.6.1
`enter (op) (sc : Ret op → Prog) (k : B → Prog)`; 14 §3.1 `Effect_H = ⟨Op_H, Fork : Op_H →
Effect, Ret_H : Op_H → Set⟩` with `impure (op) (ψ : (a : Op (Fork op)) → Hefty (Ret (Fork op) a))
(k : Ret_H op → Hefty A)`; 15 §3 `OpH :: (k f b) → (f ↝ FreeH k) → (b → FreeH k a) → FreeH k a`,
labelled *operation × internal computation × continuation*, with 15 §4 showing algebraic, scoped,
parallel and latent effects are all instances of that one shape.

10 §9/§10 give the two implementations of `catch`: **brackets** (`BCatch0 cnt (e→cnt) | ECatch0
cnt`, with `catch0 p h = begin (do x←p; end; return x) h`) and **higher-order syntax**
(`Catch0 (m x) (e → m x) (x → m a)`). 11 §1.3 records why brackets were originally dismissed:
"there is no way to guarantee that the brackets are well-paired" — 10's own handler carries
`error "Mismatched ECatch!"`.

14 §3.5 and §5.2.2 give the modularity verdict: elaboration in one go (hefty) versus weaving
(scoped handlers). "Scoped effect handlers exhibit more effect interaction by default; i.e.,
different permutations of handlers may give different semantics. In contrast, when using hefty
algebras we have to be more explicit about such effect interactions." §5.2/§5.2.2 shows the
price of the flexible option: transactional-vs-global `catch` needs `sub`/`jump` (Fiore–Staton
continuation effects) in the elaboration.

(b) Sorting the tree's list by 13's taxonomy:
- *scoped*: `uninterruptible`, `scoped`, `onExit`, `catchCause`, `provideContext`, `withSpan`,
  `timeout`, `withPermits`, `TxRef.transaction`. Control returns from the body to the operation's
  continuation.
- *latent*: `acquireRelease`'s **release**, a Layer service program stored in `memo`, a
  `DeferredCell`'s stored program (`Stores.lean:881-895`), a Stream's pull step. These run after
  the operation's continuation is long gone.

So one row kind cannot carry both. The tree already has the right two mechanisms and should stop
looking for one: **scoped bodies are program *subterms* addressed by the frame stack; latent
bodies are `Capture` values** (L3). L3's `Capture` is not a wart to be replaced by
`RowKind.program`; it is the latent-effect carrier the literature says you need separately.

The tree's `scoped` lowering (`Compile.lean:878-890`: mint a scope, set `ambientScope`, install
`.scopedExit` as a frame finalizer) is 10 §9's bracket encoding with the well-pairing enforced by
the *frame stack* rather than by types — the third design point 10 and 11 both set aside. That is
a genuine advantage and an argument for keeping the constructors: a `RowKind.program` row would
have to re-derive pairing that the frame stack gives for free.

The one thing the corpus says to change: 14 §1.2 — "elaborating higher-order operations in this
way means the operations are not part of any effect interface. So … the only way to refactor,
optimize, or change the semantics of higher-order operations defined in this way is to modify or
copy code." The direction's `StdLib/` expansions have exactly that defect. Hefty's fix is cheap
and does not touch the IR: give the expansions a **named elaboration table** instead of inlining
them at the call site.

```
structure Elab where
  name    : DerivedName          -- timeout | withPermits | transaction | …
  arity   : Nat                  -- number of program bodies
  expand  : Val → List Point → Eff → Eff
def ElabTable := List Elab       -- threaded exactly as LayerTable is (L1)
```

The program then records `Eff.derived name args bodies` and the table is applied by
`interpOf root table`. Cost: one `Eff` arm plus a table (the same threading L1 already does for
`LayerTable`). Benefit: 14 §1.3's modularity (swap `timeout`'s expansion without touching stored
program bytes) and Q9 gets a stable program identity that is not perturbed by an expansion
rewrite. If this is not wanted, the alternative is to accept 14 §1.2's defect explicitly and
record that a change to `timeout`'s expansion is a **program-bytes-breaking change**.

(c) **KEEP the default**, with two sharpenings: (i) do not introduce `RowKind.program` for the
`acquireRelease`/service-program class — 13 §2.2 and 14 §2.6.4 prove those are latent, not
scoped, and `Capture` is the right carrier; (ii) decide explicitly between the named
`ElabTable` above and "expansion changes are wire-breaking". If a scoped row kind is ever added,
use 15 §3's exact shape: `⟨request : Ty, bodies : List Ty, answer : Ty⟩`, nothing more.

## Q3. Continuations: is one-shot-by-data enough everywhere?

**Sources.** Sivaramakrishnan et al. (19) §5.2, §3.2; Kammar/Lindley/Oury, *Handlers in Action*
(20) §2.6; Xie & Leijen (09) §2.3, §2.4.

(a) 19 §5.2: "Since our primary use case is concurrency, continuations will be resumed at most
once, and copying fibers is unnecessary and inefficient. Instead, Multicore OCaml optimises
fibers for one-shot continuations." 09 §2.4 is the same fact from the compiler side: with
segmented stacks, yielding and resuming once are constant-time, "but supporting multi-shot
resumptions still requires a linear copy of the resumption stack segments (and one of the reasons
why multi-shot resumptions are not directly supported in multi-core OCaml)".

20 §2.6 is the direct evidence on the Streams/Channels question. Pipes (`Await`/`Yield`) are
implemented by **two mutually suspended one-shot continuations**: "one handles the downstream
consumer and keeps a suspended producer to resume when needed, the other handles the upstream
producer and keeps a suspended consumer". Multi-shot is never used. The paper's caveat is about
handler *depth*, not shot count: with shallow handlers the two clauses are three lines each; with
deep handlers you must introduce `data Prod s r = Prod (() → Cons s r → r)` and
`data Cons s r = Cons (s → Prod s r → r)` — "resulting in a more complex program".

(b) The tree's frame stack gives shallow-handler behaviour by construction, so the `Prod`/`Cons`
mutual encoding is not needed; the parked-fiber-plus-queue pair *is* 20 §2.6's suspended partner
pair. No continuation value in the program language is required for Streams/Channels/Sinks.

19 §3.2 adds one operational requirement the tree should honour: `discontinue k exn` — resuming
a continuation *with an exception* — and the top-level rule that an unhandled effect must
`discontinue` the continuation with `Unhandled` "so that the exception handlers may run and
clean up the resources", because "OCaml programs that use resources … are usually written
defensively with the assumption that calling a function will return exactly once". L3's
`ProgName.foreignFin (capture) (exit : ExitV)` already unifies continue and discontinue in one
arm, which is the right shape. What is not settled: what a tape-exhausted or `Stuck` machine does
to open scopes. On 19 §3.2's argument, freezing them leaks acquired resources in any host that
consumes the run's exits.

(c) **KEEP** (fibers plus queues; no continuation handles in the value language). SHARPEN: adopt
19 §3.2's rule as a stated frontier obligation — when a run ends at a frontier, the daemon's
`run` result must say which scopes are still open, or the machine must run their finalizers with
a synthetic interrupted `ExitV`. Fix this before H1, since it is part of `run`'s result shape.

## Q4. Effect typing and the profile

**Sources.** Leijen (17) §3, §3.2; Hillerström & Lindley, *Liberating Effects with Rows and
Handlers* (18) §"Handler Types"/kinds; Xie & Leijen (09) §2.5(2); Sivaramakrishnan et al. (19)
§4.1.

(a) 17 §3.2 shows what row polymorphism is *for*: `id : ∀α. α → ⟨⟩ α` makes `id(raise "hi")`
ill-typed, so Koka needs `open`/`close` rules to keep function types' effect tails polymorphic.
17 §3 also records that scoped labels allow duplicate labels (`⟨exc,exc⟩ ≠ ⟨exc⟩`) and that "in
practice we have not found many uses for duplicate effects (nor any drawbacks)". 18 needs a
further layer — six kinds including `Presence`, and `RowL` (rows that *cannot* mention labels in
`L`) — purely so a forwarding handler ("an empty, open row which means that it forwards every
operation") can be typed. 19 §4.1 is the counterexample from the host side: Multicore OCaml
deliberately has **no** effect typing at all ("effect handlers in Multicore OCaml do not
guarantee effect safety … This is important for backwards compatibility"); an unhandled effect is
a runtime `Unhandled`.

09 §2.5(2) gives the one thing effect rows buy that this tree *does* want: a statically known
row lets the evidence lookup be a constant-time index rather than a search.

(b) `Eff` is first-order: no effect-carrying arrow type exists, so 17's `open`/`close` and 18's
presence polymorphism have nothing to do. `Program/Typing.lean`'s `typeOf` computing a finite
`requires : List ServiceKey` plus `Val.hasTy` is the whole of what the corpus says is needed. The
one borrowing is Q1's: sort the profile's rows canonically so admission and evidence lookup are
positional.

(c) **KEEP.** Profile = finite set of rows with answer types plus decision permissions; admission
= membership + `hasTy`; no row polymorphism, no presence types, no duplicate labels. Record 19
§4.1 in DB-11 as the reason the Lean side must own admission: the OCaml host cannot check it.

## Q5. One coordination core

**Sources.** Sivaramakrishnan et al. (19) §3.1; Loring/Marron/Leijen, *Semantics of Asynchronous
JavaScript* (01) §2.3, §2.4; Zakowski et al., *Choice Trees* (03) §7.1.

(a) 19 §3.1 builds the whole scheduler out of two structures and one policy: a ready queue
`runq` of thunks, a waiter list `pending_reads : (channel × continuation) list`, and the rule at
`run_next` — pop `runq`; **only when `runq` is empty** consult the external source
(`do_reads todo`, which "blocks until at least one of the reads succeeds"), move completed
waiters into `runq`, recurse. Forking and yielding are the same two lines (`suspend k;
run_next ()` / `suspend k; spawn f'`). Changing FIFO to LIFO is "changing the scheduler queue to
a stack".

01 §2.3 goes further and shows the *policy* need not be a two-valued choice. Node's
`process.nextTick`, `setImmediate`, `setTimeout(f,0)`, `.then`, ordinary async I/O and general
timeouts are **all modelled by one queue with a priority number** (0 nextTick, 1 immediate, 2
timeout, 3 I/O); the browser variants differ only in which priority `timeout0` gets ("The Edge
browser … is like Micro except that the `timeout0` promise has priority 0 too"). 01 §2.4 models
every genuinely external completion with one pair of rules: `E-Register` (attach a promise to an
outstanding event) and `E-Oracle` (resolve any event with a fresh value, applicable at will).

03 §7.1 confirms the shape from the model side: the scheduler is a thread pool with a designated
active thread, and it "cannot be implemented as a simple fold" over the program.

(b) The tree already matches: `DeferredCell` waiters + completion, `due` for synchronous wake,
dispatcher arm for scheduled wake. Two amendments the corpus supports:
1. **Make the wake policy a small number, not a Boolean.** L6 fixes "the two policies" at A4.
   01 §2.3 shows four to six phases arise as soon as you have `yield`, `nextTick`-style
   microtasks, timers and foreign I/O — and Effect rc.112 has that structure. A
   `WakePhase : Nat` field on the waiter (or `deriving` order on a small enum) costs nothing now
   and avoids a store-format change when the third phase appears. This is a **cheap insurance
   change on a format that L6 says is being fixed once.**
2. **Adopt 19 §3.1's drain rule verbatim as A4's decision:** consult the tape/foreign source only
   when the runnable set is empty. It is the only rule in the corpus and it makes the run's tape
   shorter and more canonical (fewer interleavings to quantify over in `run_eq_ref`).

(c) **KEEP** the "waiter list + completion + wake policy" core; **CHANGE** the wake policy from
two values to a phase number (01 §2.3), and pin 19 §3.1's drain-before-poll rule in A4.

## Q6. Who advances time?

**Sources.** Loring/Marron/Leijen (01) §2.3, §2.4; Sivaramakrishnan et al. (19) §3.1.

(a) 01 §2.4 defines `setTimeout(f, ms) = register(timeout(now() + ms), 2).then(f)`. A timer is
**an outstanding I/O event like any other**, and its firing is the `E-Oracle` rule: "an oracle
[that] can be applied at will to resolve any event `ev` with some fresh value `v` … This is the
rule that basically models the external world." Only `setTimeout(f,0)` — a fixed priority-2
promise resolved by the deterministic queue discipline — is internal (§2.3, `H₀ = [… timeout0 ↦
(2, res(undef), [])]`).

(b) That is L6 exactly: `RunDecision.advance (to : Nat)` is `E-Oracle`; `sleep`/`clockNow` are
`register`; `clockAdjust` (TestClock) is the program-level counterpart. The corpus gives one
extra alignment: 01 makes the timer's *registration* use the same waiter machinery as I/O, which
is Q5's point and means `TimerStore` should be a priority-ordered waiter list, not a separate
kind of store. That reduces A4's footprint.

(c) **KEEP.** `advance` is a decision; `clockAdjust` is additionally a program op. SHARPEN: build
`Stores.timers` as an instance of the Q5 waiter core keyed by deadline, not as a parallel
structure — it is the same landing (L6) and saves a second wakeup path.

## Q7. The tape as the nondeterminism model

**Sources.** Xia et al., *Interaction Trees* (02) §7 (Fig. 20, Definitions 1–2); Chappe et al.,
*Choice Trees* (03) §2.2, §7.2; Loring et al. (01) §2.4.

(a) 02 §7 is the decisive result. An ITree's meaning as a set of traces uses
`TEventResponse e x t` (event `e`, environment answer `x`) and `TEventEnd e` (awaiting an answer
"perhaps one that will never come"). "Using these definitions, we can show that **trace
equivalence coincides with weak bisimulation**, i.e. that `t₁ ≈ t₂ ⇐⇒ t₁ ≡ t₂`." This holds
precisely because ITrees are *deterministic* LTSs — every branch is a visible `Vis` answered by
the environment. 02 §7 also warns that relational (`step : state → event → state → Prop`)
semantics with universally quantified inputs "are fundamentally not executable"; ITrees keep the
continuation as a function and stay extractable.

03 §2.2 states the converse for *internal* choice: a `flip` event "does not come with its
expected algebra: associativity, commutativity and idempotence", and identifying a system with
its trace set "forgets all information about when nondeterministic choices are made … such a
model leads to equivalences of programs that are too coarse to be compositional in general".
03 §2.2 also names the construct you need when a rule's transitions depend on the *existence* of
other transitions (`ContingentStep`) — "whenever the operational semantics includes a rule whose
possible transitions depend on the existence of other transitions", explicitly citing mutexes,
locks and `await`. 03 §7.2 confirms that after scheduling the equivalence is no longer a
congruence.

(b) The tape puts every scheduler choice — fire order, yield verdicts, foreign answers,
interrupts, middleware — into the ITree `Vis` position. So the tree sits at 02 §7's sweet spot
and *not* at 03's: `run_eq_ref` quantified over every tape is a weak-bisimulation-strength
statement, and `replay(program, log)` is executable, which is the property 02 §7 says the
relational style loses. Two invariants follow and should be written down:
- **INV-TAPE-1 (no off-tape choice).** Every machine transition is a function of
  `(machine, decision)`. The moment one internal choice is made without a tape entry, the model
  drops from bisimulation to trace equivalence and 03 §2.2's non-compositionality applies.
- **INV-TAPE-2 (a frontier records what it awaits).** 02 §7's trace type distinguishes `TEnd`
  ("spin or ⊥ — we cannot distinguish the two") from `TEventEnd e` (awaiting a specific event).
  The tree's frontiers currently collapse these (`Fibers.lean:31-33` files deadlock under tape
  exhaustion). L5's request projection (`parkedOn fiber token` + park name → row) is exactly
  `TEventEnd e` and is what makes the frontier legible. **This is direct literature support for
  L5**, and it means the projection must be total on frontiers, not best-effort.

Also: 03 §2.2's `ContingentStep`/`BrD` machinery is what a blocking `Queue.take` would need in a
model *without* a host — the tape removes the need for it, because the host is the introspection
oracle. Worth saying once in RUNTIME-MODEL: the tape is not a poor man's nondeterminism, it is
what buys executability and bisimulation at once.

On the sub-question "is the log tape-plus-derived-events, or must it carry events?": 02 §7's
trace type carries `(event, response)` pairs, i.e. exactly a tape plus the row it answered.
Since L5 makes the row a projection of `(fiber, token)` + program, the tape alone determines the
log. **The default is sound**, conditional on INV-TAPE-1.

(c) **KEEP.** Tape suffices; the log is tape plus derived events; snapshot = machine value + tape
position. SHARPEN: record INV-TAPE-1 and INV-TAPE-2 as named model invariants, and state that
`run_eq_ref` over all tapes is bisimulation-strength *because* of INV-TAPE-1 (02 §7), not by
assumption.

## Q8. Composing machines

**Sources.** Yoon/Zakowski/Zdancewic, *Layered Monadic Interpreters* (04) §2.3, §5, §5.1;
Yang & Wu, *Reasoning about Effect Interaction by Fusion* (21) §1.1, §5, §7.1; Chappe et al.
(03) §7.1–§7.2.

(a) 21 §1.1 states the only fusion law in the corpus: for **modular handlers**,
`handle h₂ · handle h₁ = handle (h₂ ⋄ h₁)`, and its value is that the right-hand side "is a
single catamorphism on syntax trees of programs". Theorem 5.5: equations respected separately are
respected by the composite. Theorem 6.1/7.1 give per-clause commutation conditions. §7.1 shows
even this has limits (probabilistic ⊲ nondeterministic choice "exhibits a limitation of the
fusion approach").

The precondition is fatal here: fusion applies to handlers that are folds. 03 §7.1: a scheduler
over a thread pool "cannot be implemented as a simple fold". 04 §2.3 documents what layering
costs when the layers are genuine interpreters: signature-position brittleness ("`interp_state`
forces `stateE` to be in the head position … we are forced to either change our definitions to
line up the signatures, or to duplicate the definitions"), and Vellvm's six-layer stack needing
"three auxiliary definitions for triggering E, F, and G events along with fiddly uses of
`case_`". 04 §5/§5.1's whole contribution is an `eqmR` relation framework plus higher-order
functor laws so that interpretation laws "need only be proven once … regardless of the stack" —
i.e. the cost of composing interpreters is a research-scale framework.

(b) The direction's default (the product of two machines is a host loop owning two machines and
two tapes; no fusion claimed) is the only option the corpus supports for a machine with a
scheduler. 04's evidence is also the strongest independent argument for **L1** and **Q13**: a
second `RunMachine` instantiation is a second interpreter layer, and 04 §2.3 is a catalogue of
what that costs.

(c) **KEEP.** No fusion law; the product is a host loop. Cite 21 §1.1's precondition ("handlers
that are catamorphisms") in DB-11 as the reason, so nobody re-opens it.

## Q9. Programs, runs and addresses in the CAS

**Sources.** none of the 21 papers addresses content addressing, hashing or artefact identity.
The nearest is 02 §6 (extracting ITrees), which is about extraction, not identity.

(b) One indirect constraint carries over: if Q2 adopts the named `ElabTable`, program bytes are
stable under a change of expansion and the *elaboration table* becomes part of the run address
alongside the profile. If expansions stay inlined (14 §1.2's non-modular case), the program bytes
already encode the expansion and the run address is unchanged — but then a `StdLib/` edit
silently changes every stored program's address. That is the only decision-relevant consequence
the corpus produces here.

(c) **NO GUIDANCE** on the addressing scheme itself. The default (`hash(program, profile, tape)`;
snapshot = `hash(image, tape position)`; everything a `Store.Val` tree) is untouched by the
literature. Note the Q2 coupling in the CAS design note.

## Q10. Injection and observation

**Sources.** Xia et al. (02) §3.2 (Fig. 9, Fig. 11); Bach Poulsen & van der Rest (14) §1.3,
§3.4; Loring et al. (01) §2.4.

(a) 02 §3.2: `interp (handler : E ↝ M) : itree E R → M R`, whose law is
`interp h (trigger e) ≈ h _ e` — **interpretation is exactly "substitute a computation for an
event"**, and `interp` is a monad homomorphism (Fig. 11: `InterpRet`, `InterpBind`,
`InterpTrigger`, `IgnoreTrigger`, `InterpIter`). 14 §3.4's `Elaboration H Δ = Alg_H H (Free Δ)`
is the same move one level up, with the composition operator `⋏` making elaborations a table.
01 §2.4's `E-Register`/`E-Oracle` is the same move at the host boundary: register a waiter, let
an external rule supply the value.

(b) Both readings of Q10 are literature-sanctioned, and they are *not* equivalent:
- `RunDecision.inject` carrying a program as a value tree = 02 §3.2's `interp`: the host supplies
  the computation. Interposition is total and typed by the row's answer type.
- a foreign row answered with a program *address* = 01 §2.4's `E-Register`: the answer is a
  handle the machine must then resolve, which adds a dereference step and a failure mode
  (unknown address) inside the machine.
02 §3.2's `InterpTrigger`/`IgnoreTrigger` pair is the law the direction wants ("providing then
performing equals inlining", Q1's composition law) and it is stated for the *value-tree* form.
The default is the one with a law attached.

On observation: 02 §3.2's `interp` laws say projection commutes with `ret`, `bind` and `iter`,
which is precisely "trace projections are compositional" — the review's A7 masks. No core events
are needed.

(c) **KEEP** the default (`RunDecision.inject` carries a program as a value tree; observation is
projection). SHARPEN: name the Q1/Q10 composition law after 02 Fig. 11 — `interp h (trigger e) =
h e` and `interp h (trigger e') = trigger e'` for unhandled `e'` — so the two arms are stated
together and `IgnoreTrigger` (a row the injection does not cover passes through) is not
forgotten.

## Q11. A program algebra above the IR

**Sources.** Plotkin & Pretnar, *Handling Algebraic Effects* (05) §5, §6, Appendix A;
Yang & Wu (21) §1.1, §5.5; Bach Poulsen & van der Rest (14) §4.

(a) 05 §5 fixes what "law" costs. Correctness of a handler is a *definedness assertion* `H ↓`
relative to a declared effect theory `T`; the equations you must discharge are exactly the
equations in `T`, instantiated at the handler's clauses. With `T` empty, every handler is
trivially correct. 05 §6 and Appendix A show handler correctness is decidable for finite
theories. The three unconditional laws that hold for *any* handler are the ones 05 §5 lists
before the theory-specific ones: `return x handled with H to x. N ≲ N`, the operation
homomorphism law, and `M to x. N ≃ M handled with {} to x. N`. 21 §5.5 adds the composition
result: equations respected by modular handlers separately are respected by their composite, and
every such equation is automatically a term congruence (Remark 5.2). 14 §4 makes the point
concretely by verifying `catch`'s laws over an elaboration, and reports the cost is comparable to
the non-modular version.

(b) This is a direct answer to "which laws are needed for anything we ship": **only the equations
you declare.** Declaring none is not a gap; it is a choice with a named consequence (no
rewrite is justified). The corollary that matters for `Codegen/Layer.lean`'s `merge`-chain
flattening and for `Prim.iteratorFolded`: each of those is one declared equation, and 21 Remark
5.2 says it is then a congruence for free.

(c) **KEEP.** A library of expansions in `StdLib/`, laws only where an optimization relies on
one. SHARPEN: when a law is declared, declare it as an *equation of the row's theory* in 05 §5's
sense, so the obligation is per-clause and decidable, rather than as an ad-hoc theorem about
`replayEval`.

## Q12. Callbacks: term or program?

**Sources.** Danvy & Nielsen, *Defunctionalization at Work* (16) §1, §1.3, §3; van den Berg
et al. (13) §2.2; 14 §2.6.4.

(a) 16 §1 states the three representations of a first-class function and separates two of them
precisely: a **closure** pairs "a code pointer and the denotable values of the variables
occurring free in that code" (Landin); **defunctionalization** represents a function by "a
constructor holding the values of the free variables of a function abstraction … eliminated with
a case expression dispatching over the corresponding constructors" (Reynolds), i.e. *one
constructor per abstraction site in the program*, plus one `apply`. §3 shows the canonical
instance: CPS-transform a first-order program and defunctionalize the continuation and you get a
finite `datatype cont = CONT0 | CONT1 of cont` and `apply2` — an abstract machine.

(b) The direction is right that there are only two kinds, and 16 §1 names them:
- **Pure callbacks are defunctionalized.** `Fn = ⟨body, captured⟩` over `Term`, with
  `Program/Native.lean`'s closed atom table as `apply`, is Reynolds exactly.
- **`FinName` is defunctionalization; `Capture` is closure conversion.** `FinName`'s 12-arm
  closed alphabet is "one constructor per abstraction site", which is why *adding a family adds a
  constructor* — the churn Q2 complains about. L3's
  `Capture ⟨path, env, fuel, tape, ctx⟩` is a **closure**: `path` is the code pointer into the
  program tree and `env`/`ctx` are the free values. Because `Eff` is data, that code pointer is
  first-order, so the closure costs nothing that defunctionalization was protecting.

This is the sharpest single result in the review: **L3 is the fix for `FinName`'s open-alphabet
problem, not just for `acquireRelease`.** Every future derived combinator that needs a deferred
program body should mint a `Capture`, never a `FinName` arm. Write that as a rule in DB-11, and
the "central sums change per family" complaint (Q2) is answered without touching `Eff`.

13 §2.2 supplies the boundary criterion the question asks for: a callback is a **term** if it is
pure and its result flows to the operation's continuation (13's algebraic case, and 14 §2.6.4's
existential `B`); it must be a **program at a `Point`** as soon as its execution can be deferred
past that continuation (13's latent case). By that criterion: `Ref.modify` and Schedule *decision*
functions are terms; `acquireRelease`'s release, a Stream transform that itself performs, and a
Layer service body are `Point`s. No third kind is needed and 13 §2.2 exhausts the taxonomy.

(c) **KEEP** the default, with the two rules above written down: (i) the term/program boundary is
13 §2.2's algebraic/latent line; (ii) new deferred bodies mint a `Capture`, never a `FinName` arm.

## Q13. Is the Layer algebra a machine?

**Sources.** Yoon et al. (04) §2.3, §5.1; 14 §3.4; 03 §7.1.

(a) 04 §2.3 is a catalogue of the cost of a second interpreter layer, quoted under Q8:
head-position constraints on signatures, duplicated definitions, "bureaucratic clutter in
large-scale developments", and Vellvm's six layers needing per-layer trigger definitions. §5.1
shows the fix is a framework (`eqmR`, higher-order functor laws, well-formedness conditions per
transformer) whose payoff is stated as "that work needs to be done only once" — that is, it is a
fixed cost you pay before you get any theorem. 14 §3.4 shows the alternative shape: an
`Elaboration H Δ` folded into the *same* base free monad, composed by `⋏`, with no second
carrier and no weaving.

(b) `Machine/Layer.lean` is a second `RunMachine` instantiation with its own `St`, `FinName`
(12 arms), `SyncOp`/`ProgName`/`Name`/`ActionName` (direction fact 7). By 04 §2.3 that is one
layer, and the only reason it does not yet cost is that no theorem crosses the boundary. The
moment memo, service rows or the timer need to be stated across both, you are paying 04 §5.1's
framework cost. 14 §3.4 says the cheap alternative is: keep the *algebra* (`LayerDesc`,
`LayerTable`) as data, fold it into programs over the shared stores.

(c) **KEEP L1**, and the literature makes the Fable scout's item B nearly moot: 04 §2.3 + 14 §3.4
already say "one carrier, table as data". If the scout returns "keep the second machine", the
counter-argument is 04 §5.1's fixed cost.

## Q14. Persistence and parallelism in the implementation

**Sources.** Sivaramakrishnan et al. (19) §1, §5.2, §5.6; Chappe et al. (03) §7.

(a) 19 §1: "Multicore OCaml distinguishes concurrency (overlapped execution of tasks) from
parallelism (simultaneous execution of tasks) **with distinct mechanisms** for expressing them …
parallelism … enabled by domains. The focus of this paper is the concurrency support enabled by
effect handlers." Fibers are per-domain, heap-allocated, freed when the handled computation
returns (§5.2). No effect crosses a domain boundary in the design.

(b) That is L8/Q14 verbatim. The corpus contains **no** construction for cross-machine atomicity;
03 §7 models multithreading inside one scheduler, and its Lemma 7.1 (permuting the thread pool
preserves bisimilarity) is a statement about one pool, not two.

(c) **KEEP.** No cross-machine atomicity or shared memory; anything cross-run is a service. Cite
19 §1 as the precedent (the host we compile to made the same cut).

## Q15. Cause algebra on the wire

**Sources.** Chappe et al. (03) §2.2; Plotkin & Pretnar (05) §1, §5; Piróg et al. (11) §1.2.

(a) 03 §2.2 is the closest thing to an answer and it is a warning: a branching constructor "does
not come with its expected algebra: associativity, commutativity and idempotence. To recover
these necessary equations to establish program equivalences … we need to find a suitable monad to
interpret [it] into." I.e. a raw tree constructor for combining outcomes gives *structural*
equality, and structural equality distinguishes trees the reader expects to be equal. 11 §1.2
makes the same point for `or`: "we do not assume commutativity of the choice, that is, in general
`or(a,b) ≠ or(b,a)`" — non-commutativity is a *choice*, and one that must be declared. 05 §1/§5
covers only the first-order exception case, where `raise_e()` is a nullary algebraic operation
and no combination operator exists, so no normalisation question arises.

(b) `Cause.both` is 03's branching constructor: two fibers fail concurrently, and which one lands
left depends on dispatcher order — which is a tape decision, so two hosts with different
schedulers produce structurally different `Cause` trees for the *same* logical failure. Under
Q7's INV-TAPE-1 the two runs are on different tapes and are not required to agree, so the model
is consistent. But the CAS is not tape-indexed: a run address includes the tape, a *failure*
compared across hosts does not. The default ("no normalisation; structural equality; record the
divergence rows") is therefore correct as a model decision and incomplete as a *product*
decision. The corpus's advice, from 03 §2.2, is that you either declare the equations
(commutativity + associativity + idempotence for `both`) and canonicalise at the boundary, or you
accept that `both` is ordered and that the order is host-observable.

The cheap concrete option, if you want it: leave `Cause` structural in the machine, and define
one boundary function

```
def Cause.canonical : Cause → Cause    -- flatten `both` to a sorted, deduplicated list
theorem canonical_idempotent / canonical_perm_invariant
```

used only by the CAS/daemon comparison path, never by the machine. That is 03 §2.2's "interpret
into a suitable monad" done first-order and at exactly one seam.

(c) **KEEP** structurally in the machine; **SHARPEN**: decide now whether cross-host failure
equality is a product requirement. If yes, add `Cause.canonical` at the CAS boundary before H1
(it is a new function, not a wire change). If no, write "`both` is ordered and the order is
scheduler-dependent" into DB-11 as a stated non-guarantee, next to the divergence rows.

---

## A. The five strongest changes the literature supports

1. **Write down INV-TAPE-1 (no off-tape choice) and INV-TAPE-2 (a frontier names the row it
   awaits).** ITrees §7 turns "`run_eq_ref` over all tapes" into a weak-bisimulation statement,
   but only while every choice is visible; INV-TAPE-2 is direct support for L5's request
   projection and must be total on frontiers. (Q7, L5.)
2. **`Capture` is the general fix for `FinName`'s closed alphabet, not a one-off for V1.**
   Danvy §1: `FinName` is defunctionalization (a constructor per site, hence per-family churn);
   `Capture` is closure conversion over a first-order code pointer. Rule: every future deferred
   body mints a `Capture`. This dissolves most of Q2's complaint without touching `Eff`. (Q12,
   Q2, L3.)
3. **Make the wake policy a phase number, in the same touch as L6.** Node's whole async model is
   one queue with priorities 0–3 (01 §2.3); two Boolean policies will not survive Queue,
   permits and PubSub, and the store format is being fixed exactly once. Adopt 19 §3.1's
   drain-before-poll rule as A4's decision. (Q5, Q6, L6.)
4. **Decide `timeout`/`withPermits`/`transaction` expansions: named `ElabTable` or
   wire-breaking.** Hefty §1.2 proves an inlined elaboration is "not part of any effect
   interface", so its semantics can only be changed by editing programs. Either thread an
   `ElabTable` exactly as L1 threads `LayerTable`, or record that a `StdLib/` edit changes every
   stored program's CAS address. (Q2, Q9, Q11.)
5. **Fix frontier resource semantics before H1.** OCaml §3.2: an unhandled effect must
   `discontinue` the continuation so finalizers run; a run that freezes with open scopes leaks.
   `run`'s result shape must say what happened to open scopes. (Q3, X2/H1.)

## B. Traps — designs the literature shows are expensive to retrofit

| # | Trap | Evidence | Does the direction avoid it? |
| --- | --- | --- | --- |
| T1 | **Multi-shot continuations.** Forces a linear copy of resumption stacks; in a logic, forces persistence modalities on every continuation spec. | 19 §5.2; 09 §2.4 ("one of the reasons why multi-shot resumptions are not directly supported"); de Vilhena ch.6 via the Hazel notes | **Yes.** Q3 default; frames are data, tokens one-shot. Multi-shot lives only at the machine-value level (snapshot/replay). |
| T2 | **A dynamic handler stack searched on every perform.** Linear search plus context capture per operation; the whole of 09 is the escape. | 09 §2.3, §2.5 | **Yes.** Q1 default is evidence passing. Risk if `Ctx.services` is scanned rather than indexed — fix at L2. |
| T3 | **First-class continuation values in the program language.** Makes static evidence passing unsound (the `evil` example) and forces the dynamic `(m,h,w)`+`under` machinery. | 09 §2.12.1, §2.12.2 | **Yes**, and this is *why* T2's escape is available. The coupling is currently unstated. |
| T4 | **Effect rows added late.** Koka needs `open`/`close`; Links needs `Presence` kinds and `Row_L`; retrofitting either into a typed IR is a type-system project. | 17 §3.2; 18 kinds | **Yes** — but only because `Eff` is first-order. Adding an effect-carrying arrow type later re-opens all of it. |
| T5 | **A second interpreter layer.** Signature-position brittleness, duplicated definitions, and a per-transformer framework before any theorem. | 04 §2.3, §5.1 | **Yes** under L1. `Machine/Layer.lean` is this trap today; A3 removes it. |
| T6 | **Off-tape (internal) nondeterminism.** Drops the model from bisimulation to trace equivalence and makes it non-compositional; recovering needs `Br`/`BrD` node kinds and up-to principles. | 03 §2.2, §4.4, §7.2; 02 §7 | **Yes today**, unstated. Becomes T6 the first time the dispatcher makes an unlogged choice. See INV-TAPE-1. |
| T7 | **Handler-order-dependent semantics for scoped ops.** With scoped handlers, permuting handlers changes meaning (global vs transactional state); a fixed elaboration does not. | 14 §3.5, §5.2.2; 10 §9 | **Yes.** One machine, one elaboration ⇒ no permutation to get wrong. Cost: to *offer* both semantics later you need `sub`/`jump` (14 §5.2.1). |
| T8 | **Inlined (non-modular) elaborations of derived combinators.** Semantics changeable only by editing every program that uses them. | 14 §1.2, §2.5 | **No.** This is the `StdLib/` default. See change 4. |
| T9 | **Un-normalised combination operators on the wire.** A branching/combining constructor lacks assoc/comm/idem; structural equality then distinguishes what users expect to be equal. | 03 §2.2; 11 §1.2 | **Partly.** `Cause.both` is exposed; the default records divergence rows but does not decide the product question. See Q15. |
| T10 | **Relational (Prop-valued) step semantics for the machine.** Not executable, so no extraction, no replay-as-implementation. | 02 §7; 03 §2.2 (the Vellvm `itree E _ → Prop` workaround: broken bind associativity, "nondeterminism must come last in the stack of interpretations") | **Yes.** `replayEval` is a function; the tape supplies inputs. Keep `answersValid` a *premise*, never the definition of a step. |

## C. Papers that turned out irrelevant to Q1–Q15

- **06 Data Types à la Carte** — the coproduct/injection technique only; superseded for our
  purposes by 14 §2.2 and 15 §3, which state the same construction with the higher-order case
  included. Nothing bearing on any question.
- **07 Freer Monads, More Extensible Effects** — a Haskell performance technique (co-Yoneda,
  type-aligned queues) for a free-monad library. The tree has no free-monad carrier on the `Eff`
  route; no design consequence.
- **08 Koka: Row-Polymorphic Effect Types** — subsumed by 17 §3, which restates the same row
  system for the algebraic-effect calculus and adds the compilation story. Read 17 instead.
- **20 Handlers in Action** — used only for §2.6 (pipes / shallow handlers, Q3). §3–§4's `λ_eff`
  calculus and its type system add nothing beyond 17 and 12.
- **12 A Calculus for Scoped Effects and Handlers** — a type-and-effect system and generalized
  forwarding for `λ_sc`. Its content on the *shape* of scoped operations is fully covered by 11
  §1.2 and 14 §2.6; its forwarding machinery (§7) exists to make scoped handlers composable,
  which the one-machine design (L1) removes the need for.
- **verification_with_effects.pdf, from_partial_to_monadic_combinatory_algebra_effects.pdf,
  intro_coalgebar_mathematics_state.pdf, specifying_hyperdocuments_with_effects.pdf** — the
  2026-09-05 corpus; already reviewed in `2026-09-05-effects-papers-review.md` and not re-read
  here. Their bearing on Q1–Q15 is limited to the two disagreements recorded in §0.

## D. What was read

Full or near-full at the cited sections: 09 §2.3–2.6, §2.12; 14 §1.2–1.4, §2.5–2.6, §3.1, §3.4,
§3.5, §5.2–5.4; 13 §2.1–2.3, §3 opening; 15 §3, §4.1; 10 §9, §10; 11 §1.2, §1.3; 12 headings and
§3 framing; 03 §2.2, §7.1, §7.2, §8; 02 §3.2, §7; 04 §2.3, §5, §5.1; 21 §1.1, §1.2, §7.1; 17 §3,
§3.2; 18 kinds/handler-types; 19 §1, §3.1, §3.2, §4.1, §5.2–5.4; 05 §1, §5; 01 §2.3, §2.4; 20
§2.6; 00 reading map in full.

Not read: 12 §§4–9 (term syntax, operational semantics, generalized forwarding, metatheory);
16 §§2, 4, 5 (Church encoding round-trips, the two matchers); 05 §§2–4, 6–7 (syntax, semantics,
decidability proof, recursion); 02 §§4–6 (iteration, the imp→asm case study, extraction); 03
§§3–6 (CTree combinators, up-to principles, CCS); 04 §§3–4, 6 (triggerable monads, `eqmR`
construction, the case study); 21 §§2–6, appendices; 19 §§2, 6–7; 01 §§3–5; 06, 07, 08, 20 beyond
the sections named above.
