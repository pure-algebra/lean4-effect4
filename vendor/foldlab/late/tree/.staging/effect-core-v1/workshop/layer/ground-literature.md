# Ground literature — Layers, dependencies, runtimes, and Scope

Status: **LITERATURE SCOUT / PRE-GRADE**, 2026-08-31. Claim gate: none for the
survey. The seven Lean statements in §7 are kernel-checked and carry their exact
command and axiom receipts; nothing else in this file is a claim about the
estate's soundness.

This is a survey of what is known about representing dependency provision,
resource lifetime, scoped operations, and sharing — read against R1 (inductive
carrier, no coinduction), R7 (programs are content, hosts are code), and R12
(the tower). It does not propose a design. Its one job is to tell a design team
which of the encodings in front of them are the same encoding.

---

## 0. Source discipline — what I could actually read

**The pinned PDFs are not on this host.** `.reference/papers/` is gitignored per
its own README ("per-host evidence"); a lock walk confirms that every paper in
the interaction-trees cluster is `MISSING` locally:

```text
MISSING chappe-2023-choice-trees.pdf
MISSING fadaei-sammler-2025-hitrees.pdf
MISSING frumin-timany-birkedal-2024-guarded-interaction-trees.pdf
MISSING lindley-mcbride-mclaughlin-2016-frank.pdf
MISSING xia-2020-interaction-trees.pdf
MISSING xia-2020-interaction-trees-popl-published.pdf
MISSING zakowski-2020-gpaco-weak-bisimulation.pdf
```

So I did **not** read the pinned PDFs in this session. What I read instead, and
what every "pinned" citation below rests on:

| Source | What it is | Grade |
| --- | --- | --- |
| `.reference/catalog/PAPERS.md` | The pin itself: title, identifier, digest, and the cluster's role scoping | G0-resolved pin |
| `.staging/explore/itrees-capabilities.md` | The 804-line in-repo reading record of the ITree corpus, named by `EFFECTS-BACKEND.md` as the reading behind R1–R5 | **exploration-grade** |
| `.reference/catalog/REFERENCES.md` | Non-paper pins, incl. the Effect source snapshot and the Frank role scoping | G0-resolved pin |
| `library/effects/node_modules/effect/src/Layer.ts` | The real `Layer` implementation, `effect@4.0.0-rc.112` | read here; see the version caveat below |

**Version caveat on the Effect source.** `REFERENCES.md` pins Effect at commit
`0dd7825e`, package `4.0.0-rc.111`. The tree I read is `rc.112` in
`library/effects/node_modules/`. `EC1-CE020` already works at rc.112, so the
packet is not surprised by that version — but every `Layer.ts` line number below
is an observation **about rc.112 at that path**, reproducible there, and is not
the catalog pin.

**One relevant paper is held locally but is NOT pinned**: *Aeneas: Rust
Verification by Functional Translation* (Ho & Protzenko, arXiv:2206.07185),
`.reference/papers/2206.07185v2.pdf`, zero hits in `papers.lock.json`. It is
directly on the resource-lifetime question (a value-based, ownership-centric
semantics with no memory, addresses, or pointer arithmetic) and I use it once,
marked, with no conclusion resting on it.

**Everything in §2, §3, §4 and §5 that is not in the table above is UNPINNED.**
It is marked inline. No conclusion in this file rests on an unpinned source
alone; where an unpinned source is load-bearing, a kernel-checked statement in
§7 or an existing estate theorem stands under it.

---

## 1. The headline — five costumes, one idea, and two things that are genuinely new

A design team about to write a fifth encoding of the reader monad should be
told: **items 1–5 below are one idea.** Not analogous. The same.

| # | Costume | What it actually is |
| --- | --- | --- |
| 1 | Reader monad / `MonadReader` | an argument, threaded implicitly |
| 2 | Typeclass dictionary passing | an argument, threaded implicitly, elaborated by the compiler |
| 3 | Capability passing | an argument, threaded explicitly, with an escape check |
| 4 | An effect handler for `ask` | an argument, delivered as an operation's answer |
| 5 | `ZEnvironment` / `Context<R>` in `ZLayer` / `Layer<ROut,E,RIn>` | an argument, keyed by service tag |

`EC1-T1` (§7) proves 1 ≡ 4 in this estate's own carrier: interpreting into
`ReaderT ρ M` and then supplying `r` **is** interpreting with the handler that
answers `ask` with `r`. `EC1-T2` proves 5 ≡ 4 in the strong form that matters
here: the environment a program over `S` needs, in target `M`, **is exactly a
`Handler S M`**, and `provide` is function application.

That is the whole content of "requirements tracking". `R = never` is not the
subtraction of a row. It is the moment the argument gets applied.

### What is genuinely new in `Layer`, and it is only two things

Read from the rc.112 source, `Layer` has exactly one member
(`src/Layer.ts:54,56`):

```ts
export interface Layer<in ROut, out E = never, out RIn = never> extends Variance<ROut, E, RIn>, Pipeable {
  build(memoMap: MemoMap, scope: Scope.Scope): Effect<Context.Context<ROut>, E, RIn>
}
```

So, literally: **`Layer` = a reader over `(MemoMap, Scope)` returning a program
over `RIn` that produces the services `ROut`.** Strip the two arguments and it
is a program that builds a record. The two arguments are the new content:

> **`Layer` = Reader ⊗ Scope ⊗ (a sharing policy).**

- **Reader** the estate already has, and it is `Handler` (§7 `EC1-T2`).
- **Scope** the estate has already *ruled*: R18, on `EC1-CE041` and
  `EC1-CE045`. Children stay `BlockId` data; the target carries state outside
  error, `ExceptT Refusal (StateT Word Id)`.
- **Sharing policy** is the only cluster with no estate ruling yet, and §5 is
  about it.

**Nothing here asks for a carrier.** `Layer S T := Handler S (Prog T)` typechecks
against `Cas.Lang.Handler` unchanged; layer composition is `Handler.through`,
and it is associative by `interpret_through`, which is already proved at
`Cas/Lang/Tower.lean:71` (§7 `EC1-T5`, `EC1-T6`). `Layer.merge` is
`Handler.sum` after `Prog.inl`/`Prog.inr` (§7 `EC1-T7`).

### The second collapse, which is less obvious

**A layer, a handler, and a program are the same object at three strata, and
R12 already says so.** The three "provisioning" verbs in the design space —

- *pass an environment* (`ReaderT`),
- *handle an operation* (`Handler S M`),
- *build a value* (`Layer`, `Context.Service`)

— are the three faces of R12's sentence "a service IS a handler, and a handler
CAN BE a program." Pick the face by *where you want the seam*, not by what the
thing is:

| You want the seam at | Use | Because |
| --- | --- | --- |
| interpretation time, one meaning per operation | `Handler S M` | the operation never becomes a value; nothing to hash, nothing to leak |
| the language, so the implementation is content | `Handler S (Prog T)` = a Layer | R7: it is a program, it hashes, it ships |
| the value, because a consumer wants a record | a `Prog T (Record)` and `Handler.through` | the record is first-order data; R14a keeps it out of `Prog` |

### The one asymmetry the collapse does not survive

R18's own consequence names it: **`Handler.through`'s middle must be
`Prog T`-valued, so it does not compose the scoped layer down.** A layer whose
acquisition can fail and must finalize does not sit at `Handler S (Prog T)`; it
sits at `Handler S (ExceptT Refusal (StateT Word Id))` and stops being
composable-as-a-program at that point. That is why R18 says FORK A "must be
restated per-layer". This is the single sharpest fact in this survey for the
design pass, and it is already in the record — it did not need the literature.

---

## 2. Cluster A — dependency provision

### A.1 Reader monad and `MonadReader` — UNPINNED

**Abstraction.** `Reader ρ a = ρ → a`; `MonadReader` adds `ask`/`local` as a
class so the environment threads implicitly through `bind` (Jones, *Functional
Programming with Overloading and Higher-Order Polymorphism*, 1995 — unpinned;
the `mtl` class is folklore-grade).

**Buys.** Zero-ceremony threading. `local` gives a scoped override for free,
because the environment is just the argument to a subterm.

**Costs.** Nothing else. It is a function argument. `local` is the only
operation with any content, and it is `(ρ → ρ) → m a → m a` — note that it
takes a *computation* as an argument. That is already a scoped operation, and
§4 is about what that costs.

**Costs HERE.** Nothing, because the estate does not need it: `EC1-T1` shows
the `ReaderT`-shaped provision and the handler-shaped provision agree
pointwise. Adding `ReaderT` to `Prog` would be adding a second spelling of
`Handler`. Note also that the **pinned** ITree library ships a `Reader` event in
`theories/Events/` alongside `State`, `Writer`, `Exception`, `Map`,
`Nondeterminism`, `Concurrency` — "the standard monadic effects, but as *data*
rather than as monad transformers" (`itrees-capabilities.md:78-80`,
exploration-grade, reading the pinned `xia-2020-interaction-trees.pdf`
corpus). The ITree authors already made this call. It is not a novel move.

### A.2 Typeclass dictionary passing — UNPINNED

**Abstraction.** Wadler & Blott, *How to make ad-hoc polymorphism less ad hoc*,
POPL 1989 (unpinned). A class constraint elaborates to an extra parameter
holding a record of methods; instance resolution is a compile-time search that
picks the argument.

**Buys.** The call site never writes the argument. Resolution is static and the
record is monomorphic at the use site, so it inlines.

**Costs.** *Coherence*: the whole design rests on there being exactly one
instance per type, decided globally. The moment you want two implementations of
one service you are outside the mechanism, and every language that tried
(named instances, local instances, Scala implicits) paid in either ambiguity
or a second, explicit mechanism. This is the precise reason `ZLayer` exists at
all in Scala: implicits could not carry "two databases".

**Costs HERE.** Dictionary passing is the single most tempting wrong turn in
this design space, and R7 forbids it outright. A dictionary is a record of
**functions**. It cannot be hashed, versioned, stored, or shipped to a non-Lean
consumer. Any encoding where the provided service is a Lean structure of
closures is a *host* artifact by R7 and can never become store content. The
estate's answer is already built: the service is a `Handler` whose clauses, at
F3, are `CodeId`s — first-order.

**One useful thing dictionary passing does teach.** The reason a dictionary
works at all is that it is *late-bound at elaboration and early-bound at
runtime*. `Handler S (Prog T)` has exactly that property, and the same reason:
the clause bodies are chosen before the run and are fixed during it.

### A.3 Capability passing — UNPINNED

**Abstraction.** Two lineages that arrive at the same shape. Object capabilities
(Miller, *Robust Composition*, PhD thesis 2006 — unpinned): authority travels
only by reference passing, so what a component can do is exactly what it was
handed. Effekt (Brachthäuser, Schuster, Ostermann, *Effects as Capabilities*,
OOPSLA 2020 — unpinned): effect handlers are *values* passed as second-class
capability arguments, with a type system that forbids them escaping the block
that received them.

**Buys.** The escape check. This is the one thing the reader monad does not
give you: a reader environment can be captured in a closure and outlive the
`local` that installed it; a second-class capability cannot. That is precisely
the property a resource handle needs.

**Costs.** Second-class-ness is contagious. Anything holding a capability
becomes second-class, so you get a two-tier value language, and the boundary
between the tiers is where the ergonomics go to die. Effekt pays for it with a
whole calculus.

**Costs HERE.** The escape check is a *type-system* device and R7 pushes it to
the host side. But the estate already has a first-order substitute, and it is
better for this purpose: **the region/scope is a name, not a type index**.
`ALGEBRA.md` already proposes `EC1-A17 Region` and `EC1-A24 ScopeFrame`, and
`CONTRACT-PACKET.md EC1-K18` clause 7 states the escape condition as an
invariant ("no resource token occurs in an outer-region value or daemon
capture") rather than as a typing rule. That is the R7-compatible reading of
capture checking: **capability escape becomes a checkable predicate on
first-order content, not a rank-2 type.** The pending falsifier `EC1-F04` is
already registered against it.

### A.4 `ZLayer` and `Layer<ROut,E,RIn>` — implementation read at rc.112

**Abstraction.** A recipe for constructing services, that may itself fail and
may itself need services. `ZLayer[RIn, E, ROut]` / `Layer<ROut, E, RIn>`.

**Buys.** Three things at once, and it is worth separating them because only
the second and third are new (§1):

1. requirement tracking (`RIn`) — this is the reader;
2. construction that can fail (`E`) and can acquire (`Scope`) — this is bracket;
3. sharing (`MemoMap`) — this is §5.

**Costs.** The type is a three-parameter variance puzzle (`in ROut, out E, out
RIn` at `Layer.ts:54`) whose contravariant output parameter exists only so
that `provide` subtracts correctly. Every user-facing confusion about Layers
traces to the fact that one type is doing three jobs.

**Costs HERE.** Almost nothing, *if the three jobs stay separated*. §7 shows
job 1 and the composition algebra land on `Handler`/`Handler.through`/
`Handler.sum` with no new carrier. Job 2 is R18's territory and already ruled.
Job 3 is the only open one.

**The trap.** If Effect Core v1 introduces a single `Layer` type carrying all
three jobs, it will have minted a carrier whose composition law it then has to
prove from scratch, when `interpret_through` already proves the interesting
half. The estate order is "consolidate; never mint", and here consolidation is
not a compromise: it is strictly stronger, because `interpret_through` is a
theorem about *interpretation*, not about a bespoke combinator.

### A.5 Scala 3 capture checking — UNPINNED

**Abstraction.** Capturing types (Odersky et al., *Capturing Types*, TOPLAS
2023 / arXiv:2105.11896 — unpinned; I did not read it in this session). A type
carries a *capture set* of the capabilities its values may retain;
`{c} T` means "a `T` that may capture `c`". Boxing/unboxing mediates the
first-/second-class boundary that Effekt makes syntactic.

**Buys.** It makes the escape check compositional and inferable, so
second-class-ness stops being contagious in practice.

**Costs.** It is a whole new dimension in the type system, with its own
subtyping, its own inference, and its own error messages.

**Costs HERE.** Prohibitive as stated, and unnecessary. R7 puts capture sets on
the host side; and the estate's classification plane already has the
first-order analogue: `EC1-C17 ScopeDomain` (`CLASSIFICATION.md:238`) carries
"region tree, maximum live depth bound, handler-provision sites, exit coverage,
and **escape set**". A capture set *is* an escape set. The difference is that
the estate computes it as a classification over first-order content instead of
checking it as a type. That is the right side of R7, and it is already drawn.

### A.6 The actual trade-off, stated

> **Pass an environment** when the thing provided is inert and the consumer
> only reads it. Cost: it can be captured and outlive its provider, and nothing
> stops that.
>
> **Handle an operation** when the thing provided is a *behaviour* and you want
> its meaning to be replaceable without touching the program. Cost: the
> program can no longer hold the service as a value, which is a feature until
> someone needs to pass a service to a non-Lean consumer.
>
> **Build a value** when the thing provided must be *constructed*, and
> construction can fail or acquire. Cost: you have just bought a lifetime, and
> R18 says the lifetime does not compose through `Prog`.

The three are not competing designs. They are three different answers to "when
does the meaning get fixed" — elaboration time, interpretation time, and run
time — and R10's stratification already names all three.

---

## 3. Cluster B — resource lifetime and scope

### B.1 Regions — Tofte & Talpin — UNPINNED

**Abstraction.** *Region-Based Memory Management* (Tofte & Talpin, Information
and Computation 1997 — unpinned). Allocation is annotated with a region; a
`letregion ρ in e` introduces a region whose entire contents die at the end of
`e`. A region inference assigns them.

**Buys.** Deallocation with no runtime bookkeeping, statically. And, more
important here: **lifetime becomes a lexical structure of the program**, so a
static analysis can decide it.

**Costs.** Region inference is where the bodies are buried; the classical
failure mode is a region that gets inferred too large (everything ends up in
the outermost region and nothing is freed early).

**Costs HERE.** Very low, and this is the most *transferable* item in the whole
survey. `letregion` is the shape the estate has already proposed twice
independently: `EC1-A17 Region`, `EC1-A24 ScopeFrame`, and `EC1-K43`'s
statement that "a scope may modify only its frame, descendants, registered
finalizers, owned…". A region as a **first-order name with an acyclic nesting
invariant** (`ALGEBRA.md` `RegionsWF`) is exactly the R7-legal reading. Nothing
in Tofte–Talpin's *statement* needs types; the types were how they *inferred*
it. Here it is checked, not inferred, and `EC1-K18` already carries the clauses.

### B.2 `runST` and rank-2 encapsulation — UNPINNED

**Abstraction.** Launchbury & Peyton Jones, *Lazy Functional State Threads*,
PLDI 1994 (unpinned). `runST :: (forall s. ST s a) -> a`. The phantom `s` is
universally quantified at the *elimination* site, so a reference tagged with
one thread's `s` cannot be typed at another's.

**Buys.** Encapsulation of a mutable region inside a pure function, with a
one-line type and no runtime cost.

**Costs.** It is a *typing* trick and it does exactly one thing: prevent
escape. It cannot express ordering, exactly-once release, or failure — `runST`
has no notion of a finalizer. It also does not compose: two nested `ST`
computations cannot share references.

**Costs HERE.** **Refused by R7, and it would not have helped anyway.** Rank-2
quantification is a host-side device; the escape property it buys is the same
property `EC1-K18` clause 7 states as an invariant. The important observation
for the design pass is the *negative* one: even in Haskell, `runST` is not the
resource story — `bracket` is. Rank-2 gives escape-freedom; it gives nothing
about release.

### B.3 Monadic regions — Fluet & Morrisett — UNPINNED

**Abstraction.** *Monadic Regions* (Matthew Fluet & Greg Morrisett, ICFP 2004;
JFP 2006 — unpinned). Regions in a monadic type discipline with a subtyping /
witness structure so that an inner region's handles can be used at an outer
one, extending the `ST` trick from one region to a nested family.

**Buys.** Nesting. `runST`'s `s` gives one region; monadic regions give a
region *tree* with safe inward coercions.

**Costs.** The witness plumbing is visible in every type, and the encoding
needs higher-rank types plus a subtyping relation carried in terms.

**Costs HERE.** The costs are all in the type-index machinery, which R7 puts
on the host. **The idea that survives is "region tree with a coercion", and the
estate already has both halves**: the acyclic region nesting in `RegionsWF` and
the parent-delegation dispatch in `EC1-A23 HandlerEnv` ("explicit delegation to
one named parent handler … Named parent delegation is visible in content and
checked for cycles", `ALGEBRA.md`). Named parent delegation *is* the inward
coercion, written as content instead of as a witness term.

### B.4 Lightweight monadic regions — Kiselyov & Shan — UNPINNED

**Abstraction.** *Lightweight Monadic Regions* (Oleg Kiselyov & Chung-chieh
Shan, Haskell Symposium 2008 — unpinned). The same guarantees with far less
type machinery: a monad transformer stack where region nesting is transformer
nesting, plus `MonadRaise`-style lifting, and — the part that matters — an
explicit `SHandle` that can be *promoted* to a parent region when it must
outlive its own.

**Buys.** It is the paper that shows the region discipline does not require
exotic types, only a disciplined stack. And it names the real-world escape
hatch (promotion) rather than pretending it is never needed.

**Costs.** The transformer stack becomes the region tree, so the *shape* of the
program's types encodes the *dynamic* region structure. Any dynamic region —
one whose depth depends on a value — is out of reach.

**Costs HERE, and this is the load-bearing one.** `CLASSIFICATION.md:241`
already records the exact fact that defeats the transformer-stack encoding
here: "Maximum *dynamic* depth is unbounded when recursion enters a new scope."
A transformer stack cannot express unbounded dynamic nesting; a first-order
`ScopeId` map in a `Configuration` can. **This is an independent argument for
the reference-machine shape the packet already chose, and it comes from the
region literature rather than from the effect literature.** Worth recording,
because the packet currently justifies the machine on control-flow grounds
only.

Also worth naming: the **promotion** escape hatch. `EC1-K18` currently forbids
escape flatly (clause 7). Kiselyov & Shan's experience says a real system needs
a *sanctioned* transfer of a handle to a parent scope. The estate's analogue is
already half-drawn — the `daemon` lifetime in `ALGEBRA.md` transfers ownership
to the root supervisor "and is reported". Whether resource handles get the same
sanctioned transfer is an open design question that this literature says will
be asked.

### B.5 `bracket` / RAII — UNPINNED

**Abstraction.** `bracket acquire release use` (Haskell `Control.Exception`);
destructors on scope exit (C++ RAII, Stroustrup). Both unpinned; both folklore.

**Buys.** Exactly-once release on every exit path, including the exceptional
one, with no type machinery at all. It is the *only* mechanism in this cluster
that addresses release rather than escape.

**Costs.** It is dynamic. Nothing statically prevents you from returning the
handle out of `use`. RAII and `bracket` both rely on convention for that.

**Costs HERE.** This is where R18 bites and it has already bitten. `EC1-CE045`
proves `ensuring_never_finalises_a_refusal`: sequencing a finalizer with
`Prog.bind` runs it exactly when the body **succeeds**, because
`interpretRef_bind` is refusal-strict. And `reraise_is_finalizer_blind` proves
the obstruction is structural — `Except.error r` has no word slot, so *no*
clause into `ReaderT EnvR (StateT Word (Except Refusal))` can do better. The
ruled repair is the transformer **order**: `ExceptT Refusal (StateT Word Id)`.

> **Direct consequence for Layer.** `Layer.build` acquires. `Layer.launch`
> holds the scope open (`Layer.ts:3897-3898`: `scoped(andThen(build(self),
> never))`). Both are bracket. **Therefore any Layer design in this estate
> inherits `EC1-CE045` verbatim**, and a Layer whose failure path lands in a
> target that discards the word is refuted before it is written. This is not
> an inference from the literature; it is R18 applied.

### B.6 Linear and affine types — UNPINNED

**Abstraction.** Linear logic (Girard 1987); *Linear types can change the
world!* (Wadler 1990); Linear Haskell (Bernardy, Boespflug, Newton, Peyton
Jones, Spiwack, POPL 2018); Rust's affine ownership. All unpinned.

**Buys.** Exactly-once, statically, as a property of the *value* rather than
of the *scope*. This is a genuinely different guarantee from bracket: bracket
guarantees the release *runs*; linearity guarantees the handle is not *used
after* it.

**Costs.** It infects the whole value language. Every combinator needs a linear
variant; every data structure needs a linear variant.

**Costs HERE.** R7 again: linearity is a typing judgment over a host term
language, and `Prog`'s continuations are host functions, so there is no linear
discipline to impose on them. The **locally-held, unpinned** Aeneas paper
(arXiv:2206.07185, `.reference/papers/2206.07185v2.pdf`) is interesting here
precisely because it goes the other way: it gives Rust's borrow discipline a
"value-based" semantics with "no notion of memory, addresses or pointer
arithmetic", enforcing borrow soundness "via a semantic criterion based on
loans rather than through a syntactic type-based lifetime discipline". That
is the same move the estate makes — a *semantic, checkable criterion on
first-order state* in place of a type discipline. I flag the parallel; no
conclusion here rests on it, and I did not read past the abstract.

### B.7 Structured concurrency — UNPINNED

**Abstraction.** A child task may not outlive the syntactic block that spawned
it (Sústrik's "Structured Concurrency", 2016; trio nurseries; Kotlin
`coroutineScope`). Unpinned, all of it — this is engineering folklore with no
canonical paper.

**Buys.** It makes concurrency's lifetime story the *same* story as the
resource lifetime story: one scope discipline covers both.

**Costs.** Daemon/background tasks are genuinely outside it and every system
adds an escape hatch, which is where the leaks come back.

**Costs HERE.** Already absorbed: `ALGEBRA.md`'s `fork` has exactly three
lifetimes — `scoped`, `inherited`, `daemon` — and daemon "transfers ownership
to the root supervisor and appears in the final host obligation; it does not
silently disappear". That is the escape hatch, made accountable. Note the S17
rulings record that condition 2 (daemon fibers admitted or refused in v1) is
**open with zero corpus material**. The literature will not settle it; it has
no canonical answer either.

---

## 4. Cluster C — scoped operations in effect handlers

This is the cluster where the estate's answer is already correct and the
literature's job is to say what it cost everyone else.

### C.1 The problem, stated precisely

An *algebraic* operation is one that commutes with sequencing:
`op(k) >>= f = op(λx. k x >>= f)`. Handlers for algebraic operations are
uniquely determined by a clause per operation, and everything is modular.

`catch`, `local`, `once`, `bracket`, `fork` are **not** algebraic. Their
argument is a *computation*, and the scope of the operation is that
computation, not the whole continuation. If you encode `catch e h` as an
operation of a first-order signature and let the free monad's `bind` push the
continuation inside, you get the wrong program: the handler applies to the
continuation as well as to the body.

### C.2 *Effect Handlers in Scope* — Wu, Schrijvers, Hinze, 2014 — UNPINNED

**Abstraction.** (Nicolas Wu, Tom Schrijvers, Ralf Hinze, Haskell Symposium
2014 — unpinned; I did not read the PDF in this session.) The diagnosis above,
and two encodings. The first keeps the syntax first-order and marks scopes with
explicit `begin`/`end` operations — the *bracketing* encoding. The second, which
the later line follows, makes the signature **higher-order**: the functor's
argument positions hold computations, so `Prog` is a free monad over an
endofunctor on functors, and handlers acquire a **forwarding** obligation
(`weave`) so that an outer handler's state threads correctly through a scoped
subcomputation that an inner handler owns.

**Buys.** `catch`, `local`, `once` get their intended semantics, and handler
composition order becomes an explicit, controllable part of the semantics
rather than an accident.

**What they had to give up.** Three things, and they are the whole story:

1. **First-orderness of the signature.** The syntax functor now mentions the
   computation type in a negative-ish position. The tree stops being a tree of
   data over an alphabet.
2. **Free handler composition.** Every handler must supply a `weave`/forwarding
   clause, and getting it wrong is silent. Composition stops being "sum the
   signatures".
3. **Uniqueness of the semantics.** With scoped operations, handler order is
   observable — `catch` outside `state` and `state` outside `catch` are
   different programs. That is not a defect but it is a lost law.

### C.3 The later line — all UNPINNED

- **Piróg, Schrijvers, Wu, Jaskelioff**, *Syntax and Semantics for Operations
  with Scopes*, LICS 2018. The categorical account: scoped operations are
  modelled by an indexed/graded algebra over a "scoped" endofunctor, with the
  free construction giving a syntax where scope depth is an index.
- **Yang, Paviotti, Wu, van den Berg, Schrijvers**, *Structured Handling of
  Scoped Effects*, ESOP 2022. Handlers for scoped effects as algebras of an
  indexed monad; makes the forwarding obligation a structure rather than a
  convention.
- **van den Berg & Schrijvers**, *A Framework for Higher-Order Effects &
  Handlers*, Science of Computer Programming 2024. Consolidation of the above.
- **Bach Poulsen & van der Rest**, *Hefty Algebras: Modular Elaboration of
  Higher-Order Algebraic Effects*, POPL 2023. **The most directly relevant of
  the four.** The claim: do not handle higher-order effects — *elaborate* them
  into first-order algebraic effects first, then handle. Elaboration is a
  separate, modular phase; handlers stay first-order and keep their free
  composition.

I have read none of these four in this session; all four are unpinned and none
is in `papers.lock.json`. They are named so that a design pass knows the shape
of the field and does not re-derive it.

### C.4 What the PINNED sources say

- **HITrees** (`fadaei-sammler-2025-hitrees.pdf`, arXiv:2510.14558, pinned;
  read via `itrees-capabilities.md:330`, exploration-grade). The abstract's
  claim is "the first variant of interaction trees to support higher-order
  effects in a non-guarded type theory", and the two techniques are: shape
  effects so fixpoints are ordinary inductive types, and **defunctionalize
  higher-order outputs into abstract identifiers plus a separate "invoke"
  operation.** Reasoning is a big-step relation `t ⇓ v`, not a bisimulation
  family.

  **This is the estate's answer, published.** "Children are `BlockId`s, not
  functions" is defunctionalization by address. R18 clause 1 —
  "No `HHandler`, no higher-order handler carrier. Children remain `BlockId`
  data; the existing `Handler` type is sufficient" — is the same ruling HITrees
  made, for the same reason (Lean has no native coinduction, and the authors
  chose an inductive carrier plus a big-step relation). The estate is not
  inventing here; it is on the one published Lean 4 design point.

- **Guarded Interaction Trees** (`frumin-timany-birkedal-2024-…`,
  arXiv:2307.08514, pinned; read via `itrees-capabilities.md:298-306`). The
  diagnosis: "ITrees are first-order in their events, so **higher-order**
  effects don't fit." The fix: define the trees *inside Iris* — guarded type
  theory — so recursive domain equations can be solved.

  **This is the road R1 closes.** GITrees is the well-executed version of
  "make the carrier able to hold computations", and its price is a guarded
  ambient logic. R1 refuses that by law, not by taste. Naming GITrees is how a
  design pass knows that the higher-order-carrier branch has been explored to
  its end by people with more machinery, and what it costs.

- **Frank / *Do Be Do Be Do*** (`lindley-mcbride-mclaughlin-2016-frank.pdf`,
  arXiv:1611.09259, pinned; role-scoped in `REFERENCES.md:158` to "operators,
  adjustments, and handling as first-class"). Frank's contribution to *this*
  question is the **adjustment**: an ambient ability that a handler modifies
  for the extent of a computation. That is `local` generalized to abilities,
  and it is a scoped operation by construction.

- **Choice Trees** (`chappe-2023-choice-trees.pdf`, arXiv:2211.06863, pinned;
  via `itrees-capabilities.md:287-293`). Diagnosis: ITrees model nondeterminism
  "only by pushing it into a handler, which is awkward for concurrency", so
  CTrees add branching nodes to the carrier. The pattern to notice: **when an
  effect's scope is the whole rest of the computation, pushing it into a
  handler stops working and it migrates into the carrier.** That is the
  pressure a Layer's `Scope` will apply, and the estate's answer must be the
  reference machine (`EC1-A26 Configuration`) rather than a richer `Prog`.

### C.5 What it costs HERE

**Nothing new, and this is the good news of the survey.** The estate's answer
to the scoped-operation problem is HITrees' answer, already ruled on kernel
evidence:

| The literature's problem | The estate's answer | Where it is already settled |
| --- | --- | --- |
| operation whose argument is a computation | the argument is a `BlockId`; the machine looks it up | R18 clause 1; `ALGEBRA.md` §6 |
| the carrier must go higher-order | it does not; `Sig`/`Prog`/`Handler` unchanged | `EC1-CE041` repair, no `HHandler` |
| handler needs `weave`/forwarding | the reference machine owns the scope stack | `EC1-A24 ScopeFrame`, `EC1-A26` |
| handler order is observable | admitted: `EC1-CE006` already proves sequential world effect is non-commutative | `EC1-CE006` |
| the target must observe the child's outcome | ruled: `ExceptT Refusal (StateT Word Id)` | R18 clause 2 |

The one thing the estate pays that the higher-order-syntax line does not:
**`Handler.through` stops composing at the scoped layer** (R18's FORK A
consequence). In the higher-order encodings the scoped handler is still a
handler and still composes; here it is aimed at a concrete machine target and
is not `Prog T`-valued. That is a real, named cost of the R7-legal choice, and
it is the correct trade — but a design pass should state it rather than
discover it.

---

## 5. Cluster D — memoization and sharing

The brief's framing is exactly right and I can sharpen it with evidence.

### D.1 The mechanism, read from the source

`effect@4.0.0-rc.112`, `library/effects/node_modules/effect/src/Layer.ts`:

```ts
// :432
readonly map = new Map<Layer<any, any, any>, MemoMapEntry>()

// :235-239
type MemoMapEntry = {
  observers: number
  effect: Effect<Context.Context<any>, any>
  readonly finalizer: (exit: Exit.Exit<unknown, unknown>) => Effect<void>
}
```

Three facts follow directly, and each one matters:

1. **The memo key is JavaScript reference identity.** A `Map` keyed by the
   `Layer` object. Two structurally identical layers built by two separate
   constructor calls are two keys and are built twice. *Sharing in Effect is
   not content-based; it is pointer-based.*
2. **The memo entry is a reference count** (`observers`, incremented at `:245`
   in `memoMapReuse`, decremented at `:403`, and the layer scope closed only at
   zero). So the memo map is simultaneously the **release schedule**.
   Memoization and lifetime are the same mechanism.
3. **Sharing is a parameter, not a law.** `Layer.fresh` (`:3850-3851`) is
   `fromBuildUnsafe((_, scope) => self.build(makeMemoMapUnsafe(), scope))` —
   it discards the ambient memo map and passes an empty one. If sharing were a
   semantic equality, `fresh` would be a no-op. It is not, and it ships.

### D.2 The literature's answer to "equality or quotient?"

The general theory is older than layers and it is unambiguous.

- **Call-by-need / graph reduction** (Wadsworth 1971; Ariola, Felleisen,
  Maraist, Odersky, Wadler, *A Call-By-Need Lambda Calculus*, POPL 1995 — both
  unpinned). Sharing a redex is *sound* — observationally equal to not sharing
  — in a **pure** calculus. The call-by-need calculus is proved to induce the
  same observational equivalence as call-by-name. That is the positive result,
  and it has a hard side condition: purity.
- **Observable sharing** (Claessen & Sands, *Observable Sharing for Functional
  Circuit Description*, ASIAN 1999 — unpinned). The negative result. Add a
  primitive that can *observe* whether two structures are shared (reference
  equality) and referential transparency breaks: `let x = e in f x x` and
  `f e e` become distinguishable. Their contribution is a semantics for a
  language that admits the breach deliberately, because circuit description
  needs it.
- **Hash-consing** (`Implementing and reasoning about hash-consed data
  structures in Coq`, arXiv:1311.2959, **pinned**, canonical-hashing cluster;
  and Filliâtre & Conchon, *Type-Safe Modular Hash-Consing*, ML Workshop 2006,
  doi:10.1145/1159876.1159880, cited in `itrees-capabilities.md:429-433`). The
  reconciliation: sharing is *forced* by canonicalizing to a maximally shared
  DAG, and then reference equality **is** structural equality. Sharing stops
  being observable because the two things you might have distinguished have
  been identified.
- **Maximal sharing with cycles** (`Maximal Sharing in the Lambda Calculus with
  letrec`, arXiv:1401.1460, **pinned**). Maximal sharing computed by
  bisimulation collapse of term graphs; maximally shared representatives are
  proved to exist. The sweep's own conclusion
  (`itrees-capabilities.md:443-445`): "bisimulation collapse is a viable
  canonicalization procedure exactly when the infinite object has a finite
  cyclic presentation."

**Both pinned rows carry the canonical-hashing cluster's role scoping**: they
support the working set for a content-addressing scheme with proved invariance;
they do **not** support any claim that a published scheme is sound as stated
for this estate's term algebra.

### D.3 The answer, stated

> Sharing is a **semantic equality** exactly when acquisition is a function of
> content. Otherwise it is a **quotient**, and it must be declared as an
> observation.

Both halves are checkable here, and §7 checks them.

**The equality half — and the estate already has it.** On the CAS plane, `put`
is word-idempotent on residents: `EC1-T4` (§7) proves

```text
interpretRef H (put n) w = .ok (Cas.addr H ⟨n, hwf⟩, w)
```

when `n` is already resident at its own address — the word is *unchanged*. The
characterization is the estate's own `Cas.put_duplicate_iff`
(`Cas/IR/Join.lean:213`), whose docstring already says it: "Re-admitting what
the store already carries is a no-op by characterization, not by convention."

**Therefore: on the CAS plane, the memo map IS the content address.** No
`MemoMap`, no reference-equality key, no observer count. Building the same node
twice and building it once are the same word, so they are `ObsEq`, so the
sharing question does not arise. This is R4 paying for itself in an unexpected
place.

**The quotient half.** `EC1-T3a`/`EC1-T3b` (§7) exhibit the general case in
three lines: a one-operation acquisition signature whose handler appends a
fresh token. `once` and `twice` **agree on the service value** the caller
receives (both get token `0`) and **disagree in the trace**. Sharing is
observationally distinguishable at the word even where the consumer cannot tell
from the value it was handed. `sharing_is_observable` closes by `decide`, with
no axioms.

So the brief's premise is confirmed, and confirmed sharply: *observational
indistinguishability of the service value does not imply observational
indistinguishability of the run.*

### D.4 What it costs HERE

**The rulable position, which I believe the design pass should take.** There
are three coherent options and only the third is consistent with R4/R11:

1. **Memoize by identity** (Effect's answer). Requires a key that is not
   content — reference identity. R4 forbids it as an *identity*, and R7
   forbids the key from being a host pointer if any of this is to be content.
   **Refused.**
2. **Memoize by content address.** Free on the CAS plane (`EC1-T4`). Sound
   exactly when acquisition is a pure function of content, which for a general
   `acquire` it is not (`EC1-T3b`). **Correct where it applies; not general.**
3. **Do not memoize at runtime; share in the program.** Build the service once
   and bind it — sharing becomes the DAG structure of the program term, which is
   first-order content, hashable, and inspectable. This is exactly R14a's pure
   discipline ("effect-free work stays OUTSIDE `Prog`"), and it is exactly what
   the hash-consing literature says canonicalization buys you.

Under (3), "layer memoization" is not a runtime feature at all. It is
**maximal sharing of the layer graph**, computed before the run, on content —
and the pinned sources for that are already in the corpus
(arXiv:1401.1460, arXiv:1311.2959) with their role scoping intact.

Two consequences worth putting in front of the design pass:

- **A "built twice vs once" difference is a real difference and must not be
  quotiented silently.** R11 clause 3 already established the discipline for
  this: `ObsEq` forgets the refusal-side word deliberately, and "any finer mask
  is a **new observation** and must be named as such". A sharing quotient is a
  *coarser* mask, and it is subject to the same rule: name it, or do not take it.
- **Memoization is a lifetime decision, not a performance decision.** Effect's
  `observers` counter is the proof: the memo entry decides when the layer's
  scope closes. So any sharing policy this estate adopts lands back in R18's
  territory, not in an optimization pass.

---

## 6. The mint list — what this survey says NOT to add

| Tempting to mint | Already exists | Evidence |
| --- | --- | --- |
| `Layer` as a new carrier | `Handler S (Prog T)` | `EC1-T5`, `EC1-T6` (§7) |
| A layer-composition combinator + its associativity proof | `Handler.through` + `interpret_through` | `Cas/Lang/Tower.lean:65,71` (PROVED) |
| `Layer.merge` | `Handler.sum` + `Prog.inl`/`Prog.inr` | `EC1-T7` (§7, typechecks) |
| `ReaderT`/`Env`/`Context` in the core | `Handler S M` itself | `EC1-T1`, `EC1-T2` (§7) |
| A requirements row subtracted by `provide` | function application | `EC1-T2` |
| `HHandler` / higher-order handler carrier | first-order `BlockId` children | R18 cl. 1; `EC1-CE041` |
| A rank-2 or capture-set escape check | the escape set in `EC1-C17 ScopeDomain`, invariant `EC1-K18` cl. 7 | `CLASSIFICATION.md:238`, `CONTRACT-PACKET.md:458` |
| A `MemoMap` | the content address on the CAS plane; program-level sharing elsewhere | `EC1-T4`, R4, R14a |
| A region type index | `EC1-A17 Region` as a first-order name + `RegionsWF` | `ALGEBRA.md:302` |

And the three things this survey says **do** need work, because nothing in the
estate or the literature settles them:

1. **The sharing policy** — options in §5.4. No ruling exists. It is a
   *lifetime* decision (Effect's `observers`), so it belongs with R18, not with
   an optimizer.
2. **Sanctioned handle promotion to a parent scope** — Kiselyov & Shan's
   experience says it will be asked for; `EC1-K18` cl. 7 currently forbids it
   flatly, and the `daemon` lifetime is the only sanctioned transfer in the
   packet.
3. **Where the scoped layer stops composing.** R18's FORK A consequence is
   stated but the per-layer restatement does not exist. That is the seam the
   whole design turns on, and it is currently one sentence.

---

## 7. Kernel-checked sketch

Seven statements. Written to make §1 and §5 falsifiable rather than rhetorical.
**Exit 0, no errors, no warnings.** Not promoted; nothing in `library/` was
touched.

**Command** (the file was checked at the scratch path shown; recreate it from
the source below at any path outside every lake target):

```text
cd /Users/pooks/Dev/foldlab/library/cas
lake env lean /private/tmp/claude-501/-Users-pooks-Dev-foldlab/a31288e1-481d-4d48-bbf7-34e199015bcd/scratchpad/LayerLit.lean
```

**Receipts** (verbatim output):

```text
'LayerLitScout.provide_by_env_eq_provide_by_answer' does not depend on any axioms
'LayerLitScout.provide_is_handler_application' depends on axioms: [propext, Quot.sound]
'LayerLitScout.once_twice_agree_on_first' does not depend on any axioms
'LayerLitScout.sharing_is_observable' does not depend on any axioms
'LayerLitScout.cas_put_of_resident_leaves_the_word' depends on axioms: [propext, Quot.sound]
'LayerLitScout.provide_is_two_interpretations' depends on axioms: [propext, Quot.sound]
'LayerLitScout.Layer.andThen_assoc' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`, no `Classical.choice`, no `native_decide`.

| ID here | Theorem | What it establishes |
| --- | --- | --- |
| `EC1-T1` | `provide_by_env_eq_provide_by_answer` | reader-as-transformer ≡ reader-as-effect |
| `EC1-T2` | `provide_is_handler_application` | the requirements environment **is** a `Handler`; `provide` is application |
| `EC1-T3a` | `once_twice_agree_on_first` | build-once and build-twice agree on the service value |
| `EC1-T3b` | `sharing_is_observable` | …and disagree in the acquisition trace |
| `EC1-T4` | `cas_put_of_resident_leaves_the_word` | on the CAS plane the content address is the memo map |
| `EC1-T5` | `provide_is_two_interpretations` | `Layer.provide` = `interpret_through` (already proved upstream) |
| `EC1-T6` | `Layer.andThen_assoc` | layer composition is associative with no new carrier |
| `EC1-T7` | `Layer.merge` | merge typechecks from `Handler.sum` + `Prog.inl`/`inr` (definition only; no law claimed) |

These IDs are **local to this file**. They are not registered in
`COUNTEREXAMPLES.md` and must be given register IDs before any packet row cites
them.

### Source

```lean
import Cas.Lang.Tower
import Cas.IR.Join
import Cas.Lang.Representation

namespace LayerLitScout

open Cas.Lang

/-! ## 1. Reader as an EFFECT (ITrees `Events/Reader`) -/

/-- The reader effect as first-order DATA: one operation, answering `ρ`. -/
def ReaderSig (ρ : Type) : Sig where
  Op := Unit
  Ans := fun _ => ρ

/-- `ask` is an operation, not a monad. -/
def ask (ρ : Type) : Prog (ReaderSig ρ) ρ := .vis () .pure

/-- Provision by ANSWERING: the environment is baked into the handler. -/
def constHandler {M : Type → Type} [Monad M] {ρ : Type} (r : ρ) :
    Handler (ReaderSig ρ) M where
  handle _ := pure r

/-- Provision by PASSING: the environment is the target monad's reader slot. -/
def readerHandler (M : Type → Type) [Monad M] (ρ : Type) :
    Handler (ReaderSig ρ) (ReaderT ρ M) where
  handle _ := fun r => pure r

/-- T1 — passing an environment and handling an operation are the SAME
provision. -/
theorem provide_by_env_eq_provide_by_answer
    {M : Type → Type} [Monad M] [LawfulMonad M] {ρ A : Type}
    (r : ρ) (p : Prog (ReaderSig ρ) A) :
    interpret (readerHandler M ρ) p r = interpret (constHandler (M := M) r) p := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    show ((pure r : M ρ) >>= fun a => interpret (readerHandler M ρ) (k a) r)
        = ((pure r : M ρ) >>= fun a => interpret (constHandler (M := M) r) (k a))
    rw [pure_bind, pure_bind, ih r]

/-! ## 2. The ZLayer collapse: an environment of services IS a handler -/

/-- Requirements-as-environment: the thing a `ZLayer`/`Layer<ROut,E,RIn>`
threads is, at this signature, exactly a `Handler S M`. -/
def envHandler (S : Sig) (M : Type → Type) [Monad M] :
    Handler S (ReaderT (Handler S M) M) where
  handle op := fun h => h.handle op

/-- T2 — `provide` is handler application. -/
theorem provide_is_handler_application
    {S : Sig} {M : Type → Type} [Monad M] [LawfulMonad M] {A : Type}
    (h : Handler S M) (p : Prog S A) :
    interpret (envHandler S M) p h = interpret h p := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    show (h.handle op >>= fun a => interpret (envHandler S M) (k a) h)
        = (h.handle op >>= fun a => interpret h (k a))
    exact bind_congr fun a => ih a

/-! ## 3. Sharing is OBSERVABLE in an acquisition trace -/

/-- A one-operation acquisition signature. -/
def AcqSig : Sig where
  Op := Unit
  Ans := fun _ => Nat

def acquire : Prog AcqSig Nat := .vis () .pure

/-- The tracing handler: every acquisition appends a fresh token. -/
def tracingHandler : Handler AcqSig (StateT (List Nat) Id) where
  handle _ := fun t => (t.length, t ++ [t.length])

def once : Prog AcqSig (Nat × Nat) :=
  acquire >>= fun a => .pure (a, a)

def twice : Prog AcqSig (Nat × Nat) :=
  acquire >>= fun a => acquire >>= fun b => .pure (a, b)

/-- T3a — memoized and unmemoized layers agree on the service value. -/
theorem once_twice_agree_on_first :
    (interpret tracingHandler once []).1.1 = (interpret tracingHandler twice []).1.1 := by
  rfl

/-- T3b — and they DISAGREE in the acquisition trace. -/
theorem sharing_is_observable :
    (interpret tracingHandler once []).2 ≠ (interpret tracingHandler twice []).2 := by
  decide

/-! ## 4. On the CAS plane, the memo map is the content address -/

/-- T4 — re-admitting a resident node leaves the word untouched. -/
theorem cas_put_of_resident_leaves_the_word
    (H : Cas.Bytes → Cas.Addr32) (w : Cas.Word) (n : Cas.Node) (hwf : n.WF)
    (hrefs : Cas.RefsOk (Cas.Word.toStore w) n.refs)
    (hres : Cas.Word.toStore w (Cas.addr H ⟨n, hwf⟩) = some n) :
    interpretRef H (Cas.Lang.put n) w
      = .ok (Cas.addr H ⟨n, hwf⟩, w) := by
  have hdup : Cas.put H (Cas.Word.toStore w) ⟨n, hwf⟩
      = .ok (.duplicate (Cas.addr H ⟨n, hwf⟩)) :=
    (Cas.put_duplicate_iff (H := H) (σ := Cas.Word.toStore w)
      (n := ⟨n, hwf⟩) hrefs).mpr hres
  simp only [interpretRef, interpret, Cas.Lang.put, referenceHandler]
  simp only [bind, StateT.bind, hwf, hdup, pure, StateT.pure]
  simp [Except.bind, Except.pure]

/-! ## 5. `Layer<ROut, E, RIn>` is `Handler S (Prog T)` — a type already here -/

/-- A LAYER: the services of `S` implemented as programs over the lower
signature `T`. Effect-TS `Layer<ROut, E, RIn>` with `ROut := S`, `RIn := T`,
`E` in `T`'s refusal arm. No new carrier. -/
abbrev Layer (S T : Sig) := Handler S (Prog T)

/-- Layer composition is `Handler.through` at a `Prog` target. -/
def Layer.andThen {S T U : Sig} (l : Layer S T) (m : Layer T U) : Layer S U :=
  Handler.through l m

/-- Providing a layer to a runtime is the SAME operation, at a non-`Prog`
target. -/
def Layer.provide {S T : Sig} {M : Type → Type} [Monad M]
    (l : Layer S T) (h : Handler T M) : Handler S M :=
  Handler.through l h

/-- T5 — `provide` is `interpret` twice. This is `interpret_through`,
already PROVED at `Cas/Lang/Tower.lean:71`. -/
theorem provide_is_two_interpretations
    {S T : Sig} {M : Type → Type} [Monad M] [LawfulMonad M] {A : Type}
    (l : Layer S T) (h : Handler T M) (p : Prog S A) :
    interpret h (interpret l p) = interpret (l.provide h) p :=
  interpret_through l h p

/-- T6 — layer composition is associative, with no `ZLayer` algebra and no
memo map. -/
theorem Layer.andThen_assoc {S T U V : Sig}
    (l : Layer S T) (m : Layer T U) (k : Layer U V) :
    (l.andThen m).andThen k = l.andThen (m.andThen k) := by
  unfold Layer.andThen Handler.through
  congr 1
  funext op
  exact interpret_through m k (l.handle op)

/-- T7 — `Layer.merge` needs nothing new either. Typechecks; no semantic law
is claimed for it here. -/
def Layer.merge {S T U V : Sig} (l : Layer S U) (m : Layer T V) :
    Layer (S ⊕ₛ T) (U ⊕ₛ V) :=
  Handler.sum
    (S := S) (T := T) (M := Prog (U ⊕ₛ V))
    { handle := fun op => (l.handle op).inl }
    { handle := fun op => (m.handle op).inr }

#print axioms provide_by_env_eq_provide_by_answer
#print axioms provide_is_handler_application
#print axioms once_twice_agree_on_first
#print axioms sharing_is_observable
#print axioms cas_put_of_resident_leaves_the_word
#print axioms provide_is_two_interpretations
#print axioms Layer.andThen_assoc

end LayerLitScout
```

---

## 8. Where I think the brief's framing needs correcting

Two places, stated because being assigned a framing is not being asked to
defend it.

**(a) "Scoped operations in effect handlers" is not the estate's open problem.**
The brief asks how handler formalisms represent an operation whose argument is
a computation, and notes the estate answers with defunctionalization by address.
That is right, and it is *already ruled* — R18 clause 1, on `EC1-CE041`. The
open problem is one layer down and the survey found it in R18's own last
paragraph: **`Handler.through` does not compose the scoped layer down**, so the
tower has a floor. A design pass that spends its budget on the scoped-operation
representation will be re-deciding something settled while the actual seam goes
unwritten.

**(b) The memoization question is a lifetime question, not an identity
question.** The brief frames it as "when is sharing a semantic equality versus a
quotient", which is the right general question and §5.2/§5.3 answer it. But the
rc.112 source shows the two are fused in practice: the memo entry *is* the
reference count that decides when the scope closes (`Layer.ts:236,245,403`). So
a sharing ruling here is not a separate ruling from R18 — it is a clause of it.
Filing it as an optimization question would put it in the wrong lane.

---

## 9. What I did NOT check

- **I did not read any pinned PDF.** None of the interaction-trees cluster is
  present on this host (§0). Every "pinned" citation rests on `PAPERS.md`'s
  catalog row plus the exploration-grade `itrees-capabilities.md`. A claim that
  needs the paper's own text is not established here.
- **I did not read** Wu/Schrijvers/Hinze 2014, Piróg et al. 2018, Yang et al.
  2022, Bach Poulsen & van der Rest 2023, van den Berg & Schrijvers 2024,
  Fluet & Morrisett, Kiselyov & Shan, Tofte & Talpin, Launchbury & Peyton
  Jones, Claessen & Sands, Ariola et al., Wadler & Blott, Miller, Brachthäuser
  et al., Odersky et al., or Bernardy et al. **in this session.** All are
  unpinned; none is in `papers.lock.json`. §2–§5 report them from prior
  knowledge, and every conclusion has an estate theorem or a §7 statement
  under it.
- **I did not verify the ZIO `ZLayer` claims at all.** No Scala source was read.
  Everything in §1/§2.4/§5 about memoization is read from
  `effect@4.0.0-rc.112` TypeScript at the path given. ZIO is named as lineage
  only.
- **The Effect source I read is rc.112, not the rc.111 catalog pin.** Line
  numbers are reproducible at
  `library/effects/node_modules/effect/src/Layer.ts` and nowhere else.
- **I read only the abstract** of the locally-held, unpinned Aeneas paper.
- **I did not verify** that `Layer.provide`/`provideMerge`/`mergeAll` in rc.112
  have the algebraic properties §1's mapping table implies. I read their export
  lines and `fresh`/`launch` bodies only. `EC1-T6` is a theorem about the
  estate's `Handler.through`, **not** about Effect's `Layer.provide`.
- **`EC1-T7` is a definition that typechecks. No law is proved for it.** In
  particular I did not prove that `Layer.merge` agrees with handling each side
  separately.
- **I did not run any packet gate**, did not rerun the `COUNTEREXAMPLES.md`
  evidence commands, and did not touch `workshop/s1/` or `workshop/s2/`.
- **The `EC1-T*` IDs in §7 are local to this file** and carry no register
  authority.
