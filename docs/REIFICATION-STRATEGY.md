> Copied from mepuka/lean4-WHATWG-streams at commit ed65fe0 on 2026-09-02 for the Effect4 side of the RS-D1 discussion. The streams repository holds the living copy; refine there or here, but say which is canonical when you do.

# Stratified reification: web standards as an effects algebra

Status: **DRAFT for refinement, 2026-09-02.** Every `RS-*` item below is a
PROPOSED design ruling or an open question. Nothing here is proved, and no
claim in this document is a Model Claim; it organizes what the estate would
prove. It spans three repositories: lean4-effect4 (the algebra), this
repository (the first stateful standard), and the future standard
libraries the survey in `docs/research/2026-09-01-web-reification-targets-survey.md`
ranks.

Author: coordinator, from the operator's premise ("make them flow effects
like Effect4; maximum algebraic composability") and from first-hand reads of
lean4-effect4 `docs/DESIGN-BASIS.md` and `Effect4/Algebra/*` at commit
`e9075e192bb3065e3900ccabe7c0c2a6df1ddffc`, this repository's design basis,
and the R0 documents.

## 0. The premise, sharpened

Reifying a standard as an effect means: a closed alphabet of operations
indexed by their answer types, one canonical handler transcribed from the
standard's own algorithms, laws stated at the free-program face, a
first-order checked flow for identity and lowering, a relational semantics
over explicit decisions, and generated host code checked at exact pins. That
is Effect4's shape, and the premise is that every web standard should take
it.

The refinement this document argues for: **not everything is an effect, and
composability comes from placing each standard in the right stratum of the
same algebra.** Forcing a pure parser into a signature gains nothing and
costs the equational reasoning that makes it useful. Forcing a stateful
protocol into pure functions hides the decisions that the specification
makes observable. The algebra has three strata already; the standards sort
into them.

## 1. The three strata

### RS-1 — Stratum V: the value universe (Infra, Web IDL, Encoding's scalar layer)

The WHATWG Infra Standard defines byte sequences, code points, scalar-value
strings, lists, ordered maps, structs, and JSON values. Web IDL defines the
conversions between host values and those types and the exceptions they
raise. Every other standard's operations take and return these.

In Effect4 terms this stratum is `ValueTy` / `Value` and the Schema layer,
not a signature. Its deliverables are carriers, codecs, canonical forms, and
the laws connecting decoded, encoded, and representation views. Its
theorems are round trips, injectivity of encodings on canonical forms, and
normalization idempotence.

Consequence: Infra is not a target with a standalone deliverable; it is the
universe the first stateful target is indexed by. The survey's ranking says
the same from the other direction.

### RS-2 — Stratum A: pure atoms (URL, Base64, Structured Fields, JSON grammar, Data URLs, MIME types, stateless Encoding)

These standards are total functions on Stratum V with no observable effect:
parse, serialize, normalize, classify. Their internal state machines (the
URL parser's state) are implementation detail, not observation.

In Effect4 terms each is a `PureAtom`: a named total function with a Lean
model and a separately pinned host body. Their laws are equational:

- `serialize (parse s) = normal s` and `parse (serialize u) = u` on the
  canonical domain;
- idempotence of normalization; injectivity of serialization on canonical
  records;
- failure exactly on the inputs the standard says fail, as a decidable
  predicate with the standard's own test corpus as witnesses.

Atoms compose by function composition and cross by homomorphism theorems
(a URL's origin is a function of its record; a Structured Field item's
serialization is a function of its bare item). They are the fastest route
to compiled TypeScript because Effect4's generated-code path already
produces and checks Schema documents; an atom is a Schema-typed function.

### RS-3 — Stratum S: signatures (Streams, streaming decoders, AbortSignal, the promise job queue, Fetch, WebSocket framing, the event loop)

These standards define operations over named-slot state whose behaviour
depends on decisions the host or the consumer makes: what a pull returns,
when a promise settles, whether a signal fires, what the network answers.

In Effect4 terms each is a `Signature` with `Op` indexed by `Answer`, one
canonical `Handler` transcribed from the standard's algorithms into a state
carrier over Stratum V, a foreign-boundary profile for every host-supplied
body, and a relational semantics under a named observation mask. Programs
over the signature are `Program S A` at the proof face and checked `Flow` at
the identity face.

The algebraic test that decides whether an operation belongs in the
signature is Plotkin and Power's: it is algebraic when it commutes with
sequencing. `enqueue`, `read`, `write`, `close`, `error`, `desiredSize`
pass. `pipeTo` with its shutdown clauses, an abort scope, a promise
reaction, and any operation that takes a continuation do not; they are
scoped or higher-order shapes and are handled by Effect4's rule that scoped
children are first-order `BlockId` data, never stored computations.

## 2. The composition principle

### RS-4 — The specification dependency graph is a handler tower

The standards cite each other in a fixed direction: Fetch uses Streams, URL,
Encoding, and the job queue; Streams uses Infra values and the job queue;
the job queue uses the configuration. Each edge becomes a handler:

```text
Handler Fetch     (Program (Streams ⊕ URL ⊕ Encoding ⊕ Jobs))
Handler Streams   (StateT StreamsHeap (Program Jobs))
Handler Jobs      (Configuration)
```

Effect4 already supplies the operations for this: `Handler.sum` for
disjoint signatures and `Handler.through` for towers, with composition
stated as a category across signatures and a monoid only on endomorphisms.
A standard is then one signature, one canonical handler, its laws, and its
boundary profile. Adding a standard adds a summand and a handler; it does
not reopen the ones below it.

Hyland, Plotkin, and Power's sum-versus-tensor distinction says when a plain
sum is enough. Two atoms always commute. Streams and Jobs do not commute:
enqueue then settle differs from settle then enqueue, and that order is
precisely what mask M2 observes. So Streams and Jobs combine by sum with
explicit sequencing in the handler, never by an assumed tensor. Every pair
of signatures that meet in a tower gets a ruled answer to that question
before their handlers are composed.

### RS-5 — Two realizers per signature

For each signature there are two handlers of interest:

- the **generated realizer**, lowered from the checked Flow through
  Effect4's TypeScript target, correct with respect to the Lean model by
  the lowering theorems; and
- the **host realizer**, the browser's, Node's, or Bun's native
  implementation, admitted as a handler for the same signature only by
  conformance against the standard's corpus under a named mask, and refused
  on divergence as a host-profile row.

Because both are handlers for one signature, a program's theorems are
proved once and hold under either. Nobody reimplements `new URL()` in
TypeScript unless they want to; the host's is pinned as a realizer with the
theorems intact. This is where the compatibility payoff lives, and it is
what "maximum algebraic composability" buys in practice: substitution of
realizers under proved laws.

### RS-6 — Requirement-style specifications are EffHOL, not handlers

Where a standard states requirements rather than an algorithm (Streams'
piping, parts of Fetch's shutdown), the requirement is a specification φ
over runs and the standard's algorithm is one realizer. The theorem is
realizability under a mask, in EffHOL's organization: the angle modality
as `wlp`, totality separately. This stratum does not add handlers; it adds
judgments over programs in Stratum S.

## 3. Laws per stratum

| Stratum | Law shapes | Proof technique |
| --- | --- | --- |
| V | codec round trips, canonical-form injectivity, normalization idempotence | structural induction on carriers; `Nat.eq_of_testBit_eq`-style bit reasoning for encodings |
| A | `serialize ∘ parse`, `parse ∘ serialize`, failure exactly on the standard's failure set, homomorphisms between records | induction on the parser's state machine as a total function; corpus vectors as executable evidence |
| S | monad laws inherited from `Program`; handler laws (`interpret_bind`, operation agreement); combinator laws (fusion of maps, associativity of `pipeThrough`, tee's split law) under a mask; finalization exactly-once; backpressure bounds | handler fusion in the sense of Yang and Wu: state a combinator as a handler and prove its law by fold fusion rather than by ad hoc induction over runs |
| Tower | layered refinement: a program over the upper signature refines its image over the lower ones | the layered-interpreter method of Yoon, Zakowski, and Zdancewic, adapted from interaction trees to Effect4's relational runs |

## 4. Where the survey's targets land

| Target | Stratum | Notes |
| --- | --- | --- |
| Infra | V | the universe; no standalone deliverable |
| Web IDL (binding subset) | V | conversions and exception kinds; host-only enforcement recorded as refusals |
| Encoding, UTF-8 core | V for the scalar codec; S for `TextDecoder` with `stream: true` | the streaming decoder is a small signature over the codec atom |
| URL | A | the flagship atom: parser state machine as a total function, `urltestdata.json` as witnesses |
| Base64, Data URLs, MIME types | A | small atoms with in-document vectors |
| Structured Field Values | A | the one IETF spec whose algorithms bind |
| JSON grammar | A | the RFC leaves disagreements to the implementation-defined cases; those become refusals |
| Promise jobs and event loop | S, foundational | the one signature every settlement-order theorem needs; FIFO, deterministic, so a job queue is state and not a decision |
| Streams | S | this repository; the combinator prize |
| AbortSignal | S, small | the interruption boundary already treated as foreign; dependent signals are real algebra |
| Fetch | S, integrator | the top of the tower; opened last |
| WebSocket framing | S | a framing state machine over Stratum V bytes |
| Transferable streams | refused | MessagePort protocol outside the model |

## 5. Lowering

Stratum A lowers to TypeScript functions over Schema-typed values, or to a
pinned host body under RS-5; both are checked by the compiler and the
language service at exact pins, as Effect4 already does for Schema
documents. Stratum S lowers through the checked Flow to Effect v4
`Stream`/`Channel`/`Sink` programs, or to the host's native WHATWG Streams
under RS-5 with a generated adapter. Stratum V lowers as Schema. The order
in which lowering can be trusted follows Effect4's own ledger: Schema
generation is closed, program lowering is `required-open`, so Stratum A
ships compiled artifacts before Stratum S does.

## 6. Decisions this design forces

| Id | Question | Proposed ruling |
| --- | --- | --- |
| RS-D1 | Where does the algebra live? | Extract `Effect4.Algebra` (Signature, Program, Handler, Sum, Universal, the proved laws) into a standalone, zero-dependency, pinned Lake package. Every standard library requires it. Neither lean4-effect4 nor any standard library depends on the other. |
| RS-D2 | Does this repository take that dependency now? | Not before P3 opens. The census and the SHA-256 lane need nothing from the algebra. The streams calculus at P3 is the first consumer, and the dependency policy in `PLAN.md` applies: exact-pin acceptance probe, license, transitive cost. |
| RS-D3 | Which stratum first? | Stratum V and the UTF-8 codec atom, then the URL atom, then this repository's signature on the job-queue signature. This matches the survey's order and lets compiled artifacts ship from Stratum A while Stratum S waits on lowering. |
| RS-D4 | Sum or tensor per meeting pair | Ruled per pair before handlers compose; default is sum with explicit sequencing. |
| RS-D5 | Masks | M1 and M2 from this repository become estate-wide; a signature may add masks but every theorem names one. |
| RS-D6 | Host realizer admission | Conformance under a named mask against the standard's pinned corpus; a divergence is a host-profile refusal row, never a model change. |

## 7. Open questions

| Id | Question |
| --- | --- |
| RS-Q1 | Is the job queue a signature or part of the configuration? Effect4 keeps scheduler policy in the initial configuration; the FIFO job queue may belong there too, with `Jobs` as an empty signature. Decide once Streams' handler is written against it. |
| RS-Q2 | What is the identity carrier for stream, reader, and controller objects across the tower? A heap of named-slot records keyed by first-order ids is the working assumption; locking and aliasing theorems depend on it. |
| RS-Q3 | Can Web IDL's exception kinds be Stratum V data, or do they need a signature (a `throw` operation)? |
| RS-Q4 | Do the atoms' failure predicates stay decidable through the tower, so that a Fetch program's static error row can be synthesized the way Effect4 synthesizes `E`? |
| RS-Q5 | Which layered-refinement statement transfers from interaction trees to Effect4's relational runs without adopting the tree carrier? |

## 8. Literature ledger

Roles only; these rows are from memory (INFERRED) and each receives a
fetched URL, a digest, and a provenance row before any theorem or contract
cites it.

| Source | Role in this design |
| --- | --- |
| Plotkin and Power, *Algebraic Operations and Generic Effects* (2003); *Notions of Computation Determine Monads* (2002) | the algebraicity test that sorts operations into Stratum S signatures versus scoped shapes |
| Hyland, Plotkin, Power, *Combining Effects: Sum and Tensor* (2006) | RS-D4: when two standards' signatures combine by sum and when a combined handler is owed |
| Plotkin and Pretnar, *Handling Algebraic Effects* (2013), arXiv:1312.1399; Bauer and Pretnar, *Programming with Algebraic Effects and Handlers* (2012), arXiv:1203.1539 | handlers as models; freeness; already Effect4's basis |
| Kiselyov and Ishii, *Freer Monads, More Extensible Effects* (2015) | the `vis op k` operational representation and open-union alphabet growth |
| Yang and Wu, *Reasoning about Effect Interaction by Fusion* (2021) | combinator laws by handler fusion, section 3 |
| Yoon, Zakowski, Zdancewic, *Formal Reasoning about Layered Monadic Interpreters* (2022); Xia et al., *Interaction Trees* (2019), arXiv:1906.00046; Chappe et al., *Choice Trees* (2022), arXiv:2211.06863 | handler towers as layered interpreters with refinement across layers; visible choice |
| Wu, Schrijvers, Hinze, *Effect Handlers in Scope* (2014); Piróg, Schrijvers, Wu, Jaskelioff, *Syntax and Semantics for Operations with Scopes* (2018); van den Berg and Schrijvers, arXiv:2302.01415; Bosman et al., arXiv:2304.09697 | the operations that fail the algebraic test: scopes, aborts, continuations |
| Xie and Leijen, *Generalized Evidence Passing for Effect Handlers* (2021); Leijen, *Type Directed Compilation of Row-Typed Algebraic Effects* (2017) | section 5: how handlers lower to first-order host code |
| Gibbons and Hinze, *Just do it: Simple Monadic Equational Reasoning* (2011) | the law catalog per signature |
| Cohen, Grunfeld, Kirst, Miquey, EffHOL (2025), arXiv:2506.09458 | RS-6: requirement-style specifications and realizability |
| Frumin, Timany, Birkedal, *Modular Denotational Semantics for Effects with Guarded Interaction Trees* (2023), arXiv:2307.08514 | modular handler reasoning; a comparison model, not a carrier |

## 9. What this document does not claim

No stratum assignment is a theorem. No law in section 3 is proved. The
handler tower is a design for how the estate's existing operations would
be used, not a statement that any standard has been composed. The two
realizers of RS-5 exist for no signature yet. Effect4's relational semantics
and program lowering remain `required-open` in its own ledger, and every
Stratum S deliverable inherits those open edges until they close.
