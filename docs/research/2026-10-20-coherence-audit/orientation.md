# Orientation: the project's philosophy, pedagogy and inspirations

Written 2026-10-19 by the coordinator, before the coherence audit, from:
- the authorities: `docs/core/system-map.md`, `docs/core/semantics.md`, `ocaml/STANDARDS.md` and `AGENTS.md`;
- the dated record of the organizing principle, `docs/research/history/coherence-principle.md`;
- the coordinator's memory of the owner's steers;
- 184 of the owner's own messages from 2026-08-31 to 2026-10-19, read from the session transcripts.

Every reviewer reads this first. The audit judges the code against this, not against taste.

## 1. The one thing to know

The project has one organizing idea, and the owner has said it from the first week: "we live by the
algebra; it is our language". Each kind of thing has one free object, whose signature is data. Every
other form of it is a fold of that object, or an exact embedding into it. Every behaviour is
observed, and two behaviours are related only by a simulation on a named observation. Coherence is
the uniqueness of the fold. Bloat is what grows when a piece of code is not placed in this picture.
The audit therefore asks one question of every construct: where does it sit in the picture, and if
nowhere, which pattern did we misuse?

## 2. What the project is for

- **An agent-first language of algebraic effects, with a reified engine in Lean** (owner,
  2026-09-16). Programs are typed, first-order data: one canonical tree, stored by digest, folded
  over, printed and read back.
- **One machine, three faces.** Lean proves, OCaml runs it natively (made from LCNF), and TypeScript
  interoperates with Effect rc.112. "If you can't see why OCaml is important then you don't
  understand the project."
- **Semantics once, logic per entry, implementations once** (decisions row 381). The Lean model is
  Effect's semantics, checked once against rc.112. A bank entry's claim is its behaviour under that
  semantics. The implementations agree with the meaning by language-level theorems or by trust (row
  391), never per entry.
- **Tangible semantics for agents.** "It should be like speaking a language for the agents to use";
  "write the APIs that you would want to use". The semantics must be visible through the syntax: as
  a graph, a journal, a tape and a run (2026-10-08, 2026-10-09).
- **Hosts as data.** A foreign host is modeled as rows, a protocol and tapes. So an agent can map an
  outside system's semantics, in a verified way, while it authors (2026-10-17, interaction trees).
- **Working code with rigor, fast.** "This is not a research project... what we want is working code
  with high rigor" (2026-09-02). "No shortcuts", and also: end "this endless proof cycle"
  (2026-10-17).

## 3. The organizing principle

From the coherence principle (2026-09-17), carried into the system map §§4–6:

- **Two kinds of object.** A *free object for a signature given as data* (`Eff`, `Ty`, `Term`,
  `Val`, `Representation`, `List Command`, LCNF `Code`) is constructed. A *behaviour* (the machine,
  the reference, a run) is observed, never constructed.
- **Five kinds of arrow, each with one obligation.**

| Kind | Shape | Its one obligation |
| --- | --- | --- |
| K1 fold | out of a free object | be `cataFam alg` for a named algebra; uniqueness then equates any two arrows with the same algebra |
| K2 exact embedding | `write`, `read` | total on a domain; retraction; exactness modulo a named normaliser |
| K3 simulation | into a behaviour | a relation kept by every step and reflected in a named observation, on a named fragment |
| K4 located refusal | partial elaboration | every refusal names a place and a reason; refusal absent exactly when the judgment holds |
| K5 monoid action | a journal acting on a state | a homomorphism from the free monoid; replay, resumption and splitting at once |

- **Coherence is counted per sort.** The principle allows one free object per sort, any number of K2
  embeddings with all three laws, and folds, which are views, not representations. "Anything else is
  a leak."
- **Generation is a fixed point.** The power belongs in the tables (`binders.json`, the manifest,
  the template table, the builtin rows). The generator is a total function from tables to
  declarations with no semantics of its own. It may emit an algebra, never a traversal that is not
  one, and its inputs are data in the tree.
- **A new representation is admitted only by naming its signature and the kind of each of its
  arrows.** That sentence is in `AGENTS.md` because, as the principle says, "there is nowhere to go,
  and the vocabulary is what makes that usable".

## 4. The five constructions, and why the design is bounded

System map §10.1. The tree rests on five constructions:
1. types as a free object with a signature-generic order;
2. stored programs as first-order trees, with residual typing over a Kripke world;
3. the machine as a transition system whose invariant one lift rule carries;
4. handlers that meet their protocols by one adequacy theorem;
5. the claim as one route theorem over the boundary's exact embeddings.

Every refutation found in the formal pass was a clause written outside a construction. Each repair
moved the clause inside, and none changed a construction. So expansion is bounded: a clause can be
missing in only a few enumerated places. The same reasoning drives this audit. Code that sits
outside the constructions and the arrow kinds is where bloat and defects grow.

## 5. The working philosophy, in the owner's words

| Steer | The owner, dated |
| --- | --- |
| The algebra guides | "a rock solid beautiful functional programming... guided by the algebra to simplify, clarify and master complexity and abstraction" (2026-09-04); "the algebra we live by, the algebra it is our language" (2026-09-10) |
| One level higher | "whatever your first instinct for implementation is, go one level higher in Lean, closer to the algebra"; the fold API "should land any new Eff type without any work or needing to update multiple places" (2026-09-10) |
| Coherence, not consumers | "lack of consumer isn't really a metric... it should be coherence of the overall algebra... based on the universal initial algebra"; convert by metaprogram, slot in, then delete (2026-09-18). On 2026-10-17 the owner ruled that the no-consumer rule does not apply to code we are building toward, such as the OCaml store before its consumers arrive |
| The model indicates the minimum | "keep pushing and using the math structure to consolidate code simply by reasoning about what the math model indicates the minimal representations should be" (2026-10-11) |
| Consolidation is the signal | "we know we're on the right track when we're leading to consolidation" (2026-10-13) |
| General over casework | a match "on a bunch of things that could grow arbitrarily" wants the general form and its theory (2026-10-02) |
| Tables as data | "the robust fix... having the table be data... a proper compiler standard way" (2026-10-05) |
| Reuse, deep modules | "a problem with us remaking given the scale of the codebase, so let's be clean and deliberate" (2026-10-15); deep modules "in the Matt Pocock sense" (2026-10-17) |
| Cut what is superseded | "you don't need to preserve stuff for the sake of preserving it... this is all greenfield" (2026-10-02) |
| Tried and true patterns | "we were trying to force patterns that don't fit with Lean... use tried and true patterns, functional abstractions that give us a tight implementation" (2026-10-17) |
| Effect as the map | Effect's choice of modules is "close to ideal... the concepts you think about in terms of general computational semantics"; reify the runtime, compose the rest (2026-10-08) |
| Justified divergence | match Effect's semantics, but when verification reveals a law, "the divergence is often justified" (2026-10-05) |
| Build, don't circle | "I want to actually start building stuff with this and not be doing these endless proof graphs" (2026-10-14); the lowering is trusted (row 391) |
| Respect | "a clean, deep, performant, idiomatic set of abstractions based on deep respect for good code and math, but also respect for the deep research and lit reviews that led here" (2026-10-18) |
| Bloat is mis-modeling | "if there's bloat, it means that we didn't model our system properly... there's a case or a pattern that we're misusing"; "the elegance comes from minimality with regards to desired behavior" (2026-10-19) |
| Not over-engineering | "we don't want to introduce added complexity, only simplification, coherence, clarity, uniformity and expressiveness based on mathematical soundness" (2026-10-06) |

## 6. The estate's discipline

`ocaml/STANDARDS.md`, in one line each:
1. libraries first, drivers thin, no `Obj` or `Marshal`;
2. one component per file, with a property list at its head;
3. generated is generated, and the OCaml made from LCNF is the machine, while hand OCaml is host code
   or a carrier that LCNF code replaces;
4. every number behind a command;
5. interfaces once and small, with checked values abstract;
6. a refusal is a value, never a swallowed exception or a status that reads as success;
7. numbers exact, comparison by type;
8. mutation behind pure interfaces;
9. outside libraries by contract, Jane Street's first.

The direction is "anything not made directly from LCNF should be ditched" (2026-09-17). The
coordinator's rule for getting there is to never break `make check-ocaml` on the way.

## 7. The pedagogy: how the project explains and decides

- **One meaning per word.** The dictionary (`docs/core/controlled-english.md` §3) gives each word
  its tree anchor, its literature term and the words not to use. A second word for one fact is
  drift in prose, as a second type is drift in code.
- **Evidence words.** Proved, tested, reading and assumed are kept apart. A finite probe is reported
  as one.
- **Placement before work.** An obligation names its concept, its claim, its reach, what it does
  not establish, and what it unlocks. There are "no proofs to nowhere".
- **Show the abstraction and the code.** The owner asks to see the existing abstraction, the
  current code and the target code, in plain words, with concrete examples and diagrams. A
  recommendation comes after a survey of the math and the existing patterns. The owner: "please
  don't offer recommendations when you haven't actually surveyed or engaged with the math".
- **Decide what is evident.** Ask the owner only about meaning, supported domain or
  representation. Decide the rest with evidence, and record it.

## 8. The inspirations

| Area | Sources, and what each gives us |
| --- | --- |
| Algebra and folds | Goguen, Thatcher, Wagner and Wright: initial algebra semantics. Meijer, Fokkinga and Paterson: the fold laws. Hutton: the universality of fold. Wadler's views with Gill, Launchbury and Peyton Jones's `build`. Benke, Dybjer and Jansson, and Chapman, Dagand, McBride and Morris: signatures as data. Abbott, Altenkirch and Ghani: containers. |
| Binding and syntax | Fiore, Plotkin and Turi, and Allais, Atkey, Chapman, McBride and McKinna: one binding description, one generic traversal. Rendel and Ostermann: invertible syntax. Pickering, Gibbons and Wu: profunctor optics. Foster and others: lenses. |
| Effects | Plotkin and Power: free algebras against theories with equations. Plotkin and Pretnar: handlers. Interaction trees and their Rocq library. Effect rc.112 as the operational source. |
| Behaviour | Rutten and Jacobs: coalgebra. Lynch and Vaandrager: simulation. TAPL and PLF: the safety method. Ahmed: worlds. Kripke monotonicity. |
| Compilers | Leroy: CompCert. Pnueli, Siegel and Singerman: translation validation. Yang, Chen, Eide and Regehr: Csmith. Bahr and Hutton: calculated compilers. Taha and Sheard: staging. MLIR's ODS and Cranelift's ISLE: instruction tables as data. OCaml's compiler-libs. |
| Editing | Omar and others: Hazelnut and total marking. Carroll, Madhavapeddy and Omar: bidirectional type slicing. |
| Engineering | Jane Street's libraries, derivers, `Stable` modules and shape digests. dune and opam. Matt Pocock's deep modules. |

## 9. How bloat grew here: the failure modes on record

Each mode is a misuse of the picture in §3:
- **A hand mirror beside a generated face.** Examples: hand JSON twins of Lean codecs, and the list
  twins of the engine. The generated face was not reached, so a copy grew.
- **A parallel type for one fact.** Example: `verify_error` beside the generated `E4_admission`.
  The one refusal type was not reached.
- **A second implementation kept "as history".** Examples: `E4_cas.verify` beside `checked_image`,
  and two logs that each promise an all-or-none append.
- **Casework where a fold or a table exists.** Examples: twenty-arm transports, and the record
  header parsed twice.
- **Process in place of abstraction.** The 2026-10-18 verdict: "the absolute bloat and cruft of all
  the gates, bloated AGENTS.md, complete lack of focus on the core abstractions desired".
- **Patches over modeling.** Fixing each finding where it surfaced, instead of the misused pattern
  that allowed it (2026-10-19).
- **Proofs to nowhere, and claims too strong.** Lemmas with no consumer on the route, and review
  rounds that added premises without building.
- **Consumer-count reasoning.** Deleting by "no caller" where the question is coherence. Keeping by
  "someone cites it" where the rule is one owner.

## 10. The questions a reviewer asks of any construct

1. Which sort does it carry, and is that sort's one free object the thing it uses?
2. Which arrow kind is it (K1 to K5), and does it meet that kind's one obligation?
3. Which of the five constructions does it belong to, or which boundary does it serve?
4. Who owns the fact it encodes: Lean, a table, the generator, or this code? If not this code, why
   is it written here?
5. Is it the minimum for the behaviour the semantics asks for? What would delete it, and what
   observation would that change?
6. Is its failure a located refusal of the right judgment, in the one refusal type?
7. Would a top compiler or language designer recognise the pattern, and would Effect's module map
   name it?
8. Does the fix move it into the picture, or only patch it where it stands? A fix that adds a
   construct must remove more than it adds.
