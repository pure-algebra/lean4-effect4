# 2026-10-06 brief for seat GAP: what a true gap with holes would give

Status: a brief (history, not authority). Base: the head that the dispatch message names. It
is a design study. It edits no tracked source, and it rules nothing.

## The owner's words

2026-10-06, by voice (decisions row 281, point 4). "I do want a deep exploration of what
adding a true type gap with holes would give. … it might be the key last gap of the language
system and of the type system that will make composition and agent-first design principles
truly powerful and expressive." And then: "be creative and exploratory here … you should be
reading these actual papers to get the actual calculus terms and proof terms so that you're
not guessing, and so that we'll be able to surface connections that we otherwise might not
even know that we have. … I'm wondering what we can get for free from the algebra, based on
the fact that we have this very careful initial algebra approach to our typing and
representation."

So the study has two duties. **Read the papers themselves**, and take each term of a
calculus and each theorem from its page. **Ask of each piece what our algebra already gives**,
before you propose anything new.

## Read first

1. `AGENTS.md`, in full. Its vocabulary section is the estate's algebra in short: free
   object, algebra and fold, agreement of folds, exact embedding, located refusal, foreign
   transformation, the seven judgments.
2. `docs/research/2026-10-06-type-slicing-plan.md`: the coordinator's plan. Its section 4.3
   names three candidates. You study candidate G, with N and A as its neighbours.
3. The papers, from `vendor/papers/program-graphs/`, each **in full** where it is marked:
   - "Bidirectional Type Slicing" (in full): precision, consistency, the gap, context typing,
     marking, the lattice.
   - "Hazelnut" (in full): typed holes, the cursor, edit actions, its sensibility theorems.
   - "A Type and Scope Safe Universe of Syntaxes with Binding" (in full): what one
     description of a syntax gives generically, and how its proofs are shared.
   - "The Zipper" (in full): one-hole contexts.
   - "Combinators for Bi-Directional Tree Transformations": the laws of a view with its
     update, where a focus or a slice is a view.
   - "Interaction Trees": a program whose events are not yet interpreted, for the reading of
     a hole at run time.
   A paper that is not under `vendor/papers/` is not read. The coordinator has asked the
   owner for seven more (the marking calculus, live typed holes, the gradual guarantee,
   gradual typing with unions and subtyping, abstracting gradual typing, the derivative of a
   type, the survey of bidirectional typing). If they arrive, the coordinator sends their
   paths. Until then name such a work without a locator, mark it "not read", and say which
   of your statements would need it.
4. Our algebra: `src/Effect4/Program/Fold.lean` (`TyAlgebra`, `TermAlgebra`, `EffAlgebra`,
   `hom_eq_cata_eff`), `src/Effect4/Program/LayerView.lean` (`cataFam`),
   `src/Effect4/Program/FoldOf.lean` (the command `fold_of`),
   `src/Effect4/Program/Binders.lean` and `src/Effect4/Program/Scoped.lean`,
   `src/Effect4/Laws/Program/Signature.lean` (`EffAlgebra.AgreeOn`, `cata_eff_congr_on`),
   `src/Effect4/Program/TyFoldExtras.lean` (`TyAlgebra.Commutes`),
   `docs/core/traversal-census.md` and `docs/core/system-map.md` (the sorts and the arrow
   kinds).
5. Our checker and types: `src/Effect4/Program/Checker.lean`,
   `src/Effect4/Program/Typing/Rules.lean`, `src/Effect4/Program/TyCore.lean`,
   `src/Effect4/Program/Ty.lean` (`sub`, `join`, `normalize`, `members`),
   `src/Effect4/Program/Record.lean`, `src/Effect4/Program/Node.lean` and `Refs.lean`
   (addresses, `replaceAt`).
6. What the tree already says of holes: `docs/research/2026-09-07-hazel-design-notes.md` and
   `docs/research/2026-09-08-hazel-external-row.md`. Say what of them still stands.
7. The host boundary and the frame: `docs/core/host-boundary.md`, and R1, R2, R5 and R6 in
   `docs/core/system-map.md`.

## Six readings to test

The coordinator gave the owner these six on 2026-10-06, each as a reading and no result.
**Test each one against the tree and against the papers. Confirm it, correct it or refute
it, with the declaration or the page that decides.** Then go past them: the owner asked for
connections that we do not know we have.

1. **Holes are the free construction over the same signature.** A program with holes is a
   term of the same signature with one more leaf. Each fold extends to it once a hole has a
   meaning in the carrier. On a program with no hole the extended fold is the old one, by
   the uniqueness of folds. Is conservativity then a corollary of `hom_eq_cata_eff`?
2. **Graduality is a monotone algebra.** Where each operation of the checker's algebra is
   monotone in an information order and a hole means its least element, the fold is
   monotone. Is there one generic theorem, the ordered form of agreement of folds, with one
   lemma for each constructor? Which constructors of our checker fail the lemma today?
3. **The focus is the derivative of the signature.** One-hole contexts are derived from a
   signature. The environment that a child inherits is written in each arm of the checker.
   Can context typing be generated from the checker, with the paper's composition law as
   the statement that the checker is a fold?
4. **Marking is the same algebra with errors as data.** The checker threads a failure. Run
   the same algebra where a failure is recorded, and the result is a checker that reports
   every refusal. Is its erasure law a fusion law?
5. **We have typed holes in two places already.** An effect hole is an operation with a
   declared row and no implementation; filling it is provision. A term hole is a foreign
   transformation: a name with a type signature and no meaning. What is then missing: the
   gap type for a place with no expected type, the monotonicity theorem, and the tooling?
6. **Running to a hole is a frontier.** A hole met at run time names what it awaits and at
   what type, which is the host boundary's shape. Does reply admission (R6) already state
   the law of filling it?

## What the study must answer

**Part 1. The gap in our type language.** Our types have subtyping, canonical unions,
literals, records with optional keys, tuples, nominal references, row templates and
invariant cells. The paper has none of these.
- Define precision and consistent subtyping for `Ty`. Derive each lifted operation (`join`,
  `normalize`, `fieldType`, `setType`, `Decision.arms`, `fiberTy`, a scheme's application)
  by one recipe, and say the recipe.
- Build a small executable model in scratch: a fragment of `Ty` with the gap. Test each
  candidate law by exhaustive enumeration at a small depth before you state it. A law with
  a counterexample is a finding: keep the counterexample.
- Say what a canonical form is with a gap. Is `gap | T` the gap? What does `normalize` owe?
- State downwards static graduality for our checker with a gap, in the form that Lean would
  take, and the shape of its proof.

**Part 2. Holes in the syntax.** Which sorts get a hole: `Term`, `Eff`, a cause, a
statement, an action, a layer? Is a hole a new constructor, or a use of what the language
has (reading 5)? What does each of the seven judgments say of a hole and of a gap? What do
R2's clauses C1 to C8 ask of an append? Count the cost by reading: each generated algebra,
fold, wire tag, mirror, reader and printer that an append touches (`docs/GENERATED.md`).

**Part 3. A hole at run time.** Three candidates: a program with a hole does not run; a
hole is a frontier with a typed answer; a hole is an operation that a layer provides. Say
what typed state (`reachable_typed`) needs for each, and what a gap in a running program's
type would mean. Hazelnut and the two notes of item 6 are the start.

**Part 4. What it gives.** Concrete stories, each with a program of ours before and after:
authoring a skeleton first; asking what can stand at a place; filling a hole with a law
that the whole stays admitted; folding to holes for a slice with cells; every refusal with
its repair place; running to a hole; a program with holes as a template that composes.
Compare a hole with a required service: both are a typed dependency that is supplied
later. Say what an MCP tool's operations would be, each with the law behind it.

**Part 5. The plan and the limits.** The stages from the least change to the most, each
with its obligations placed (concept, proposed claim, reach, what it does not establish,
consumer), the relation to candidates A and N, what stays unknown, and the questions that
only the owner can answer. Give a recommendation.

## The rules

- You edit no tracked source. Scratch files live in the scratch folder of the dispatch. You
  commit only notes and filed texts under `docs/research/`, each with `git add -f`.
- A statement about the tree that you compiled in scratch against the tree's modules is
  marked "compiled in scratch". Every other Lean text is marked "not compiled".
- A statement about a paper carries its page. A statement from memory is marked so, and it
  is not a premise of a recommendation.
- No install and no download. The shell's rules are in the dispatch message.
- Seat CENSUS measures the checker's graduality in parallel
  (`docs/research/2026-10-05-claude-lead/briefs/seat-census-brief.md`). Read its receipt if
  it exists when you need a number. Do not wait for it.

## The study

`docs/research/2026-10-06-seat-GAP-study.md`, with its scratch models filed beside it as
text. Open with the one thing that the owner should know. Then the six readings, each with
its verdict. Then the five parts. End with the obligations as a table, the connections that
you found and nobody asked for, and the open questions. Send one short message at each of
these points: after the papers, with what surprised you; after the model of part 1, with its
counterexamples; at the hand-back. Your last message gives the head, the study's path and
its first item.
