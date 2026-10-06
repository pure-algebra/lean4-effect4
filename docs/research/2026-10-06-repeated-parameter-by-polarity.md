# 2026-10-06 a type parameter at two places: the rule by polarity

Status: a research note (history, not authority), written by the coordinator under decisions
row 292, point 4. It is a design input for stage 0b of the plan of the study of a gap with
holes. It rules nothing, and no statement below is compiled.

## Question

An operation's template binds a type parameter at its first occurrence. So `getOrElse(o, d)`,
`ite(c, a, b)` and a list append refuse two arguments whose types have no order between them,
and the verdict depends on the order of the arguments. What is the right rule, and what does
it give beyond the repair?

## What was read or run

- **Read**: Dolan and Mycroft, "Polymorphism, Subtyping, and Type Inference in MLsub", POPL
  2017, in the vendored copy (`vendor/papers/gradual-holes/README.md`). Pages 1, 2, 6 and 8 of
  the PDF were read. The paper was not read in full: its sections 2, 5 and 6 are not used here.
- **Read**: seat GAP's study, sections 5.5 and 9.6 (b)
  (`docs/research/2026-10-06-seat-GAP-study.md`), and seat CENSUS's receipt, section 6.3
  (`docs/research/2026-10-06-seat-CENSUS-receipt.md`).
- **Run**: the tsgo probe of `docs/research/2026-10-06-uniform-eliminators-landing-probe.md`.
  Its forms `getOrElse(o, "d")`, `ite(c, 1, "a")` and `append(l1, l2)` are refused by tsgo 7
  with the prelude's one parameter, and `cons("a", l1)` is accepted with its two.

## Findings

### 1. The paper's example is ours (read, page 1)

The paper opens with `select p v d = if (p v) then v else d`. ML gives it one parameter for the
value, the default and the result. The paper calls that scheme strange: it demands that the
default be acceptable to the predicate, and the program never passes the default to the
predicate. The paper's own scheme has two parameters and a join in the result:
`(α → bool) → α → β → (α ⊔ β)`. Our `getOrElse` and `ite` have the first shape. rc.112's own
`Option.getOrElse` has the second (the study, 9.6 (b)).

### 2. The principle: inputs and outputs are kept apart (read, pages 1, 2 and 6)

- A subtyping constraint follows the direction of data flow, from a source to a destination. A
  type parameter of a scheme is an edge of that flow, from the inputs to the outputs.
- A join arises only where a type describes an output, and a meet only where it describes an
  input (section 3.2, "Polar Types", page 6). The paper's positive and negative types are that
  restriction as a syntax.
- Every expression that has any typing scheme has a principal one in that restricted form (the
  same page). So the restriction loses nothing for inference.

### 3. The algorithm: bounds in place of equations (read, page 8)

Unification solves equations. Biunification solves constraints of one form, an output type
below an input type (Figure 7, page 8). A parameter gets its lower bounds and its upper bounds
apart: a positive occurrence takes the join of the lower bounds, and a negative occurrence
takes the meet of the upper bounds (section 4.4, the same page).

### 4. What it is in our type language (the coordinator's reading; not compiled)

Our templates are simpler than the paper's schemes. `Ty` has no function type. A parameter
occurs in a request at covariant places (`option A`, `list A`, a pair's part) and at invariant
places (a cell, a deferred, a map's key). So the rule needs joins and no meet:

1. **A parameter with an invariant occurrence is fixed by it.** Each invariant occurrence gives
   the same type, up to the normal form. Each covariant candidate is below it.
2. **A parameter with covariant occurrences only is the join of its candidates.** With no
   candidate it is `never`. The join always exists, so this case never refuses.
3. The instance is then checked as today: each argument is below the instantiated template.

The order of the arguments no longer matters. An admitted program keeps its type up to the
normal form: where the present rule succeeds with two candidates, one is above the other, and
the join is that one.

### 5. What it would give beyond the repair (hypotheses to test)

- **A completeness theorem without the anchored premise.** The claim `template-match-anchored`
  proves the match complete where each parameter first occurs as an invariant handle's
  argument. It claims nothing at a parameter first met covariantly
  (`docs/core/semantics.md`, section 2.6). With joins for the covariant case the hypothesis is
  the full statement: a request below some instance has a match, and the match is the least
  one. That is the paper's principality, for our templates.
- **Monotonicity at a template**: a join is monotone in each candidate. It is the template's
  share of the open claim `checker-monotone`.
- **One algorithm with the gap's rule at a cell.** The study's exact rule for a gap under an
  invariant constructor collects a lower and an upper bound from each member and asks each
  lower bound below each upper bound (its section 5.5). That is the same solving of bounds. If
  the two are one function, stage 0b and stage 6 share it.
- **The prelude's signature is generated by polarity.** The scheme keeps one parameter in Lean,
  with the join as its meaning. The generator of `harness/truth/prelude-atoms.gen.ts` writes
  one TypeScript parameter for each covariant occurrence and their union in the answer, which
  is the form that tsgo accepts for `cons` today. No scheme is written twice.

## Proposals (not rulings)

1. Stage 0b becomes "the match by bounds": one function in place of the first-occurrence
   binding and its `join` flag, with the rule of finding 4.
2. Probes before a brief, in scratch: the function on every template application of the two
   corpora, against the present match (equal on every admitted program; count the new
   admissions); tsgo on the generated signatures of `getOrElse`, `ite` and the list append.
3. Its statements, each placed before work: the match is sound; it is the least instance; it is
   complete with no anchored premise; it equals the present match where that one succeeds.
4. It stays out of this stage: a loop's cursor and a fold's accumulator with no stated type.
   Each is a fixed point of its body, which the paper solves with recursive types. A stated
   type or the gap serves them.

## What this does not establish

- Nothing is compiled, and no count exists for the new rule.
- The paper is about a language with functions and recursive types. Its theorems are not
  theorems of our type language: each transfer needs its own statement and proof.
- The reading that the gap's rule at a cell is the same function is a hypothesis.
- The prelude is a face of the target. Its change is reported to the owner before it lands
  (decisions row 288, point 6 b).
