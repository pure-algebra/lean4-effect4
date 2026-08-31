import Cas.Llm.Judge
import Cas.Llm.JudgeRate
import Cas.Llm.Rewriter

/-!
# CasLlm — the frozen completion call as a mathematical object

This is the published root of the `CasLlm` stratum. It sits beside
`CasValues` at the floor of the library and, like it, knows nothing
about a store: everything here is about ONE PINNED COMPLETION CALL,
read as a total function of its input, and about what may honestly be
proved of such a thing.

The stratum is organized by a split of KIND, and the split is the
design rather than a filing convenience.

**LLMs as FUNCTIONS** — `Rewriter`. A rewrite PRODUCES. Frozen, a
completion call is a plain `String → String` and nothing special, so
the mathematics is composition and only composition: a pipeline is a
monoid (`andThen`, with `Rewriter.id` as unit), schema-forced decoding
is the statement that every output lands in a constrained sublanguage
(`Into`, whose contract the LAST stage decides and whose staged
versions chain), and a canonicalizer is an `Idempotent` rewriter —
STATED, never assumed, because the estate's own canonicalizer turned
out to be an involution where an idempotent was required (CX-003).

**LLMs as DECISION POINTS** — `Judge` and `JudgeRate`. A verdict
SELECTS. `Judge` is an uninterpreted `String → Bool`, quantified over
exactly as the store quantifies over the hash `H`, and it carries the
judge-hypothesis lattice: acceptance carves a SUBALGEBRA out of a
named algebra, rejection propagates, and blame localizes so a label
can be bisected to the segment that fails — each conditional on a
NAMED rung. The practical shape is a `Panel`, a judgment as parallel
cheap calls frozen to one judge through its AGGREGATOR, and which
aggregator is chosen decides whether the rung survives: `Panel.all`
preserves compositionality, `Panel.any` demonstrably does not.
`JudgeRate` is the MEASUREMENT that keeps the hypotheses honest —
`defectCount` over an explicit finite fragment, a monoid hom into
`Nat` so a study grows by its suffix, with zero defects recovering the
exact law ON THE FRAGMENT and on nothing outside it.

## Why the split is load-bearing

The two kinds have different contracts, and fusing them would hang
production off a predicate's trust story.

A function's contract is its OUTPUT LANGUAGE. What a rewriter is worth
is settled by where its results land: `Into Q` is a property of the
output alone, it needs no hypothesis about the stages upstream, and it
composes down a pipeline mechanically.

A decision's contract is WHICH HYPOTHESES ABOUT IT HAVE BEEN MEASURED.
Nothing about a verdict is readable off the verdict. A judge enters a
proof as a premise, and the only honest statement about a particular
one is the rung a finite study on a named fragment has actually
reached — which is why every theorem here is conditional, every
conditional names its rung, and the fragment is carried in the
statement rather than quietly universalized.

## What belongs here

LLM-call abstractions that know NOTHING of the store: the frozen call
as a function or as a predicate, the algebra of composing calls, and
the arithmetic that measures a hypothesis about one. The test is
mechanical rather than a matter of taste — a module belongs here only
if it compiles with no `import Cas.*` outside `Cas.Llm`.

## What never belongs here

Anything that mentions the model. A judge OF store content, a panel
wired to sorts, a rewriter whose output language is a schema code: all
of that CONSUMES the abstractions defined here and therefore lives
above, in the `Cas` stratum. The naming function is a parameter
throughout precisely so that no front end's naming homomorphism has to
be imported to state a law about the judge that reads its output.

Publishability: this stratum stands alone. `lake build CasLlm` builds
these three modules and the front page that roots them, and nothing
else in the package — which is what "knows nothing of the store" has
to mean to be worth saying.

## Where the rest of it lives

The mathematics here is deliberately meaning-free. The operational
doctrine that surrounds it — the human as judge of record, the ban on
model-on-model loops, finite panels, the judge-pin schema, the
visibility rule and the blinding abstraction, the white-box NLP tier —
is written up in `.staging/frontend-trunk/JUDGE.md`, and the pinning
and visibility disciplines are ratified as decisions 36–38 in
`docs/SPECS.md` (36: the judge architecture; 37: anti-smuggling
estate-wide; 38: the lattice ranking these docstrings number against).
A real model enters gated work only as a pinned artifact under those
rulings; the uninterpreted function is what gets proved about.

`Judge` carries a debt marker at Level 3 of the ladder — LIMIT-STABLE
has no definition yet — so it stays a visible row in
`meta/out/debts.META.json` until one is written.

The declared strata order, and the rule that keeps it, are written at
the head of `library/cas/lakefile.toml`, where the boundaries are
actually declared.
-/
