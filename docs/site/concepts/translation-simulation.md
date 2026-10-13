# Translation and simulation metatheory

This page explains translation and simulation metatheory in Effect4. It covers how operational execution relates to denotational meaning through equal-observation theorems over restricted fragments.

## The runtime concept {#runtime-concept}

Effect programs execute in JavaScript or TypeScript environments, but Effect4 also provides alternative execution targets like an OCaml engine.

Effect4 formalizes multiple execution faces: denotational semantics (`meaning`), a term reference machine, and the defunctionalized frame machine (`RunMachine`).

Simulation metatheory establishes that these different execution engines produce equal observable outcomes when evaluated on matching programs.

## Literature foundations {#literature}

Compiler correctness and semantic preservation relative to source behaviors adapt the formal methods of Leroy (2009). Transformations must keep source behavior under observable criteria.

Forward simulations and trace inclusions adapt Lynch and Vaandrager (1995). Simulation relations relate small-step transition systems step by step.

Deterministic behavior functions on decision tapes adapt the coalgebraic Moore machine models of Jacobs (2012).

## What Effect4 keeps and what it cuts {#adaptations-and-cuts}

Effect4 establishes equivalence strictly through equal-observation theorems over explicitly named program fragments:
- On the `Straight` fragment without loops or host calls, `run_eq_meaning` states that the frame machine's run matches the denotational meaning.
- On the `Looped` fragment, `loopAgreement` relates iterative execution steps to loop denotations.
- At the empty row table, `run_eq_ref` relates the frame machine to the term reference machine.

The milestone theorem `m7_of_ledger` (`src/Effect4/Laws/Program/Typed/Assembly.lean`) states that loading (M5) and preservation (M6) imply M7.

Effect4 cuts universal equivalence claims without a stated observation across unconstrained programs. M7 is restricted to `M7Fragment`: an admitted source, an empty row table, closed requirement rows, and an answer-free tape.

Non-empty row table agreement is separated into R6. Lowering through LCNF to OCaml remains a separate route outside the core M7 safety claim.

## How to read the claims {#reading-claims}

Claims under this concept relate different execution models through equal-observation statements on specified fragments.

Key properties to inspect:
- [`run-eq-meaning`](#claim:run-eq-meaning): Frame machine execution matches denotational meaning on the `Straight` fragment.
- [`run-eq-ref`](#claim:run-eq-ref): Frame machine replay matches the reference machine at the empty row table.
- [`m7-route`](#claim:m7-route): Milestone M5 and M6 imply M7 through the route theorem.

The table of claims on this page gives each claim's status and its statement.
