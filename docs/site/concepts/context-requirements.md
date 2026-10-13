# Context requirements and provision

This page explains context requirements and provision in Effect4. It covers how environmental service dependencies are tracked through requirement rows and discharged by layer construction.

## The runtime concept {#runtime-concept}

Effect programs declare service dependencies using ambient context parameters in the `R` type parameter of an effect. In Effect rc.112, layers build and supply services before execution begins.

Effect4 models context mapping in `Context` (`src/Effect4/Machine/ContextMap.lean`). Services are keyed by unique `ServiceKey` identifiers.

A program executes only after required services are provided by enclosing layers.

## Literature foundations {#literature}

The metatheory adapts coeffect calculi from Petricek, Orchard, and Mycroft (2014). Coeffects grade computational terms by the context resources required for execution.

Row operations adapt the row polymorphism principles of Leijen (2014). Operations like union and difference track capability requirements across composition boundaries.

## What Effect4 keeps and what it cuts {#adaptations-and-cuts}

Effect4 adapts flat coeffects where a requirement row is a flat collection of service keys (`Row ServiceKey`). Context satisfaction is simple subset inclusion (`Satisfies self r := r.Subset self.keysRow`, `src/Effect4/Machine/Context.lean`).

Effect4 cuts comonadic adjunctions and complex grading semirings. Flat key inclusion models service availability directly.

Top-level program execution requires an empty requirement row at load time (decisions row 117). Frames transporting a missing service defect across boundaries are excluded (`E4-TYPED-CE-008`).

Layer bodies build at closed lexical points (`Point.layerBuild`), and produced services must fit declared types (decisions rows 104 and 105).

A shared layer is built once: `Test/Program/LayerSharingContract.lean` compares one reference site with two nested ones under the same table.

## How to read the claims {#reading-claims}

The claims under this concept state that context satisfaction behaves monotonically and that layer provision discharges service requirements cleanly.

Key properties to inspect:
- [`satisfies-empty`](#claim:satisfies-empty): An empty requirement row is unconditionally satisfied by any context.
- [`satisfies-weaken`](#claim:satisfies-weaken): Context satisfaction is monotone under context extension.
- [`provide-discharges`](#claim:provide-discharges): Providing a layer discharges its declared requirement keys from the program.

The table of claims on this page gives each claim's status and its statement.
