# Store typing and value membership

This page explains the store typing concept in Effect4. It covers how mutable reference cells and runtime values are typed across allocated worlds without stored closures.

## The runtime concept {#runtime-concept}

Effect programs read and update mutable memory through reference cells, deferred completions, and resource scopes. In Effect rc.112, these objects hold mutable state across concurrent fibers.

Effect4 models this state using explicit partitioned stores in `Stores` (`src/Effect4/Machine/Stores.lean`). Each reference cell, deferred promise, and scope carries a typed identifier.

Value membership defines whether a runtime value conforms to a semantic type within a given allocation state.

## Literature foundations {#literature}

The metatheory adapts store typings from Pierce (TAPL §13.4). In that formulation, a store typing assigns static types to memory locations to break circularity during assignment.

Monotonic store weakening adapts the approach of Software Foundations (`References.v`). Extending a store with newly allocated locations keeps existing typings valid.

World indexing adapts Kripke models from Crary (ATTAPL ch. 6) and Ahmed (2004). Types are interpreted relative to worlds ordered by extension.

## What Effect4 keeps and what it cuts {#adaptations-and-cuts}

Effect4 keeps world-indexed typing through `World` (`src/Effect4/Laws/Program/Typed/World.lean`). A world records static types for fibers, promises, heap reference cells, and guard tokens.

The value membership judgment is `Fits` (`src/Effect4/Laws/Program/Typed/Membership.lean`). It asserts that a value inhabits a semantic type at a specific world.

Effect4 cuts stored functions (decisions row 163). Stored programs and values contain no closures or host functions.

Because the object language lacks stored arrows, `Fits` has no arrow constructor. Reference cells store syntactic type declarations rather than recursive semantic contents.

This cut avoids step indexing while keeping first-order reference safety intact. Scope handles additionally require scope persistence via `ScopeLive` (decisions row 156).

## How to read the claims {#reading-claims}

The claims under this concept state that value membership behaves lawfully as execution progresses and worlds grow.

Key properties to inspect:
- [`fits-mono`](#claim:fits-mono): Value membership is monotone across accessible future worlds.
- [`fits-subn`](#claim:fits-subn): Value membership is closed under normalized subtyping.
- [`fits-normalize`](#claim:fits-normalize): Value membership is invariant under type normalization.

The table of claims on this page gives each claim's status and its statement.
