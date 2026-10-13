# Initial algebras and catamorphic folds

This page explains initial algebras and catamorphic folds in Effect4. It covers how programs and types are modeled as free objects, how catamorphisms unify traversals, and why ad-hoc pattern matches are restricted.

## The runtime concept {#runtime-concept}

Effect programs and schemas are structured trees of computational nodes. Transforming these trees involves tasks like type checking, program printing, scoping, and dependency analysis.

Effect4 represents every core program syntax sort as a first-order free object. Programs (`Eff`), types (`Ty`), and values (`Store.Val`) are generated from formal syntax signatures.

Systematic traversals process these tree structures uniformly rather than relying on disparate hand-written recursions.

## Literature foundations {#literature}

The metatheory adapts initial algebra semantics and catamorphisms from Meijer, Fokkinga, and Paterson (1991). Initial algebras possess unique homomorphisms into carrier algebras.

Algebraic calculation and fold uniqueness adapt Gibbons (2002). Catamorphism fusion laws prove that two folds agree whenever their underlying algebra operations agree.

Free monad handler models connect to Plotkin and Pretnar (2009), where effect handlers operate as algebra maps over free syntactic structures.

## What Effect4 keeps and what it cuts {#adaptations-and-cuts}

Effect4 models each syntax sort as an initial algebra with a generated carrier structure (`EffAlgebra`, `TyAlgebra`). Traversals are unique folds (`cata_eff`, `cata_ty`).

The fundamental uniqueness theorem is `hom_eq_cata_eff` (`src/Effect4/Program/Fold.lean`). Any algebra homomorphism out of `Eff` equals `cata_eff`.

Effect4 cuts ad-hoc pattern matching across syntax sorts. Hand `match` statements are prohibited unless recorded in the traversal census (`#traversal_census`, `docs/core/traversal-census.md`).

Fold uniqueness is a theorem whose proof is an induction (`hom_eq_cata_eff`), not a definitional equality (`rfl`).

Infinite equi-recursive unfolds are cut (decisions row 127). The type emptiness test `inhabited` (`src/Effect4/Program/Columns.lean`) is a finite catamorphic fold over syntax trees.

## How to read the claims {#reading-claims}

The claims under this concept state that tree traversals agree with universal algebraic properties and that transformations compose reliably.

Key properties to inspect:
- [`hom-eq-cata-eff`](#claim:hom-eq-cata-eff): Any algebra homomorphism out of `Eff` is pointwise equal to `cata_eff`.
- [`inhabited-iff-fits`](#claim:inhabited-iff-fits): The syntactic `inhabited` fold characterizes semantic inhabitance in `Fits`.
- [`typed-replacement`](#claim:typed-replacement): A typed node splits at an address, allowing any fitting sub-program to replace the focus.

The table of claims on this page gives each claim's status and its statement.
