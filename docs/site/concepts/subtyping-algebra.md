# Subtyping algebra and normalization

This page explains subtyping algebra and normalization in Effect4. It covers how types normalize into canonical forms, how subtyping evaluates over joins, and why raw subtyping is replaced by normalized subtyping.

## The runtime concept {#runtime-concept}

Effect programs classify data and errors using unions, records, tuples, maps, and primitive types. Subtyping determines whether a produced value or error satisfies an expected type signature.

Effect4 defines the static type language in `Ty` (`src/Effect4/Program/TyCore.lean`). Normalization transforms types into canonical normal forms `CTy`.

Canonical types form a bounded join-semilattice where the least upper bound is computed by `Ty.join`.

## Literature foundations {#literature}

The metatheory adapts subtyping and subsumption from Pierce (TAPL ch. 15–16). In that setting, subtyping forms a preorder equipped with join operations.

Algorithmic subtyping over union and bottom types connects to Castagna (2024). Types order algebraically through set-theoretic unions and canonical representatives.

## What Effect4 keeps and what it cuts {#adaptations-and-cuts}

Effect4 keeps algebraic subtyping evaluated on normalized canonical forms through `Ty.subN` (`src/Effect4/Laws/Program/TypeAlgebra.lean`):
- Subtyping compares normal forms: `subN a b := sub a.normalize b.normalize`.
- Normalized subtyping is reflexive and transitive.
- Two types are mutually subtyped exactly when their normal forms are equal (`subN_equiv_iff`).

Effect4 cuts raw subtyping from the checker (decisions row 137, `E4-TYPED-CE-009`). Raw subtyping fails to distribute products over unions, so `subN` replaces raw `sub`.

Effect4 cuts function arrow types from `Ty` (decisions row 163). Types model stored data without arrow subtyping.

Record subtyping has no width rule (decisions row 178). Records with identical canonical names compare field by field covariantly.

Template instantiation replaces match by first occurrence with match by bounds (`Bounds.matchB`, decisions row 303), binding parameters to joins of lower bounds.

## How to read the claims {#reading-claims}

The claims under this concept state the algebraic order laws governing type normalization and subtyping checks.

Key properties to inspect:
- [`subn-refl`](#claim:subn-refl): Normalized subtyping is reflexive.
- [`subn-trans`](#claim:subn-trans): Normalized subtyping is transitive.
- [`subn-equiv-iff`](#claim:subn-equiv-iff): Two-way subtyping coincides with normal-form equality.

The table of claims on this page gives each claim's status and its statement.
