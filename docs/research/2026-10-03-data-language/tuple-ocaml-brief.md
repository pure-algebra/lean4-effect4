# Tuple and record-tag OCaml consumers

Start an owned branch from `c40b96b8` in the existing Schema seat's worktree.
Retain the old branch and its finished commits.
The root coordinator integrates the new source checkpoint and owns every producer.

## Scope and property

Extend existing conversions for `Term.tupleAt` and `Decision.recordTag`.
Keep the exact stored natural index and tag string.
Retain existing constructor positions; append tuple projection at position six.
Keep the existing program representation and canonical wire identity.

The slice provides finite compatibility evidence for R2 and R3.
No universal theorem follows from these finite checks.
The existing canonical wire laws remain the semantic owner of encoding.

## Files

Own `src/OCaml5/Eff/Goldens.lean` for constructor conversion and corpus examples.
Own `ocaml/engine/e4_program.ml` and `ocaml/engine/e4_program.mli` for conversion and constructor-position helpers.
Own `ocaml/eff/test/prop_wire.ml` for generated wire controls.
Own `ocaml/engine/test/test_engine.ml` for exact constructor and payload controls.
Write a receipt in this research directory.
Do not edit generated files, manifests, root imports, decisions, Schema or tuple proof modules.

## Stages and verification

1. Draft the conversions and finite controls.
2. Request the shared Lean lane for `OCaml5.Eff.Goldens`, `OCaml5.Tools.EffGen` and `OCaml5.Tools.EffWire`.
3. Commit the checked Lean source checkpoint and request the coordinator's generated companions.
4. Run focused OCaml builds and tests only through `opam exec --switch=effect4`.
5. Check constructor positions, exact raw indices, record tags and nested uses.
6. Commit explicit paths after their checks.

The coordinator runs the `lcnf`, `eff`, `wire` and `cas` producers, including repeat-output comparisons.
Use the commands in `record-ocaml-receipt.md` for the existing test directories.
Record every result, generator dependency and remaining boundary.
Do not push, merge into the main checkout or run a full sweep.
