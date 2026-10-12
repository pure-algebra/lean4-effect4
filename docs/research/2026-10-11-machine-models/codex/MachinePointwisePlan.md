# Shared list relation: caller plan

The slice removes `Modules.Pointwise` after its callers use the existing `Effect4.ListRel`.
It retains the named theorems and the reading and typing observations.

Base: `c31acf15b`.

## Placement

1. Concept: `translation-simulation`, requirement R10, for step-language reading and Pool construction.
2. Question: this slice serves the existing `step-language-sound` and `pool-expansion-agrees` claims.
   `Pool.make_makes` consumes the resource relation through `reads_initial`.
   `TypesAll` also serves `step-language-typed`, requirement R4.
3. Reach: lists relate each pair of entries through the same supplied predicate.
   Reading still requires successful authoring elaboration and evaluation at the supplied scope and values.
   Typing still requires the supplied signature and environment.
4. Limits: this slice states no new run, progress or host claim.
   `Program.Fits` remains behind its existing connector until a Typed slice touches it.
5. Unlock: item 11 uses one list relation before the name and world relations move.

## Files

- `src/Effect4/Laws/Step/Reading.lean`
- `src/Effect4/Laws/Step/Checking.lean`
- `src/Effect4/Laws/Library/Pool/Ops.lean`
- `src/Effect4/Laws/Data/ListRelConnectors.lean`
- `src/Effect4/Laws/Data/ListRel.lean`

## Finish criteria

- Delete the private relation and its duplicate map proof.
- Retain `Pointwise.of_map` as an instance of `ListRel.of_map_left`.
- Retain `Data.pointwise_iff` as a reflexive connector.
- Check `Test.Program.StepConstruction` and `Test.Program.PoolOps` with the changed law modules.
- Audit the changed modules and both readers at the permitted axioms.
- Compare theorem headers and record the exact relation substitution.
- Measure lines and record the commands before committing explicit paths.
