# Effects v0.9.0

The coalgebra layer, and the gate's exact axiom walk. Every change is an addition except one
move: the signature morphisms leave the opt-in experimental root for `Effects.Lens`, with their
names unchanged, so `import Effects` now reaches them.

## Added

- `Effects.Lens`: `Signature.Hom`, `Program.map`, `Handler.pull`, `interpret_map`,
  `Program.map_id`, `Program.map_comp`.
- `Effects.Coalgebra`: `Step`, `System`, `Bisim`, `Comodel`, `Protocol`, `Run`. Packet
  `test/contracts/coalgebra.contract.md`.
- `EffectsTest/Audit/Axioms.lean` and `EffectsTest/Audit/AxiomWalk.lean`: the exact walk and its
  controls.

## Changed

- The gate reads axioms with the exact walk, not `Lean.collectAxioms`.
- `EffectsTest.Audit.Axioms` is an admitted `Classical.choice` module (`docs/CLAIM-BOUNDARY.md`).
- `Effects.Experimental.Morphism` keeps the sum isomorphisms and imports `Effects.Lens`.

## Downstream

A consumer that imported `Effects.Experimental.Morphism` for `Signature.Hom` may import
`Effects.Lens` instead; the old import still works. No declaration of `Effects/Algebra` changed
(the parity receipt holds).
