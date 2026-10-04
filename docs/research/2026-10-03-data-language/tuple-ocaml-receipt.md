# Tuple and record-tag OCaml conversion receipt

The manual source changes require the coordinator's generated companions before OCaml checks.
Base: `41d75f62` on `codex/tuple-ocaml`, after the source base and documentation commits named in the brief.
The earlier `codex/record-operations` branch and worktree remain unchanged.

## Placement

Concept: Translation & Simulation Metatheory in `docs/core/semantics.md`.
Property: retain stored program syntax across the existing OCaml conversion.
Role: finite compatibility evidence for R2 and R3.
No semantics registry claim closes through these checks.
The canonical wire laws retain ownership of encoding.

`OCaml5.Eff.termV` and `decisionV` in `src/OCaml5/Eff/Goldens.lean` produce generic wire trees.
`E4_program.Make.of_term` and `of_decision` in `ocaml/engine/e4_program.ml` convert those source constructors into generated engine constructors.
The scope is `Term.tupleAt` and `Decision.recordTag`, including nested uses and raw payloads.
The Lean conversion retains each stored natural index.
The OCaml controls retain indices representable by the existing `int` carrier.
They establish no support for arbitrary Lean naturals in that carrier.
Record tags retain their exact strings.
The conversions perform no normalization or program admission.

The constructor positions remain those in `tools/Effect4Gen/wire-tags.json`.
Tuple projection follows the existing term constructors at position six.
Record tag selection follows the existing decisions at position three.
These controls establish no universal conversion theorem, OCaml simulation, or target-library agreement.
They add no premise or conclusion to M5, M6, or M7.
The host boundary remains in `docs/core/host-boundary.md`.

## Files

- `src/OCaml5/Eff/Goldens.lean`: conversions and constructor corpus.
- `ocaml/engine/e4_program.ml`: conversions and constructor-position helpers.
- `ocaml/engine/e4_program.mli`: decision conversion and position interface.
- `ocaml/eff/test/prop_wire.ml`: random and focused wire controls.
- `ocaml/engine/test/test_engine.ml`: constructor coverage and exact payload controls.
- This receipt.

## Verification

The source checkpoint passes:

`LEAN_NUM_THREADS=3 lake build OCaml5.Eff.Goldens OCaml5.Tools.EffGen OCaml5.Tools.EffWire`

The build reports 94 jobs.
The log is `/private/tmp/effect4-tuple-ocaml-source.log`.
This checkpoint contains the Lean conversion and this receipt only.
Manual OCaml changes remain pending the generated companions and focused checks.

The switch probe uses `opam exec --switch=effect4 -- ocaml -noinit -noprompt`.
It reports OCaml 5.1.1, `Sys.int_size = 63`, and `max_int = 4611686018427387903`.
The large-index controls use `9007199254740993` and `max_int` within that range.
The first index exceeds the exact JavaScript integer range without exceeding this OCaml carrier.
No TypeScript execution claim follows from these OCaml controls.
The coordinator owns all generators and generated files.
No theorem or axiom query belongs to this finite conversion slice.
