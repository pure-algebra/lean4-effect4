# Effect4

Effect4 is a Lean 4 library that models Effect TypeScript (`effect@4.0.0-rc.112`)
closely enough to generate it. Its product is **Effect codegen**: a first-order
program syntax (`Eff`) that prints as Effect TS and compiles to the rc.112
frame machine, a reference fiber machine (`Machine`) that runs those frames the
way rc.112's run loop does, and the Effect Schema data plane with its
TypeScript generation, optics and surface carriers beside it.

```text
 Effect TS text  ⇄  Eff program  →  rc.112 frames  →  Machine
   print / read      compile                          replay / runSync

 Schema document ⇄  representation  →  Schema.Struct({…}) syntax, JSON Schema
```

## The application face

Import `Effect4.Api` (`src/Effect4/Api.lean`). It is the program interface:
`typeOf`, `print`, `printDecl`, `compile`, `replay`, `run`, `runSync`,
and the Schema syntax (`schemaDocument`, `schemaRepresentation`, `jsonExpr`).
Its program printers answer TypeScript **syntax**; the explicit `render` operation
crosses from a codegen artefact to bytes. Surface construction uses the carrier
modules under `Effect4.Surface`, and
`Test/Api/ApiContract.lean` is the receipt that crosses it the way a
caller does.

The library lives under `src/Effect4`, its batteries under `Test/`, and its
generators and drivers under `tools/`. The OCaml estate spans `src/OCaml5` and
the dune workspace `ocaml/`; the TypeScript reader lives in `ts/eff`.
[Architecture](docs/ARCHITECTURE.md#source-tree) owns the source-tree table
and the dependency boundaries.

The earlier Flow route is retained in git history and on branch `archive/flow-route`.

## Building

The toolchain is pinned by `lean-toolchain`. Dependencies are pinned by exact
commit in `lakefile.toml`: `effects` (the portable effect algebra),
`typescript` (target syntax and rendering), `hash` (a proved SHA-256).

```text
lake build Effect4
```

builds the library; a bare `lake build` also builds `Test`, the
green battery, whose root runs the module-closure and axiom gate: every
declaration under `Effect4.*` and `Test.*` is audited at
`[propext, Quot.sound]` with a short list of exact, named rendering
exceptions, and every battery file must be reachable from `Test/All.lean`.
The five area targets are `TestSchema`, `TestMachine`, `TestStore`,
`TestProgram`, and `TestCodegen`. A single battery builds by its module name,
for example `lake build Test.Api.ApiContract`. Run one `lake` at a time. `lake build OCaml5`
builds the Lean half of the OCaml estate; the OCaml half is `dune build` in
`ocaml/` under the `effect4` opam switch (`ocaml/README.md`). `lake build Tools`
type-checks the `--run` drivers under `tools/Tools/`; one runs as
`lake env lean -M4096 --run tools/Tools/<Driver>.lean …`.

The gates beyond the build (bash; on Windows run them through WSL):

```text
scripts/test-trust-gate.sh                       # the gate's own self-test
scripts/check-source-citations.sh                # live paths and immutable historical references
scripts/check-armmap-citations.sh                # avatar citation resolution, without OCaml
scripts/check-effect-runtime-census.sh           # the rc.112 mechanism census join
npm ci --prefix harness/schema-host # pinned Schema host and compiler integrations
scripts/test-schema-structural-assurance-gate.sh # the Schema assurance projection
scripts/check-ts-eff.sh                          # ts/eff/*.gen.ts are what Lean emits
scripts/check-ts-eff-corpus.sh                   # the TypeScript reader = Lean's reader (bun)
scripts/check-rc112-surface.sh                   # the pinned typed surface projection (Node)
scripts/check-truth.sh                           # bounded Lean/rc.112 differential (bun)
scripts/sweep.sh --hermetic                      # every hermetic gate, stamped
scripts/sweep.sh --ocaml                         # avatar, daemon protocol and dune tests
```

Surface extraction uses the compiler pinned in `ts/eff/package.json`; install it
with `bun install --frozen-lockfile --cwd ts/eff`. The truth lane selects its pinned
host through `EFFECT4_EFFECT_NODE_MODULES`. OCaml gates require the `effect4` opam
switch and print `SKIP` when `ocamlrun` is absent. Archived receipt paths are checked
against their recorded git history; this does not refresh their original verdicts.

`docs/ARCHITECTURE.md` owns module boundaries and dependency direction,
`docs/DESIGN-BASIS.md` the representation decisions, `docs/RUNTIME-COVERAGE.md`
the one coverage report format, and `Test/Counterexamples/REGISTER.md` the
stable IDs of every declaration-changing counterexample. `AGENTS.md` is the
router for agents working in this tree.
