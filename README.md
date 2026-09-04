# Effect4

Effect4 is a Lean 4 library that models Effect TypeScript (`effect@4.0.0-rc.112`)
closely enough to generate it. Its product is **Effect codegen**: a first-order
program syntax (`Eff`) that prints as Effect TS and compiles to the rc.112
frame machine, a reference fiber machine (`Deep`) that runs those frames the
way rc.112's run loop does, and the Effect Schema data plane with its
TypeScript generation, optics and surface carriers beside it.

```text
 Effect TS text  ⇄  Eff program  →  rc.112 frames  →  Deep machine
   print / read      compile                          replay / runSync

 Schema document ⇄  representation  →  Schema.Struct({…}) syntax, JSON Schema
```

## The application face

Import `Effect4.Api` (`src/Effect4/Api.lean`). It is the one module an application
needs: `typeOf`, `print`, `printDecl`, `compile`, `replay`, `run`, `runSync`,
and the Schema syntax (`schemaDocument`, `schemaRepresentation`, `jsonExpr`).
It answers TypeScript **syntax** and never text; rendering is one call to the
pinned `typescript` package (`TypeScript.Render.expr house0 0 e`). Everything
else in the library is implementation behind that seam, and
`Test/Api/ApiContract.lean` is the receipt that crosses it the way a
caller does.

## Source tree

| Area | What it holds |
| --- | --- |
| `src/Effect4/Program` | `Eff`, the program AST (24 constructors, one rc.112 line each); its typing, printer, native operation alphabet and defunctionalising compile to frames |
| `src/Effect4/Machine` | one layer, flat: the frame alphabet (`Prim`, `PrimInterp`, `FrameFiber`, `Frames.lean`) and the rc.112 `Scope` state machine; `Cause`/`Exit`, fiber ids, supervision vocabulary and service keys; and the reference fiber machine over those frames — fibers, stores (Ref, Deferred, Scope), Context and Layer models, the clause theorems tagged by census row, the executable witnesses |
| `src/Effect4/Data` | rows, JSON and optics |
| `src/Effect4/Schema` | the persisted Schema carrier, annotations, checker, authoring face; the host pins under `Schema/Pins/` (values, getters, transformations, codecs) |
| `src/Effect4/Codegen`, `src/Effect4/Ingest` | the pinned Effect v4 profile (spellings, service rows), the printer, the Schema and annotated-field generators and the surface emitters; the readers that go the other way |
| `src/Effect4/Store`, `src/Effect4/Evidence` | the content-addressed store; architecture and surface views as Schema documents, the pinned rc.112 export census (`Evidence/StdLib`) and the characterized components lane (`Evidence/Char`) |
| `src/Effect4/Surface` | the surface carriers (entities, HTTP API, MCP agent, deployment, site) |
| `Test/` | one battery per area; `Test/Audit/AxiomGate.lean` audits every declaration; `RuntimeCoverage.lean` joins the rc.112 mechanism census to the machine witnesses |

The Flow route of earlier work — the Effects-flow language, its runner and
simulations, the TypeScript flow lowering and the store families — lives on
branch `archive/flow-route` (`docs/research/2026-09-04-prod-cleanup-inventory.md`).

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
A narrower sweep is a per-area target (`lake build TestMachine`,
`TestProgram`, `TestSchema`, …). Run one `lake` at a time.

The gates beyond the build (bash; on Windows run them through WSL):

```text
./scripts/test-trust-gate.sh                       # the gate's own self-test
./scripts/check-effect-runtime-census.sh           # the rc.112 mechanism census join
./scripts/test-schema-structural-assurance-gate.sh # the Schema assurance projection
./scripts/sweep.sh --hermetic                      # every hermetic gate, stamped
```

`docs/ARCHITECTURE.md` owns module boundaries and dependency direction,
`docs/DESIGN-BASIS.md` the representation decisions, `docs/RUNTIME-COVERAGE.md`
the one coverage report format, and `Test/Counterexamples/REGISTER.md` the
stable IDs of every declaration-changing counterexample. `AGENTS.md` is the
router for agents working in this tree.
