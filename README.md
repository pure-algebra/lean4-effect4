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

Import `Effect4.Api` (`Effect4/Api.lean`). It is the one module an application
needs: `typeOf`, `print`, `printDecl`, `compile`, `replay`, `run`, `runSync`,
and the Schema syntax (`schemaDocument`, `schemaRepresentation`, `jsonExpr`).
It answers TypeScript **syntax** and never text; rendering is one call to the
pinned `typescript` package (`TypeScript.Render.expr house0 0 e`). Everything
else in the library is implementation behind that seam, and
`Effect4Test/Api/ApiContract.lean` is the receipt that crosses it the way a
caller does.

## Source tree

| Area | What it holds |
| --- | --- |
| `Effect4/Syntax` | `Eff`, the program AST (24 constructors, one rc.112 line each); its typing, printer, native operation alphabet and defunctionalising compile to frames |
| `Effect4/Deep` | the reference fiber machine over the rc.112 frames: fibers, stores (Ref, Deferred, Scope), Context and Layer models, the clause theorems tagged by census row, the executable witnesses |
| `Effect4/Runtime` | the frame alphabet (`Prim`, `PrimInterp`, `FrameFiber`) and the rc.112 `Scope` state machine the Deep machine builds on |
| `Effect4/Semantics`, `Effect4/Concurrency`, `Effect4/Context`, `Effect4/Data` | `Cause`/`Exit`, fiber ids and supervision vocabulary, service keys, rows, JSON and optics |
| `Effect4/Schema` | the persisted Schema carrier, annotations, checker, authoring face, values, getters, transformations, codecs |
| `Effect4/Target/TypeScript` | the pinned Effect v4 profile (spellings, service rows) and the Schema and annotated-field generators |
| `Effect4/Store`, `Effect4/Arch`, `Effect4/StdLib` | the content-addressed store, architecture views as Schema documents, the pinned rc.112 export census as store content |
| `Effect4/Surface`, `Effect4/Char` | the surface carriers (entities, HTTP API, MCP agent, deployment, site) and the characterized components lane |
| `Effect4Test/` | one battery per area; `Effect4Test/Audit/AxiomGate.lean` audits every declaration; `RuntimeCoverage.lean` joins the rc.112 mechanism census to the Deep witnesses |

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

builds the library; a bare `lake build` also builds `Effect4TestGreen`, the
green battery, whose root runs the module-closure and axiom gate: every
declaration under `Effect4.*` and `Effect4Test.*` is audited at
`[propext, Quot.sound]` with a short list of exact, named rendering
exceptions, and every battery file must be reachable from `Effect4Test.lean`.
A narrower sweep is a per-area target (`lake build Effect4TestDeep`,
`Effect4TestSyntax`, `Effect4TestSchema`, …). Run one `lake` at a time.

The gates beyond the build (bash; on Windows run them through WSL):

```text
./scripts/test-trust-gate.sh                       # the gate's own self-test
./scripts/check-effect-runtime-census.sh           # the rc.112 mechanism census join
./scripts/test-schema-structural-assurance-gate.sh # the Schema assurance projection
./scripts/sweep.sh --hermetic                      # every hermetic gate, stamped
```

`docs/ARCHITECTURE.md` owns module boundaries and dependency direction,
`docs/DESIGN-BASIS.md` the representation decisions, `docs/RUNTIME-COVERAGE.md`
the one coverage report format, and `test/counterexamples/REGISTER.md` the
stable IDs of every declaration-changing counterexample. `AGENTS.md` is the
router for agents working in this tree.
