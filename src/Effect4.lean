-- The core alphabet: requirement rows, JSON, optics.
import Effect4.Data.Row
import Effect4.Data.Json
import Effect4.Data.Optic
-- The generic content-addressed store (2026-09-04): canonical bytes, a proved
-- SHA-256 address, ids by insertion, names by path trie. The substrate every
-- ingested surface — a standard library, a schema surface, a code blob and
-- the syntax read from it — is modelled in as data.
import Effect4.Store.Canonical
import Effect4.Store.Digest
import Effect4.Store.Trie
import Effect4.Store.Store
import Effect4.Store.Pin
-- The error channel everywhere.
import Effect4.Machine.Cause
import Effect4.Machine.Exit
-- The Schema data plane: the persisted carrier, the annotation data plane, the
-- checker, the authoring face, and the value, getter, transformation, codec,
-- registry and foreign rows.
import Effect4.Schema.Payload
import Effect4.Schema.Representation
import Effect4.Schema.Annotations
import Effect4.Schema.EffectfulField
import Effect4.Schema.Document
import Effect4.Schema.Check
import Effect4.Schema.Authoring
import Effect4.Schema.Pins.Value
import Effect4.Schema.Pins.Getter
import Effect4.Schema.Pins.Transformation
import Effect4.Schema.Pins.Codec
import Effect4.Schema.Pins.Registry
import Effect4.Schema.Pins.Foreign
-- Service keys, the rc.112 scope state machine, the frame alphabet (`Prim`,
-- `PrimInterp`, `FrameFiber`), and the frame-level facts that still pin it.
import Effect4.Machine.Key
import Effect4.Machine.Scope
import Effect4.Machine.ScopeMachine
import Effect4.Machine.ScopeRestoration
import Effect4.Machine.Frames
import Effect4.Machine.LiveStack
-- Fiber ids and the supervision vocabulary the machine speaks.
import Effect4.Machine.Fiber
import Effect4.Machine.Supervision
-- The Effect TypeScript target: the pinned v4 profile (spellings, service
-- rows), and the Schema and annotated-field generators.
import Effect4.Codegen.Profile
import Effect4.Codegen.Schema
import Effect4.Codegen.EffectfulField
-- The reference machine (docs/research/2026-09-03-deep-plan.md): one
-- program-carrying fiber machine over the rc.112 frames, the stores it drives,
-- the witnesses over them, and the Context and Layer models. Promoted from the
-- `workshop/Deep` spike on 2026-09-04; the old fiber and scheduler carriers
-- were retired the same day (`docs/research/2026-09-04-retire-old-machines.md`)
-- and the Flow route (the Effects-flow compile and its simulations) was
-- archived to branch `archive/flow-route` the same day
-- (`docs/research/2026-09-04-prod-cleanup-inventory.md`).
import Effect4.Machine.Fibers
import Effect4.Machine.Clauses
import Effect4.Machine.Stores
import Effect4.Machine.Witnesses
import Effect4.Machine.Context
import Effect4.Machine.Layer
-- The middle tier (2026-09-04): architecture views as Effect Schema documents
-- with payloads projected from the proof carriers, the JSON canonical form that
-- makes schemas store content, the structural acceptance checker, and the
-- pinned standard library as store entries.
import Effect4.Store.JsonCanonical
import Effect4.Schema.Accepts
import Effect4.Evidence.Views
import Effect4.Evidence.StdLib.Entry
import Effect4.Evidence.StdLib.Rc112
-- The Surface library (docs/research/2026-09-04-surface-library-plan.md), wave
-- 1a: the substrate. `Kind` is the typed embedding, a representation with a
-- kernel-checked kind, so an ill-kinded slot of a surface is unrepresentable
-- rather than caught; `Facts` is the one closed `Refusal` and the clause lists
-- every check is read from (§14.2); `Annotate` is the semantic layer, the
-- typed annotation keys and the estate's brand, which §15 makes mandatory
-- rather than optional; `Spell` is the `Schema.Struct({…})` rendering admitted
-- as a view of the persisted one; `Entity` and `Domain` are the first carriers,
-- with their clause-by-clause `check`, their `Arch` document views and their
-- store content; `JsonSchema` is draft 2020-12 in both directions on one
-- fragment, read off rc.112's own compiler; `Emit` is the rule census and the
-- stance, where every rule is `emitted` until its receipt lands; and `Views` is
-- the surface store.
--
-- Waves 2a to 2c are the carriers the plan's §2 names. `Api` is the HTTP
-- surface, its responses indexed by status and its path algebra decided over
-- `List Char` (the `String` spelling of the round trip is an owed row, because
-- `String.toList` reaches `Classical.choice` on this toolchain), and `Api.Emit`
-- renders the rc.112 `HttpApi` module, its client and the OpenAPI 3.1 document.
-- `Agent` is the MCP surface and `Agent.Emit` its tools listing. `Deploy` and
-- `Deploy.Emit` are the worker and its bindings, read against the vendored
-- wrangler schema. `Site` is the static carrier. `Ingest` has no module of its
-- own: `ofMcpToolsList` and `ofWrangler` live with the emitters that read them.
import Effect4.Surface.Kind
import Effect4.Surface.Refusal
import Effect4.Surface.Annotate
import Effect4.Codegen.Spell
import Effect4.Surface.Entity
import Effect4.Codegen.JsonSchema
import Effect4.Codegen.Rules
import Effect4.Evidence.SurfaceViews
import Effect4.Surface.Api
import Effect4.Codegen.HttpApi
import Effect4.Surface.Agent
import Effect4.Codegen.Mcp
import Effect4.Surface.Deploy
import Effect4.Codegen.Worker
import Effect4.Surface.Site
-- The characterized components lane (workshop/Char/): a component is its kinds,
-- its failure set and the order they induce, so a lossy table still gets `order`
-- from one generic theorem rather than a hand-written word induction. `Queue` is
-- the first port, the rc.112 `Queue.ts` step emitted arm by arm and checked
-- against the source theorems it claims, with its reachability invariant, its
-- crash reading, its graded axes, and its acceptance and mutant-kill suites
-- decided in the kernel so a survivor is a build failure. `Conformance`,
-- `Manifest` and `Evidence` are the lane's census, its component table and its
-- receipts.
import Effect4.Evidence.Char.Conformance
import Effect4.Evidence.Char.Manifest
import Effect4.Evidence.Char.Queue.Grade
import Effect4.Evidence.Char.Queue.Mutants
-- The AST relation (docs/research/2026-09-04-ast-relation-plan.md), lane A1:
-- the Effect TS program syntax `Eff` and its typing, first-order and
-- decidable throughout; the printer, the compile and the parser follow. `Eff`
-- is the one program IR of this library; it compiles to the frame alphabet the
-- Deep machine runs.
import Effect4.Program.Eff
import Effect4.Program.Typing
import Effect4.Codegen.Print
import Effect4.Program.Native
import Effect4.Program.Compile
-- The canonical bytes of a program and the exact decoder (2026-09-04): how a
-- program crosses the store, the OCaml host and the daemon, and comes back as
-- exactly itself. `workshop/OCaml5/eff` implements the same rule in OCaml.
import Effect4.Program.Wire
-- The application face: one module, the whole pipeline (type, print, compile,
-- run; the Schema syntax), answering syntax and never text. Import this.
import Effect4.Api

/-!
# Effect4

Standalone Lean library for a closed, first-order, effectful core and its
proof-bearing bridges. The semantic modules are introduced only after their
contract packets and counterexample batteries are frozen.
-/
