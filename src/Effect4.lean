-- The core alphabet: requirement rows, JSON, optics, and the optic at a key of a JSON
-- object with its laws (the model of every generated `Optic.id<S>().key(…)`).
import Effect4.Data.Row
import Effect4.Data.Ascii
import Effect4.Data.Json
import Effect4.Data.JsonNumber
import Effect4.Data.Optic
import Effect4.Data.JsonOptic
-- The content-addressed store as one trait (docs/research/2026-09-04-cas-trait-plan.md,
-- landed 2026-09-05), in dependency order: the digit strings and the strict UTF-8 of the
-- byte codec; the value tree `Val` with its one exact codec; the SHA-256 digest and the one
-- hex codec; the kind table; the shape language with the spec `Document` and the JSON
-- printer derived from it; the `Canonical` trait, its laws as fields, and the primitives;
-- the node (`version ∷ kind ∷ spec ∷ payload`), the typed `Ref` and the address lattice
-- proved once; the store with admission and roots; words (replay, closure, the layered
-- read, the outbox, verify); traits as annotation nodes; the generated instances of `Json`
-- and of the Schema carriers; the genesis (`Content Document`, so the meta-schema is the
-- zero-spec node); the pin and its generated instance at kind `source`.
import Effect4.Store.Carrier.Digits
import Effect4.Store.Carrier.Utf8
import Effect4.Store.Carrier.Val
-- The shape-free exact-image trait (U0, 2026-09-07): the views of the shared carrier the
-- Machine layer uses without naming a `Shape`; `Canonical.image` is the bridge.
import Effect4.Store.Carrier.Image
import Effect4.Store.Carrier.Image.Containers
import Effect4.Store.Carrier.Digest
import Effect4.Store.Carrier.Kind
import Effect4.Store.Domain.Shape
import Effect4.Store.Domain.Canonical
import Effect4.Store.Domain.Clock
import Effect4.Store.Domain.RowCanonical
import Effect4.Store.Domain.Node
import Effect4.Store.Domain.Store
import Effect4.Store.Domain.Word
import Effect4.Store.Domain.Traits
import Effect4.Store.Domain.Derived.Json
import Effect4.Store.Domain.Derived.Schema
import Effect4.Store.Domain.Genesis
import Effect4.Store.Domain.Pin
import Effect4.Store.Domain.PinDerived
-- The error channel everywhere.
import Effect4.Machine.Cause
import Effect4.Machine.Exit
-- The shared value foundation, Machine side (U0): the handle-kind and runtime constructor
-- tables, the `Value.*` spellings, and the generic cause/exit images over the carrier.
import Effect4.Machine.Value
-- The Schema data plane: the persisted carriers, annotations and raw authoring face.
import Effect4.Schema.Payload
import Effect4.Schema.Representation
import Effect4.Schema.Annotations
import Effect4.Schema.Document
import Effect4.Schema.Authoring
-- Service keys, the rc.112 scope state machine, the frame alphabet (`Prim`,
-- `PrimInterp`, `FrameFiber`).
import Effect4.Machine.Key
import Effect4.Machine.Scope
import Effect4.Program.Decision
import Effect4.Machine.Frames
-- Fiber ids and the supervision vocabulary the machine speaks.
import Effect4.Machine.Fiber
import Effect4.Machine.Supervision
-- The Effect TypeScript target: the Schema generator.
import Effect4.Codegen.Schema
-- The reference machine (docs/research/2026-09-03-deep-plan.md): one
-- program-carrying fiber machine over the rc.112 frames, the stores it drives,
-- the service map and the fiber context. Promoted from the
-- `workshop/Deep` spike on 2026-09-04; the old fiber and scheduler carriers
-- were retired the same day (`docs/research/2026-09-04-retire-old-machines.md`)
-- and the Flow route (the Effects-flow compile and its simulations) was
-- archived to branch `archive/flow-route` the same day
-- (`docs/research/2026-09-04-prod-cleanup-inventory.md`).
import Effect4.Machine.Fibers
import Effect4.Machine.Alphabets
import Effect4.Machine.Term
import Effect4.Machine.Stores
import Effect4.Machine.Context
-- The codegen target and artefact definitions with the one crossing to bytes.
import Effect4.Codegen.Target
import Effect4.Codegen.Template
-- The AST relation (docs/research/2026-09-04-ast-relation-plan.md), lane A1:
-- the Effect TS program syntax `Eff` and its typing, first-order and
-- decidable throughout; the printer, the compile and the parser follow. `Eff`
-- is the one program IR of this library; it compiles to the frame alphabet the
-- Deep machine runs.
import Effect4.Program.Eff
import Effect4.Program.Fold
import Effect4.Program.LayerView
import Effect4.Program.TyFoldExtras
import Effect4.Program.TyClasses
import Effect4.Program.Bounds
import Effect4.Schema.Template
import Effect4.Schema.TyFaces
import Effect4.Program.Typing
import Effect4.Program.Typing.Blame
-- A sketch (decisions row 288): a program with its hole table, and its check. Reachable from
-- this root, imported by no module of the API.
import Effect4.Program.Sketch
import Effect4.Program.Binders
import Effect4.Program.Scoped
import Effect4.Program.Authoring
import Effect4.Program.Authoring.Lifts
import Effect4.Program.Authoring.Rows
import Effect4.Program.Authoring.Atoms
import Effect4.Codegen.Authoring.Forms
import Effect4.Api.TestClock
import Effect4.Program.Authoring.Sugar
import Effect4.Program.Authoring.Declare
import Effect4.Program.Authoring.Loops
import Effect4.Program.Authoring.Mask
-- A term at a declared type (`ascribe`): reachable from this root, imported by no module of the API.
import Effect4.Program.Authoring.Ascribe
import Effect4.Codegen.Print
import Effect4.Codegen.Diagnostics
import Effect4.Codegen.Read
import Effect4.Codegen.Metadata
import Effect4.Codegen.Templates
import Effect4.Program.Native
import Effect4.Program.Compile
-- The target profile as data and as specification (DB-09's three parts; S6a): reachable from
-- this root, imported by nothing in the API, so the library-root gate sees it here.
import Effect4.Program.Profile
import Effect4.Program.HostBoundary
-- The provision algebra (docs/research/2026-09-04-provision-algebra.md): `Row.diff`, the
-- layer signature `LayerTy` and its laws, the layer term `LayerTerm` over `Eff` bodies,
-- `App` (`Effect.provide`), the build specification (its totality theorem was cut at
-- `b08f3b58`; restoring it is owed under R5), and the compile-route runs of the docs deployment.
import Effect4.Program.Provision
-- Configuration as an algebra: rc.112's `ConfigProvider` in its `makeSource`/`makeOrElse`
-- normal form (a fallback monoid under a path-transformation action), the `Config` reader with
-- its tri-state resolution, dotenv substitution with fuel, and the configuration requirement
-- row (`docs/research/2026-09-04-production-standards-spike.md` §4).
import Effect4.Program.Config
-- The configuration values as an exact image of the shared carrier with their six-frame
-- admission (U0; U1c makes them the carrier plus the admission).
import Effect4.Program.ConfigValue
-- The canonical bytes of a program (2026-09-04; one trait since 2026-09-05): the
-- generated `Canonical (Eff NativeOp)` and its family, then the Wire face over
-- it — `encodeProgram`, `decodeProgram`, the round trip and exactness as
-- theorems, the corpus held to the goldens — so a program crosses the store,
-- the OCaml host and the daemon and comes back as exactly itself. `ocaml/eff`
-- implements the same rule in OCaml.
import Effect4.Store.Domain.Derived.Program
import Effect4.Store.Domain.ProgramWire
-- The application face: one module, the whole pipeline (type, print, compile,
-- run; the Schema syntax), answering syntax and never text. Import this.
import Effect4.Api
import Effect4.Program.Stream
import Effect4.Api.HostSession
import Effect4.Api.Runner
import Effect4.Api.RunnerBytes
-- The application surface (2026-09-17): a built program, its author, its run, its daemons.
import Effect4.Api.Built
import Effect4.Store.Carrier.Fold
import Effect4.Program.FoldOf
import Effect4.Program.Checker
import Effect4.Program.Typing.Agreement
-- The focus at an address (decisions row 292): the sub-program, its environment and its type.
import Effect4.Program.Typing.Focus
-- The address table (decisions row 302): each address with its environment and the checker's
-- answer, the list of refusals, and the environments of the term slots.
import Effect4.Program.Typing.Table
import Effect4.Program.Typing.Call
import Effect4.Api.Author
import Effect4.Api.Supervision
import Effect4.Run
-- What a tool reads off a run: the machine's view, the raw replay, the tape, a funded run, rest.
import Effect4.Run.Tape
-- Foreign-source ingestion tables and constructed target spellings.
import Effect4.Ingest.Taxonomy
import Effect4.Codegen.Forms
import Effect4.Codegen.Styles
-- The words of a step term that the composed modules share, in the namespace `Effect4.Modules`.
import Effect4.Modules.Words
-- The composed modules, programs over the authoring surface (decisions row 255): the Queue's
-- cell and its steps.
import Effect4.Modules.Queue.Cell
import Effect4.Modules.Queue.Steps
-- The shared pieces of a module that waits (decisions rows 221, 238 and 240), and the Queue's
-- first operations over them.
import Effect4.Modules.Waiting
import Effect4.Modules.Queue.Ops
-- Semaphore's cell and its five steps (decisions row 265).
import Effect4.Modules.Semaphore.Cell
import Effect4.Modules.Semaphore.Steps
-- Semaphore's first operations, with the protected permit (decisions rows 259 to 261 and 276).
import Effect4.Modules.Semaphore.Ops
-- Pool's cell and its six steps (decisions rows 267 to 269 and 276).
import Effect4.Modules.Pool.Cell
import Effect4.Modules.Pool.Steps
-- Pool's first operations: `Pool.make`, `Pool.use` and the close that `make` registers
-- (decisions rows 267 to 269, 276 and 279).
import Effect4.Modules.Pool.Ops
-- Stream's source, steps and operations (decisions row 309).
import Effect4.Modules.Stream.Source
import Effect4.Modules.Stream.Steps
import Effect4.Modules.Stream.Ops

/-!
# Effect4

The application API and functional utilities for a closed, first-order effectful core.
The separate `Effect4.Laws` root imports the proof graph; this root never reaches it.
-/
