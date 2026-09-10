-- The core alphabet: requirement rows, JSON, optics, and the optic at a key of a JSON
-- object with its laws (the model of every generated `Optic.id<S>().key(…)`).
import Effect4.Data.Row
import Effect4.Data.Ascii
import Effect4.Data.Json
import Effect4.Arch.JsonNumber
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
import Effect4.Store.Digits
import Effect4.Store.Utf8
import Effect4.Store.Val
-- The shape-free exact-image trait (U0, 2026-09-07): the views of the shared carrier the
-- Machine layer uses without naming a `Shape`; `Canonical.image` is the bridge.
import Effect4.Store.Image
import Effect4.Store.Image.Containers
import Effect4.Store.Digest
import Effect4.Store.Kind
import Effect4.Store.Shape
import Effect4.Store.Canonical
import Effect4.Store.RowCanonical
import Effect4.Store.Node
import Effect4.Store.Store
import Effect4.Store.Word
import Effect4.Store.Traits
import Effect4.Store.Derived.Json
import Effect4.Store.Derived.Schema
import Effect4.Store.Genesis
import Effect4.Store.Pin
import Effect4.Store.PinDerived
-- The error channel everywhere.
import Effect4.Machine.Cause
import Effect4.Machine.Exit
-- The shared value foundation, Machine side (U0): the handle-kind and runtime constructor
-- tables, the `Value.*` spellings, and the generic cause/exit images over the carrier.
import Effect4.Machine.Value
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
import Effect4.Schema.Dimension
-- Service keys, the rc.112 scope state machine, the frame alphabet (`Prim`,
-- `PrimInterp`, `FrameFiber`).
import Effect4.Machine.Key
import Effect4.Machine.Scope
import Effect4.Machine.Frames
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
-- the service map and the fiber context. Promoted from the
-- `workshop/Deep` spike on 2026-09-04; the old fiber and scheduler carriers
-- were retired the same day (`docs/research/2026-09-04-retire-old-machines.md`)
-- and the Flow route (the Effects-flow compile and its simulations) was
-- archived to branch `archive/flow-route` the same day
-- (`docs/research/2026-09-04-prod-cleanup-inventory.md`).
import Effect4.Machine.Fibers
import Effect4.Machine.Stores
import Effect4.Machine.Context
-- Structural acceptance of persisted Schema documents.
import Effect4.Arch.Accepts
-- The codegen target and artefact definitions with the one crossing to bytes.
import Effect4.Codegen.Target
-- The AST relation (docs/research/2026-09-04-ast-relation-plan.md), lane A1:
-- the Effect TS program syntax `Eff` and its typing, first-order and
-- decidable throughout; the printer, the compile and the parser follow. `Eff`
-- is the one program IR of this library; it compiles to the frame alphabet the
-- Deep machine runs.
import Effect4.Program.Eff
import Effect4.Program.Typing
import Effect4.Codegen.Print
import Effect4.Codegen.Read
import Effect4.Program.Native
import Effect4.Program.Compile
-- The target profile as data and as specification (DB-09's three parts; S6a): reachable from
-- this root, imported by nothing in the API, so the library-root gate sees it here.
import Effect4.Program.Profile
import Effect4.Program.HostBoundary
-- The provision algebra (docs/research/2026-09-04-provision-algebra.md): `Row.diff`, the
-- layer signature `LayerTy` and its laws, the layer term `LayerTerm` over `Eff` bodies,
-- `App` (`Effect.provide`), the build specification with its totality theorem, and the
-- compile-route runs of the docs deployment.
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
import Effect4.Program.Derived
import Effect4.Program.Wire
-- The application face: one module, the whole pipeline (type, print, compile,
-- run; the Schema syntax), answering syntax and never text. Import this.
import Effect4.Api
import Effect4.Api.HostSession
-- Foreign-source ingestion tables and constructed target spellings.
import Effect4.Ingest.Taxonomy
import Effect4.Codegen.Forms
import Effect4.Codegen.Styles

/-!
# Effect4

The application API and functional utilities for a closed, first-order effectful core.
The separate `Effect4.Laws` root imports the proof graph; this root never reaches it.
-/
