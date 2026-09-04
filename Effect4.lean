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
import Effect4.Flow.Region
import Effect4.Flow.Decision
import Effect4.Flow.Interrupt
import Effect4.Semantics.Cause
import Effect4.Semantics.Exit
import Effect4.Semantics.Frontier
import Effect4.Semantics.Runs
import Effect4.Semantics.Fuel
import Effect4.Semantics.PlanInversion
import Effect4.Semantics.Denotation
import Effect4.Semantics.RegionDenotation
import Effect4.Semantics.RegionTotal
import Effect4.Semantics.RegionSafety
import Effect4.Semantics.Approximation
import Effect4.Semantics.Observation
import Effect4.Semantics.Equivalence
import Effect4.Semantics.Logic
import Effect4.Schema.Payload
import Effect4.Schema.Representation
import Effect4.Schema.Annotations
import Effect4.Schema.EffectfulField
import Effect4.Schema.Document
import Effect4.Schema.Check
import Effect4.Schema.Authoring
import Effect4.Schema.Value
import Effect4.Schema.Getter
import Effect4.Schema.Transformation
import Effect4.Schema.Codec
import Effect4.Schema.Registry
import Effect4.Schema.Foreign
import Effect4.Context.Key
import Effect4.Context.ContextFamily
import Effect4.Layer.LayerFamily
import Effect4.Runtime.Scope
import Effect4.Runtime.ScopeFamily
import Effect4.Runtime.ScopeMachine
import Effect4.Runtime.ScopeRestoration
import Effect4.Runtime.Runtime
import Effect4.Runtime.LiveStack
-- Packet D4 fence B. Above both Semantics and Runtime: it imports the frame
-- machine. See `test/contracts/frame-simulation.contract.md` ruling 5.
import Effect4.Semantics.FrameSimulation
import Effect4.Concurrency.Fiber
import Effect4.Concurrency.Scheduler
import Effect4.Concurrency.Interrupt
import Effect4.Concurrency.Supervision
import Effect4.Stateful.RefFamily
import Effect4.Stateful.DeferredFamily
import Effect4.Target.TypeScript.EffectV4
import Effect4.Target.TypeScript.Trace
import Effect4.Target.TypeScript.ScriptFlow
import Effect4.Target.TypeScript.ScriptDenotation
import Effect4.Target.TypeScript.Skeleton
import Effect4.Target.TypeScript.FlowLower
import Effect4.Target.TypeScript.RegionLower
import Effect4.Target.TypeScript.StructuredLower
import Effect4.Target.TypeScript.StructureLaws
import Effect4.Target.TypeScript.StructureOrder
import Effect4.Target.TypeScript.StructureDominators
import Effect4.Target.TypeScript.StructureSemantics
import Effect4.Target.TypeScript.SkeletonSemantics
import Effect4.Target.TypeScript.Lower
import Effect4.Target.TypeScript.Schema
import Effect4.Target.TypeScript.EffectfulField
import Effect4.Target.TypeScript.Simulation
-- Packet D4, the finalizer half. Above Runtime, Flow and the trace bridge:
-- it relates the region runner to the frame machine under a mask.
import Effect4.Semantics.RegionSimulation
-- The reference machine (docs/research/2026-09-03-deep-plan.md): one
-- program-carrying fiber machine over the rc.112 frames, the stores it drives,
-- the witnesses over them, the fork-profile compile, and the Context and Layer
-- models. Promoted from the `workshop/Deep` spike on 2026-09-04; the old
-- `FiberState`/`Supervision.Fiber`/`Scheduler.Machine` carriers are now its
-- computed projections and retire with the witnesses phase.
import Effect4.Deep.Fibers
import Effect4.Deep.Clauses
import Effect4.Deep.Stores
import Effect4.Deep.Witnesses
import Effect4.Deep.ForkFlow
import Effect4.Deep.Context
import Effect4.Deep.Layer
-- The middle tier (2026-09-04): architecture views as Effect Schema documents
-- with payloads projected from the proof carriers, the JSON canonical form that
-- makes schemas store content, the structural acceptance checker, and the
-- pinned standard library as store entries with checked links to the model.
import Effect4.Arch.JsonCanonical
import Effect4.Arch.Accepts
import Effect4.Arch.Views
import Effect4.StdLib.Entry
import Effect4.StdLib.Rc112
import Effect4.StdLib.Links
import Effect4.Meta.Derive

/-!
# Effect4

Standalone Lean library for a closed, first-order, effectful core and its
proof-bearing bridges. The semantic modules are introduced only after their
contract packets and counterexample batteries are frozen.
-/
