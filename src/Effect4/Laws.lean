-- 1. `store-typing`: Store Typing
import Effect4.Laws.Library.Stream.Definitions
import Effect4.Laws.Library.Stream.Ops
import Effect4.Laws.Library.Stream.Typing
import Effect4.Laws.Library.SynchronizedRef.Ops
import Effect4.Laws.Machine.AnswerFlowActions
import Effect4.Laws.Machine.AnswerFlowCausePop
import Effect4.Laws.Machine.ContextValue
import Effect4.Laws.Machine.StoresValue
import Effect4.Laws.Program.AtomRules
import Effect4.Laws.Program.Handles
import Effect4.Laws.Program.PlaceFunding.Flow
import Effect4.Laws.Program.TyDeclsInhabited
import Effect4.Laws.Program.Typed.ForkSource
import Effect4.Laws.Program.Typed.Frames
import Effect4.Laws.Program.Typed.ListFold
import Effect4.Laws.Schema.Modeled

-- 2. `residual-program-typing`: Residual Program Typing
import Effect4.Laws.Codegen.Forms
import Effect4.Laws.Program.SoundAnySignature
import Effect4.Laws.Program.Typed.AdmittedSource
import Effect4.Laws.Program.Typing.Check

-- 3. `scope-lifetime-finalization`: Scope Lifetime & Finalization
import Effect4.Laws.Api.MaskRuns
import Effect4.Laws.Machine.ScopeRestoration
import Effect4.Laws.Program.FinalizerSourceHistory
import Effect4.Laws.Program.LedgerFinalizer
import Effect4.Laws.Program.ReleaseCustody.Execution
import Effect4.Laws.Program.StackRegionRun

-- 4. `reactive-scheduling`: Reactive Scheduling
import Effect4.Laws.Api.Supervision
import Effect4.Laws.Library.Queue.Invariant
import Effect4.Laws.Machine.Descent
import Effect4.Laws.Machine.LiveStack
import Effect4.Laws.Machine.RaceFirst
import Effect4.Laws.Machine.Scheduling
import Effect4.Laws.Machine.Witnesses
import Effect4.Laws.Program.Guard.Handshake

-- 5. `exact-codecs`: Exact Codecs
import Effect4.Laws.Api.ModuleReadable
import Effect4.Laws.Codegen.Mask
import Effect4.Laws.Program.ValueModel
import Effect4.Laws.Schema.DocumentJson
import Effect4.Laws.Store.CanonicalSpec
import Effect4.Laws.Store.Results
import Effect4.Laws.Tool.CodecProfile
import Effect4.Laws.Tool.Wire

-- 6. `subtyping-algebra`: Subtyping Algebra
import Effect4.Laws.Api.Formation
import Effect4.Laws.Codegen.TargetOrder
import Effect4.Laws.Program.Polarity
import Effect4.Laws.Program.Typing.Closed
import Effect4.Laws.Slice.Lattice

-- 7. `initial-algebras-folds`: Initial Algebras & Folds
import Effect4.Laws.Data.ListRelConnectors
import Effect4.Laws.Effects.Sum
import Effect4.Laws.Machine.Folds.Stores
import Effect4.Laws.Machine.Folds.Val
import Effect4.Laws.Program.Authoring.Atoms
import Effect4.Laws.Program.Authoring.Forms
import Effect4.Laws.Program.FiberSumConnect
import Effect4.Laws.Program.FillSet
import Effect4.Laws.Program.Folds.Looped
import Effect4.Laws.Program.Folds.Projections
import Effect4.Laws.Program.Folds.Provision
import Effect4.Laws.Program.Folds.Representation
import Effect4.Laws.Program.Folds.Term
import Effect4.Laws.Program.Folds.TyCache
import Effect4.Laws.Program.SketchAdmission
import Effect4.Laws.Program.SourceDocument
import Effect4.Laws.Program.Typing.FoldAgreement
import Effect4.Laws.Store.Folds.Val

-- 8. `context-requirements`: Context Requirements
import Effect4.Laws.Program.BuildTotal
import Effect4.Laws.Program.LayerSharing
import Effect4.Laws.Program.ScopedTyping
import Effect4.Laws.Program.Typed.ProtocolObligations

-- 9. `host-session-protocol`: Host Session Protocol
import Effect4.Laws.Api.Guard
import Effect4.Laws.Api.LiveRecord
import Effect4.Laws.Api.RunnerBytes
import Effect4.Laws.Api.Session
import Effect4.Laws.Program.Handler
import Effect4.Laws.Program.HostBoundary
import Effect4.Laws.Program.Invocation
import Effect4.Laws.Run.CallMap
import Effect4.Laws.Run.Outcome
import Effect4.Laws.Run.Runner
import Effect4.Laws.Tool.Exchange

-- 10. `translation-simulation`: Translation & Simulation
import Effect4.Laws.Api.AuthorBuild
import Effect4.Laws.Api.Fuel
import Effect4.Laws.Api.Preview
import Effect4.Laws.Library.Channel.Protocol
import Effect4.Laws.Library.Latch.Registration
import Effect4.Laws.Library.PartitionedSemaphore.Steps
import Effect4.Laws.Library.Pool.Ops
import Effect4.Laws.Library.PubSub.Steps
import Effect4.Laws.Library.Queue.Execution
import Effect4.Laws.Library.Ref.Cache
import Effect4.Laws.Library.Stream.Array
import Effect4.Laws.Library.Stream.Steps
import Effect4.Laws.Machine.IntegerProfile
import Effect4.Laws.Machine.Refinement
import Effect4.Laws.Program.DenoteCtl
import Effect4.Laws.Program.DenoteRowsAppend
import Effect4.Laws.Program.IterLimit
import Effect4.Laws.Program.ProfileSupport
import Effect4.Laws.Program.ScopeMarkers
import Effect4.Laws.Program.StoreComodel
import Effect4.Laws.Program.Typed.Results
import Effect4.Laws.Program.TypedRun
import Effect4.Laws.Program.ValidatedBlocks
import Effect4.Laws.Run.CallTree
import Effect4.Laws.Store.Recovery

-- The author's entry module, `#explain`, and the instruments: commands and tactics, no claim
import Effect4.Laws.Author
import Effect4.Laws.Author.Explain
import Effect4.Laws.Auto.AnswerGate
import Effect4.Laws.Auto.BankCensus
import Effect4.Laws.Auto.Exhaustive
import Effect4.Laws.Auto.KernelRfl
import Effect4.Laws.Machine.Clock

/-!
# Effect4 proof graph

The machine and program judgments, simulation, composition and execution laws. The root names the
law graph's tops, the modules that no other law module imports, under the concept of
`docs/core/semantics.md` that their theorems serve; each top imports the rest. `make build` adds a
new top here (`scripts/wire-roots.py`), and the semantics report places each theorem
(`generated/semantics.md`). These modules continue their definition modules' namespaces; the
module paths separate build targets. `import Effect4` never reaches this root.
-/
