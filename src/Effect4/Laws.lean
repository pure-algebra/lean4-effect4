import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Machine.RefKernel
import Effect4.Laws.Machine.StoresLaws
import Effect4.Laws.Machine.Clock
import Effect4.Laws.Machine.Behaviour
import Effect4.Laws.Machine.Book
import Effect4.Laws.Machine.ContextValue
import Effect4.Laws.Machine.Handles
import Effect4.Laws.Machine.LiveStack
import Effect4.Laws.Machine.Scheduling
import Effect4.Laws.Machine.ScopeMachine
import Effect4.Laws.Machine.ScopeRestoration
import Effect4.Laws.Machine.StoresValue
import Effect4.Laws.Machine.Witnesses
import Effect4.Laws.Program.Denote
import Effect4.Laws.Program.Iter
import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.Folds.Looped
import Effect4.Laws.Program.Folds.Denote
import Effect4.Laws.Machine.Folds.Val
import Effect4.Laws.Program.LoopAgreement
import Effect4.Laws.Program.MeaningSound
import Effect4.Laws.Program.LoopSound
import Effect4.Laws.Program.TypedRun
import Effect4.Laws.Program.Agreement.Loop
import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Program.Sched
import Effect4.Laws.Program.DenoteR
import Effect4.Laws.Program.InterpR
import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Program.Typed
import Effect4.Laws.Program.ScopedTyping
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.Template
import Effect4.Laws.Program.Residual
import Effect4.Laws.Program.Decision
import Effect4.Laws.Program.HostBoundary
import Effect4.Laws.Api.HostSession
import Effect4.Laws.Api.Runner
import Effect4.Laws.Api.RunnerBytes
import Effect4.Laws.Api.Frontier
import Effect4.Laws.Api.Fuel
import Effect4.Laws.Api.Guard
import Effect4.Laws.Api.Supervision
import Effect4.Laws.Api.Codegen
import Effect4.Laws.Run
import Effect4.Laws.Program.Handles
import Effect4.Laws.Program.Means
import Effect4.Laws.Program.Intro
import Effect4.Laws.Program.Progress
import Effect4.Laws.Program.Simulation.Hooks
import Effect4.Laws.Program.Simulation.Walk
import Effect4.Laws.Program.Simulation.Fibers
import Effect4.Laws.Program.Simulation.Deliver
import Effect4.Laws.Program.Simulation.Actions
import Effect4.Laws.Program.Simulation.Evaluate
import Effect4.Laws.Program.Simulation.Pending
import Effect4.Laws.Program.Simulation.Drive
import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Program.ReasonsR
import Effect4.Laws.Program.Guard
import Effect4.Laws.Program.LayerSharing
import Effect4.Laws.Program.ReferenceTyping
import Effect4.Laws.Program.Hoisting
import Effect4.Laws.Program.HoistingTotal
import Effect4.Laws.Program.Invocation
import Effect4.Laws.Program.ValueModel
import Effect4.Laws.Program.LinkedRows
import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Program.Typing.Check
import Effect4.Laws.Program.Typing.CheckInversion
import Effect4.Laws.Program.Typing.CheckSound
import Effect4.Laws.Codegen.Forms
import Effect4.Laws.Codegen.Module
import Effect4.Laws.Auto.RuleSets
import Effect4.Laws.Program.AtomRules
import Effect4.Laws.Program.TyView
import Effect4.Laws.Program.Admits
import Effect4.Laws.Auto.Inversion
import Effect4.Laws.Auto.Census
import Effect4.Laws.Auto.Traversals
import Effect4.Laws.Auto.Exhaustive
import Effect4.Laws.Auto.Positions
import Effect4.Laws.Program.Typed.PositionGate
import Effect4.Laws.Program.Typed.TypedStateDecl
import Effect4.Laws.Auto.Frames
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Effects.Protocol
import Effect4.Laws.Program.Typed.Vocabulary
import Effect4.Laws.Program.Typed.TypedSources
import Effect4.Laws.Program.Typed.Sources
import Effect4.Laws.Program.Typed.State
import Effect4.Laws.Program.Typed.Frames
import Effect4.Laws.Codegen.Template
import Effect4.Laws.Codegen.Read
import Effect4.Laws.Codegen.ReadPrint
import Effect4.Laws.Codegen.PrintReadable
import Effect4.Laws.Api.ModuleReadable
import Effect4.Laws.Store.CanonicalSpec
import Effect4.Laws.Schema.Codec
import Effect4.Laws.Schema.Image
import Effect4.Laws.Program.Authoring
import Effect4.Laws.Program.Authoring.Lifts
import Effect4.Laws.Program.Authoring.Rows
import Effect4.Laws.Program.Authoring.Forms
import Effect4.Laws.Program.Authoring.Sugar
import Effect4.Laws.Program.Authoring.Loops
import Effect4.Laws.Program.Author
import Effect4.Laws.Machine.Refinement
import Effect4.Laws.Program.Typed.World
import Effect4.Laws.Program.Typed.Contracts
import Effect4.Laws.Program.Typed.ForkSource
import Effect4.Laws.Program.Guard.TraceOrigin
import Effect4.Laws.Machine.Handshake
import Effect4.Laws.Program.Guard.Handshake

import Effect4.Laws.Program.Folds.Checker
import Effect4.Laws.Program.Folds.Projections
import Effect4.Laws.Program.Folds.Provision
import Effect4.Laws.Program.Folds.Representation
import Effect4.Laws.Program.Folds.Straight
import Effect4.Laws.Program.Folds.Term
import Effect4.Laws.Program.Folds.Ty
import Effect4.Laws.Machine.Folds.Stores
import Effect4.Laws.Store.Folds.Val
import Effect4.Laws.Program.Typing.FoldAgreement

/-!
# Effect4 proof graph

The machine and program judgments, simulation, composition and execution laws.
These modules continue their definition modules' namespaces; the module paths
separate build targets. `import Effect4` never reaches this root.
-/

#typed_state_obligations Effect4.Machine.M1.DeferredWanted ceiling 0
  using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel, Effect4.Fibers]) (add safe forward [Effect4.Machine.Refinement.factors_trans])
#typed_state_obligations Effect4.Machine.M1Clock ceiling 1
  using aesop (rule_sets := [Effect4.Stores, Effect4.StoreKernel, Effect4.Fibers])
