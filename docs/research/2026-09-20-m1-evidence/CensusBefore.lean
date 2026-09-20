import Test.Api.HostSessionContract
import Test.Api.KeyedHostContract
import Test.Audit.PositionCensus
import Test.Audit.RuntimeCoverage
import Test.Machine.Fuzz
import Test.Machine.Runtime.StoresLawsContract
import Test.Program.RuntimeRShapesContract
import Effect4.Api.HostSession
import Effect4.Laws.Api.HostSession
import Effect4.Laws.Auto.Frames
import Effect4.Laws.Auto.RuleSets
import Effect4.Laws.Machine.Handles
import Effect4.Laws.Machine.StoresLaws
import Effect4.Laws.Machine.Witnesses
import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.FrameOwned
import Effect4.Laws.Program.Guard.NativeState
import Effect4.Laws.Program.Guard.RaceSites
import Effect4.Laws.Program.Guard.Settle
import Effect4.Laws.Program.Handles.Hooks
import Effect4.Laws.Program.InterpR
import Effect4.Laws.Program.LayerSharing
import Effect4.Laws.Program.Simulation.Actions
import Effect4.Laws.Program.Simulation.Deliver
import Effect4.Laws.Program.Simulation.Drive
import Effect4.Laws.Program.Simulation.Evaluate
import Effect4.Laws.Program.Simulation.Hooks
import Effect4.Laws.Program.Typed.Frames
import Effect4.Laws.Program.Typed.Sources
import Effect4.Laws.Run
import Effect4.Machine.Stores
import Effect4.Program.Admit
import Effect4.Program.Compile
import OCaml5.Lcnf.Externs
import OCaml5.Lcnf.Translate
import OCaml5.Lcnf.Types
import OCaml5.Tools.CasGoldens
import Effect4.Laws.Auto.Census

#auto_census Test.Api.HostSessionContract using aesop
#auto_census Test.Api.KeyedHostContract using aesop
#auto_census Test.Audit.PositionCensus using aesop
#auto_census Test.Audit.RuntimeCoverage using aesop
#auto_census Test.Machine.Fuzz using aesop
#auto_census Test.Machine.Runtime.StoresLawsContract using aesop
#auto_census Test.Program.RuntimeRShapesContract using aesop
#auto_census Effect4.Api.HostSession using aesop
#auto_census Effect4.Laws.Api.HostSession using aesop
#auto_census Effect4.Laws.Auto.Frames using aesop
#auto_census Effect4.Laws.Auto.RuleSets using aesop
#auto_census Effect4.Laws.Machine.Handles using aesop
#auto_census Effect4.Laws.Machine.StoresLaws using aesop
#auto_census Effect4.Laws.Machine.Witnesses using aesop
#auto_census Effect4.Laws.Program.Agreement.Machine using aesop
#auto_census Effect4.Laws.Program.Guard.Core using aesop
#auto_census Effect4.Laws.Program.Guard.FrameOwned using aesop
#auto_census Effect4.Laws.Program.Guard.NativeState using aesop
#auto_census Effect4.Laws.Program.Guard.RaceSites using aesop
#auto_census Effect4.Laws.Program.Guard.Settle using aesop
#auto_census Effect4.Laws.Program.Handles.Hooks using aesop
#auto_census Effect4.Laws.Program.InterpR using aesop
#auto_census Effect4.Laws.Program.LayerSharing using aesop
#auto_census Effect4.Laws.Program.Simulation.Actions using aesop
#auto_census Effect4.Laws.Program.Simulation.Deliver using aesop
#auto_census Effect4.Laws.Program.Simulation.Drive using aesop
#auto_census Effect4.Laws.Program.Simulation.Evaluate using aesop
#auto_census Effect4.Laws.Program.Simulation.Hooks using aesop
#auto_census Effect4.Laws.Program.Typed.Frames using aesop
#auto_census Effect4.Laws.Program.Typed.Sources using aesop
#auto_census Effect4.Laws.Run using aesop
#auto_census Effect4.Machine.Stores using aesop
#auto_census Effect4.Program.Admit using aesop
#auto_census Effect4.Program.Compile using aesop
#auto_census OCaml5.Lcnf.Externs using aesop
#auto_census OCaml5.Lcnf.Translate using aesop
#auto_census OCaml5.Lcnf.Types using aesop
#auto_census OCaml5.Tools.CasGoldens using aesop
