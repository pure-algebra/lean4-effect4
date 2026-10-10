import Tools.View.Specimen
import Tools.View.FlowSpecimen

open Tools.View

-- Finite evaluations on the existing layered-graph and program-flow viewer examples.
#guard Tools.View.Specimen.frames.all fun page =>
  (page.graph.map (·.laid.edgesDescend)).getD false
#guard Tools.View.FlowSpecimen.frames.all fun page =>
  (page.graph.map (·.laid.edgesDescend)).getD false

#eval do
  let graph := Tools.View.Specimen.frames.filterMap (fun (page : Page) => page.graph)
  let flow := Tools.View.FlowSpecimen.frames.filterMap (fun (page : Page) => page.graph)
  IO.println s!"SPECIMENS graph={graph.length}, passing={graph.filter (fun (panel : Panel) => panel.laid.edgesDescend) |>.length}; flow={flow.length}, passing={flow.filter (fun (panel : Panel) => panel.laid.edgesDescend) |>.length}"
