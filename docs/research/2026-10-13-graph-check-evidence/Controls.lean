import Tools.View.GraphCheck
import Tools.View.FlowSpecimen

namespace GraphCheckControls
open Tools.View Tools.View.GraphCheck

local instance : BEq (Except Refusal Unit) where
  beq a b := match a, b with
    | .ok (), .ok () => true
    | .error x, .error y => x == y
    | _, _ => false

private def node (key : Key) : GNode := ⟨key, key, "", false⟩

-- Empty input and layout remain valid.
#guard (input {}).isOk && (laid {}).isOk

-- Input positions and keys refuse at their actual locations.
#guard input { nodes := #[node "a"], edges := #[⟨"bad", 1, 0⟩] } ==
  .error ⟨.edge, 0, .source, .endpointOutside 1 1⟩
#guard input { nodes := #[node "a"], edges := #[⟨"bad", 0, 2⟩] } ==
  .error ⟨.edge, 0, .target, .endpointOutside 2 1⟩
#guard input { nodes := #[node "a", node ""] } == .error ⟨.node, 1, .key, .emptyKey⟩
#guard input { nodes := #[node "a", node "a"] } == .error ⟨.node, 1, .key, .duplicateKey⟩

private def valid : Laid :=
  { width := 16, height := 120,
    placed := #[{ key := "a", x := 0, y := 0, w := 8, node := some (node "a") },
      { key := "b", x := 0, y := 72, w := 8, node := some (node "b") }],
    routes := #[.down "forward" ["a", "b"], .back "back" "b" "a" 0, .loop "loop" "a"] }

-- Every route kind admits resolved keys.
#guard (laid valid).isOk

-- The old back-route check passes while its edge silently disappears.
#guard
  let bad : Graph := { nodes := #[node "a"], edges := #[⟨"bad", 1, 0⟩] }
  let l := bad.layout
  l.boxesApart && l.edgesDescend && l.dimsValid &&
    !(input bad).isOk && !(laid l).isOk

-- Down, back and loop references each refuse at their own endpoint.
#guard laid { valid with routes := #[.down "bad" ["a", "missing"]] } ==
  .error ⟨.route, 0, .vertex 1, .unresolvedKey "missing"⟩
#guard laid { valid with routes := #[.back "bad" "missing" "b" 0] } ==
  .error ⟨.route, 0, .source, .unresolvedKey "missing"⟩
#guard laid { valid with routes := #[.back "bad" "a" "missing" 0] } ==
  .error ⟨.route, 0, .target, .unresolvedKey "missing"⟩
#guard laid { valid with routes := #[.loop "bad" "missing"] } ==
  .error ⟨.route, 0, .vertex 0, .unresolvedKey "missing"⟩
#guard laid { valid with routes := #[.down "bad" ["a"]] } ==
  .error ⟨.route, 0, .length, .tooShort⟩

-- A repeated placed key would make lookup ambiguous.
#guard laid { valid with placed := valid.placed.push ({ key := "a", x := 0, y := 0, w := 8, node := some (node "a") } : Placed) } ==
  .error ⟨.placed, 2, .key, .duplicateKey⟩

-- Allocation bounds are independent from valid XML.
#guard laid { valid with width := -1 } == .error ⟨.canvas, 0, .width, .negative (-1)⟩
#guard laid { valid with placed := #[{ key := "a", x := 9, y := 0, w := 8 }] } ==
  .error ⟨.placed, 0, .right, .outside 17 16⟩
#guard laid { valid with regions := #[⟨"r", "region", 0, -1, 8, 8⟩] } ==
  .error ⟨.region, 0, .y, .negative (-1)⟩

-- A resolved downward route still needs downward allocation order.
#guard laid { valid with routes := #[.down "bad" ["b", "a"]] } ==
  .error ⟨.route, 0, .downward 0, .doesNotDescend⟩

private def siteText : Site → String
  | .canvas => "canvas" | .node => "node" | .edge => "edge"
  | .placed => "placed" | .route => "route" | .region => "region"

private def fieldText : Field → String
  | .key => "key" | .source => "source" | .target => "target"
  | .vertex i => s!"vertex[{i}]"
  | .width => "width" | .height => "height" | .x => "x" | .y => "y"
  | .right => "right" | .bottom => "bottom" | .length => "length"
  | .downward i => s!"downward[{i}]"

private def reasonText : Reason → String
  | .emptyKey => "empty key" | .duplicateKey => "duplicate key"
  | .endpointOutside p n => s!"position {p} outside {n} nodes"
  | .unresolvedKey k => s!"unresolved key {k}"
  | .tooShort => "fewer than two route keys"
  | .negative n => s!"negative allocation {n}"
  | .outside far bound => s!"allocation {far} exceeds {bound}"
  | .doesNotDescend => "allocated endpoints do not descend"

private def report (name : String) (l : Laid) : String :=
  match laid l with
  | .ok () => s!"PASS {name}"
  | .error r => s!"FAIL {name}: {siteText r.site}[{r.index}].{fieldText r.field}: {reasonText r.reason}"

#eval FlowSpecimen.programs.zip FlowSpecimen.frames |>.map fun ((name, _, _), page) =>
  match page.graph with
  | none => s!"FAIL {name}: no graph"
  | some graph => report name graph.laid

-- Empty source regions expose allocation that the former sign checks miss.
#guard
  let l := Flow.layout (Flow.ofProgram (.scoped (.gen .nil)))
  l.dimsValid && !(laid l).isOk

#eval report "empty scoped generator" (Flow.layout (Flow.ofProgram (.scoped (.gen .nil))))

end GraphCheckControls
