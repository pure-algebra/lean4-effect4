import Tools.View.Specimen
import Tools.View.FlowSpecimen
import Tools.View.Tokens
import ProofGraph.AxiomAudit

/-! Finite graph admission controls. These observe rendering data, not machine execution. -/

open Tools.View

private def pair : Graph :=
  { nodes := #[⟨"a", "A", "", false⟩, ⟨"b", "B", "", false⟩],
    edges := #[⟨"first", 0, 1⟩, ⟨"second", 0, 1⟩] }

private def refusalIs (g : Graph) (site : GraphCheck.Site) (index : Nat)
    (field : GraphCheck.Field) (reason : GraphCheck.Reason) : Bool :=
  match GraphLayout.checked g with
  | .error found => found == ⟨site, index, field, reason⟩
  | .ok _ => false

#guard (GraphLayout.checked {}).isOk
#guard match GraphLayout.checked pair with
  | .ok result => result.value.routes.toList.map (·.key) == ["first", "second"]
  | .error _ => false
#guard refusalIs { pair with edges := #[⟨"", 0, 1⟩] } .edge 0 .key .emptyKey
#guard refusalIs { pair with edges := #[⟨"repeat", 0, 1⟩, ⟨"repeat", 1, 0⟩] }
  .edge 1 .key .duplicateKey
#guard refusalIs { pair with edges := #[⟨"bad", 2, 0⟩] }
  .edge 0 .source (.endpointOutside 2 2)
#guard refusalIs { pair with edges := #[⟨"bad", 0, 2⟩] }
  .edge 0 .target (.endpointOutside 2 2)

-- Identity checks precede endpoint checks, irrespective of edge order.
#guard refusalIs { pair with edges := #[⟨"repeat", 2, 0⟩, ⟨"repeat", 0, 1⟩] }
  .edge 1 .key .duplicateKey

private def generatedCollision : Graph :=
  { nodes := #[⟨"a", "A", "", false⟩, ⟨"long@1", "B", "", false⟩,
      ⟨"c", "C", "", false⟩],
    edges := #[⟨"ab", 0, 1⟩, ⟨"bc", 1, 2⟩, ⟨"long", 0, 2⟩] }

#guard (GraphCheck.input generatedCollision).isOk
#guard match GraphLayout.checked generatedCollision with
  | .error found => found.site == .placed && found.field == .key &&
      found.reason == .duplicateKey
  | .ok _ => false

#guard match Specimen.checkedFrames with
  | .ok frames => frames.map (·.graph.map (·.laid)) ==
      Specimen.frames.map (·.graph.map (·.laid))
  | .error _ => false

-- Allocation reserves the self-loop control hull; painted stroke margins remain separate.
private def selfLoop : Graph :=
  { nodes := #[⟨"a", "A", "", false⟩], edges := #[⟨"loop", 0, 0⟩] }

#guard (GraphLayout.checked selfLoop).isOk
#guard let value := selfLoop.layout
  match value.placed[0]? with
  | some p => p.x + p.w + 2 * LOOP_REACH ≤ value.width
  | none => false

#axiom_audit Tools.View.GraphCheck

def main : IO Unit := do
  let .ok frames := Specimen.checkedFrames | throw (IO.userError "specimen admission failed")
  IO.println s!"checked specimen frames: {frames.length}"
  let admitted := FlowSpecimen.frames.filter fun p =>
    p.graph.any fun g => (GraphCheck.laid g.laid).isOk
  IO.println s!"flow allocation controls: {admitted.length}/{FlowSpecimen.frames.length}"
  if admitted.length != FlowSpecimen.frames.length then
    throw (IO.userError "flow allocation control failed")
  IO.println "identity, parallel edge, first refusal, generated point collision controls: pass"
  IO.println "self-loop allocation control: full control hull fits the canvas"
