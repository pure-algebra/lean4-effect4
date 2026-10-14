import Tools.View.GraphAttachment
import Tools.View.FlowSpecimen
import ProofGraph.AxiomAudit

/-! Finite controls for explicit attachment lookup and the current Flow producers.

Placement: graph-defects plan, concept 7, R14's contact inspection.
The readers use existing index laws. The guards establish finite observations only.
-/

open Tools.View Tools.View.GraphAttachment

namespace GraphAttachmentProbe

def point (key : Key) (x y : Int) : Placed :=
  { key, x := x - CELL, y, w := 2 * CELL }

def duplicateLayout : Laid :=
  { marks := #[.bar "mark→left->right" 10 30 40,
      .diamond "mark→left->right" 999 999, .diamond "mark→left" 20 40],
    attachments := #[⟨"port→a->b", "mark→left->right"⟩,
      ⟨"port→a->b", "mark→left"⟩, ⟨"port→a", "mark→left"⟩] }

#guard (Index.of duplicateLayout).findMark "mark→left->right" =
  some (.bar "mark→left->right" 10 30 40)
#guard (Index.of duplicateLayout).findMark "mark→left" = some (.diamond "mark→left" 20 40)
#guard (Index.of duplicateLayout).findMark "mark→left->missing" = none
#guard (Index.of duplicateLayout).findAttachment "port→a->b" =
  some ⟨"port→a->b", "mark→left->right"⟩
#guard (Index.of duplicateLayout).findAttachment "port→a" = some ⟨"port→a", "mark→left"⟩
#guard (Index.of duplicateLayout).findAttachment "port→a->missing" = none
#guard (Index.of {}).findMark "missing" = none
#guard (Index.of {}).findAttachment "missing" = none

-- Readers instantiate the lookup laws at conflicting duplicate metadata.
example : (Index.of duplicateLayout).findMark "mark→left->right" =
    duplicateLayout.marks.toList.find? (fun m => decide (m.key = "mark→left->right")) :=
  Index.findMark_of duplicateLayout "mark→left->right"
example : (Index.of duplicateLayout).findAttachment "port→a->b" =
    duplicateLayout.attachments.toList.find? (fun a => decide (a.port = "port→a->b")) :=
  Index.findAttachment_of duplicateLayout "port→a->b"

-- Bar contact includes both lips. Point width and growth do not change its center.
#guard markContains (.bar "bar" 10 30 40) (point "left" 10 40)
#guard markContains (.bar "bar" 10 30 40) (point "middle" 20 40)
#guard markContains (.bar "bar" 10 30 40) (point "right" 30 40)
#guard !markContains (.bar "bar" 10 30 40) (point "outside-left" 9 40)
#guard !markContains (.bar "bar" 10 30 40) (point "outside-right" 31 40)
#guard !markContains (.bar "bar" 10 30 40) (point "wrong-height" 20 41)
#guard markContains (.bar "zero-span" 20 20 40) (point "singleton" 20 40)
#guard !markContains (.bar "reversed" 30 10 40) (point "middle" 20 40)
#guard markContains (.bar "bar" 10 30 40) { (point "wide" 20 40) with w := 900, grow := 0 }

#guard markContains (.diamond "diamond" 20 40) (point "tip" 20 40)
#guard !markContains (.diamond "diamond" 20 40) (point "off-center" 21 40)
#guard !markContains (.diamond "diamond" 20 40) (point "wrong-height" 20 39)
#guard !markContains (.bar "bar" 10 30 40)
  { key := "node", x := 12, y := 40, w := 16, node := some { key := "node", line1 := "" } }
#guard !markContains (.diamond "diamond" 20 40)
  { key := "node", x := 12, y := 40, w := 16,
    node := some { key := "node", line1 := "" }, grow := 0 }

-- This observation checks every explicit binding, including unindexed duplicates.
def contactsAtRest (l : Laid) : Bool :=
  l.attachments.toList.all fun a =>
    match l.find a.port, (Index.of l).findMark a.mark with
    | some p, some m => markContains m p
    | _, _ => false

def attachedLayout : Laid :=
  { placed := #[point "port→left->right" 20 40],
    marks := #[.bar "mark→left->right" 10 30 40],
    attachments := #[⟨"port→left->right", "mark→left->right"⟩] }

#guard contactsAtRest attachedLayout
#guard !contactsAtRest { attachedLayout with placed := #[] }
#guard !contactsAtRest { attachedLayout with marks := #[] }
#guard !contactsAtRest { attachedLayout with
  attachments := #[⟨"port→left", "mark→left->right"⟩] }
#guard !contactsAtRest { attachedLayout with
  attachments := #[⟨"port→left->right", "mark→left"⟩] }

-- The producer controls also reject duplicate keys and duplicate port bindings.
def producerMetadata (l : Laid) : Bool :=
  contactsAtRest l &&
  decide (l.marks.toList.Pairwise (fun a b => a.key ≠ b.key)) &&
  decide (l.attachments.toList.Pairwise (fun a b => a.port ≠ b.port)) &&
  l.marks.toList.all (fun m => l.attachments.toList.any (fun a => a.mark == m.key)) &&
  l.placed.toList.all (fun p => p.grow == 1000) &&
  l.routes.toList.all (fun r => r.reveal == 1000)

#guard producerMetadata attachedLayout
#guard !producerMetadata { attachedLayout with
  attachments := attachedLayout.attachments ++ attachedLayout.attachments }
#guard !producerMetadata { attachedLayout with marks := attachedLayout.marks ++ attachedLayout.marks }

-- Keep generated source text inside guards, rather than strict battery declarations.
#guard FlowSpecimen.frames.length == FlowSpecimen.programs.length
#guard FlowSpecimen.frames.all fun p => match p.graph with
  | some g => producerMetadata g.laid
  | none => false
#guard FlowSpecimen.frames.any fun p => match p.graph with
  | some g => !g.laid.attachments.isEmpty
  | none => false

#axiom_audit checked Tools.View.GraphAttachment

end GraphAttachmentProbe

def main : IO Unit := do
  let mut attachments := 0
  let mut marks := 0
  for ((name, _, _), p) in FlowSpecimen.programs.zip FlowSpecimen.frames do
    match p.graph with
    | none => throw (IO.userError "Flow specimen has no graph")
    | some g =>
      attachments := attachments + g.laid.attachments.size
      marks := marks + g.laid.marks.size
      IO.println s!"{name}: {g.laid.attachments.size} attachments, {g.laid.marks.size} marks"
  IO.println s!"graph-attachment: {FlowSpecimen.frames.length} frames, \
    {attachments} attachments, {marks} marks pass"
  IO.println "graph-attachment: first lookup, contact boundaries, nodes, arbitrary keys controls pass"
