import Tools.View.Graph

/-! # Explicit point-to-mark lookup

This index retains the first occurrence of each mark and point attachment.
The checker owns validity; unchecked duplicate data remains deterministic.
Placement: `docs/research/2026-10-13-graph-defects-plan.md`, concept 7, R14.
-/

namespace Tools.View.GraphAttachment

def markTable (marks : List FlowMark) : KeyMap Key FlowMark :=
  KeyMap.firstBy FlowMark.key marks

def attachmentTable (attachments : List PortAttachment) : KeyMap Key PortAttachment :=
  KeyMap.firstBy PortAttachment.port attachments

structure Index where
  marks : KeyMap Key FlowMark
  attachments : KeyMap Key PortAttachment

def Index.of (l : Laid) : Index :=
  ⟨markTable l.marks.toList, attachmentTable l.attachments.toList⟩

def Index.findMark (ix : Index) (key : Key) : Option FlowMark := ix.marks.get? key

def Index.findAttachment (ix : Index) (port : Key) : Option PortAttachment :=
  ix.attachments.get? port

/-- The mark index answers the first declared mark. A contact-lookup helper. -/
theorem Index.findMark_of (l : Laid) (key : Key) :
    (Index.of l).findMark key = l.marks.toList.find? (fun m => decide (m.key = key)) :=
  KeyMap.get?_firstBy _ _ _

/-- The attachment index answers the first declared binding. A contact-lookup helper. -/
theorem Index.findAttachment_of (l : Laid) (port : Key) :
    (Index.of l).findAttachment port =
      l.attachments.toList.find? (fun a => decide (a.port = port)) :=
  KeyMap.get?_firstBy _ _ _

/-- Whether a point lies on its declared mark in logical coordinates. -/
def markContains (mark : FlowMark) (p : Placed) : Bool :=
  p.node.isNone && match mark with
  | .bar _ x0 x1 y => p.y == y && x0 ≤ Laid.middle p && Laid.middle p ≤ x1
  | .diamond _ x y => p.y == y && Laid.middle p == x

end Tools.View.GraphAttachment
