import Tools.View.GraphAttachment

/-!
# Mark and port motion from explicit incidence

Preparation retains mark and region matches and explicit port attachments.
The production sampler aligns attached points with the sampled mark.
Named tool laws serve concept 7 and R14 view navigation.
Placement: `docs/research/2026-10-13-graph-attachment-motion-plan.md`.
Missing metadata establishes no attachment observation.
-/

namespace Tools.View.GraphAttachmentMotion

/-- Bound mark movement to the endpoint interval, independently of box growth. -/
def progress (moved : Int) : Int := max 0 (min 1000 moved)

/-- A retained mark match, including a removed mark with no target replacement. -/
structure MarkEntry where
  next : FlowMark
  old : Option FlowMark

/-- Sample a kept mark's coordinates; different constructors use the target form. -/
def MarkEntry.sample (entry : MarkEntry) (moved : Int) : FlowMark :=
  match entry.old, entry.next with
  | some (.bar _ a b y), .bar key c d z =>
      .bar key (lerp a c moved) (lerp b d moved) (lerp y z moved)
  | some (.diamond _ x y), .diamond key u v => .diamond key (lerp x u moved) (lerp y v moved)
  | _, mark => mark

/-- A retained region match. -/
structure RegionEntry where
  next : Region
  old : Option Region

/-- Interpolate a kept region's allocated origin and size. -/
def RegionEntry.sample (entry : RegionEntry) (moved : Int) : Region :=
  match entry.old with
  | none => entry.next
  | some old =>
    { entry.next with
      x := lerp old.x entry.next.x moved
      y := lerp old.y entry.next.y moved
      w := lerp old.w entry.next.w moved
      h := lerp old.h entry.next.h moved }

/-- First-key region lookup. -/
def regionIndex (regions : List Region) : KeyMap Key Region :=
  KeyMap.firstBy Region.key regions

/-- Retained attachment data for one point key. -/
structure Dock where
  mark : Key
  reference : FlowMark
  remap : Bool

/-- Prepared mark, region, and point incidence data. -/
structure Prepared where
  marks : List MarkEntry
  regions : List RegionEntry
  attachments : List PortAttachment
  docks : KeyMap Key (Option Dock)

/-- Keep target incidence first; retain source incidence where the target has no port entry. -/
def attachments (a b : Laid) : List PortAttachment :=
  b.attachments.toList ++ a.attachments.toList.filter fun old =>
    !(b.attachments.toList.any fun next => next.port == old.port)

/-- Prepare mark matches, region matches, and explicit point attachment policies once. -/
def prepare (a b : Laid) : Prepared :=
  let old := GraphAttachment.Index.of a
  let next := GraphAttachment.Index.of b
  let oldMarks := old.marks
  let nextMarks := next.marks
  let oldRegions := regionIndex a.regions.toList
  let nextRegions := regionIndex b.regions.toList
  let oldPlaces := Laid.Ix.of a
  let nextPlaces := Laid.Ix.of b
  let incidence := attachments a b
  let docks := incidence.foldr (fun attachment table =>
    let target := (next.findAttachment attachment.port).isSome
    let reference := if target then nextMarks.get? attachment.mark else oldMarks.get? attachment.mark
    let kept := (oldPlaces.find attachment.port).isSome &&
      (nextPlaces.find attachment.port).isSome
    table.insert attachment.port (reference.map fun mark => ⟨attachment.mark, mark, !kept⟩)) {}
  { marks := (a.marks.toList.filter fun old => (nextMarks.get? old.key).isNone).map
        (fun mark => ⟨mark, none⟩) ++
      b.marks.toList.map (fun mark => ⟨mark, oldMarks.get? mark.key⟩)
    regions := (a.regions.toList.filter fun old => (nextRegions.get? old.key).isNone).map
        (fun region => ⟨region, none⟩) ++
      b.regions.toList.map (fun region => ⟨region, oldRegions.get? region.key⟩)
    attachments := incidence, docks }

/-- Align a point's centre with its current mark; entering and leaving points map relative position.
Nodes retain their placement, even if unchecked metadata names them. -/
def dock (attachment : Dock) (current : FlowMark) (point : Placed) : Placed :=
  if point.node.isSome then point else
  match current with
  | .diamond _ x y => { point with x := x - CELL, y }
  | .bar _ x0 x1 y =>
    let centre := if attachment.remap then
      match attachment.reference with
      | .bar _ a b _ => if a < b then
          x0 + (Laid.middle point - a) * (x1 - x0) / (b - a)
        else Laid.middle point
      | .diamond _ _ _ => (x0 + x1) / 2
      else Laid.middle point
    { point with x := max x0 (min x1 centre) - CELL, y }

/-- Read explicit incidence against the current mark table. -/
def applyDock (docks : KeyMap Key (Option Dock)) (marks : KeyMap Key FlowMark) (point : Placed) : Placed :=
  match (docks.get? point.key).bind id with
  | none => point
  | some attachment => match marks.get? attachment.mark with
    | none => point
    | some current => dock attachment current point

/-- An aligned point lies on its current ordered bar.
Local preservation for production sampling; endpoint metadata validity remains a separate judgment. -/
theorem dock_bar (attachment : Dock) (key : Key) (x0 x1 y : Int) (point : Placed)
    (hn : point.node = none) (ordered : x0 ≤ x1) :
    (dock attachment (.bar key x0 x1 y) point).node = none ∧
    (dock attachment (.bar key x0 x1 y) point).y = y ∧
    x0 ≤ Laid.middle (dock attachment (.bar key x0 x1 y) point) ∧
    Laid.middle (dock attachment (.bar key x0 x1 y) point) ≤ x1 := by
  simp only [dock, hn, Option.isSome_none, Bool.false_eq_true, if_false, Laid.middle,
    Int.sub_add_cancel, true_and]
  exact ⟨Int.le_max_left _ _, Int.max_le.mpr ⟨ordered, Int.min_le_left _ _⟩⟩

/-- An aligned point lies at its current diamond centre.
Local preservation for production sampling; the caller supplies resolved incidence. -/
theorem dock_diamond (attachment : Dock) (key : Key) (x y : Int) (point : Placed)
    (hn : point.node = none) :
    (dock attachment (.diamond key x y) point).node = none ∧
    (dock attachment (.diamond key x y) point).y = y ∧
    Laid.middle (dock attachment (.diamond key x y) point) = x := by
  simp only [dock, hn, Option.isSome_none, Bool.false_eq_true, if_false, Laid.middle,
    Int.sub_add_cancel, true_and]

end Tools.View.GraphAttachmentMotion
