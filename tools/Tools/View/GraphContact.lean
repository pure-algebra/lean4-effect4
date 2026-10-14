import Tools.View.GraphAttachment

/-! # Logical contacts for graph inspection and styling

Contacts name their route occurrence, endpoint, and declared surface without decoding keys.
Points follow the rendered route centreline and the organic bar offset.
They support selection and crops; they do not measure the painted perimeter or text ink.
Occurrence indices belong to one layout snapshot, not to arbitrary route reorderings.
-/

namespace Tools.View.GraphContact

inductive Side where
  | source | target
  deriving DecidableEq, Repr

inductive Surface where
  | node | point | bar (mark : Key) | diamond (mark : Key)
  deriving DecidableEq, Repr

structure Contact where
  route : Key
  occurrence : Nat
  side : Side
  item : Key
  surface : Surface
  point : Int × Int
  docked : Bool
  deriving DecidableEq, Repr

/-- The declared surface, independent of spelling and of the route's reveal. -/
def surface (ix : GraphAttachment.Index) (p : Placed) : Surface :=
  if p.node.isSome then .node else
  match (ix.findAttachment p.key).bind (fun a => ix.findMark a.mark) with
  | some (.bar key ..) => .bar key
  | some (.diamond key ..) => .diamond key
  | none => .point

private def endpoints : Route → Option (Key × Key)
  | .down _ ks .. => do return (← ks.head?, ← ks.getLast?)
  | .back _ a b .. => some (a, b)
  | .loop _ a .. => some (a, a)

/-- Logical contacts for the visible part of a route. An unfinished target is a moving tip. -/
def route (L : Look) (l : Laid) (places : Laid.Ix) (attachments : GraphAttachment.Index)
    (occurrence : Nat) (r : Route) : List Contact := Id.run do
  let some (a, b) := endpoints r | return []
  let some source := places.find a | return []
  let some target := places.find b | return []
  let cs := Laid.segments L places.find l.routeWidth r
  let budget : Int := (cs.map (·.size)).foldl (· + ·) 0 * r.reveal / 1000
  let shown := Laid.revealed cs budget
  let some first := shown.head? | return []
  let some last := shown.getLast? | return []
  let whole := 1000 ≤ r.reveal
  let organic := match r with | .down .. => L.organic.trunk != 0 | _ => false
  let onSurface (p : Placed) :=
    (p.node.isSome && p.grow != 0) || places.onBar p
  let offset (p : Placed) (down visible : Bool) :=
    if organic && visible && places.onBar p then Laid.barSurface down / 1000 else 0
  return [
    { route := r.key, occurrence, side := .source, item := a,
      surface := surface attachments source,
      point := (first.p0.1, first.p0.2 + offset source true true),
      docked := onSurface source },
    { route := r.key, occurrence, side := .target, item := b,
      surface := surface attachments target,
      point := (last.p3.1, last.p3.2 + offset target false whole),
      docked := whole && onSurface target }]

/-- Build lookup tables once and enumerate contacts in route occurrence order. -/
def collect (L : Look) (l : Laid) : List Contact :=
  let places := Laid.Ix.of l
  let attachments := GraphAttachment.Index.of l
  l.routes.toList.zipIdx.flatMap fun (r, i) => route L l places attachments i r

end Tools.View.GraphContact
