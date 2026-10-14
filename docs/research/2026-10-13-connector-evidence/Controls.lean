import Tools.View.Connector

open Tools.View
open Tools.View.Connector

namespace ConnectorEvidence

def noiseLook : Organic := { noise := 350, wave := 40000 }
def dock : Option Dock := some ⟨0, 6000⟩

def fixtures : List (List Cubic) :=
  [[Grow.line (0, 0) (0, 40)],
   [⟨(0, 0), (0, 20), (30, 20), (30, 40)⟩],
   [Grow.line (0, 0) (30, 40)],
   [Grow.line (0, 0) (0, 20), Grow.line (0, 20) (30, 20), Grow.line (30, 20) (30, 40)],
   [Grow.line (0, 0) (0, 2)],
   [⟨(0, 0), (0, 0), (0, 0), (0, 40)⟩]]

def contact (a b : Cubic) : Bool := a.p3 == b.p0
def tangent (a b : Cubic) : Bool :=
  let u := (a.p3.1 - a.p2.1, a.p3.2 - a.p2.2)
  let v := (b.p1.1 - b.p0.1, b.p1.2 - b.p0.2)
  u == v && u != (0, 0)

def closed (cs : List Cubic) : Bool :=
  !(cs.isEmpty) && (cs.zip (cs.drop 1)).all (fun (a, b) => contact a b) &&
    match cs.head?, cs.getLast? with
    | some a, some z => contact z a
    | _, _ => false

def smooth (cs : List Cubic) : Bool := (smoothJoins cs).all fun i =>
  match cs[i]?, cs[i + 1]? with
  | some a, some b => tangent a b
  | _, _ => false

def cap (c : Cubic) : Bool := c.p0 == c.p1 && c.p2 == c.p3
def caps (cs : List Cubic) : Bool := (capSegments cs).all fun i =>
  match cs[i]? with
  | some c => cap c
  | none => false

def passes (cs : List Cubic) : Bool := closed cs && smooth cs && caps cs

-- Every intended side seam has nonzero, exactly equal milli tangent handles.
-- This finite control includes linear, bumpY, stepY, short, and duplicate-control routes.
#guard (List.range 64).all fun seed => fixtures.all fun cs =>
  passes (stroke seed noiseLook 2400 cs false dock dock)

-- The target dock has no effect while the connector grows.
#guard fixtures.all fun cs =>
  stroke 91 noiseLook 2400 cs true dock dock == stroke 91 noiseLook 2400 cs true dock none
#guard fixtures.all fun cs => passes (stroke 91 noiseLook 2400 cs true dock dock)

-- Wave zero does not move a docked neck's prescribed width.
#guard let b := body 91 { noise := 350, wave := 0 } 2400 fixtures[1]! false dock dock
  (b.left[1]?).map (·.p0) == some (-1200, 6000) &&
    (b.right[1]?).map (·.p0) == some (1200, 6000)

-- Relative surfaces include unequal bar offsets and bounded asymmetric radii.
#guard fixtures.all fun cs =>
  passes (stroke 13 noiseLook 2400 cs false (some ⟨500, 3000⟩) (some ⟨-500, 6000⟩))

-- No body appears before a growing route clears the source surface.
#guard stroke 0 noiseLook 2400 [Grow.line (0, 0) (0, 1)] true (some ⟨1000, 6000⟩) none == []
#guard stroke 0 noiseLook 0 fixtures[0]! false dock dock == []
#guard stroke 0 noiseLook 2400 [] false dock dock == []
#guard stroke 0 noiseLook 2400 [Grow.line (0, 0) (0, 0)] false dock dock == []

-- Two thousandths is the smallest effective flare with a nonzero integer handle.
#guard radius 1 10000 40000 == 0
#guard radius 2 10000 40000 == 2 && handle 2 == 1

-- Local changes cannot hide a failed seam by shrinking the structural index list.
#guard let cs := stroke 0 noiseLook 2400 fixtures[1]! false dock dock
  let damaged := cs.mapIdx fun i c => if i == 1 then { c with p1 := (c.p1.1 + 1, c.p1.2) } else c
  closed damaged && !(smooth damaged) && smoothJoins damaged == smoothJoins cs

-- The old representation consists of three closed paths, with no shared body/flare seam.
#guard let cs := fixtures[1]!
  let old := [Grow.stroke 0 noiseLook 2400 cs false,
    Grow.collar 0 0 2400 6000 true, Grow.collar 30000 40000 2400 6000 false]
  old.length == 3 && (stroke 0 noiseLook 2400 cs false dock dock).length % 2 == 0

#eval fixtures.map fun cs =>
  let path := stroke 0 noiseLook 2400 cs false dock dock
  (path.length, (smoothJoins path).length, passes path)

end ConnectorEvidence
