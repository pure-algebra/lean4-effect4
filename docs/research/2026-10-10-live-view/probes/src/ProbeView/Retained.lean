import ProbeView.Fast

/-!
# Probe: a retained picture, and the patch from one frame to the next

A picture is a list of keyed calls (`Tools.View.Picture`). This probe reads it as **objects**: a
maximal run of consecutive calls with one key. An object's identity is its key and the rank of
its run among the runs of that key, so a line, its box in the graph and its text in the code
plane, which share one key, stay three objects. An object holds its **anchor**, the place of its
first call that has one, and its calls moved to that anchor (`Call.move`).

Between two frames, the **patch** says, for each object, nothing (kept), `move` (the same calls
at another anchor), `put` (new calls) or `drop`; and the order of the objects when it changed.
The C side keeps the objects and applies patches; a move is the motion it can interpolate itself,
exactly, by the move law of the lowering (`lowerAll_move`, `tools/Tools/View/Picture.lean`).

The checks: a picture read as objects and flattened is the picture (`Scene.of_flatten`), and the
old picture patched is the new picture (`apply_diff`), on every two consecutive frames.
-/

open Effect4 Effect4.Program Tools.View Tools.View.Build

namespace Tools.View.Retained

/-- An object's identity: its group, its key, and the rank of its run among the runs of that key
in that group. -/
structure ObjId where
  group : String
  key : Key
  nth : Nat
deriving DecidableEq, Hashable, Repr

/-- The place a call is drawn from, in logical pixels: a shape's first point, rounded down. -/
def Call.anchor : Call → Option (Int × Int)
  | .fill _ _ x y _ _ => some (x, y)
  | .frame _ x y _ _ _ => some (x, y)
  | .curve _ c _ => some c.p0
  | .cells x b _ _ => some (x, b)
  | .text _ x b _ _ => some (x, b)
  | .cut x y _ _ => some (x, y)
  | .uncut => none
  | .hit x y _ _ => some (x, y)
  | .shape _ _ ps => (ps.head?.bind List.head?).map fun c => (c.p0.1 / 1000, c.p0.2 / 1000)

/-- An object: its anchor in its group and its calls, moved so the anchor is the origin. -/
structure Obj where
  anchor : Int × Int
  rel : List Call
deriving DecidableEq

def Obj.of (cs : List Call) : Obj :=
  let a := (cs.findSome? Call.anchor).getD (0, 0)
  ⟨a, cs.map (Call.move (-a.1) (-a.2))⟩

def Obj.calls (o : Obj) : List Call := o.rel.map (Call.move o.anchor.1 o.anchor.2)

/-- The maximal runs of consecutive calls with one key, in order. -/
def runs : List (Keyed Call) → List (Key × List Call)
  | [] => []
  | c :: rest =>
    match runs rest with
    | (k, cs) :: more => if k == c.key then (k, c.call :: cs) :: more else (c.key, [c.call]) :: (k, cs) :: more
    | [] => [(c.key, [c.call])]

/-- **A group** of a picture: its name, its origin, and its calls relative to that origin. A
panel of a page is a group, so the panel moves as one. -/
structure Group where
  name : String
  origin : Int × Int := (0, 0)
  calls : List (Keyed Call)

/-- A retained picture: the origin of each group, its objects by identity, and their order of
painting. -/
structure Scene where
  origins : Std.HashMap String (Int × Int) := {}
  objs : Std.HashMap ObjId Obj := {}
  order : List ObjId := []

/-- A picture given as groups, read as objects. -/
def Scene.ofGroups (gs : List Group) : Scene :=
  let (_, scene) := gs.foldl (fun (acc : Std.HashMap (String × Key) Nat × Scene) g =>
    (runs g.calls).foldl (fun (acc : Std.HashMap (String × Key) Nat × Scene) (k, run) =>
      let n := acc.1.getD (g.name, k) 0
      let id : ObjId := ⟨g.name, k, n⟩
      (acc.1.insert (g.name, k) (n + 1),
        { acc.2 with objs := acc.2.objs.insert id (Obj.of run), order := id :: acc.2.order }))
      (acc.1, { acc.2 with origins := acc.2.origins.insert g.name g.origin }))
    ({}, {})
  { scene with order := scene.order.reverse }

/-- A picture read as objects of one group at the origin. -/
def Scene.of (cs : List (Keyed Call)) : Scene := Scene.ofGroups [{ name := "", calls := cs }]

/-- The picture of a retained scene: each object's calls, moved to its group's origin. -/
def Scene.flatten (s : Scene) : List (Keyed Call) :=
  s.order.flatMap fun id =>
    let (ox, oy) := s.origins.getD id.group (0, 0)
    ((s.objs[id]?).map fun o => o.calls.map fun c => ⟨id.key, c.move ox oy⟩).getD []

/-- One operation of a patch. -/
inductive Op where
  | put (id : ObjId) (o : Obj)
  | move (id : ObjId) (dx dy : Int)
  | drop (id : ObjId)
  | shift (group : String) (dx dy : Int)

/-- A patch: its operations; the new objects' places in the order of painting, each after the
object before it (none: first), when the old objects kept their order; else the whole new order. -/
structure Patch where
  ops : List Op
  inserts : List (ObjId × Option ObjId) := []
  order : Option (List ObjId) := none

/-- **The patch from one scene to the next**: each group's shift, then each object's change in
its group. -/
def diff (old new : Scene) : Patch :=
  let groups := (new.order.map (·.group)).eraseDups
  let shifts := groups.filterMap fun g =>
    let (a, b) := (old.origins.getD g (0, 0), new.origins.getD g (0, 0))
    if a == b then none else some (Op.shift g (b.1 - a.1) (b.2 - a.2))
  let puts := new.order.filterMap fun id =>
    match new.objs[id]?, old.objs[id]? with
    | some o, some p =>
      if o.rel == p.rel then
        if o.anchor == p.anchor then none
        else some (Op.move id (o.anchor.1 - p.anchor.1) (o.anchor.2 - p.anchor.2))
      else some (Op.put id o)
    | some o, none => some (Op.put id o)
    | none, _ => none
  let drops := old.order.filterMap fun id => if new.objs.contains id then none else some (Op.drop id)
  let ops := shifts ++ puts ++ drops
  if new.order == old.order then { ops } else
  -- the old objects that stay, in the old order and in the new: then the new ones are inserts
  let stay := old.order.filter new.objs.contains
  if new.order.filter old.objs.contains == stay then
    let (ins, _) := new.order.foldl (fun (acc : List (ObjId × Option ObjId) × Option ObjId) id =>
      (if old.objs.contains id then acc.1 else (id, acc.2) :: acc.1, some id)) ([], none)
    { ops, inserts := ins.reverse }
  else { ops, order := some new.order }

/-- **A patch applied** to a retained scene. -/
def Scene.apply (s : Scene) (p : Patch) : Scene :=
  let (origins, objs) := p.ops.foldl (fun (acc : Std.HashMap String (Int × Int) × Std.HashMap ObjId Obj) op =>
    let (os, m) := acc
    match op with
    | .put id o => (os, m.insert id o)
    | .move id dx dy => match m[id]? with
      | some o => (os, m.insert id { o with anchor := (o.anchor.1 + dx, o.anchor.2 + dy) })
      | none => (os, m)
    | .drop id => (os, m.erase id)
    | .shift g dx dy =>
      let (x, y) := os.getD g (0, 0)
      (os.insert g (x + dx, y + dy), m)) (s.origins, s.objs)
  let dropped := p.ops.filterMap fun | .drop id => some id | _ => none
  let base := s.order.filter fun id => !dropped.contains id
  let insertAfter (order : List ObjId) (id : ObjId) : Option ObjId → List ObjId
    | none => id :: order
    | some prev =>
      let rec go : List ObjId → List ObjId
        | [] => [id]
        | x :: xs => if x == prev then x :: id :: xs else x :: go xs
      go order
  let order := match p.order with
    | some o => o
    | none => p.inserts.foldl (fun o (id, prev) => insertAfter o id prev) base
  { origins, objs, order }

/-- The size of a patch: its shifts, moves, puts (new objects and changed ones), drops, and the
calls its puts carry. -/
structure Size where
  shifts : Nat := 0
  moves : Nat := 0
  putsNew : Nat := 0
  putsChanged : Nat := 0
  drops : Nat := 0
  calls : Nat := 0
  reordered : Nat := 0
deriving Repr

def Patch.size (old : Scene) (p : Patch) : Size :=
  p.ops.foldl (fun (z : Size) op =>
    match op with
    | .shift .. => { z with shifts := z.shifts + 1 }
    | .move .. => { z with moves := z.moves + 1 }
    | .put id o => if old.objs.contains id then { z with putsChanged := z.putsChanged + 1, calls := z.calls + o.rel.length }
      else { z with putsNew := z.putsNew + 1, calls := z.calls + o.rel.length }
    | .drop .. => { z with drops := z.drops + 1 }) { reordered := if p.order.isSome then 1 else 0 }

/-- How many ids a patch's order rows carry: one for each insert, or the whole order. -/
def Patch.orderIds (p : Patch) : Nat := match p.order with
  | some o => o.length
  | none => p.inserts.length

end Tools.View.Retained

