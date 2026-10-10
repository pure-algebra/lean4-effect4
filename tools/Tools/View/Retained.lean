import Tools.View.Picture
import Tools.View.KeyMap

/-!
# A retained picture, and the patch from one frame to the next

A picture is a list of keyed calls (`Tools.View.Picture`). A retained picture reads it as
**objects**: a maximal run of consecutive calls with one key. An object's identity is its group,
its key and the rank of its run among the runs of that key (`ObjId`), so a line, its box in the
graph and its text in the code, which share one key, stay three objects. An object holds its
**anchor**, the place of its first call that has one, and its calls moved to that anchor
(`Call.move`). A **group** holds an origin, and its objects stand relative to it, so a panel that
moves down the page moves as one. This is slice LV-5 of the live view
(`docs/research/2026-10-10-live-view/LANDING.md`).

Between two frames, the **patch** (`diff`) says, for each object, nothing (kept), `move` (the same
calls at another anchor), `put` (new calls) or `drop`; for each group, `shift`; and the order of
painting, by the new objects' places when the old objects kept their order, else whole. A retained
store applies it (`Scene.apply`): Lean's here, and C's in `tools/view/scene.h`, row by row.

## The laws

- `of_flatten`: a picture read as objects and flattened is the picture;
- `apply_diff`: a scene patched by the diff to another flattens to the other, for every two
  scenes that are well formed (`Scene.WF`), as every scene read from groups with distinct names is
  (`ofGroups_wf`).

They are a tool's laws, not registry claims (decisions row 334, point 3). They serve concept
`initial-algebras-folds` and R14's live authoring. Their consumer is the live step
(`Tools.View.Live.step`), which answers each edit with a patch.

**What they do not establish.** They say nothing of C's store: its agreement with these laws is a
byte comparison on the frames the C check runs (`tools/view/scene_test.c`). No law bounds a patch's
size.
-/

namespace Tools.View.Retained

/-! ## Objects -/

/-- An object's identity: its group, its key, and the rank of its run among the runs of that key
in that group. -/
structure ObjId where
  group : String
  key : Key
  nth : Nat
deriving DecidableEq, Hashable, Repr

/-- The place a call is drawn from, in logical pixels: a shape's first point, rounded down. -/
def anchorOf : Call → Option (Int × Int)
  | .fill _ _ x y _ _ => some (x, y)
  | .frame _ x y _ _ _ => some (x, y)
  | .curve _ c _ => some c.p0
  | .cells x b _ _ => some (x, b)
  | .text _ x b _ _ => some (x, b)
  | .cut x y _ _ => some (x, y)
  | .uncut => none
  | .hit x y _ _ => some (x, y)
  | .shape _ _ ps => (ps.head?.bind List.head?).map fun c => (c.p0.1 / 1000, c.p0.2 / 1000)

/-- An object: its anchor in its group, and its calls moved so the anchor is the origin. -/
structure Obj where
  anchor : Int × Int
  rel : List Call
deriving DecidableEq

/-- Calls as an object, at the anchor of the first call that has one. -/
def Obj.of (cs : List Call) : Obj :=
  let a := (cs.findSome? anchorOf).getD (0, 0)
  ⟨a, cs.map (Call.move (-a.1) (-a.2))⟩

/-- An object's calls, at its anchor. -/
def Obj.calls (o : Obj) : List Call := o.rel.map (Call.move o.anchor.1 o.anchor.2)

/-- An object read from calls gives the calls back. A step of `of_flatten`. -/
theorem Obj.calls_of (cs : List Call) : (Obj.of cs).calls = cs := by
  simp only [Obj.of, Obj.calls, List.map_map, Function.comp_def, Call.move_move, Int.add_left_neg,
    Call.move_zero, List.map_id']

/-- The maximal runs of consecutive calls with one key, in order. -/
def runs : List (Keyed Call) → List (Key × List Call)
  | [] => []
  | c :: rest =>
    match runs rest with
    | (k, cs) :: more => if k = c.key then (k, c.call :: cs) :: more else (c.key, [c.call]) :: (k, cs) :: more
    | [] => [(c.key, [c.call])]

/-- A run's calls, each with the run's key. -/
def Keyed.run (r : Key × List Call) : List (Keyed Call) := r.2.map fun c => ⟨r.1, c⟩

/-- **The runs of a picture, keyed again, are the picture.** A step of `of_flatten`. -/
theorem runs_flatten : ∀ (cs : List (Keyed Call)), (runs cs).flatMap Keyed.run = cs
  | [] => rfl
  | c :: rest => by
    have ih := runs_flatten rest
    simp only [runs]
    cases h : runs rest with
    | nil =>
      rw [h, List.flatMap_nil] at ih
      subst ih
      rfl
    | cons r more =>
      obtain ⟨k, cs⟩ := r
      rw [h] at ih
      by_cases hk : k = c.key
      · subst hk
        simp only [if_true, List.flatMap_cons, Keyed.run, List.map_cons, List.cons_append]
        simp only [List.flatMap_cons, Keyed.run] at ih
        rw [ih]
      · simp only [hk, if_false, List.flatMap_cons, Keyed.run, List.map_cons, List.map_nil,
          List.singleton_append]
        simp only [List.flatMap_cons, Keyed.run] at ih
        rw [ih]

/-! ## Groups and scenes -/

/-- **A group** of a picture: its name, its origin, and its calls relative to that origin. -/
structure Group where
  name : String
  origin : Int × Int := (0, 0)
  calls : List (Keyed Call)

/-- A retained picture: its groups' names, the origin of each group, its objects by identity, and
their order of painting. -/
structure Scene where
  groups : List String := []
  origins : KeyMap String (Int × Int) := {}
  objs : KeyMap ObjId Obj := {}
  order : List ObjId := []

/-- The identities of a group's runs, each its run's rank among the runs of its key before it,
counted on from `counts`; with the counts after. -/
def rank (g : String) : KeyMap (String × Key) Nat → List (Key × List Call) →
    KeyMap (String × Key) Nat × List (ObjId × List Call)
  | counts, [] => (counts, [])
  | counts, (k, run) :: rest =>
    let n := counts.getD (g, k) 0
    let next := rank g (counts.insert (g, k) (n + 1)) rest
    (next.1, (⟨g, k, n⟩, run) :: next.2)

/-- The objects of groups, each with its identity; the counts run on across the groups. -/
def entries : KeyMap (String × Key) Nat → List Group → List (ObjId × List Call)
  | _, [] => []
  | counts, g :: gs =>
    let r := rank g.name counts (runs g.calls)
    r.2 ++ entries r.1 gs

/-- **A picture given as groups, read as objects.** -/
def Scene.ofGroups (gs : List Group) : Scene :=
  let es := entries {} gs
  { groups := gs.map (·.name)
    origins := gs.foldr (fun g m => m.insert g.name g.origin) {}
    objs := es.foldr (fun e m => m.insert e.1 (Obj.of e.2)) {}
    order := es.map (·.1) }

/-- A picture read as the objects of one group at the origin. -/
def Scene.of (cs : List (Keyed Call)) : Scene := Scene.ofGroups [{ name := "", calls := cs }]

/-- The calls of one object of a scene, each moved to its group's origin and keyed. -/
def Scene.callsOf (s : Scene) (id : ObjId) : List (Keyed Call) :=
  let o := s.origins.getD id.group (0, 0)
  ((s.objs.get? id).map fun ob => ob.calls.map fun c => (⟨id.key, c.move o.1 o.2⟩ : Keyed Call)).getD []

/-- **The picture of a retained scene**: each object's calls, moved to its group's origin, in the
order of painting. -/
def Scene.flatten (s : Scene) : List (Keyed Call) := s.order.flatMap s.callsOf

/-! ## The patch -/

/-- One operation of a patch. -/
inductive Op where
  | put (id : ObjId) (o : Obj)
  | move (id : ObjId) (dx dy : Int)
  | drop (id : ObjId)
  | shift (group : String) (dx dy : Int)

/-- A patch: its operations; the new objects' places in the order of painting, each after the
object before it in the new order (none: first), when the old objects kept their order; else the
whole new order. -/
structure Patch where
  ops : List Op
  inserts : List (ObjId × Option ObjId) := []
  order : Option (List ObjId) := none

/-- The shift of a group's origin from one scene to the next, when it moved. -/
def shiftOf (old new : Scene) (g : String) : Option Op :=
  let a := old.origins.getD g (0, 0)
  let b := new.origins.getD g (0, 0)
  if a = b then none else some (.shift g (b.1 - a.1) (b.2 - a.2))

/-- The change of one object from one scene to the next: nothing when it is kept, a move when
only its anchor changed, else a put. -/
def change (old new : Scene) (id : ObjId) : Option Op :=
  match new.objs.get? id, old.objs.get? id with
  | some o, some p =>
    if o.rel = p.rel then
      if o.anchor = p.anchor then none
      else some (.move id (o.anchor.1 - p.anchor.1) (o.anchor.2 - p.anchor.2))
    else some (.put id o)
  | some o, none => some (.put id o)
  | none, _ => none

/-- The drop of an old object that the new scene lacks. -/
def dropOf (new : Scene) (id : ObjId) : Option Op :=
  if new.objs.contains id then none else some (.drop id)

/-- The new objects of an order, each with the object before it in that order. -/
def insertsFrom (old : Scene) : Option ObjId → List ObjId → List (ObjId × Option ObjId)
  | _, [] => []
  | prev, id :: rest => (if old.objs.contains id then [] else [(id, prev)]) ++ insertsFrom old (some id) rest

/-- **The patch from one scene to the next**: each group's shift, each object's change, each old
object's drop; then the order, by the new objects' places when the old objects kept their order. -/
def diff (old new : Scene) : Patch :=
  let ops := new.groups.filterMap (shiftOf old new) ++ new.order.filterMap (change old new) ++
    old.order.filterMap (dropOf new)
  if new.order = old.order then { ops }
  else if new.order.filter old.objs.contains = old.order.filter new.objs.contains then
    { ops, inserts := insertsFrom old none new.order }
  else { ops, order := some new.order }

/-- One operation on a scene's origins and objects. -/
def applyOp (st : KeyMap String (Int × Int) × KeyMap ObjId Obj) : Op →
    KeyMap String (Int × Int) × KeyMap ObjId Obj
  | .put id o => (st.1, st.2.insert id o)
  | .move id dx dy =>
    match st.2.get? id with
    | some o => (st.1, st.2.insert id { o with anchor := (o.anchor.1 + dx, o.anchor.2 + dy) })
    | none => st
  | .drop id => (st.1, st.2.erase id)
  | .shift g dx dy =>
    let o := st.1.getD g (0, 0)
    (st.1.insert g (o.1 + dx, o.2 + dy), st.2)

/-- An order with `id` put after `prev`, or first. -/
def insertAfter (id : ObjId) : Option ObjId → List ObjId → List ObjId
  | none, order => id :: order
  | some prev, order => go prev order
where
  /-- Put `id` after the first `prev`, or last. -/
  go (prev : ObjId) : List ObjId → List ObjId
    | [] => [id]
    | x :: xs => if x = prev then x :: id :: xs else x :: go prev xs

/-- The object an operation drops, if any. -/
def Op.dropped? : Op → Option ObjId
  | .drop id => some id
  | _ => none

/-- The objects a patch drops. -/
def Patch.dropped (p : Patch) : List ObjId := p.ops.filterMap Op.dropped?

/-- **A patch applied** to a retained scene: its operations in turn, then the order. -/
def Scene.apply (s : Scene) (p : Patch) : Scene :=
  let st := p.ops.foldl applyOp (s.origins, s.objs)
  let base := s.order.filter fun id => !p.dropped.contains id
  { groups := s.groups, origins := st.1, objs := st.2,
    order := match p.order with
      | some o => o
      | none => p.inserts.foldl (fun o x => insertAfter x.1 x.2 o) base }

/-- The size of a patch: its shifts, moves, puts of new objects and of changed ones, drops, the
calls its puts carry, and whether it carries a whole order. -/
structure Size where
  shifts : Nat := 0
  moves : Nat := 0
  putsNew : Nat := 0
  putsChanged : Nat := 0
  drops : Nat := 0
  calls : Nat := 0
  reordered : Nat := 0
deriving Repr

/-- A patch's size, from the scene it applies to. -/
def Patch.size (old : Scene) (p : Patch) : Size :=
  p.ops.foldl (fun (z : Size) op =>
    match op with
    | .shift .. => { z with shifts := z.shifts + 1 }
    | .move .. => { z with moves := z.moves + 1 }
    | .put id o =>
      if old.objs.contains id then { z with putsChanged := z.putsChanged + 1, calls := z.calls + o.rel.length }
      else { z with putsNew := z.putsNew + 1, calls := z.calls + o.rel.length }
    | .drop .. => { z with drops := z.drops + 1 }) { reordered := if p.order.isSome then 1 else 0 }

/-! ## The law of reading: a picture read as objects and flattened is the picture -/

/-- Two maps of a list's items to lists agree when they agree at each item. -/
theorem flatMap_congr_mem {α β : Type} {f g : α → List β} : ∀ (l : List α), (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congr_mem xs fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- A sum of a pair and the difference to another pair is the other. -/
theorem add_sub_pair (a b : Int × Int) : (a.1 + (b.1 - a.1), a.2 + (b.2 - a.2)) = b := by
  obtain ⟨b1, b2⟩ := b
  simp only [Prod.mk.injEq]
  exact ⟨by omega, by omega⟩

/-- The ranks keep the runs, in order. A step of `of_flatten`. -/
theorem rank_runs (g : String) : ∀ (counts : KeyMap (String × Key) Nat) (rs : List (Key × List Call)),
    (rank g counts rs).2.map (fun e => (e.1.key, e.2)) = rs
  | _, [] => rfl
  | counts, (k, run) :: rest => by
    simp only [rank, List.map_cons, rank_runs g _ rest]

/-- Every identity a group's ranks give names the group. A step of `of_flatten`. -/
theorem rank_group (g : String) : ∀ (counts : KeyMap (String × Key) Nat) (rs : List (Key × List Call)),
    ∀ e ∈ (rank g counts rs).2, e.1.group = g
  | _, [], _, h => absurd h List.not_mem_nil
  | counts, (k, run) :: rest, e, h => by
    simp only [rank, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact rank_group g _ rest e h

/-- A rank is never below the count it starts from. A step of `rank_nodup`. -/
theorem rank_ge (g : String) : ∀ (counts : KeyMap (String × Key) Nat) (rs : List (Key × List Call)),
    ∀ e ∈ (rank g counts rs).2, counts.getD (g, e.1.key) 0 ≤ e.1.nth
  | _, [], _, h => absurd h List.not_mem_nil
  | counts, (k, run) :: rest, e, h => by
    simp only [rank, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · refine Nat.le_trans ?_ (rank_ge g _ rest e h)
      rw [KeyMap.getD_insert]
      by_cases hk : ((g, k) : String × Key) = (g, e.1.key)
      · rw [if_pos hk, ← hk]
        exact Nat.le_succ _
      · rw [if_neg hk]
        exact Nat.le_refl _

/-- **A group's identities are distinct**: two runs of one key have two ranks. A step of
`of_flatten` and `ofGroups_wf`. -/
theorem rank_nodup (g : String) : ∀ (counts : KeyMap (String × Key) Nat) (rs : List (Key × List Call)),
    ((rank g counts rs).2.map (·.1)).Nodup
  | _, [] => List.nodup_nil
  | counts, (k, run) :: rest => by
    simp only [rank, List.map_cons]
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, rank_nodup g _ rest⟩
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
    have hge := rank_ge g _ rest e he
    rw [heq, KeyMap.getD_insert, if_pos rfl] at hge
    exact Nat.not_succ_le_self _ hge

/-- A list's first entry at the identity of one of its members is that member, when its identities
are distinct. A step of `of_flatten` and `ofGroups_wf`. -/
theorem find?_member {β : Type} : ∀ (l : List (ObjId × β)) (e : ObjId × β), (l.map (·.1)).Nodup → e ∈ l →
    l.find? (fun x => decide (x.1 = e.1)) = some e
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: xs, e, hnd, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    rcases List.mem_cons.mp h with rfl | h
    · rw [decide_eq_true rfl]
    · have hne : x.1 ≠ e.1 := fun hx => hnd.1 (hx ▸ List.mem_map_of_mem h)
      rw [decide_eq_false hne]
      exact find?_member xs e hnd.2 h

/-- A table built from a list, the first entry at a key standing, answers each key's first entry. A
step of `of_flatten` and `ofGroups_wf`. -/
theorem foldr_get? {β : Type} (f : ObjId × β → Obj) : ∀ (l : List (ObjId × β)) (id : ObjId),
    (l.foldr (fun e m => m.insert e.1 (f e)) ({} : KeyMap ObjId Obj)).get? id =
      (l.find? fun x => decide (x.1 = id)).map f
  | [], id => KeyMap.get?_empty id
  | x :: xs, id => by
    rw [List.foldr_cons, KeyMap.get?_insert, foldr_get? f xs id, List.find?_cons]
    by_cases h : x.1 = id
    · rw [if_pos h, decide_eq_true h]
      rfl
    · rw [if_neg h, decide_eq_false h]

/-- The origins of a list of groups, the first of a name standing, answer that group's origin. -/
theorem origins_get (gs : List Group) (g : Group) (hg : g ∈ gs) (hnd : (gs.map (·.name)).Nodup) :
    (gs.foldr (fun g m => m.insert g.name g.origin) ({} : KeyMap String (Int × Int))).getD g.name (0, 0) =
      g.origin := by
  induction gs with
  | nil => exact absurd hg List.not_mem_nil
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldr_cons, KeyMap.getD_insert]
    rcases List.mem_cons.mp hg with rfl | h
    · rw [if_pos rfl]
    · have hne : x.name ≠ g.name := fun hx => hnd.1 (hx ▸ List.mem_map_of_mem h)
      rw [if_neg hne]
      exact ih h hnd.2

/-- **A picture read as objects and flattened is the picture.** Each run of one key becomes one
object at its anchor, and its calls come back moved to the anchor and back (`Obj.calls_of`). A
tool law; its consumer is the live step, whose first patch puts a whole picture. Placement: concept
`initial-algebras-folds`, R14's live authoring. -/
theorem of_flatten (cs : List (Keyed Call)) : (Scene.of cs).flatten = cs := by
  have hes : entries {} [{ name := "", calls := cs }] = (rank "" {} (runs cs)).2 := by
    simp only [entries, List.append_nil]
  have hnd := rank_nodup "" {} (runs cs)
  conv => rhs; rw [← runs_flatten cs, ← rank_runs "" {} (runs cs)]
  unfold Scene.of Scene.ofGroups Scene.flatten
  simp only [hes, List.flatMap_map]
  apply flatMap_congr_mem
  intro e he
  have hgroup := rank_group "" {} (runs cs) e he
  have hobj := foldr_get? (fun e => Obj.of e.2) (rank "" {} (runs cs)).2 e.1
  rw [find?_member _ e hnd he, Option.map_some] at hobj
  simp only [Scene.callsOf, hobj, Option.map_some, Option.getD_some, hgroup, List.foldr_cons,
    List.foldr_nil, KeyMap.getD_insert, if_true, Obj.calls_of, Call.move_zero, Keyed.run]

/-! ## The law of patching: a scene patched by the diff to another flattens to the other -/

/-- **A well-formed scene**: its order and its groups hold no repeat, an identity has an object
exactly when the order holds it, and each object's group stands among the groups. -/
def Scene.WF (s : Scene) : Prop :=
  s.order.Nodup ∧ s.groups.Nodup ∧ (∀ id, (s.objs.get? id).isSome = true ↔ id ∈ s.order) ∧
    ∀ id ∈ s.order, id.group ∈ s.groups

/-- The identity an operation reads or writes, if any. -/
def Op.target : Op → Option ObjId
  | .put id _ | .move id _ _ | .drop id => some id
  | .shift .. => none

/-- The group an operation shifts, if any. -/
def Op.group : Op → Option String
  | .shift g _ _ => some g
  | _ => none

/-- Operations that target no identity `id` leave its object. A step of `apply_diff`. -/
theorem fold_objs_other (id : ObjId) : ∀ (ops : List Op) (st : KeyMap String (Int × Int) × KeyMap ObjId Obj),
    (∀ op ∈ ops, op.target ≠ some id) → (ops.foldl applyOp st).2.get? id = st.2.get? id
  | [], _, _ => rfl
  | op :: ops, st, h => by
    rw [List.foldl_cons, fold_objs_other id ops _ fun o ho => h o (List.mem_cons_of_mem op ho)]
    have hop := h op List.mem_cons_self
    cases op with
    | put id' o =>
      have hne : id' ≠ id := fun e => hop (by rw [e]; rfl)
      simp only [applyOp, KeyMap.get?_insert, hne, if_false]
    | move id' dx dy =>
      have hne : id' ≠ id := fun e => hop (by rw [e]; rfl)
      simp only [applyOp]
      cases st.2.get? id' with
      | none => rfl
      | some o => simp only [KeyMap.get?_insert, hne, if_false]
    | drop id' =>
      have hne : id' ≠ id := fun e => hop (by rw [e]; rfl)
      simp only [applyOp, KeyMap.get?_erase, hne, if_false]
    | shift g dx dy => rfl

/-- Operations that shift no group `g` leave its origin. A step of `apply_diff`. -/
theorem fold_origins_other (g : String) : ∀ (ops : List Op) (st : KeyMap String (Int × Int) × KeyMap ObjId Obj),
    (∀ op ∈ ops, op.group ≠ some g) → (ops.foldl applyOp st).1.getD g (0, 0) = st.1.getD g (0, 0)
  | [], _, _ => rfl
  | op :: ops, st, h => by
    rw [List.foldl_cons, fold_origins_other g ops _ fun o ho => h o (List.mem_cons_of_mem op ho)]
    have hop := h op List.mem_cons_self
    cases op with
    | put id' o => rfl
    | move id' dx dy =>
      simp only [applyOp]
      cases st.2.get? id' <;> rfl
    | drop id' => rfl
    | shift g' dx dy =>
      have hne : g' ≠ g := fun e => hop (by rw [e]; rfl)
      simp only [applyOp, KeyMap.getD_insert, hne, if_false]

/-- The effect of an operation on the object at its target. -/
def opAt (o : Option Obj) : Op → Option Obj
  | .put _ ob => some ob
  | .move _ dx dy => o.map fun ob => { ob with anchor := (ob.anchor.1 + dx, ob.anchor.2 + dy) }
  | .drop _ => none
  | .shift .. => o

/-- An operation acts on the object at its target as `opAt` says. A step of `apply_diff`. -/
theorem applyOp_target (st : KeyMap String (Int × Int) × KeyMap ObjId Obj) (op : Op) (id : ObjId)
    (h : op.target = some id) : (applyOp st op).2.get? id = opAt (st.2.get? id) op := by
  cases op with
  | put id' ob =>
    cases h
    simp only [applyOp, KeyMap.get?_insert, if_true, opAt]
  | move id' dx dy =>
    cases h
    simp only [applyOp, opAt]
    split
    · rename_i o ho
      rw [ho, Option.map_some]
      simp only [KeyMap.get?_insert, if_true]
    · rename_i ho
      rw [ho, Option.map_none]
  | drop id' =>
    cases h
    simp only [applyOp, KeyMap.get?_erase, if_true, opAt]
  | shift g dx dy => cases h

/-- The effect of a shift on its group's origin. -/
def shiftAt (o : Int × Int) : Op → Int × Int
  | .shift _ dx dy => (o.1 + dx, o.2 + dy)
  | _ => o

/-- A shift acts on its group's origin as `shiftAt` says. A step of `apply_diff`. -/
theorem applyOp_group (st : KeyMap String (Int × Int) × KeyMap ObjId Obj) (op : Op) (g : String)
    (h : op.group = some g) : (applyOp st op).1.getD g (0, 0) = shiftAt (st.1.getD g (0, 0)) op := by
  cases op with
  | shift g' dx dy =>
    cases h
    simp only [applyOp, KeyMap.getD_insert, if_true, shiftAt]
  | _ => cases h

/-- **One member's operation, among operations on other identities**, acts alone on its identity.
A step of `apply_diff`. -/
theorem fold_filterMap_at {α : Type} (f : α → Option Op) (key : α → ObjId)
    (hf : ∀ a op, f a = some op → op.target = some (key a)) (a : α) (pre post : List α)
    (st : KeyMap String (Int × Int) × KeyMap ObjId Obj)
    (hpre : ∀ b ∈ pre, key b ≠ key a) (hpost : ∀ b ∈ post, key b ≠ key a) :
    (((pre ++ a :: post).filterMap f).foldl applyOp st).2.get? (key a) =
      ((f a).map (opAt (st.2.get? (key a)))).getD (st.2.get? (key a)) := by
  have hother : ∀ (l : List α), (∀ b ∈ l, key b ≠ key a) → ∀ op ∈ l.filterMap f, op.target ≠ some (key a) := by
    intro l hl op hop htarget
    obtain ⟨b, hb, hfb⟩ := List.mem_filterMap.mp hop
    rw [hf b op hfb, Option.some.injEq] at htarget
    exact hl b hb htarget
  rw [List.filterMap_append, List.foldl_append, List.filterMap_cons]
  cases hfa : f a with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [fold_objs_other (key a) _ _ (hother post hpost), fold_objs_other (key a) _ _ (hother pre hpre)]
  | some op =>
    simp only [Option.map_some, Option.getD_some, List.foldl_cons]
    rw [fold_objs_other (key a) _ _ (hother post hpost), applyOp_target _ op _ (hf a op hfa),
      fold_objs_other (key a) _ _ (hother pre hpre)]

/-- **One group's shift, among shifts of other groups**, acts alone on its origin. A step of
`apply_diff`. -/
theorem fold_shifts_at (f : String → Option Op) (hf : ∀ g op, f g = some op → op.group = some g)
    (g : String) (pre post : List String) (st : KeyMap String (Int × Int) × KeyMap ObjId Obj)
    (hpre : g ∉ pre) (hpost : g ∉ post) :
    (((pre ++ g :: post).filterMap f).foldl applyOp st).1.getD g (0, 0) =
      ((f g).map (shiftAt (st.1.getD g (0, 0)))).getD (st.1.getD g (0, 0)) := by
  have hother : ∀ (l : List String), g ∉ l → ∀ op ∈ l.filterMap f, op.group ≠ some g := by
    intro l hl op hop hgroup
    obtain ⟨b, hb, hfb⟩ := List.mem_filterMap.mp hop
    rw [hf b op hfb, Option.some.injEq] at hgroup
    exact hl (hgroup ▸ hb)
  rw [List.filterMap_append, List.foldl_append, List.filterMap_cons]
  cases hfg : f g with
  | none =>
    simp only [Option.map_none, Option.getD_none]
    rw [fold_origins_other g _ _ (hother post hpost), fold_origins_other g _ _ (hother pre hpre)]
  | some op =>
    simp only [Option.map_some, Option.getD_some, List.foldl_cons]
    rw [fold_origins_other g _ _ (hother post hpost), applyOp_group _ op _ (hf g op hfg),
      fold_origins_other g _ _ (hother pre hpre)]

/-- A member of a list with no repeat splits it into the part before and the part after, neither
holding it. A step of `apply_diff`. -/
theorem split_nodup {α : Type} : ∀ (l : List α) (a : α), l.Nodup → a ∈ l →
    ∃ pre post, l = pre ++ a :: post ∧ a ∉ pre ∧ a ∉ post
  | [], _, _, h => absurd h List.not_mem_nil
  | x :: xs, a, hnd, h => by
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨[], xs, rfl, List.not_mem_nil, hnd.1⟩
    · obtain ⟨pre, post, rfl, hpre, hpost⟩ := split_nodup xs a hnd.2 h
      refine ⟨x :: pre, post, rfl, ?_, hpost⟩
      intro hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hnd.1 (List.mem_append_right pre List.mem_cons_self)
      · exact hpre hx

/-- A change targets its own identity. -/
theorem change_target (old new : Scene) (id : ObjId) (op : Op) (h : change old new id = some op) :
    op.target = some id := by
  unfold change at h
  split at h
  · split at h
    · split at h
      · cases h
      · cases h; rfl
    · cases h; rfl
  · cases h; rfl
  · cases h

/-- A drop targets its own identity. -/
theorem dropOf_target (new : Scene) (id : ObjId) (op : Op) (h : dropOf new id = some op) :
    op.target = some id := by
  unfold dropOf at h
  split at h
  · cases h
  · cases h; rfl

/-- A shift shifts its own group. -/
theorem shiftOf_group (old new : Scene) (g : String) (op : Op) (h : shiftOf old new g = some op) :
    op.group = some g := by
  unfold shiftOf at h
  dsimp only at h
  split at h
  · cases h
  · cases h; rfl

/-- A change of an object the new scene holds gives the new object. A step of `apply_diff`. -/
theorem change_gives (old new : Scene) (id : ObjId) (o : Obj) (h : new.objs.get? id = some o) :
    ((change old new id).map (opAt (old.objs.get? id))).getD (old.objs.get? id) = some o := by
  unfold change
  rw [h]
  cases hp : old.objs.get? id with
  | none => rfl
  | some p =>
    by_cases hr : o.rel = p.rel
    · by_cases ha : o.anchor = p.anchor
      · simp only [hr, ha, if_true, Option.map_none, Option.getD_none]
        cases o; cases p
        simp only at hr ha
        rw [hr, ha]
      · simp only [hr, ha, if_true, if_false, Option.map_some, Option.getD_some, opAt, add_sub_pair]
        cases o; cases p
        simp only at hr ⊢
        rw [hr]
    · simp only [hr, if_false, Option.map_some, Option.getD_some, opAt]

/-- Membership in a list of identities, as `List.contains` answers it. -/
theorem contains_ids (a : ObjId) : ∀ (l : List ObjId), l.contains a = decide (a ∈ l)
  | [] => (decide_eq_false List.not_mem_nil).symm
  | b :: l => by
    rw [List.contains_cons, contains_ids a l]
    by_cases h : a = b
    · rw [show (a == b) = true from decide_eq_true h, decide_eq_true (List.mem_cons.mpr (Or.inl h))]
      rfl
    · by_cases hl : a ∈ l
      · rw [show (a == b) = false from decide_eq_false h, decide_eq_true hl,
          decide_eq_true (List.mem_cons_of_mem b hl)]
        rfl
      · have hn : a ∉ b :: l := fun hm => (List.mem_cons.mp hm).elim h hl
        rw [show (a == b) = false from decide_eq_false h, decide_eq_false hl, decide_eq_false hn]
        rfl

/-- A list mapped to nothing at each member is empty. A step of `diff_dropped`. -/
theorem filterMap_nothing {α β : Type} (f : α → Option β) : ∀ (l : List α), (∀ x ∈ l, f x = none) →
    l.filterMap f = []
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filterMap_cons, h x List.mem_cons_self]
    exact filterMap_nothing f xs fun y hy => h y (List.mem_cons_of_mem x hy)

/-- Options mapped twice are the options bound. A step of `diff_dropped`. -/
theorem filterMap_twice {α β γ : Type} (f : α → Option β) (g : β → Option γ) : ∀ (l : List α),
    (l.filterMap f).filterMap g = l.filterMap fun x => (f x).bind g
  | [] => rfl
  | x :: xs => by
    rw [List.filterMap_cons]
    cases hf : f x with
    | none => rw [List.filterMap_cons, hf, Option.bind_none, filterMap_twice f g xs]
    | some b => rw [List.filterMap_cons, List.filterMap_cons, hf, Option.bind_some, filterMap_twice f g xs]

/-- The objects a diff drops: the old order's objects the new scene lacks. A step of `apply_diff`. -/
theorem diff_dropped (old new : Scene) :
    (diff old new).dropped = old.order.filterMap fun id => if new.objs.contains id then none else some id := by
  have hops : (diff old new).ops = new.groups.filterMap (shiftOf old new) ++ new.order.filterMap (change old new) ++
      old.order.filterMap (dropOf new) := by
    unfold diff
    split
    · rfl
    · split <;> rfl
  have hshift : (new.groups.filterMap (shiftOf old new)).filterMap Op.dropped? = [] := by
    rw [filterMap_twice]
    refine filterMap_nothing _ _ fun g _ => ?_
    cases h : shiftOf old new g with
    | none => rfl
    | some op =>
      have := shiftOf_group old new g op h
      cases op <;> simp only [Op.group, reduceCtorEq] at this ⊢ <;> rfl
  have hchange : (new.order.filterMap (change old new)).filterMap Op.dropped? = [] := by
    rw [filterMap_twice]
    refine filterMap_nothing _ _ fun id _ => ?_
    cases h : change old new id with
    | none => rfl
    | some op =>
      unfold change at h
      split at h
      · split at h
        · split at h
          · cases h
          · cases h; rfl
        · cases h; rfl
      · cases h; rfl
      · cases h
  have hdrop : (old.order.filterMap (dropOf new)).filterMap Op.dropped? =
      old.order.filterMap fun id => if new.objs.contains id then none else some id := by
    rw [filterMap_twice]
    congr 1
    funext id
    unfold dropOf
    split <;> rfl
  rw [Patch.dropped, hops, List.filterMap_append, List.filterMap_append, hshift, hchange, hdrop,
    List.nil_append, List.nil_append]

/-- A filter that keeps every member is the list. A step of `apply_diff`. -/
theorem filter_all {α : Type} (p : α → Bool) : ∀ (l : List α), (∀ x ∈ l, p x = true) → l.filter p = l
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filter_cons, if_pos (h x List.mem_cons_self),
      filter_all p xs fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- Two filters that agree at each member agree. A step of `apply_diff`. -/
theorem filter_congr_mem {α : Type} {p q : α → Bool} : ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.filter p = l.filter q
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filter_cons, List.filter_cons, h x List.mem_cons_self,
      filter_congr_mem xs fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- An object put after the last of a prefix with no repeat of it stands right after it. A step of
`apply_diff`. -/
theorem insertAfter_go (id last : ObjId) (rest : List ObjId) : ∀ (pre : List ObjId), last ∉ pre →
    insertAfter.go id last (pre ++ last :: rest) = pre ++ last :: id :: rest
  | [], _ => by simp only [List.nil_append, insertAfter.go, if_true]
  | x :: xs, h => by
    have hx : x ≠ last := fun e => h (e ▸ List.mem_cons_self)
    simp only [List.cons_append, insertAfter.go, hx, if_false,
      insertAfter_go id last rest xs fun hm => h (List.mem_cons_of_mem x hm)]

/-- **The inserts rebuild the new order** from its old objects, after a prefix that ends at `last`.
A step of `apply_diff`. -/
theorem inserts_rebuild (old : Scene) : ∀ (Q pre : List ObjId) (last : ObjId), (pre ++ last :: Q).Nodup →
    (insertsFrom old (some last) Q).foldl (fun o x => insertAfter x.1 x.2 o)
      (pre ++ last :: Q.filter old.objs.contains) = pre ++ last :: Q
  | [], _, _, _ => by simp only [insertsFrom, List.foldl_nil, List.filter_nil]
  | x :: Q, pre, last, hnd => by
    have hlast : last ∉ pre := (List.nodup_append.mp hnd).2.2 |> fun h hm => h last hm last List.mem_cons_self rfl
    have hnd' : ((pre ++ [last]) ++ x :: Q).Nodup := by
      rw [List.append_assoc, List.singleton_append]; exact hnd
    simp only [insertsFrom, List.foldl_append, List.filter_cons]
    by_cases hc : old.objs.contains x = true
    · simp only [hc, if_true, List.foldl_nil]
      have := inserts_rebuild old Q (pre ++ [last]) x hnd'
      simp only [List.append_assoc, List.singleton_append] at this
      exact this
    · simp only [hc, Bool.false_eq_true, if_false, List.foldl_cons, List.foldl_nil, insertAfter,
        insertAfter_go x last _ pre hlast]
      have := inserts_rebuild old Q (pre ++ [last]) x hnd'
      simp only [List.append_assoc, List.singleton_append] at this
      exact this

/-- The objects a diff drops leave the old order's objects the new scene holds. A step of
`apply_diff`. -/
theorem dropped_contains (old new : Scene) (id : ObjId) (hid : id ∈ old.order) :
    (!(diff old new).dropped.contains id) = new.objs.contains id := by
  rw [diff_dropped, contains_ids]
  by_cases hc : new.objs.contains id = true
  · have hn : id ∉ old.order.filterMap fun id => if new.objs.contains id then none else some id := by
      intro hm
      obtain ⟨b, -, hb⟩ := List.mem_filterMap.mp hm
      by_cases hbc : new.objs.contains b = true
      · rw [if_pos hbc] at hb; cases hb
      · rw [if_neg hbc, Option.some.injEq] at hb
        subst hb
        exact hbc hc
    rw [decide_eq_false hn, hc]
    rfl
  · have hm : id ∈ old.order.filterMap fun id => if new.objs.contains id then none else some id :=
      List.mem_filterMap.mpr ⟨id, hid, by rw [if_neg hc]⟩
    rw [decide_eq_true hm]
    cases hv : new.objs.contains id
    · rfl
    · exact absurd hv hc

/-- **The order a patch leaves is the new order**, for two well-formed scenes. A step of
`apply_diff`. -/
theorem apply_diff_order {s t : Scene} (hs : s.WF) (ht : t.WF) : (s.apply (diff s t)).order = t.order := by
  obtain ⟨hsnd, -, hsobj, -⟩ := hs
  obtain ⟨htnd, -, htobj, -⟩ := ht
  have hbase : s.order.filter (fun id => !(diff s t).dropped.contains id) = s.order.filter t.objs.contains :=
    filter_congr_mem s.order fun id hid => dropped_contains s t id hid
  unfold Scene.apply
  simp only []
  rw [hbase]
  unfold diff
  by_cases heq : t.order = s.order
  · simp only [heq, if_true, List.foldl_nil]
    exact filter_all _ s.order fun id hid => (htobj id).mpr (heq ▸ hid)
  · simp only [heq, if_false]
    by_cases hkeep : t.order.filter s.objs.contains = s.order.filter t.objs.contains
    · simp only [hkeep, if_true]
      rw [← hkeep]
      cases ho : t.order with
      | nil => rfl
      | cons x Q =>
        rw [ho] at htnd
        simp only [insertsFrom, List.foldl_append, List.filter_cons]
        by_cases hc : s.objs.contains x = true
        · simp only [hc, if_true, List.foldl_nil]
          exact inserts_rebuild s Q [] x htnd
        · simp only [hc, Bool.false_eq_true, if_false, List.foldl_cons, List.foldl_nil, insertAfter]
          exact inserts_rebuild s Q [] x htnd
    · simp only [hkeep, if_false]

/-- A shift of a group's origin from one scene to the next gives the new origin. A step of
`apply_diff`. -/
theorem shiftOf_gives (old new : Scene) (g : String) :
    ((shiftOf old new g).map (shiftAt (old.origins.getD g (0, 0)))).getD (old.origins.getD g (0, 0)) =
      new.origins.getD g (0, 0) := by
  unfold shiftOf
  by_cases h : old.origins.getD g (0, 0) = new.origins.getD g (0, 0)
  · simp only [h, if_true, Option.map_none, Option.getD_none]
  · simp only [h, if_false, Option.map_some, Option.getD_some, shiftAt, add_sub_pair]

/-- **A scene patched by the diff to another flattens to the other.** For two well-formed scenes:
each object the new scene holds comes back by its change, each group's origin by its shift, and
the order by its inserts or whole. A tool law; its consumer is the live step, whose patch rows C
applies row by row (`tools/view/scene.h`). Placement: concept `initial-algebras-folds`, R14's live
authoring. -/
theorem apply_diff {s t : Scene} (hs : s.WF) (ht : t.WF) : (s.apply (diff s t)).flatten = t.flatten := by
  have horder := apply_diff_order hs ht
  obtain ⟨hsnd, -, hsobj, -⟩ := hs
  obtain ⟨htnd, htg, htobj, htgroup⟩ := ht
  have hops : (diff s t).ops = t.groups.filterMap (shiftOf s t) ++ t.order.filterMap (change s t) ++
      s.order.filterMap (dropOf t) := by
    unfold diff
    split
    · rfl
    · split <;> rfl
  have hobjs : ∀ oid ∈ t.order, (s.apply (diff s t)).objs.get? oid = t.objs.get? oid := by
    intro oid hid
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp ((htobj oid).mpr hid)
    show ((diff s t).ops.foldl applyOp (s.origins, s.objs)).2.get? oid = _
    rw [hops, List.foldl_append, List.foldl_append]
    have hdrops : ∀ op ∈ s.order.filterMap (dropOf t), op.target ≠ some oid := by
      intro op hop htarget
      obtain ⟨b, -, hb⟩ := List.mem_filterMap.mp hop
      rw [dropOf_target t b op hb, Option.some.injEq] at htarget
      subst htarget
      unfold dropOf at hb
      rw [if_pos (by unfold KeyMap.contains; rw [ho]; rfl)] at hb
      cases hb
    have hshifts : ∀ op ∈ t.groups.filterMap (shiftOf s t), op.target ≠ some oid := by
      intro op hop htarget
      obtain ⟨g, -, hg⟩ := List.mem_filterMap.mp hop
      have := shiftOf_group s t g op hg
      cases op <;> simp only [Op.group, Op.target, reduceCtorEq] at this htarget
    obtain ⟨pre, post, hsplit, hpre, hpost⟩ := split_nodup t.order oid htnd hid
    rw [fold_objs_other oid _ _ hdrops, hsplit,
      fold_filterMap_at (change s t) (fun x => x) (change_target s t) oid pre post _
        (fun b hb e => hpre (e ▸ hb)) (fun b hb e => hpost (e ▸ hb)),
      fold_objs_other oid _ _ hshifts, ho]
    exact change_gives s t oid o ho
  have horig : ∀ g ∈ t.groups, (s.apply (diff s t)).origins.getD g (0, 0) = t.origins.getD g (0, 0) := by
    intro g hg
    show ((diff s t).ops.foldl applyOp (s.origins, s.objs)).1.getD g (0, 0) = _
    rw [hops, List.foldl_append, List.foldl_append]
    have hrest : ∀ (l : List Op), (∀ op ∈ l, op.group = none) → ∀ op ∈ l, op.group ≠ some g := by
      intro l hl op hop e
      rw [hl op hop] at e
      cases e
    have hdrops : ∀ op ∈ s.order.filterMap (dropOf t), op.group = none := by
      intro op hop
      obtain ⟨b, -, hb⟩ := List.mem_filterMap.mp hop
      have := dropOf_target t b op hb
      cases op <;> simp only [Op.group, Op.target, reduceCtorEq] at this ⊢
    have hputs : ∀ op ∈ t.order.filterMap (change s t), op.group = none := by
      intro op hop
      obtain ⟨b, -, hb⟩ := List.mem_filterMap.mp hop
      have := change_target s t b op hb
      cases op <;> simp only [Op.group, Op.target, reduceCtorEq] at this ⊢
    obtain ⟨pre, post, hsplit, hpre, hpost⟩ := split_nodup t.groups g htg hg
    rw [fold_origins_other g _ _ (hrest _ hdrops), fold_origins_other g _ _ (hrest _ hputs), hsplit,
      fold_shifts_at (shiftOf s t) (shiftOf_group s t) g pre post _ hpre hpost]
    exact shiftOf_gives s t g
  unfold Scene.flatten
  rw [horder]
  apply flatMap_congr_mem
  intro oid hid
  simp only [Scene.callsOf, hobjs oid hid, horig oid.group (htgroup oid hid)]

/-- Every identity of the entries of groups names one of the groups. A step of `ofGroups_wf`. -/
theorem entries_group : ∀ (counts : KeyMap (String × Key) Nat) (gs : List Group),
    ∀ e ∈ entries counts gs, e.1.group ∈ gs.map (·.name)
  | _, [], _, h => absurd h List.not_mem_nil
  | counts, g :: gs, e, h => by
    simp only [entries, List.mem_append] at h
    rcases h with h | h
    · rw [rank_group g.name counts (runs g.calls) e h]
      exact List.mem_map_of_mem List.mem_cons_self
    · exact List.mem_cons_of_mem _ (entries_group _ gs e h)

/-- The identities of the entries of groups with distinct names are distinct. A step of
`ofGroups_wf`. -/
theorem entries_nodup : ∀ (counts : KeyMap (String × Key) Nat) (gs : List Group), (gs.map (·.name)).Nodup →
    ((entries counts gs).map (·.1)).Nodup
  | _, [], _ => List.nodup_nil
  | counts, g :: gs, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [entries, List.map_append]
    refine List.nodup_append.mpr ⟨rank_nodup g.name counts (runs g.calls), entries_nodup _ gs hnd.2, ?_⟩
    intro a ha b hb heq
    obtain ⟨ea, hea, rfl⟩ := List.mem_map.mp ha
    obtain ⟨eb, heb, rfl⟩ := List.mem_map.mp hb
    have hga := rank_group g.name counts (runs g.calls) ea hea
    have hgb := entries_group _ gs eb heb
    rw [← heq, hga] at hgb
    exact hnd.1 hgb

/-- A table built from a list answers a key exactly when the list holds it. A step of
`ofGroups_wf`. -/
theorem foldr_isSome {β : Type} (f : ObjId × β → Obj) : ∀ (l : List (ObjId × β)) (id : ObjId),
    ((l.foldr (fun e m => m.insert e.1 (f e)) ({} : KeyMap ObjId Obj)).get? id).isSome = true ↔
      id ∈ l.map (·.1)
  | [], oid => by
    rw [List.foldr_nil, KeyMap.get?_empty]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h List.not_mem_nil⟩
  | x :: xs, oid => by
    rw [List.foldr_cons, KeyMap.get?_insert, List.map_cons, List.mem_cons]
    by_cases h : x.1 = oid
    · rw [if_pos h]
      exact ⟨fun _ => .inl h.symm, fun _ => rfl⟩
    · rw [if_neg h, foldr_isSome f xs oid]
      exact ⟨.inr, fun hm => hm.elim (fun e => absurd e.symm h) fun h' => h'⟩

/-- **A picture read from groups with distinct names is a well-formed scene.** A step of the live
step's patch law: each frame's scene meets `apply_diff`'s premise. -/
theorem ofGroups_wf (gs : List Group) (hnd : (gs.map (·.name)).Nodup) : (Scene.ofGroups gs).WF := by
  refine ⟨entries_nodup {} gs hnd, hnd, fun id => foldr_isSome _ _ id, fun id hid => ?_⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hid
  exact entries_group {} gs e he

end Tools.View.Retained
