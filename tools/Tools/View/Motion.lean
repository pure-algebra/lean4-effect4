import Tools.View.Page

/-!
# Motion: the data join, transitions and easing

Slice V3 of the visual pipeline (`docs/research/2026-10-09-visual-pipeline.md`; the owner's steer of
2026-10-09: snappy, the lines drawn, the boxes expanding out, with D3's way of tying elements to
data as the pattern). The pattern, recalled from D3's selections and transitions, not read here:

- **The join.** A frame's elements are joined to the next frame's by key (`join`): the new keys
  *enter*, the kept keys *update*, the old keys *exit*. Every element falls in one of them
  (`join_new`, `join_old`).
- **Transitions.** Each selection takes a transition: a delay, a duration and an easing, in per
  mille of one step (`Transition`). A transition held in its step ends at exactly one
  (`Transition.within_at_end`), and every easing starts at 0 and ends at 1 (`Ease.at_start`,
  `Ease.at_end`).
- **Attributes as fields of the scene.** A line's offset and how much of it is written, a box's
  growth, an edge's reveal are fields of the page (`Line.shift`, `Line.reveal`, `Placed.grow`,
  `Route.reveal`). A still frame has them at rest. So a moment of a transition is a page like any
  other (`sample`), drawn by the one drawing, and the move law makes each moved call exact
  (`lowerCall_move`).

**The choreography** (`Choreography`) is data with defaults: the kept elements make room first
(ease in and out); then, level by level from the top, each new edge draws from its source toward
its target (ease out), and the box at its end expands out with a slight overshoot (ease out,
back); a new or changed line writes itself cell by cell, each a little after the one before; an
old element shrinks or unwrites (ease in). A step's sample at its end is the next frame: the
driver checks it on every transition.
-/

namespace Tools.View

/-! ## Easing -/

/-- An easing: a progress in per mille to an eased progress in per mille. `outBack` overshoots a
little before it settles. -/
inductive Ease where
  | linear | in_ | out | inOut | outBack
deriving Repr, DecidableEq

/-- The eased progress at `p` per mille (cubic curves; `outBack` with the usual 1.70158). -/
def Ease.at : Ease → Nat → Int
  | .linear, p => p
  | .in_, p => (p : Int) ^ 3 / 1000000
  | .out, p => 1000 - (1000 - (p : Int)) ^ 3 / 1000000
  | .inOut, p =>
    if p < 500 then 4 * (p : Int) ^ 3 / 1000000 else 1000 - (2 * (1000 - (p : Int))) ^ 3 / 2000000
  | .outBack, p =>
    let q : Int := (p : Int) - 1000
    1000 + 2702 * q ^ 3 / 1000000000 + 1702 * q ^ 2 / 1000000

/-- Every easing starts at 0. -/
theorem Ease.at_start (e : Ease) : e.at 0 = 0 := by cases e <;> rfl

/-- Every easing ends at 1. -/
theorem Ease.at_end (e : Ease) : e.at 1000 = 1000 := by cases e <;> rfl

/-! ## Transitions -/

/-- A transition: a delay, a duration and an easing, in per mille of one step. -/
structure Transition where
  delay : Nat := 0
  duration : Nat := 1000
  ease : Ease := .inOut
deriving Repr

/-- The eased progress of a transition at the moment `t` of a step. -/
def Transition.at (tr : Transition) (t : Nat) : Int :=
  if tr.delay + tr.duration ≤ t then 1000
  else if t ≤ tr.delay then tr.ease.at 0
  else tr.ease.at ((t - tr.delay) * 1000 / tr.duration)

/-- A transition is done at its end. -/
theorem Transition.at_end (tr : Transition) (t : Nat) (h : tr.delay + tr.duration ≤ t) :
    tr.at t = 1000 := by
  simp only [Transition.at, h, if_true]

/-- A transition held inside its step: it starts by the step's end and ends by it. -/
def Transition.within (tr : Transition) : Transition :=
  { tr with delay := min tr.delay 1000, duration := min tr.duration (1000 - min tr.delay 1000) }

/-- A held transition ends by the step's end. -/
theorem Transition.within_end (tr : Transition) : tr.within.delay + tr.within.duration ≤ 1000 := by
  simp only [Transition.within]
  omega

/-- So it is done at the step's end. -/
theorem Transition.within_at_end (tr : Transition) : tr.within.at 1000 = 1000 :=
  tr.within.at_end 1000 tr.within_end

/-- A transition started `d` later, held inside its step. -/
def Transition.after (tr : Transition) (d : Nat) : Transition :=
  ({ tr with delay := tr.delay + d } : Transition).within

/-! ## The join -/

/-- The three selections of a join: the new elements that enter, the kept ones as pairs of the
old and the new, and the old elements that exit. -/
structure Join (α : Type) where
  enter : List α
  update : List (α × α)
  exit : List α

/-- **The data join by key** of an old list and a new one. -/
def join {α : Type} (key : α → Key) (old new : List α) : Join α where
  enter := new.filter fun n => !(old.any fun o => key o == key n)
  update := new.filterMap fun n => (old.find? fun o => key o == key n).map (·, n)
  exit := old.filter fun o => !(new.any fun n => key n == key o)

/-- Every new element enters, or updates an old one with its key. -/
theorem join_new {α : Type} (key : α → Key) (old new : List α) (n : α) (h : n ∈ new) :
    n ∈ (join key old new).enter ∨ ∃ o, (o, n) ∈ (join key old new).update := by
  cases hf : old.find? (fun o => key o == key n) with
  | none =>
    left
    refine List.mem_filter.mpr ⟨h, ?_⟩
    have hall := List.find?_eq_none.mp hf
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false]
    exact fun o ho => hall o ho
  | some o =>
    right
    exact ⟨o, List.mem_filterMap.mpr ⟨n, h, by simp only [hf, Option.map_some]⟩⟩

/-- Every old element exits, or a new element has its key. -/
theorem join_old {α : Type} (key : α → Key) (old new : List α) (o : α) (h : o ∈ old) :
    o ∈ (join key old new).exit ∨ ∃ n ∈ new, key n = key o := by
  cases hany : new.any (fun n => key n == key o) with
  | false =>
    left
    exact List.mem_filter.mpr ⟨h, by simp only [hany, Bool.not_false]⟩
  | true =>
    right
    obtain ⟨n, hn, he⟩ := List.any_eq_true.mp hany
    exact ⟨n, hn, beq_iff_eq.mp he⟩

/-! ## The choreography, and a moment of a step -/

/-- **The choreography**: the transition of each selection. -/
structure Choreography where
  /-- the kept elements move to their new places -/
  move : Transition := { duration := 450, ease := .inOut }
  /-- the old elements shrink or unwrite -/
  leave : Transition := { duration := 250, ease := .in_ }
  /-- a new or changed line writes itself, cell by cell -/
  write : Transition := { delay := 300, duration := 300, ease := .linear }
  /-- the delay from one new line to the next -/
  stagger : Nat := 60
  /-- when the new parts of a graph start, after the room is made -/
  enterFrom : Nat := 300
  /-- a new edge draws from its source toward its target -/
  draw : Transition := { duration := 220, ease := .out }
  /-- the box at its end expands out -/
  expand : Transition := { duration := 300, ease := .outBack }
deriving Repr

/-- The value `e` per mille of the way from `u` to `v`. -/
def lerp (u v e : Int) : Int := v + (u - v) * (1000 - e) / 1000

/-- A transition started later is done at the step's end too. -/
theorem Transition.after_at_end (tr : Transition) (d : Nat) : (tr.after d).at 1000 = 1000 :=
  Transition.within_at_end _

/-- At the end, the value is the target. -/
theorem lerp_end (u v : Int) : lerp u v 1000 = v := by
  simp only [lerp, Int.sub_self, Int.mul_zero, Int.zero_ediv, Int.add_zero]

/-- A line to be written: no old line has its key and its text. -/
def fresh (old : List Line) (n : Line) : Bool := !(old.any fun o => o.key == n.key && o.text == n.text)

/-- **The update and the enter of a line**: the new line `n` at row `i`, at the moment `t`, when the
kept lines have moved `moved` per mille. A kept line stands off its row by what remains of its
move; a fresh line is written as far as its own transition. -/
def lineAt (c : Choreography) (old writing : List Line) (moved : Int) (t : Nat) (n : Line) (i : Nat) :
    Line :=
  let m : Line := if old.any (·.key == n.key) then
      { n with shift := ROWH * ((old.findIdx (·.key == n.key) : Int) - i) * (1000 - moved) / 1000 }
    else n
  if fresh old n then
    { m with reveal := ((c.write.after (writing.findIdx (·.key == n.key) * c.stagger)).at t).toNat }
  else m

/-- **The exit of a line**: the old line `o`, from row `i`, standing below the `k`-th of the new
lines, unwritten as far as its transition. -/
def lineGone (c : Choreography) (newCount : Nat) (t : Nat) (o : Line) (i k : Nat) : Line :=
  { o with shift := ROWH * ((i : Int) - (newCount + k)), reveal := (1000 - c.leave.within.at t).toNat,
           state := .plain }

/-- The lines at the moment `t` of the step from `g1` to `g2`: the kept lines move from their old
rows; a new line, or a kept one whose text changed, writes itself after the ones before it; an old
line unwrites at its old row. -/
def sampleLines (c : Choreography) (g1 g2 : Page) (t : Nat) : Array Line :=
  let old := g1.lines.toList
  let new := g2.lines.toList
  let writing := new.filter (fresh old)
  let kept := new.zipIdx.map fun (n, i) => lineAt c old writing (c.move.within.at t) t n i
  let leaving : List Line := if 1000 ≤ t then [] else
    ((old.zipIdx.filter fun (o, _) => !(new.any (·.key == o.key))).zipIdx.map fun ((o, i), k) =>
      lineGone c new.length t o i k)
  (kept ++ leaving).toArray

/-- **The update and the enter of a placed item**: a kept item moves `moved` per mille of the way
from its old place; a new one grows as far as `grow` says. -/
def placedAt (a : Laid) (moved : Int) (grow : Placed → Nat) (p : Placed) : Placed :=
  match a.find p.key with
  | some q => { p with x := lerp q.x p.x moved, y := lerp q.y p.y moved }
  | none => { p with grow := grow p }

/-- **The update and the enter of a route**: a kept route is drawn whole, and a new one as far as
`reveal` says. -/
def routeAt (a : Laid) (reveal : Route → Nat) (r : Route) : Route :=
  if a.routes.toList.any (·.key == r.key) then r else r.withReveal (reveal r)

/-- The layout at the moment `t` of the step from `a` to `b`: the kept items move; level by level
from the top, each new edge draws and then the boxes at its end expand; the old items shrink and
retract. -/
def sampleLaid (c : Choreography) (a b : Laid) (t : Nat) : Laid :=
  let left := c.leave.within.at t
  let newBoxes := b.placed.toList.filter fun p => (a.find p.key).isNone
  let newRoutes := b.routes.toList.filter fun r => !(a.routes.toList.any (·.key == r.key))
  let targetY : Route → Int
    | .down _ ks _ => ((ks.getLast?.bind b.find).map (·.y)).getD 0
    | .back _ _ d _ _ => ((b.find d).map (·.y)).getD 0
    | .loop _ k _ => ((b.find k).map (·.y)).getD 0
  let levels := ((newBoxes.map (·.y)) ++ (newRoutes.map targetY)).eraseDups.mergeSort (· ≤ ·)
  let slot := if levels.isEmpty then 0 else (1000 - c.enterFrom) / levels.length
  let start (y : Int) : Nat := c.enterFrom + levels.findIdx (· == y) * slot
  let drawAt (y : Int) : Transition :=
    ({ c.draw with duration := min c.draw.duration (slot * 45 / 100) } : Transition).after (start y)
  let expandAt (y : Int) : Transition :=
    ({ c.expand with duration := min c.expand.duration (slot * 60 / 100) } : Transition).after
      (start y + slot * 40 / 100)
  let placed := b.placed.toList.map (placedAt a (c.move.within.at t) fun p => ((expandAt p.y).at t).toNat)
  let routes := b.routes.toList.map (routeAt a fun r => ((drawAt (targetY r)).at t).toNat)
  let gone := if 1000 ≤ t then [] else
    (a.placed.toList.filter fun p => (b.find p.key).isNone).map fun p => { p with grow := (1000 - left).toNat }
  let retracting := if 1000 ≤ t then [] else
    (a.routes.toList.filter fun r => !(b.routes.toList.any (·.key == r.key))).map fun r =>
      r.withReveal (1000 - left).toNat
  { placed := (gone ++ placed).toArray, routes := (retracting ++ routes).toArray,
    width := if 1000 ≤ t then b.width else max a.width b.width,
    height := if 1000 ≤ t then b.height else max a.height b.height }

/-- **The moment `t` of the step from `g1` to `g2`**, as a page: `g2`'s, with its lines and its
graph sampled. A graph that appears enters from an empty one. -/
def sample (c : Choreography) (g1 g2 : Page) (t : Nat) : Page :=
  { g2 with
    lines := sampleLines c g1 g2 t
    graph := g2.graph.map fun p => { p with laid := sampleLaid c ((g1.graph.map (·.laid)).getD {}) p.laid t } }

/-! ## The end law: a step's last moment is the next frame -/

/-- A layout at rest: every box grown whole, every route drawn whole. -/
def Laid.AtRest (l : Laid) : Prop :=
  (∀ p ∈ l.placed.toList, p.grow = 1000) ∧ (∀ r ∈ l.routes.toList, r.reveal = 1000)

/-- A page at rest: its lines and its graph. A still frame is at rest. -/
def Page.AtRest (g : Page) : Prop :=
  (∀ l ∈ g.lines.toList, l.AtRest) ∧ ∀ p, g.graph = some p → p.laid.AtRest

/-- A line at rest is its own update and enter at the end. -/
theorem lineAt_end (c : Choreography) (old writing : List Line) (n : Line) (i : Nat)
    (h : n.AtRest) : lineAt c old writing 1000 1000 n i = n := by
  obtain ⟨hs, hr⟩ := h
  simp only [lineAt, Int.sub_self, Int.mul_zero, Int.zero_ediv, Transition.after_at_end]
  cases n
  simp only at hs hr
  subst hs hr
  split <;> split <;> rfl

/-- The lines at a step's end are the next frame's. -/
theorem sampleLines_end (c : Choreography) (g1 g2 : Page) (h : ∀ l ∈ g2.lines.toList, l.AtRest) :
    sampleLines c g1 g2 1000 = g2.lines := by
  simp only [sampleLines, Transition.within_at_end, Nat.le_refl, ↓reduceIte, List.append_nil]
  rw [List.map_congr_left (g := Prod.fst), List.zipIdx_map_fst, Array.toArray_toList]
  intro ⟨n, i⟩ hmem
  have hn := List.mem_map_of_mem (f := Prod.fst) hmem
  rw [List.zipIdx_map_fst] at hn
  exact lineAt_end c _ _ n i (h n hn)

/-- A placed item at rest is its own update and enter at the end. -/
theorem placedAt_end (a : Laid) (grow : Placed → Nat) (p : Placed) (h : p.grow = 1000)
    (hg : grow p = 1000) : placedAt a 1000 grow p = p := by
  unfold placedAt
  split
  · simp only [lerp_end]
  · rw [hg, ← h]

/-- A route at rest is its own update and enter at the end. -/
theorem routeAt_end (a : Laid) (reveal : Route → Nat) (r : Route) (h : r.reveal = 1000)
    (hr : reveal r = 1000) : routeAt a reveal r = r := by
  unfold routeAt
  split
  · rfl
  · rw [hr, ← h, Route.withReveal_self]

/-- The layout at a step's end is the next frame's. -/
theorem sampleLaid_end (c : Choreography) (a b : Laid) (h : b.AtRest) : sampleLaid c a b 1000 = b := by
  obtain ⟨hp, hr⟩ := h
  simp only [sampleLaid, Nat.le_refl, ↓reduceIte, List.nil_append, Transition.within_at_end,
    Transition.after_at_end]
  rw [List.map_congr_left (g := id) fun p hm => placedAt_end a _ p (hp p hm) rfl,
    List.map_congr_left (g := id) fun r hm => routeAt_end a _ r (hr r hm) rfl,
    List.map_id, List.map_id, Array.toArray_toList, Array.toArray_toList]

/-- **The end law.** A step's last moment is the next frame: sampling the step from any page to a
page at rest, at its end, gives that page. -/
theorem sample_end (c : Choreography) (g1 g2 : Page) (h : g2.AtRest) : sample c g1 g2 1000 = g2 := by
  obtain ⟨hl, hg⟩ := h
  unfold sample
  rw [sampleLines_end c g1 g2 hl]
  cases g2 with
  | mk title judgment heads lines foot place gutter marks graph =>
    cases graph with
    | none => rfl
    | some p => simp only [Option.map_some, sampleLaid_end c _ p.laid (hg p rfl)]

/-! ## The splice, read on two frames -/

/-- The key `k` lies in the subtree whose root has the key `a`, both written as `[1 0]`: it is
`a`, or it extends `a`'s address. The root `[]` holds every key. -/
def underKey (a k : Key) : Bool :=
  a == "[]" || k == a || k.startsWith ((a.dropEnd 1).toString ++ " ")

/-- The splice, read on two frames: the lines that both frames hold outside the subtree at
`edited`, and how many of them keep their text, their type and their note. -/
def keptUnchanged (g1 g2 : Page) (edited : Key) : Nat × Nat :=
  let outside (l : Line) : Bool := !(underKey edited l.key)
  let pairs := g2.lines.toList.filterMap fun l2 =>
    if outside l2 then (g1.lines.toList.find? (·.key == l2.key)).map (·, l2) else none
  (pairs.length, (pairs.filter fun (l1, l2) =>
    l1.text == l2.text && l1.type == l2.type && l1.note == l2.note).length)

end Tools.View
