import Tools.View.Build
import Tools.View.Output
import Std.Data.HashMap

/-!
# Probe: the view's hot paths, made fast, each equal to the tree's function

Four replacements, each a drop-in for one declaration of `tools/Tools/View/`, each checked equal
to the tree's declaration by `#guard` on every frame of the probe's programs:

1. `isqrt`: Newton's steps from `2 ^ (log₂ n / 2 + 1)`, which is above `√n`, instead of from `n`.
   The steps fall to the same fixed point, the greatest `s` with `s * s ≤ n`, in about five steps
   instead of about twenty on a squared distance in thousandths. It replaces `Grow.isqrt`
   (`tools/Tools/View/Organic.lean`).
2. `Ix`: a laid graph's places by key, built once per drawing. It replaces the linear `Laid.find`
   inside `Laid.calls` (`tools/Tools/View/Graph.lean`), and the scan of every mark by `onBar`.
3. `StrokeCache`: an organic stroke keyed by its seed, its width, its tip and its segments moved
   to the origin. A stroke commutes with a move by whole pixels (`Equi.lean`: 160 of 160), so a
   route that only moved reuses its stroke, moved. It serves a sequence of frames.
4. `sessionPageIx`: the session page with the table's entries indexed by address and the hole
   rows built once. It replaces the per-line `List.find?` of `Program.sessionPage`
   (`tools/Tools/View/Program.lean`).

The timings are of Lean's interpreter (`lake env lean`), so their ratios matter, not their sizes.
-/

open Effect4 Effect4.Program Tools.View Tools.View.Build

/-! The tree derives no equality for these three. Since LV-0, `Call` and `Keyed` derive
`DecidableEq` and `Cubic` derives `Hashable` at their declarations (`tools/Tools/View/Picture.lean`). -/
deriving instance DecidableEq for Tools.View.Shape
deriving instance DecidableEq for Tools.View.Part
deriving instance DecidableEq for Tools.View.Line

namespace Tools.View.Fast

/-! ## 1. The integer square root -/

/-- **The integer square root by Newton's steps from above `√n`**: from `2 ^ (log₂ n / 2 + 1)`.
Every start above `⌊√n⌋` falls to `⌊√n⌋`, so this is `Grow.isqrt` with fewer steps. -/
def isqrt (n : Nat) : Nat :=
  if n < 2 then n else
  let rec go : Nat → Nat → Nat
    | 0, x => x
    | fuel + 1, x => let y := (x + n / x) / 2; if y < x then go fuel y else x
  go 128 (1 <<< (n.log2 / 2 + 1))

-- every value below 2^15, and squares, their neighbours and powers of two up to 2^60
#guard (List.range 32768).all fun n => isqrt n == Grow.isqrt n
#guard (List.range 61).all fun k =>
  let p := 2 ^ k
  [p - 1, p, p + 1, p * p - 1, p * p, p * p + 1, 3 * p + 7].all fun n => isqrt n == Grow.isqrt n
#guard [999999999999, 1000000000000, 123456789012345, 4611686018427387903].all fun n =>
  isqrt n == Grow.isqrt n

/-! ## The stroke, on the fast square root

`Grow.stroke` (`tools/Tools/View/Organic.lean`) with `dist` and `normal` on `isqrt`, and the
running lengths accumulated in reverse instead of by `acc ++ [x]`. -/

def dist (a b : Grow.P) : Nat := isqrt ((a.1 - b.1).natAbs ^ 2 + (a.2 - b.2).natAbs ^ 2)

def normal (d : Grow.P) : Grow.P :=
  let len : Int := isqrt (d.1.natAbs * d.1.natAbs + d.2.natAbs * d.2.natAbs)
  if len = 0 then (1000, 0) else (-d.2 * 1000 / len, d.1 * 1000 / len)

/-- The running lengths along the samples, from `0`. -/
def runningLengths (ss : List (Grow.P × Grow.P)) : List Nat :=
  ((ss.zip (ss.drop 1)).foldl (fun (acc : List Nat × Nat) ((a, _), (b, _)) =>
    let s := acc.2 + dist a b
    (s :: acc.1, s)) ([0], 0)).1.reverse

def stroke (seed : Nat) (o : Organic) (w : Int) (cs : List Cubic) (tip : Bool) : List Cubic :=
  let ss := Grow.samples 8 cs
  match ss with
  | [] => []
  | _ =>
    let lens := runningLengths ss
    let S := lens.getLast?.getD 0
    let ramp := o.wave / 2
    let hw := w / 2
    let side (sd : Nat) (sign : Int) : List Grow.P :=
      (ss.zip lens).map fun ((p, d), s) =>
        let h := Grow.halfWidth hw o.noise (Grow.envelope ramp S s) (Grow.noise (seed + sd) o.wave s)
        let h := if tip && S > 0 then h * (min 1000 ((S - s) * 3000 / max 1 S + 200) : Nat) / 1000 else h
        let n := normal d
        (p.1 + sign * n.1 * h / 1000, p.2 + sign * n.2 * h / 1000)
    let left := side 0 1
    let right := (side 7 (-1)).reverse
    match left.getLast?, right.head?, right.getLast?, left.head? with
    | some le, some rh, some rl, some lh =>
      Grow.through left ++ [Grow.line le rh] ++ Grow.through right ++ [Grow.line rl lh]
    | _, _, _, _ => []

/-! ## 2. The places by key, and 3. the stroke cache -/

/-- A laid graph's places by key, and the places that stand on a bar. The first place of a key
answers, as `Array.find?` does. -/
structure Ix where
  at_ : Std.HashMap Key Placed
  bars : List (Int × Int × Int)

def Ix.of (l : Laid) : Ix :=
  { at_ := l.placed.foldr (fun p m => m.insert p.key p) {}
    bars := l.marks.toList.filterMap fun
      | .bar _ x0 x1 y => some (x0, x1, y)
      | _ => none }

def Ix.find (ix : Ix) (k : Key) : Option Placed := ix.at_[k]?

def Ix.onBar (ix : Ix) (p : Placed) : Bool :=
  p.node.isNone && ix.bars.any fun (x0, x1, y) => y == p.y && x0 ≤ Laid.middle p && Laid.middle p ≤ x1

/-- **The stroke cache**: a stroke by its seed, width, tip and segments moved to the origin. -/
abbrev StrokeCache := Std.HashMap (Nat × Int × Bool × List Cubic) (List Cubic)

/-- A stroke from the cache, moved into place; or computed, and kept at the origin. The organic
settings are the look's, one look per cache. -/
def cachedStroke (cache : StrokeCache) (seed : Nat) (o : Organic) (w : Int) (cs : List Cubic)
    (tip : Bool) : List Cubic × StrokeCache :=
  match cs.head? with
  | none => (stroke seed o w cs tip, cache)
  | some c =>
    let (ox, oy) := c.p0
    let rel := cs.map (Cubic.move (-ox) (-oy))
    let key := (seed, w, tip, rel)
    let moved (s : List Cubic) := s.map (Cubic.move (1000 * ox) (1000 * oy))
    match cache[key]? with
    | some s => (moved s, cache)
    | none =>
      let s := stroke seed o w rel tip
      (moved s, cache.insert key s)

/-- `Laid.segments` on the index. -/
def segments (L : Look) (ix : Ix) (width : Int) : Route → List Cubic
  | .down _ ks _ _ =>
    let ps := ks.filterMap ix.find
    if ps.length != ks.length then [] else
    match ps with
    | [] => []
    | a :: rest =>
      let n := rest.length
      (rest.zipIdx.foldl (fun (acc : List Cubic × Laid.Pt) (b, i) =>
        if i + 1 == n then
          let into := Laid.entryAt b
          (acc.1 ++ Laid.stepDown L acc.2 into, into)
        else
          let into : Laid.Pt := (Laid.middle b, b.y)
          let out : Laid.Pt := (Laid.middle b, b.y + ROWH * BOXROWS)
          (acc.1 ++ Laid.stepDown L acc.2 into ++ [Laid.straight into out], out)) ([], Laid.exitAt a)).1
  | .back _ s d lane _ =>
    match ix.find s, ix.find d with
    | some a, some b =>
      let lx := width - CELL * (2 * lane + 1)
      let side (p : Placed) (rise : Int) : Laid.Pt :=
        if p.node.isSome then (p.x + p.w, p.y + ROWH - rise) else (p.x + 2 * CELL, p.y)
      let p : Laid.Pt := side a 0
      let q : Laid.Pt := side b BACK_RISE
      let cx := lx + (lx - max p.1 q.1) / 3
      [⟨p, (cx, p.2), (cx, q.2), q⟩]
    | _, _ => []
  | .loop _ k _ =>
    match ix.find k with
    | some a =>
      let x := a.x + a.w
      let y := a.y + ROWH
      [⟨(x, y - LOOP_HALF), (x + 2 * LOOP_REACH, y - 2 * LOOP_HALF),
        (x + 2 * LOOP_REACH, y + 2 * LOOP_HALF), (x, y + LOOP_HALF)⟩]
    | none => []

/-- `Laid.organicCalls` on the index and the cache. -/
def organicCalls (ix : Ix) (cache : StrokeCache) (L : Look) (key : Key) (ks : List Key)
    (share : Nat) (cs : List Cubic) (whole : Bool) : List (Keyed Call) × StrokeCache :=
  let o := L.organic
  let w : Int := max (o.fine : Int) ((o.trunk : Int) * share / 1000000)
  let R : Int := (o.flare : Int) * w / max 1 (o.trunk : Int)
  let surface (k : Key) : Option Int := (ix.find k).bind fun p =>
    if p.node.isSome then some 0 else if ix.onBar p then some (500 * Laid.BAR) else none
  let (body, cache) := cachedStroke cache (Grow.seedOf key) o w cs (!whole)
  let start := match cs.head?, ks.head?.bind surface with
    | some c, some off => [Grow.collar (1000 * c.p0.1) (1000 * c.p0.2 + off) w R true]
    | _, _ => []
  let finish := match whole, cs.getLast?, ks.getLast?.bind surface with
    | true, some c, some off => [Grow.collar (1000 * c.p3.1) (1000 * c.p3.2 - off) w R false]
    | _, _, _ => []
  if body.isEmpty then ([], cache) else
    (([body] ++ start ++ finish).map fun path => ⟨key, .shape .ink 1000 [path]⟩, cache)

/-- `Laid.routeCalls` on the index and the cache. -/
def routeCalls (L : Look) (ix : Ix) (width : Int) (dx dy : Int) (cache : StrokeCache) (rt : Route) :
    List (Keyed Call) × StrokeCache :=
  let cs := segments L ix width rt
  let budget : Int := (cs.map (·.size)).foldl (· + ·) 0 * rt.reveal / 1000
  let body := Laid.drawn rt.key L.strokes.edge dx dy cs budget
  match rt, cs.getLast? with
  | .down key ks _ share, _ =>
    if L.organic.trunk = 0 then (body, cache)
    else organicCalls ix cache L key ks share ((Laid.revealed cs budget).map (Cubic.move dx dy)) (1000 ≤ rt.reveal)
  | .back .., some last =>
    (if 1000 ≤ rt.reveal then body ++ Laid.arrowhead rt.key L.strokes.edge dx dy last else body, cache)
  | _, _ => (body, cache)

/-- **`Laid.calls` on the index and the cache**: equal to the tree's (`#guard`s below). -/
def calls (L : Look) (l : Laid) (dx dy : Int) (cache : StrokeCache := {}) :
    List (Keyed Call) × StrokeCache :=
  let ix := Ix.of l
  let (routes, cache) := l.routes.toList.foldl (fun (acc : List (List (Keyed Call)) × StrokeCache) rt =>
    let (cs, c) := routeCalls L ix l.width dx dy acc.2 rt
    (cs :: acc.1, c)) ([], cache)
  (l.regions.toList.flatMap (Laid.regionCalls L dx dy) ++
    routes.reverse.flatten ++
    l.marks.toList.flatMap (Laid.markCalls L dx dy) ++
    l.placed.toList.flatMap fun p => match p.node with
      | some n => Laid.boxCalls L dx dy p n
      | none => [], cache)

/-! ## 4. The session page, indexed -/

/-- **`Program.sessionPage` with the table indexed by address** and the hole rows built once. -/
def sessionPageIx (l : EditSession) (lit : Option (List Nat)) (title judgment place foot : String) :
    Page :=
  let entries : Std.HashMap (List Nat) _ := l.table.foldr (fun e m => m.insert e.path e) {}
  let rows := (l.app.withHoles l.sketch.holes).rows
  let line (n : Program.Node) : Tools.View.Line :=
    let entry := entries[n.path]?
    let result := entry.bind (·.result)
    let refusedHere := match result with
      | some (.error r) => decide (r.path = n.path)
      | _ => false
    let state : LineState :=
      if refusedHere then .refused
      else match lit with
        | some a => if a.isPrefixOf n.path then .lit else .plain
        | none => .plain
    let type := match result with
      | some (.ok t) => Tools.Code.effTyText t
      | _ => ""
    let note := match result with
      | some (.error r) => if refusedHere then "refused: " ++ Program.reasonText r else ""
      | _ => ""
    let text := match Program.holeName l n with
      | some h => "hole " ++ h
      | none => n.text
    let mark := n.op.bind fun op => Program.rowMark (nativeRowOf rows op)
    { gutter := Program.bracket n.path, depth := n.depth, text, type, mark, note,
      key := Program.bracket n.path, state }
  { title, judgment, place, foot, lines := ((Program.lines l.sketch.program).map line).toArray }

end Tools.View.Fast

