import Tools.View.Tube.Draw
import Whatwg.Svg.Scene.Join

/-!
# Tools.View.Tube.Motion — how one picture of tubes becomes the next

The step from one picture to the next is the kit's (`Whatwg.Svg.Scene`): the join of the two
lists by key says what enters, what is kept and what leaves (`join`), and each change runs on a
`Transition`, a delay, a duration and an easing, read by `Transition.at` as a browser reads an
animation that fills both ways. A track is a key, a change and a transition, as `Track` is in
`Whatwg.Svg.Scene.Motion`.

The kit's changes are a shift, a size, a part revealed, an opacity and a change of shape point by
point. A stroke needs three it lacks, so they are here in the kit's form (`Stroke`, `Pose`,
`Track.at`), to move into it (asks W32 and W33 of `docs/research/2026-10-12-whatwg-requests.md`):

* **`bend`**: the centreline, by the intrinsic morph of `Tube.mix`, through a pose if one is given.
  Every moment of it keeps the bend law (`Tube.mix_ok`).
* **`width`**: the stroke's width; **`swell`**, a width that rises from nothing and falls back.
* **`window`**: one dash, its start and its length along the stroke: a unit carried along a pipe.

**Why SMIL.** The kit writes a track as CSS (`Whatwg.Html.Node.SvgMotion`), and WebKit animates no
CSS `d` (decisions row 354's probe). So this module writes each track as SVG `animate` elements,
the track's poses at twenty moments of its transition (decisions row 369). A reader who prefers
reduced motion sees the last picture still (`filmFigure`).
-/

namespace Tools.View.Tube
open Tools.View Whatwg.Html
open Whatwg.Svg.Scene (Easing join)
open Whatwg.Svg.Value (Path)

/-- What a stroke's track sets at a moment. -/
inductive Pose where
  | path (t : Tube)
  | width (w : Int)
  | window (start len : Int)
deriving Repr, Inhabited

/-- A progress held in `[0, 1000]`, for the morph, whose law asks for it. -/
def clamp (e : Int) : Nat := e.toNat.min 1000

/-- **A change of a stroke.** -/
inductive Stroke where
  /-- The centreline from `a` to `b` by the intrinsic morph, through `via` at the halfway of the
  easing where one is given: a span loaded suddenly passes its rest and comes back. -/
  | bend (a b : Tube) (via : Option Tube)
  | width (a b : Int)
  /-- One dash: its start and its length, from `a` to `b`, through `via` at the halfway of the
  easing where one is given: a valve that opens to let a unit in and closes behind it. -/
  | window (a b : Int × Int) (via : Option (Int × Int))
deriving Repr, Inhabited

/-- **The pose of a change** at an eased progress `e` in thousandths. -/
def Stroke.at : Stroke → Int → Pose
  | .bend a b none, e => .path (a.mix b (clamp e))
  | .bend a b (some v), e =>
    if e ≤ 500 then .path (a.mix v (clamp (2 * e))) else .path (v.mix b (clamp (2 * e - 1000)))
  | .width a b, e => .width (Whatwg.Svg.Scene.mix a b e)
  | .window a b none, e => .window (Whatwg.Svg.Scene.mix a.1 b.1 e) (Whatwg.Svg.Scene.mix a.2 b.2 e)
  | .window a b (some v), e =>
    if e ≤ 500 then .window (Whatwg.Svg.Scene.mix a.1 v.1 (2 * e)) (Whatwg.Svg.Scene.mix a.2 v.2 (2 * e))
    else .window (Whatwg.Svg.Scene.mix v.1 b.1 (2 * e - 1000)) (Whatwg.Svg.Scene.mix v.2 b.2 (2 * e - 1000))

/-- **A track**: the key of the thing it changes, the change, and its transition, in thousandths
of a beat. -/
structure Track where
  key : String
  change : Stroke
  timing : Timing

/-- **A track at the moment `t`** of its beat: its change at the transition's eased progress. -/
def Track.at (tr : Track) (t : Nat) : Pose := tr.change.at (tr.timing.at t)

/-- **The end law**: once its transition is over, a track stands at its change's end. -/
theorem Track.at_done (tr : Track) (t : Nat) (h : tr.timing.delay + tr.timing.duration ≤ t) :
    tr.at t = tr.change.at (tr.timing.ease.at 1000) := by
  unfold Track.at Whatwg.Svg.Scene.Transition.at
  rw [if_pos h]

/-! ## Pictures and steps -/

/-- **An event**: a stretch of a body that lives only during the beat that leads to its picture,
a swell that runs along the body of the mark `follows` (its tube as it stands at each moment, or
`tube` where the step has no such mark) from `from_` to `to` on `timing`, its width rising by
`peak` and falling back. -/
structure Event where
  key : String
  follows : String
  tube : Tube
  width : Nat
  len : Nat
  from_ : Int
  to : Int
  peak : Nat
  timing : Timing
  level : Nat := 0
deriving Inhabited

/-- **A picture**: its marks, the poses some of them pass through on the way to it, its events,
and its solid joins. -/
structure Picture where
  marks : List Mark
  via : List Mark := []
  events : List Event := []
  joins : List Join := []
deriving Inhabited

/-- **A swell** round a unit carried along the body `follows` from the dash `a` to the dash `b`, on
the unit's timing: the body widens round it and closes behind it, as a tube's wall does round a
bolus that peristalsis drives (Shapiro, Jaffrin and Weinberg 1969). One smooth stretch, its width
eased in and out, so the body's outline keeps its tangent. -/
def swellOf (key follows : String) (t : Tube) (a b : Int × Nat) (timing : Timing)
    (within : Option (Int × Int) := none) : List Event :=
  let reach : Nat := 12000
  let len := a.2 + 2 * reach
  -- a swell in a vessel stays on its middle, clear of the reducers at its ends
  let keep (x : Int) : Int := match within with
    | some (lo, hi) => max lo (min x (hi - (len : Int)))
    | none => x
  [{ key, follows, tube := t, width := body t.bore, len, from_ := keep (a.1 - reach),
     to := keep (b.1 - reach), peak := 2 * SWELL, timing }]

/-- **The tracks of a mark** from `a` to `b`, through `via` where one is given: its centreline on
the tube's time, its width and its dash on its own. -/
def tracksOf (a b : Mark) (via : Option Mark) : List Track :=
  let viaTube := via.bind fun v => if v.tube != b.tube then some v.tube else none
  let viaDash : Option (Int × Int) := via.bind fun v =>
    match v.dash with | some d => if v.dash != b.dash then some (d.1, d.2) else none | none => none
  (if a.tube != b.tube || viaTube.isSome then
    [⟨b.key, .bend a.tube b.tube viaTube, b.shape.getD b.move⟩] else []) ++
  (if a.width != b.width then [⟨b.key, .width a.width b.width, b.move⟩] else []) ++
  match a.dash, b.dash with
  | some d, some d' =>
    if d != d' || viaDash.isSome then [⟨b.key, .window (d.1, d.2) (d'.1, d'.2) viaDash, b.move⟩] else []
  | _, _ => []

/-- **A step** (`Picture.step`): the kit's join of two pictures by key, and the tracks of what it keeps, what enters
(from nothing where it stands) and what leaves (to nothing where it stood). -/
def Picture.step (A B : Picture) : List Track :=
  let j := join (·.key) A.marks B.marks
  j.update.flatMap (fun (a, b) => tracksOf a b (B.via.find? (·.key == b.key))) ++
  j.enter.flatMap (fun b => tracksOf b.gone b none) ++
  j.exit.flatMap (fun a => tracksOf a a.gone none)

/-! ## Writing a film -/

/-- Moments sampled of a change: twenty, so a change follows its easing to a twentieth. -/
def MOMENTS : Nat := 20

/-- **A mark under its tracks** at the moment `t` of a step: each track of its key applied. -/
def Mark.under (m : Mark) (trs : List Track) (t : Nat) : Mark :=
  trs.foldl (fun m tr => if tr.key != m.key then m else match tr.at t with
    | .path tb => { m with tube := tb }
    | .width w => { m with width := w.toNat }
    | .window s l => { m with dash := some (s, l.toNat) }) m

/-- The span of a step that some tracks take, from the first start to the last end. -/
def span (trs : List Track) : Nat × Nat :=
  (trs.foldl (fun a tr => min a tr.timing.delay) 1000,
   trs.foldl (fun a tr => max a (tr.timing.delay + tr.timing.duration)) 0)

/-- The moments of a span, `n` steps of it. -/
def moments (sp : Nat × Nat) (n : Nat := MOMENTS) : List Nat :=
  (List.range (n + 1)).map fun k => sp.1 + k * (sp.2 - sp.1) / n

/-- Moments sampled of a swell: ten, since its bump runs evenly and the browser draws straight
between close samples. -/
def SWELL_MOMENTS : Nat := 10

/-- **One attribute animated** through its values over a span of a step: begun `start`
milliseconds into the film (and as long after a click), for the span's duration, holding its end. A
beat is `beat` milliseconds. Nothing where the values do not change. -/
def animate (id : String) (beat start : Nat) (sp : Nat × Nat) (attr : String) (vs : List String) :
    List SvgNode :=
  if vs.all (· == vs.headD "") then [] else
  let ms (pm : Nat) : Nat := pm * beat / 1000
  let at_ := start + ms sp.1
  [.element .animate
    [.attr .attributeName attr, .attr .values (";".intercalate vs),
     .attr .begin s!"{at_}ms;{id}.click+{at_ - min at_ 500}ms",
     .attr .dur s!"{max 1 (ms (sp.2 - sp.1))}ms", .attr .fill "freeze", .attr .calcMode "linear"] []]

/-- A path as SVG writes it. -/
def print (p : Path) : String := String.ofList (Path.grammar.print p)

/-- **An element's animation in one step**: the mark under its tracks at every moment of their
span, each attribute of the element that changes as one `animate`: its path (a centreline, or a
filled outline that follows its tube and its width at once), and where it is stroked, its width
and its dash. -/
def partAnims (id : String) (beat start : Nat) (p : Part) (m : Mark) (trs : List Track) :
    List SvgNode :=
  let mine := trs.filter (·.key == m.key)
  if mine.isEmpty then [] else
  let sp := span mine
  let states := (moments sp).map (m.under mine)
  animate id beat start sp "d" (states.map fun s => print (p.d s)) ++
  if p.filled then [] else
    animate id beat start sp "stroke-width" (states.map (num ·.width)) ++
    animate id beat start sp "stroke-dasharray"
      (states.map fun s => match s.dash with | some (_, l) => num l ++ " " ++ num BIG | none => "none") ++
    animate id beat start sp "stroke-dashoffset"
      (states.map fun s => match s.dash with | some (a, _) => num (-a) | none => "0")

/-- **An event at a moment**: its stretch along the body it follows, as that body stands then. -/
def Event.at (e : Event) (along : Nat → Tube) (t : Nat) : Mark :=
  let p := e.timing.at t
  let lin := ({ e.timing with ease := Easing.linear } : Timing).at t
  let l := clamp lin
  let amp : Int := (e.peak * 4 * l * (1000 - l) / 1000000 : Nat)
  stretchOf e.key (along t) (Whatwg.Svg.Scene.mix e.from_ e.to p) e.len e.width e.width
    (e.width + amp.toNat) (e.len / 2)

/-- An event before it starts and after it ends: a stretch of no length and no width, which
draws nothing, cased or not, sampled at as many points as the swell. -/
def Event.rest (e : Event) : Mark :=
  stretchOf e.key e.tube e.from_ 0 0 0 0 1

/-- **A film**: pictures played one beat each, every step the kit's join of two pictures and the
marks under their tracks. It starts half a second after the page loads, and again from a click on
it; it holds its end. Each level is drawn in turn, its layers in order. `id` names the picture,
and must be unique on the page. -/
def film (id : String) (W H : Nat) (pictures : List Picture) (beat : Nat := 1000) : SvgNode :=
  match pictures with
  | [] => still W H []
  | first :: _ =>
    let steps := (pictures.zip (pictures.drop 1)).zipIdx
    let start (i : Nat) : Nat := 500 + i * beat
    -- each mark of the film once, as it stands in the first picture, or as nothing where it is
    -- first seen
    let all := pictures.flatMap (·.marks)
    let keys := (all.map (·.key)).eraseDups
    let marks := keys.filterMap fun k =>
      (first.marks.find? (·.key == k)).orElse fun _ => (all.find? (·.key == k)).map (·.gone)
    let stepTracks : List (Picture × Picture × Nat × List Track) :=
      steps.map fun ((A, B), i) => (A, B, i, A.step B)
    -- a mark as a step starts from: its pose in the second picture, or in the first where it leaves
    let baseOf (A B : Picture) (k : String) : Option Mark :=
      (B.marks.find? (·.key == k)).orElse fun _ => A.marks.find? (·.key == k)
    let animsOf (m : Mark) (p : Part) : List SvgNode :=
      stepTracks.flatMap fun (A, B, i, trs) =>
        match baseOf A B m.key with
        | some b => partAnims id beat (start i) p b trs
        | none => []
    -- a cased body is one path, defined once with its animations and drawn twice
    let bodyPath : Part := ⟨BODIES, .casing, true, fun s => closedPath s.inner.outline⟩
    let cased := (marks.filter (·.cased)).zipIdx.map fun (m, k) =>
      (m.key, s!"{id}-b{k}", pathDef s!"{id}-b{k}" (bodyPath.d m) (animsOf m bodyPath))
    let defOf (k : String) : String := ((cased.find? (·.1 == k)).map (·.2.1)).getD ""
    -- an event's path at every moment of the event, drawn twice
    let events : List (Nat × String × SvgNode) := stepTracks.zipIdx.flatMap fun ((A, B, i, trs), si) =>
      B.events.zipIdx.map fun (e, ei) =>
        let along (t : Nat) : Tube :=
          ((baseOf A B e.follows).map fun m => (m.under trs t).tube).getD e.tube
        let sp := (e.timing.delay, e.timing.delay + e.timing.duration)
        let states := (moments sp SWELL_MOMENTS).zipIdx.map fun (t, k) =>
          if k == 0 || k == SWELL_MOMENTS then { e.rest with tube := along t } else e.at along t
        let did := s!"{id}-e{si}-{ei}"
        (e.level, did, pathDef did (bodyPath.d e.rest)
          (animate id beat (start i) sp "d" (states.map fun st => print (bodyPath.d st))))
    let joinKeys : List Join := (pictures.flatMap (·.joins)).foldl
      (fun js j => if js.any (·.key == j.key) then js else js ++ [j]) []
    let joins : List (Nat × String × SvgNode) := joinKeys.zipIdx.map fun (j, k) =>
      let lv := ((all.find? (·.key == j.branch)).map (·.level)).getD 0
      let web (ms : List Mark) : Path := closedPath (j.web ms LINE)
      let anims := stepTracks.flatMap fun (A, B, i, trs) =>
        let mine := trs.filter fun tr => tr.key == j.parent || tr.key == j.branch
        if mine.isEmpty then [] else
        let sp := span mine
        let ms := [j.parent, j.branch].filterMap (baseOf A B)
        animate id beat (start i) sp "d" ((moments sp).map fun t => print (web (ms.map (·.under mine t))))
      (lv, s!"{id}-j{k}", pathDef s!"{id}-j{k}" (web first.marks) anims)
    let deepest := max (depth all) (events.foldl (fun d e => max d e.1) 0)
    let twice (layer : Nat) (did : String) : List SvgNode :=
      if layer == BODIES then [useOf did "tube-casing"]
      else if layer == INTERIORS then [useOf did "tube-ground"] else []
    Svg.Frame.svg { width := W, height := H, ratio := 1 } [.className "tube-view", .ident id]
      ([Svg.defs (cased.map (·.2.2) ++ events.map (·.2.2) ++ joins.map (·.2.2))] ++
       (List.range (deepest + 1)).flatMap fun lv => (List.range LAYERS).flatMap fun l =>
        ((marks.filter (·.level == lv)).flatMap fun m =>
          if m.cased then (if m.fill == .ink && l == INTERIORS then [] else twice l (defOf m.key))
          else (m.parts.filter (·.layer == l)).map fun p => partNode p m (animsOf m p)) ++
        ((events.filter (·.1 == lv)).flatMap fun e => twice l e.2.1) ++
        ((joins.filter (·.1 == lv)).flatMap fun e => twice l e.2.1))

/-- The rules of a film's figure: its last picture stands for it where the reader prefers
reduced motion. -/
def filmCss : String :=
  ".tube-film > .tube-end { display: none; }\n" ++
  "@media (prefers-reduced-motion: reduce) { .tube-film > .tube-anim { display: none; } " ++
  ".tube-film > .tube-end { display: block; } }\n"

end Tools.View.Tube
