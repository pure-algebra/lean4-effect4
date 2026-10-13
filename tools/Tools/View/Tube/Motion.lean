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
  /-- A width that rises from nothing to `peak` at the halfway and falls back. -/
  | swell (peak : Int)
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
  | .swell p, e => .width (p * 4 * (clamp e) * (1000 - clamp e) / 1000000)
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

/-- **An event**: a stroke that lives only during the beat that leads to its picture. Its dash runs
from `from_` to `to` along the tube on `timing`, while its width swells to `peak` and back. -/
structure Event where
  key : String
  layer : Nat
  tube : Tube
  tone : Tone
  len : Nat
  from_ : Int
  to : Int
  peak : Nat
  timing : Timing
deriving Inhabited

/-- **A picture**: its marks, the poses some of them pass through on the way to it, and its
events. -/
structure Picture where
  marks : List Mark
  via : List Mark := []
  events : List Event := []
deriving Inhabited

/-- **A swell** round a unit carried along a tube from the dash `a` to the dash `b`, on the unit's
timing: the wall and the lumen widen round it and close behind it, as a tube's wall does round a
bolus that peristalsis drives (Shapiro, Jaffrin and Weinberg 1969). Two widths, so it tapers. -/
def swellOf (key : String) (t : Tube) (a b : Int × Nat) (timing : Timing) : List Event :=
  let one (k : String) (layer : Nat) (tone : Tone) (w : Nat) (extra : Nat) : Event :=
    { key := k, layer, tube := t, tone, len := a.2 + 2 * extra, from_ := a.1 - extra,
      to := b.1 - extra, peak := w, timing }
  [one (key ++ ":w1") WALLS .wall (body t.bore + SWELL) 6000,
   one (key ++ ":w2") WALLS .wall (body t.bore + 2 * SWELL) 0,
   one (key ++ ":l1") LUMENS .lumen (lumen t.bore + SWELL) 6000,
   one (key ++ ":l2") LUMENS .lumen (lumen t.bore + 2 * SWELL) 0]

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

/-- An event's tracks: its dash on its timing, its swell on the same moments, linear. -/
def Event.tracks (e : Event) : List Track :=
  [⟨e.key, .window (e.from_, e.len) (e.to, e.len) none, e.timing⟩,
   ⟨e.key, .swell e.peak, { e.timing with ease := Easing.linear }⟩]

/-! ## Writing a film -/

/-- Moments sampled of a transition: twenty, so a change follows its easing to a twentieth. -/
def MOMENTS : Nat := 20

/-- **A track as SMIL**: its poses at `MOMENTS + 1` moments of its transition, as one `animate`
for each attribute they set, from `start` milliseconds into the film (and as long after a click)
for the transition's duration. A beat is `beat` milliseconds. -/
def smil (id : String) (fromEnd : Bool) (beat start : Nat) (tr : Track) : List SvgNode :=
  let d := tr.timing.delay
  let n := max 1 tr.timing.duration
  let poses := (List.range (MOMENTS + 1)).map fun k => tr.at (d + k * n / MOMENTS)
  let ms (pm : Nat) : Nat := pm * beat / 1000
  let begin_ := s!"{start + ms d}ms;{id}.click+{start + ms d - min (start + ms d) 500}ms"
  let anim (attr : String) (vs : List String) : List SvgNode :=
    if vs.all (· == vs.headD "") then [] else
    [.element .animate
      [.attr .attributeName attr, .attr .values (";".intercalate vs), .attr .begin begin_,
       .attr .dur s!"{max 1 (ms n)}ms", .attr .fill "freeze", .attr .calcMode "linear"] []]
  match tr.change with
  | .bend .. => anim "d" (poses.map fun | .path t => pathText (if fromEnd then t.reverse else t) | _ => "")
  | .width .. | .swell _ => anim "stroke-width" (poses.map fun | .width w => num w | _ => "0")
  | .window .. =>
    anim "stroke-dasharray" (poses.map fun | .window _ l => num l ++ " " ++ num BIG | _ => "none") ++
    anim "stroke-dashoffset" (poses.map fun | .window s _ => num (-s) | _ => "0")

/-- **A film**: pictures played one beat each, every step the kit's join of two pictures and its
tracks. It starts half a second after the page loads, and again from a click on it; it holds its
end. `id` names the picture, and must be unique on the page. -/
def film (id : String) (W H : Nat) (pictures : List Picture) (beat : Nat := 1000) : SvgNode :=
  match pictures with
  | [] => still W H []
  | first :: _ =>
    let steps := (pictures.zip (pictures.drop 1)).zipIdx
    let start (i : Nat) : Nat := 500 + i * beat
    -- each mark of the film once, as it stands in the first picture, or as nothing where it is
    -- first seen
    let keys := (pictures.flatMap (·.marks.map (·.key))).eraseDups
    let marks := keys.filterMap fun k =>
      (first.marks.find? (·.key == k)).orElse fun _ =>
        ((pictures.flatMap (·.marks)).find? (·.key == k)).map (·.gone)
    let tracks := steps.flatMap fun ((A, B), i) => (A.step B).map (i, ·)
    let animsOf (m : Mark) : List SvgNode :=
      tracks.flatMap fun (i, tr) => if tr.key == m.key then smil id m.fromEnd beat (start i) tr else []
    let events := steps.flatMap fun ((_, B), i) => B.events.map fun e =>
      (e.layer, pathNode e.tube ("tube-" ++ e.tone.name) 0 true (some (e.from_, e.len))
        (e.tracks.flatMap (smil id false beat (start i))))
    Svg.Frame.svg { width := W, height := H, ratio := 1 } [.className "tube-view", .ident id]
      ((List.range LAYERS).flatMap fun l =>
        ((marks.filter (·.layer == l)).map fun m => node m (animsOf m)) ++
        ((events.filter (·.1 == l)).map (·.2)))

/-- The rules of a film's figure: its last picture stands for it where the reader prefers
reduced motion. -/
def filmCss : String :=
  ".tube-film > .tube-end { display: none; }\n" ++
  "@media (prefers-reduced-motion: reduce) { .tube-film > .tube-anim { display: none; } " ++
  ".tube-film > .tube-end { display: block; } }\n"

end Tools.View.Tube
