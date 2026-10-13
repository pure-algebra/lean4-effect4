import Tools.View.Living.Level
import Tools.View.Living.Beat
import Tools.View.Living.Totals

/-!
# Tools.View.Living.Sheet — the Queue alive, frame by frame (the studio page `living.html`)

Each frame of the Queue scene drawn as one organism (`Living.Organism`): the membrane of its soft
field, the channels at their Physarum conductivities, and the units. The page is viewing
ergonomics only; nothing reads it.
-/

namespace Tools.View.Living.Sheet
open Tools.View Whatwg.Html

private def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-- A picture of logical size `w` by `h`. -/
def pic (w h : Int) (calls : List (Keyed Call)) : RawNode :=
  (SvgOut.picture {} w.toNat h.toNat 1 (lowerAll 1 calls)).toRaw

/-- A figure with its caption. -/
def figure (pics : List RawNode) (caption : String) (cls : String := "living") : RawNode :=
  el "figure" (pics ++ [el "figcaption" [.text caption]]) [("class", cls)]

/-- **A scene's blocks**: its level, its channels' lives, the beats named sampled, and the frames
named, all on the plan of its run. -/
def sceneBlocks (sc : CellSheet.Scene) (beats frames : List Nat) : List RawNode :=
  match Organism.run sc with
  | .error why => [el "p" [.text ("The scene stops: " ++ why)]]
  | .ok (plan, fs) =>
    let ms := fs.map (·.2.1)
    let ds := Organism.conductivities ms
    let form := match plan.form with | .lane => "a lane of slots" | .disc => "a disc whose units stand as a sunflower's florets"
    [el "p" [.text s!"Capacity {sc.capacity}, drawn as {form}: a unit's radius {plan.unit}, the body {plan.W} by {plan.H}."],
     figure [pic Level.LW Level.LEVEL_H (Level.level ms)]
       "The run as one level: takers waiting below zero, messages held up to the brim, offers waiting above it; a bar line for each command.",
     figure [pic Level.LW Level.LIVES_H (Level.lives ds)]
       "The lives of the channels: in from the world, into the vessel, out of it, and out to the world; each as thick at each command as its conductivity draws it.",
     figure [pic Totals.W Totals.H (Totals.picture (Totals.totals ms))]
       "Where the messages went: each split at Murray's angles, each sheath by the cube law, each lit core as wide as its count."] ++
    beats.filterMap (fun i => do
      let before ← ms[i - 1]?
      let after ← ms[i]?
      let words ← (fs[i]?).map (·.1)
      pure (figure ((Beat.samples plan before after (ds.getD (i - 1) []) (ds.getD i []) 3).map
          (fun (_, calls) => pic plan.W plan.H calls))
        s!"One beat, sampled at its start, a third, two thirds and its end: {words}." "living beat")) ++
    frames.filterMap fun i => (fs[i]?).map fun (words, _, calls) => figure [pic plan.W plan.H calls] words

/-- **The page's blocks**: what the page shows, then each scene. -/
def blocks : List RawNode :=
  [el "p" [.text "The Queue as one organism, drawn by the laws of tissue (docs/research/2026-10-13-living-quantities/anatomy.md). Offers enter from the left and wait at the inlet; the vessel holds the messages; takers wait at the outlet on the right. A channel's sheath is its history (Physarum, Tero et al. 2010), its lit core the messages it carries in the step. The vessel distends with the pressure of what it holds and draws in under the suction of takers that wait (Laplace with Hooke). Up to a capacity of eight the vessel is a lane of slots; above it, a disc whose units stand as a sunflower's florets (Vogel), the newest at the centre and the front at the rim."],
   el "h2" [.text "Capacity 2"]] ++
  sceneBlocks CellSheet.scene [3, 4, 8] (List.range 10) ++
  [el "h2" [.text "Capacity 13"]] ++
  sceneBlocks CellSheet.large [1, 14, 17] [0, 13, 16, 19, 22, 26]

/-! ## The play: a run's beats as one reel -/

/-- The samples of each beat, and the length of a beat in milliseconds: one equal beat for each
command (row 367, point 10). -/
def SAMPLES : Nat := 10
def BEAT_MS : Nat := 1000

/-- **A run's reel**: each beat of the frames named, sampled at `SAMPLES` shares, each sample a
whole picture with the beat's words in its corner. -/
def reel (sc : CellSheet.Scene) (beats : List Nat) : Organism.Plan × List (List (Keyed Call)) :=
  match Organism.run sc with
  | .error _ => (Organism.Plan.of sc.capacity 0 0, [])
  | .ok (plan, fs) =>
    let ms := fs.map (·.2.1)
    let ds := Organism.conductivities ms
    (plan, beats.flatMap fun i =>
      match ms[i - 1]?, ms[i]?, fs[i]? with
      | some before, some after, some (words, _, _) =>
        ((Beat.samples plan before after (ds.getD (i - 1) []) (ds.getD i []) SAMPLES).drop
            (if i == beats.head?.getD 0 then 0 else 1)).map fun (_, calls) =>
          calls ++ [⟨"words", .text .label 12 22 400 words⟩]
      | _, _, _ => [])

/-- **The play page's blocks**: each scene's reel, its frames stacked, each shown in its turn. -/
def playBlocks : List RawNode :=
  let one (title : String) (sc : CellSheet.Scene) (beats : List Nat) (cls : String) : List RawNode :=
    let (plan, frames) := reel sc beats
    [el "h2" [.text title],
     el "div" (frames.map fun calls => pic plan.W plan.H calls) [("class", "reel " ++ cls)]]
  [el "p" [.text "The Queue's runs, played: one beat a second, each beat sampled ten times, every sample a whole field computed from the run. It plays once and holds its end; a reader who prefers reduced motion sees the end at once. "],
   el "p" [el "a" [.text "Play again"] [("href", "play.html?again")]]] ++
  one "Capacity 2: the whole run" CellSheet.scene (List.range' 1 9) "small" ++
  one "Capacity 13: filling, overflowing, taking" CellSheet.large (List.range' 11 10) "large"

/-- The play's rules: the frames of a reel stacked, each made visible at its turn and kept, so
the latest stands on top. Generated for the frames there are; no script. -/
def playCss : String :=
  let frameMs := BEAT_MS / SAMPLES
  let rules (cls : String) (n : Nat) : String :=
    String.join ((List.range n).map fun k =>
      s!".reel.{cls} > svg:nth-child({k + 1}) \{ animation-delay: {k * frameMs}ms; }\n")
  ".reel { position: relative; width: 100%; margin: 0 0 2rem; }\n" ++
  ".reel > svg { display: block; width: 100%; height: auto; opacity: 0; animation: e4-frame 1ms linear forwards; }\n" ++
  ".reel > svg:not(:first-child) { position: absolute; left: 0; top: 0; }\n" ++
  ".reel > svg:first-child { opacity: 1; }\n" ++
  "@keyframes e4-frame { from { opacity: 1; } to { opacity: 1; } }\n" ++
  "@media (prefers-reduced-motion: reduce) { .reel > svg { animation: none; } .reel > svg:last-child { opacity: 1; } }\n" ++
  rules "small" (9 * SAMPLES + 1) ++ rules "large" (10 * SAMPLES + 1)

/-- The page's rule for its figures: the caption small and muted under each picture. -/
def css : String :=
  "figure.living { margin: 0 0 1.25rem; max-width: none; }\n" ++
  "figure.living svg { width: 100%; height: auto; display: block; }\n" ++
  "figure.living figcaption { font-size: 0.8rem; opacity: 0.6; font-style: italic; }\n"

end Tools.View.Living.Sheet
