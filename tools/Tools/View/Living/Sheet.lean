import Tools.View.Living.Level

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

/-- **The page's blocks**: what the page shows, then a figure per frame. -/
def blocks : List RawNode :=
  let intro := el "p" [.text "The Queue at capacity 2 as one organism, frame by frame. Offers enter from the left and wait at the inlet; the vessel holds the messages, one slot each; takers wait at the outlet on the right. Each channel thickens with the messages that have passed through it and withers when idle (the conductivity of Physarum, Tero et al. 2010); the membrane is a level of one soft field (Wyvill's soft objects), so the vessel swells with what it holds and the inlet with the offers that press. A fine arc marks each message that moved in the step."]
  match Organism.scene with
  | .error why => [intro, el "p" [.text ("The scene stops: " ++ why)]]
  | .ok frames =>
    let ms := frames.map (·.2.1)
    let n := ms.length
    let pic (w h : Int) (calls : List (Keyed Call)) : RawNode :=
      (SvgOut.picture {} w.toNat h.toNat 1 (lowerAll 1 calls)).toRaw
    [intro,
     el "figure" [pic (Level.W n) Level.LEVEL_H (Level.level ms),
       el "figcaption" [.text "The run as one level: takers waiting below zero, messages held up to the brim, offers waiting above it; a bar line for each command."]]
       [("class", "living")],
     el "figure" [pic (Level.W n) Level.LIVES_H (Level.lives (Organism.conductivities ms)),
       el "figcaption" [.text "The lives of the channels: in from the world, into the vessel, out of it, and out to the world; each as thick at each command as its conductivity draws it."]]
       [("class", "living")]] ++
    frames.map fun (words, _, calls) =>
      el "figure" [
        (SvgOut.picture {} Organism.W.toNat Organism.H.toNat 1 (lowerAll 1 calls)).toRaw,
        el "figcaption" [.text words]]
        [("class", "living")]

/-- The page's rule for its figures: the caption small and muted under each picture. -/
def css : String :=
  "figure.living { margin: 0 0 1.25rem; max-width: none; }\n" ++
  "figure.living svg { width: 100%; height: auto; display: block; }\n" ++
  "figure.living figcaption { font-size: 0.8rem; opacity: 0.6; font-style: italic; }\n"

end Tools.View.Living.Sheet
