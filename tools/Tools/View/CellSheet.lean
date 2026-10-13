import Tools.View.Cell
import Tools.View.SvgOut
import Effect4.Library.Queue.Steps

/-!
# Tools.View.CellSheet — the Queue's cell, drawn by its type, step by step (VS-2, row 367)

A scene of the Queue at capacity two: offers and takes, each the Queue's own step term
(`src/Effect4/Library/Queue/Steps.lean`) evaluated by the machine's term evaluator (`evalTerm`)
on the cell the step before left. Each step's answer is drawn at the answer type that the step's
own type states (`Data.take`, `Data.offer`: a `Step Γ t` answers `t`), and the cell at its type
(`cellTy`). Nothing on the page is drawn by hand: a value's picture is `Cell.draw` at its type.

A request's identity and its hint are deferreds: request `n` is the deferred `n`, and its hint
the deferred `10 + n`. The scene is the tool's for now. The module's own view file
(`Library/Queue/View.lean`, row 367, point 5) takes it with the roles of VS-3.
-/

namespace Tools.View.CellSheet
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Tools.View Whatwg.Html
open Tools.View.Cell (Fig draw)
abbrev Val := Effect4.Store.Val

/-- One step of a scene: an offer of a message by a request, or a take by a request. -/
inductive Beat where
  | offer (req message : Nat)
  | take (req : Nat)

/-- **A scene**: a capacity, its beats, and the numbering of the hints (request `n`'s hint is the
deferred `hintBase + n`, so no hint shares a numeral with an identity). -/
structure Scene where
  capacity : Nat
  beats : List Beat
  hintBase : Nat := 10

/-- The scene of the cells: three offers fill the buffer and leave one pending; three takes empty
it, the first letting the pending offer in; a fourth take waits, an offer wakes it, and it takes
again. -/
def scene : Scene :=
  ⟨2, [.offer 1 10, .offer 2 20, .offer 3 30, .take 4, .take 5, .take 6, .take 7, .offer 8 40, .take 7], 10⟩

/-- A larger scene, at capacity thirteen, request `n` offering the message `10 n`: sixteen offers fill it and leave three pending at the
inlet; six takes let the three in and drain it to ten; then four more offers fill it again and
leave one pending. -/
def large : Scene :=
  ⟨13, ((List.range' 1 16).map fun n => Beat.offer n (10 * n)) ++ ((List.range' 17 6).map Beat.take) ++
      ((List.range' 23 4).map fun n => Beat.offer n (10 * n)), 100⟩

/-- The message type. -/
def A : Ty := .nat

/-- The scene of the cells' capacity. -/
def capacity : Nat := scene.capacity

/-- The answer type of a step: what its type states. -/
def answerOf {Γ : List Ty} {t : Ty} (_ : Step Γ t) : Ty := t

/-- The requests a scene names. -/
def Beat.req : Beat → Nat
  | .offer r _ => r
  | .take r => r

/-- The names a step term reads, and their values: each request's identity and hint, then the
cell. -/
def Scene.requests (sc : Scene) : List Nat := (sc.beats.map Beat.req).eraseDups
def Scene.names (sc : Scene) : List String := sc.requests.flatMap (fun n => [s!"i{n}", s!"h{n}"]) ++ ["cell"]
def Scene.values (sc : Scene) (cell : Val) : List Val :=
  sc.requests.flatMap (fun n => [Value.promise n, Value.promise (sc.hintBase + n)]) ++ [cell]

/-- A term's value in a scene, with the cell bound. -/
def Scene.evalAt (sc : Scene) (cell : Val) (src : TermSrc) : Option Val :=
  (src { names := sc.names } []).toOption.bind (evalTerm (sc.values cell) ·)

/-- A beat in words. -/
def Beat.words : Beat → String
  | .offer r m => s!"offer {m}, request {r}"
  | .take r => s!"take, request {r}"

/-- A beat's step term over the cell, and its answer type. -/
def Beat.step : Beat → TermSrc × Ty
  | .offer r m => (Queue.offerStep A (var s!"i{r}") (var s!"h{r}") (nat m) (var "cell"), answerOf (Queue.Data.offer A))
  | .take r => (Queue.takeStep A (var s!"i{r}") (var s!"h{r}") (var "cell"), answerOf (Queue.Data.take A))

/-- One frame of the scene: its words, the answer with its type, and the cell after. -/
structure Frame where
  words : String
  answer : Option (Ty × Val)
  cell : Val

/-- **A scene run**: the empty cell, then the frame of each beat, each step on the cell the step
before left. A step whose term has no value stops the scene, with the reason. -/
def Scene.run (sc : Scene) : Except String (List Frame) := do
  let some start := sc.evalAt .unit (Queue.empty A sc.capacity) | throw "the empty cell has no value"
  let (_, out) ← sc.beats.foldlM (fun (cell, out) beat => do
      let (src, t) := beat.step
      let some v := sc.evalAt cell src | throw s!"{beat.words}: the step's term has no value"
      match t, v with
      | .prod r _, .list [reply, next] => pure (next, out ++ [⟨beat.words, some (r, reply), next⟩])
      | _, _ => throw s!"{beat.words}: the answer is no pair of a reply and a cell")
    (start, [{ words := s!"the empty cell, capacity {sc.capacity}", answer := none, cell := start }])
  return out

/-- The cells' scene, run. -/
def frames : Except String (List Frame) := scene.run

/-- A value's picture as an SVG node, in the base look. -/
def svg (f : Fig) : RawNode :=
  (SvgOut.picture {} f.w f.h 1 (lowerAll 1 f.lay.items)).toRaw

private def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-- Every picture of the scene: each answer at its type and each cell at the cell's type. -/
def pictures (fs : List Frame) : List Fig :=
  fs.flatMap fun f => (f.answer.map fun (t, v) => draw t v).toList ++ [draw (Queue.cellTy A) f.cell]

/-- The page's rule for the pictures' names: muted and small (rule 3 of the composition grammar).
The label face's tone belongs in the look, for the player in C too; until then the page says it. -/
def css : String := ".e4-face-label { fill-opacity: 0.55; font-size: 12px; }\n"

/-- **The page's blocks**: what the page shows, the verdict of the composition grammar over every
picture, then a table with a row per frame: the step, its answer at its type, and the cell after
it. -/
def blocks : List RawNode :=
  let intro := el "p" [.text s!"The Queue at capacity {capacity}, step by step. Each step is the Queue's own step term, evaluated by the machine's term evaluator on the cell the step before left. The answer is drawn at the type the step states, and the cell at the cell's type: a record is a system of rows with its names once at the left; a list is a lane read from its front, the thin tick; a list of records sets each element in a column; an option is a low shelf; a request's identity or hint is the hollow dot of its deferred."]
  match frames with
  | .error why => [intro, el "p" [.text ("The scene stops: " ++ why)]]
  | .ok fs =>
    let row (f : Frame) : RawNode :=
      el "tr" [el "td" [.text f.words],
        el "td" (match f.answer with | some (t, v) => [svg (draw t v)] | none => []),
        el "td" [svg (draw (Queue.cellTy A) f.cell)]]
    let faults := (pictures fs).flatMap Cell.problems
    let verdict := if faults.isEmpty then
        "Every picture keeps the composition grammar: each text on the row grid, and no container drawn by a frame."
      else "The composition grammar refuses: " ++ "; ".intercalate faults ++ "."
    [intro, el "p" [.text verdict],
     el "div" [el "table" [
         el "thead" [el "tr" (["Step", "Answer", "Cell after"].map fun h => el "th" [.text h] [("scope", "col")])],
         el "tbody" (fs.map row)]]
       [("class", "scroll"), ("role", "region"), ("tabindex", "0"), ("aria-label", "Table: Step, Answer, Cell after")]]

end Tools.View.CellSheet
