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
the deferred `100 + n`. The scene is the tool's for now. The module's own view file
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

/-- The scene: three offers fill the buffer and leave one pending; three takes empty it, the
first letting the pending offer in; a fourth take waits, an offer wakes it, and it takes again. -/
def scene : List Beat :=
  [.offer 1 10, .offer 2 20, .offer 3 30, .take 4, .take 5, .take 6, .take 7, .offer 8 40, .take 7]

/-- The capacity, and the message type. -/
def capacity : Nat := 2
def A : Ty := .nat

/-- The answer type of a step: what its type states. -/
def answerOf {Γ : List Ty} {t : Ty} (_ : Step Γ t) : Ty := t

/-- The names a step term reads, and their values: each request's identity and hint, then the
cell. -/
def requests : List Nat := List.range' 1 9
def names : List String := requests.flatMap (fun n => [s!"i{n}", s!"h{n}"]) ++ ["cell"]
def values (cell : Val) : List Val :=
  requests.flatMap (fun n => [Value.promise n, Value.promise (100 + n)]) ++ [cell]

/-- A term's value with the cell bound. -/
def evalAt (cell : Val) (src : TermSrc) : Option Val :=
  (src { names := names } []).toOption.bind (evalTerm (values cell) ·)

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

/-- **The scene run**: the empty cell, then the frame of each beat, each step on the cell the step
before left. A step whose term has no value stops the scene, with the reason. -/
def frames : Except String (List Frame) := do
  let some start := evalAt .unit (Queue.empty A capacity) | throw "the empty cell has no value"
  let (_, out) ← scene.foldlM (fun (cell, out) beat => do
      let (src, t) := beat.step
      let some v := evalAt cell src | throw s!"{beat.words}: the step's term has no value"
      match t, v with
      | .prod r _, .list [reply, next] => pure (next, out ++ [⟨beat.words, some (r, reply), next⟩])
      | _, _ => throw s!"{beat.words}: the answer is no pair of a reply and a cell")
    (start, [{ words := "the empty cell, capacity 2", answer := none, cell := start }])
  return out

/-- A value's picture as an SVG node, in the base look. -/
def svg (f : Fig) : RawNode :=
  (SvgOut.picture {} f.w f.h 1 (lowerAll 1 f.lay.items)).toRaw

private def el (tag : String) (children : List RawNode) (attrs : List (String × String) := []) : RawNode :=
  .element tag attrs children

/-- **The page's blocks**: what the page shows, then a table with a row per frame: the step, its
answer at its type, and the cell after it. -/
def blocks : List RawNode :=
  let intro := el "p" [.text s!"The Queue at capacity {capacity}, step by step. Each step is the Queue's own step term, evaluated by the machine's term evaluator on the cell the step before left. The answer is drawn at the type the step states, and the cell at the cell's type: a record is a panel of its fields, a list a row of cells with the first at the left, an option a cup, a request's identity or hint the hollow dot of its deferred."]
  match frames with
  | .error why => [intro, el "p" [.text ("The scene stops: " ++ why)]]
  | .ok fs =>
    let row (f : Frame) : RawNode :=
      el "tr" [el "td" [.text f.words],
        el "td" (match f.answer with | some (t, v) => [svg (draw t v)] | none => []),
        el "td" [svg (draw (Queue.cellTy A) f.cell)]]
    [intro,
     el "div" [el "table" [
         el "thead" [el "tr" (["Step", "Answer", "Cell after"].map fun h => el "th" [.text h] [("scope", "col")])],
         el "tbody" (fs.map row)]]
       [("class", "scroll"), ("role", "region"), ("tabindex", "0"), ("aria-label", "Table: Step, Answer, Cell after")]]

end Tools.View.CellSheet
