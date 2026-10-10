import ProbeView.Retained
import ProbeView.Inc
import ProbeView.Layout
import Tools.View.Output

/-!
# The live loop: one request in, one patch out

A resident session (`Tools.Session`) answers one request at a time. After each request that
changes the session, `step` draws the session's page as `Build.frames` does, and answers the
**patch** from the picture before to the picture after (`Retained.diff`), as rows that extend
the stream `tools/view/draw.c` replays (`Tools.View.stream`).

Three changes from the batch frames (`Build.frames`):

- **The graph's calls** come from the fast drawing with one stroke cache for the whole session
  (`Fast.calls`): a route that only moved reuses its stroke, moved.
- **The columns are causal.** The batch fixes the gutter and the code's column at the widest of
  the whole sequence, which a live session cannot know. Here each grows, never shrinks, and grows
  in steps of `gutterStep` cells, so the page moves across rarely (`ratchet`).
- **The output is a patch.** Moves carry no calls; a put carries its object's device calls,
  relative to its anchor.

## The patch rows

| Row | Fields | Meaning |
| --- | --- | --- |
| `P` | as the stream's first row | the target, when its size changed; the look's rows follow on the first patch |
| `O` | id, anchor x, anchor y (logical pixels) | an object put; its device rows follow, relative to the anchor, until `o` |
| `M` | id, dx, dy (logical pixels) | an object moved |
| `X` | id | an object dropped |
| `G` | group, dx, dy (logical pixels) | a group's origin moved: every object in it moves |
| `I` | id, the id before it (empty: first) | a new object's place in the order of painting |
| `Q` | ids | the whole order of painting, when the old objects did not keep their order |
| `E` | frame number | the end of the patch |

An id is the object's group, its key and its run's rank, `group/key#n`. A put's anchor is in its
group; the group's origin is set by the first patch that names the group (`G` from `(0, 0)`). A device row moved by `(dx, dy)` logical
pixels is `Dev.move ratio dx dy` of it (`tools/Tools/View/Picture.lean`), so the painter offsets a
fill, a curve and a pointer box by `ratio` times the move, a text and a cut by the move, in their
own units.
-/

namespace Tools.View.Live

open Effect4 Effect4.Program Effect4.Store Tools.View Tools.View.Build Tools.View.Retained

/-- How the live loop draws. -/
structure Settings where
  look : Look := {}
  width : Int := 1280
  ratio : Nat := 2
  /-- the gutter and the code's column grow in steps of this many cells -/
  gutterStep : Nat := 8

/-- **A causal column**: never narrower than before, and grown in whole steps. -/
def ratchet (step before own : Nat) : Nat :=
  if own ≤ before then before else (own + max 1 step - 1) / max 1 step * max 1 step

/-- A causal column covers the page's own need. -/
theorem ratchet_ge_own (step before own : Nat) : own ≤ ratchet step before own := by
  unfold ratchet
  split
  · assumption
  · have hs : 0 < max 1 step := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 step)
    have := Nat.lt_div_mul_add (a := own + max 1 step - 1) hs
    omega

/-- A causal column never narrows. -/
theorem ratchet_ge_before (step before own : Nat) : before ≤ ratchet step before own := by
  unfold ratchet
  split
  · exact Nat.le_refl _
  · have := ratchet_ge_own step before own
    unfold ratchet at this
    split at this <;> omega

/-- The loop's state: the session tool's state, the retained picture, the stroke cache, the two
columns and the frame's number and size. -/
structure State where
  tool : Tools.Session.State := {}
  scene : Scene := {}
  cache : Fast.StrokeCache := {}
  gutter : Nat := 0
  codeAt : Nat := 0
  frame : Nat := 0
  size : Int × Int := (0, 0)
  /-- the texts and waits the last frame leaves (`Inc.Memo`) -/
  memo : Inc.Memo := {}

/-- The code panel's calls, each line keyed by its text (`code:` and the text), so a line that
only moved is kept, moved; the tree keys them all `""` (`codeCalls`, `tools/Tools/View/Page.lean`). -/
def codeCallsKeyed (L : Look) (W : Int) (g : Page) : List (Keyed Call) :=
  match g.code with
  | none => []
  | some c =>
    let x := col (codeCol g)
    let room := (W - LEFT - x) / CELL
    [⟨"", .vrule .rule (col (codeCol g - CODE_RULE)) HEAD_RULE (TOP + ROWH * bodyRows g - HEAD_RULE) L.strokes.rule⟩] ++
      c.lines.toList.zipIdx.flatMap fun (s, i) => cellsAt ("code:" ++ s) x (TOP + ROWH * i + BASE) s room

/-- **A page as groups**: the ground, the lines, the code, the graph at its panel's origin, and
the chrome. The graph's calls are drawn fast, on the session's stroke cache, relative to the
panel's origin, so a panel that moves down the page moves as one. -/
def pageGroups (L : Look) (W : Int) (g : Page) (cache : Fast.StrokeCache) :
    List Retained.Group × Fast.StrokeCache :=
  let (W, H) := pageSize W g
  let (graph, cache) := match g.graph with
    | none => ([], cache)
    | some p =>
      let (cs, c) := Fast.calls L p.laid 0 0 cache
      (textAt "" .label 0 (- ROWH + BASE - GRAPH_GAP) p.title HEAD_ROOM ++ cs, c)
  ([{ name := "ground", calls := groundCalls W H },
    { name := "lines", calls := g.lines.toList.zipIdx.flatMap fun (l, i) =>
        lineCalls L (linesWidth W g) (gutterCols g) i l g.marks },
    { name := "code", calls := codeCallsKeyed L W g },
    { name := "graph", origin := (LEFT, graphTop g), calls := graph },
    { name := "chrome", calls := chromeCalls L W H g }], cache)

/-- `Program.sessionPage` on given lines and the table indexed by address. -/
def sessionPageOf (l : EditSession) (ls : List Program.Node) (lit : Option (List Nat))
    (title judgment place foot : String) : Page :=
  let entries : Std.HashMap (List Nat) _ := l.table.foldr (fun e m => m.insert e.path e) {}
  let rows := (l.app.withHoles l.sketch.holes).rows
  let line (n : Program.Node) : Tools.View.Line :=
    let result := entries[n.path]?.bind (·.result)
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
  { title, judgment, place, foot, lines := (ls.map line).toArray }

/-- The page of a session after a request, as `Build.frames` titles and fills it, without the
place in a sequence, which a live session does not know. Its lines and its flow are the folds
along the edit (`Inc`); it answers the memo they leave. -/
def page (title : String) (r : Tools.Session.Request) (st' : Tools.Session.State)
    (ans : Tools.Query.Answer) (l : EditSession) (memo : Inc.Memo := {}) : Page × Inc.Memo :=
  let lit := if r.op == "open" then none else some r.path
  let edited := if r.op == "fill" || r.op == "omit" then some r.path else none
  let delta := match st'.journal, ans.ok, r.op with
    | s :: _, true, "fill" => deltaText s.delta ++ "   "
    | s :: _, true, "omit" => deltaText s.delta ++ "   "
    | _, false, _ => "refused: " ++ (ans.error.getD "") ++ "   "
    | _, _, _ => ""
  let laws := "laws: " ++ ", ".intercalate (ans.laws.map lawText)
  let prog := l.sketch.program
  let ls := Inc.lines memo edited prog
  let page := sessionPageOf l ls lit (title ++ " · " ++ requestText r) (delta ++ sessionText l) "" laws
  let holes := l.sketch.holes.map (·.name)
  let code := Program.codePanel prog (l.app.withHoles l.sketch.holes).rows holes
  let page := { page with code }
  let ws := Inc.waits memo edited prog
  let label (k : Key) : Option (String × String) :=
    (page.lines.toList.find? (·.key == k)).map fun l => (l.text, l.type)
  let laid := FastLayout.layout ((Inc.flow memo edited prog ws).relabel label)
  ({ page with graph := some { title := "program", laid } }, Inc.Memo.next ls ws)

/-- An object's id as a row field: its group, its key and its rank. -/
def idText (id : ObjId) : String := id.group ++ "/" ++ oneLine id.key ++ "#" ++ toString id.nth

/-- **A patch as rows**: each put with its device rows relative to its anchor, each move, each
drop, the order when it changed, and the end. -/
def patchRows (ratio : Nat) (frame : Nat) (p : Patch) : List String :=
  p.ops.flatMap (fun
    | .put id o =>
      s!"O\t{idText id}\t{o.anchor.1}\t{o.anchor.2}" ::
        ((lowerAll ratio (o.rel.map fun c => ⟨id.key, c⟩)).map fun d => d.call.row d.key) ++ ["o"]
    | .move id dx dy => [s!"M\t{idText id}\t{dx}\t{dy}"]
    | .drop id => [s!"X\t{idText id}"]
    | .shift g dx dy => [s!"G\t{g}\t{dx}\t{dy}"]) ++
  p.inserts.map (fun (id, prev) => s!"I\t{idText id}\t{(prev.map idText).getD ""}") ++
  (match p.order with
    | some ids => ["Q\t" ++ "\t".intercalate (ids.map idText)]
    | none => []) ++
  [s!"E\t{frame}"]

/-- **One step of the live loop**: the session's answer, and the patch rows when the request
changed the session. -/
def step (s : Settings) (title : String) (st : State) (r : Tools.Session.Request) :
    State × Tools.Query.Answer × List String :=
  let (tool, ans) := Tools.Session.answer st.tool r
  match tool.session with
  | none => ({ st with tool }, ans, [])
  | some l =>
    if r.op == "view" || r.op == "journal" || r.op == "sketch" then ({ st with tool }, ans, []) else
    let (g, memo) := page title r tool ans l st.memo
    let gutter := ratchet s.gutterStep st.gutter (ownGutter g)
    let codeAt := ratchet s.gutterStep st.codeAt (ownCodeAt g)
    let g := { g with gutter, codeAt }
    let (groups, cache) := pageGroups s.look s.width g st.cache
    let scene := Scene.ofGroups groups
    let patch := diff st.scene scene
    let size := pageSize s.width g
    let head := if size == st.size then [] else
      s!"P\t{size.1.toNat * 1000}\t{size.2.toNat * 1000}\t{s.ratio * 1000}\t{if s.look.scheme = .light then 1 else 0}\t{if s.look.hue then 1 else 0}\t{s.look.motion.step}" ::
        (if st.frame == 0 then lookRows s.look else [])
    ({ tool, scene, cache, gutter, codeAt, frame := st.frame + 1, size, memo },
      ans, head ++ patchRows s.ratio (st.frame + 1) patch)

end Tools.View.Live
