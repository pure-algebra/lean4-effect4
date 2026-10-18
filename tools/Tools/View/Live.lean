import Tools.View.Build
import Tools.View.Inc
import Tools.View.Retained
import Tools.View.Output

/-!
# The live loop: one request in, one patch out

A resident tool state (`Effect4.Tool.serve`) answers one request at a time. After each request that
changes the session, `step` draws the session's page as `Build.frames` does, and answers the
**patch** from the picture before to the picture after (`Retained.diff`), as rows that extend the
stream `tools/view/replay.h` replays (`Tools.View.stream`). This is slice LV-6 of the live view
(`docs/research/2026-10-10-live-view/LANDING.md`); the driver is `tools/Drivers/Live.lean`.

Three things differ from the batch frames (`Build.frames`):

- **The page's folds run along the edit.** The lines and the flow take each text outside the
  edited subtree from the memo the frame before left (`Inc.lines`, `Inc.flow`); the waits are
  computed fresh.
- **The graph's calls** come from one stroke cache for the whole session (`Laid.callsCached`): a
  route that only moved reuses its stroke, moved.
- **The columns look back.** The batch fixes the gutter and the code's column at the widest of the
  whole sequence, which a live session cannot know. Here each column is the widest so far
  (`ratchet` at a step of one cell), never narrower than before. A step of more cells is LV-8's
  proposal, which waits for the owner (`Settings.columnStep`).

The code lines keep the tree's key, the empty one (`codeCalls`): keys by a line's text are LV-8's.

## The patch rows

| Row | Fields | Meaning |
| --- | --- | --- |
| `P` | as the stream's first row | the target, when its size changed; the look's rows follow on the first patch |
| `G` | group, dx, dy (logical pixels) | a group's origin moved: every object in it moves |
| `O` | id, anchor x, anchor y (logical pixels) | an object put; its device rows follow, relative to the anchor, until `o` |
| `M` | id, dx, dy (logical pixels) | an object moved |
| `X` | id | an object dropped |
| `I` | id, the id before it (empty: first) | a new object's place in the order of painting |
| `Q` | ids | the whole order of painting, when the old objects did not keep their order |
| `E` | frame number | the end of the patch |

An id is the object's group, its key and its run's rank, `group/key#n`. A group's origin starts at
`(0, 0)`. A device row moved by `(dx, dy)` logical pixels is `Dev.move ratio dx dy` of it
(`tools/Tools/View/Picture.lean`): the painter offsets a fill, a curve and a pointer box by `ratio`
times the move, a text and a cut by the move, in their own units. By the lowering's move law
(`lowerCall_move`) and the patch law (`Retained.apply_diff`), a store that applies the rows writes
the stream of the whole page.
-/

namespace Tools.View.Live

open Effect4 Effect4.Program Effect4.Store Tools.View Tools.View.Build Tools.View.Retained

/-- How the live loop draws. -/
structure Settings where
  look : Look := {}
  width : Int := 1280
  ratio : Nat := 2
  /-- the gutter and the code's column grow in steps of this many cells; one cell is the batch's
  rule read causally, the widest so far -/
  columnStep : Nat := 1

/-- **A causal column**: never narrower than before, and grown in whole steps. -/
def ratchet (step before own : Nat) : Nat :=
  if own ≤ before then before else (own + max 1 step - 1) / max 1 step * max 1 step

/-- A causal column covers the page's own need. A tool law; its consumer is the live step, whose
lines never stand under the code. Placement: concept `initial-algebras-folds`, R14's live
authoring. -/
theorem ratchet_ge_own (step before own : Nat) : own ≤ ratchet step before own := by
  unfold ratchet
  split
  · assumption
  · have hs : 0 < max 1 step := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 step)
    have := Nat.lt_div_mul_add (a := own + max 1 step - 1) hs
    generalize (own + max 1 step - 1) / max 1 step * max 1 step = x at this ⊢
    generalize max 1 step = m at hs this ⊢
    omega

/-- A causal column never narrows. A tool law; its consumer is the live step, whose page moves
across only when a column grows. Placement: concept `initial-algebras-folds`, R14's live
authoring. -/
theorem ratchet_ge_before (step before own : Nat) : before ≤ ratchet step before own := by
  have h := ratchet_ge_own step before own
  unfold ratchet at h ⊢
  split
  · exact Nat.le_refl _
  · rename_i hlt
    rw [if_neg hlt] at h
    exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_not_le hlt)) h

/-- The loop's state: the session tool's state, the retained picture, the stroke cache, the two
columns, the frame's number and size, and the texts the last frame leaves. -/
structure State where
  tool : Effect4.Tool.State := Effect4.Tool.empty
  scene : Scene := {}
  cache : Laid.StrokeCache := {}
  gutter : Nat := 0
  codeAt : Nat := 0
  frame : Nat := 0
  size : Int × Int := (0, 0)
  memo : Inc.Memo := {}

/-- **A page as groups**: the ground, the lines, the code, the graph at its panel's origin, and the
chrome. The graph's calls are drawn on the session's stroke cache, relative to the panel's origin,
so a panel that moves down the page moves as one. -/
def drawingGroups (drawing : PageDrawing) : List Group :=
  [{ name := "ground", calls := drawing.ground },
   { name := "lines", calls := drawing.lines },
   { name := "code", calls := drawing.code },
   { name := "graph", origin := drawing.graphOrigin, calls := drawing.graph },
   { name := "chrome", calls := drawing.chrome }]

/-- Prepare a page once and retain its drawing groups. -/
def pageGroups (L : Look) (W : Int) (g : Page) (cache : Laid.StrokeCache) :
    List Group × Laid.StrokeCache :=
  let drawing := pageDrawingCached L W g cache
  (drawingGroups drawing, drawing.cache)

/-- The page of a session after a request, as `Build.frames` titles and fills it, without the
place in a sequence, which a live session does not know. Its lines and its flow are the folds
along the edit (`Inc`); it answers the memo they leave. -/
def page (title : String) (r : Effect4.Tool.Request) (before : Effect4.Tool.State)
    (ans : Effect4.Tool.Reply) (l : EditSession) (memo : Inc.Memo) : Page × Inc.Memo :=
  let lit := editPath before r
  let edited := if ans.result.isOk then lit else none
  let delta := (deltaOf ans).1
  let laws := ""
  let prog := l.sketch.program
  let ls := Inc.lines memo edited prog
  let pg := Program.sessionPageOf l ls lit (title ++ " · " ++ requestText r) (delta ++ sessionText l) "" laws
  let holes := l.sketch.holes.map (·.name)
  let pg := { pg with code := Program.codePanel prog (l.app.withHoles l.sketch.holes).rows holes }
  let label (k : Key) : Option (String × String) :=
    (pg.lines.toList.find? (·.key == k)).map fun n => (n.text, n.type)
  let laid := Flow.layout ((Inc.flow memo edited prog).relabel label)
  ({ pg with graph := some { title := "program", laid } }, Inc.Memo.next ls)

/-- An object's id as a row field: its group, its key and its rank. -/
def idText (id : ObjId) : String := id.group ++ "/" ++ oneLine id.key ++ "#" ++ toString id.nth

/-- **A patch as rows**: each operation, then each new object's place or the whole order, then the
end. A put carries its device rows relative to its anchor. -/
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

/-- The target's row, as the stream's first row writes it (`Tools.View.stream`). -/
def targetRow (L : Look) (ratio : Nat) (size : Int × Int) : String :=
  s!"P\t{size.1.toNat * 1000}\t{size.2.toNat * 1000}\t{ratio * 1000}\t{if L.scheme = .light then 1 else 0}\t{if L.hue then 1 else 0}\t{L.motion.step}"

/-- **One step of the live loop**: the session's answer, and the patch rows when the request
changed the session. A view of the session, its journal or its sketch changes nothing. -/
def step (s : Settings) (title : String) (st : State) (r : Effect4.Tool.Request) :
    State × Effect4.Tool.Reply × List String :=
  let (tool, ans) := (Effect4.Tool.serve Effect4.Program.Check.Oracle.uncached st.tool r).value
  match tool.raw.doc with
  | none => ({ st with tool }, ans, [])
  | some doc =>
    if !redraws r then ({ st with tool }, ans, []) else
    let l := doc.session.shown
    let (g, memo) := page title r st.tool ans l st.memo
    let gutter := ratchet s.columnStep st.gutter (ownGutter g)
    let codeAt := ratchet s.columnStep st.codeAt (ownCodeAt g)
    let g := { g with gutter, codeAt }
    let drawing := pageDrawingCached s.look s.width g st.cache
    let cache := drawing.cache
    let scene := Scene.ofGroups (drawingGroups drawing)
    let patch := diff st.scene scene
    let size := drawing.size
    let head := if size == st.size then [] else
      targetRow s.look s.ratio size :: (if st.frame == 0 then lookRows s.look else [])
    ({ tool, scene, cache, gutter, codeAt, frame := st.frame + 1, size, memo },
      ans, head ++ patchRows s.ratio (st.frame + 1) patch)

/-- The whole stream of the page a step drew, as the batch writes a frame (`Tools.View.stream`):
what the patch rows rebuild in a store that applies them. -/
def wholeStream (s : Settings) (st : State) : List String :=
  stream s.look st.size.1.toNat st.size.2.toNat s.ratio (lowerAll s.ratio st.scene.flatten)

end Tools.View.Live
