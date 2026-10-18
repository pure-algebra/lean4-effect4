import Tools.View.Build
import Tools.View.Inc
import Tools.View.Retained
import Tools.View.Live
import Tools.View.GraphCheck

/-!
# The live view's checks

Each slice of the live view (`docs/research/2026-10-10-live-view/LANDING.md`) replaces named
functions of the view with faster ones, and its laws stand beside its functions. This module holds
what no theorem covers, on every frame of the view's builds: the wire corpus
(`Effect4.Program.Wire.Corpus.all`) and two generated families of programs. Each line is a reader
of a law at the frames the view draws, a control that shows why a premise stands, or a finite
evaluation that no theorem covers.
-/

open Effect4 Effect4.Program Tools.View Tools.View.Build

namespace Tools.View.LiveChecks

/-- A fork's options: the parent does not wait, and the child inherits. -/
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩

/-- `n` forks, each awaited at once. -/
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))

/-- `n` forks, then `k` awaits, the first forked awaited first. -/
def forksInOrder : Nat → Nat → Nat → NativeEff
  | 0, L, k => awaits k 0 L
  | n + 1, L, k =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (forksInOrder n (L + 1) k)
where
  /-- `j` awaits of the fibers from the `i`-th. -/
  awaits : Nat → Nat → Nat → NativeEff
    | 0, _, _ => .succeed (.lit .unit)
    | j + 1, i, L => .bind (.awaitFiber (.var i) .awaitValue) (awaits j (i + 1) (L + 1))

/-- The programs the checks build: the corpus, a chain and forks awaited first first. -/
def programs : List NativeEff :=
  Effect4.Program.Wire.Corpus.all.map (·.2) ++ [chain 4 0, forksInOrder 3 0 3]

/-- Every frame of a program built by edits. -/
def framesOf (p : NativeEff) : List Frame := ((requests p).map (frames "t")).getD []

/-- A frame's laid graph. -/
def laidOf (f : Frame) : Laid := (f.page.graph.map (·.laid)).getD {}

/-- The laid graphs of a program's frames, with the moments of motion at a quarter, a half and
three quarters of each step (`sampleLaid`). -/
def laidsOf (L : Look) (p : NativeEff) : List Laid :=
  let ls := (framesOf p).map laidOf
  match ls with
  | [] => []
  | first :: _ => first :: (ls.zip (ls.drop 1)).flatMap fun (a, b) =>
      [250, 500, 750].map (sampleLaid L.motion.norm a b) ++ [b]

-- The session accepts every request of a build: each fill carries its whole target, which the
-- checked commit requires, so every frame after the opening shows an accepted fill.
#guard programs.all fun p =>
  match requests p with
  | none => true
  | some reqs => (reqs.foldl (fun (acc : Tools.Session.State × Bool) r =>
      let (st', ans) := Tools.Session.answer acc.1 r
      (st', acc.2 && ans.ok)) ({}, true)).2

-- A control: the same build with its targets dropped is refused at its first fill.
#guard programs.any fun p =>
  match requests p with
  | some (opening :: fill :: _) =>
    let (st, _) := Tools.Session.answer {} opening
    !(Tools.Session.answer st { fill with revision := none }).2.ok
  | _ => false

/-! ## LV-2: the graph's calls on a key index and a stroke cache -/

-- One stroke cache carried along every frame and every moment of motion of a build answers each
-- drawing's calls on a fresh cache: `Connector.cached_eq`, read at the drawings the driver writes.
#guard programs.all fun p =>
  let L : Look := {}
  ((laidsOf L p).foldl (fun (acc : Bool × Laid.StrokeCache) l =>
    let (cs, c) := l.callsCached L 24 200 acc.2
    (acc.1 && cs == l.calls L 24 200, c)) (true, {})).1

/-- A line for the controls: a bump, then a straight run. -/
def controlLine : List Cubic := [⟨(0, 0), (0, 12), (40, 18), (40, 30)⟩, Grow.line (40, 30) (40, 60)]

-- The controls of the cache's key. A growing stroke is not the whole one, so the key holds the
-- tip; another noise draws another stroke, so the key holds the noise.
#guard Connector.stroke 7 {} 2400 controlLine true none none !=
  Connector.stroke 7 {} 2400 controlLine false none none
#guard Connector.stroke 7 {} 2400 controlLine false none none !=
  Connector.stroke 7 { noise := 100 } 2400 controlLine false none none

/-- A connector request for finite cache controls. -/
def dockRequest : Connector.Request := {
  seed := 7, noise := 0, wave := 40000, width := 2400, tip := false,
  segments := controlLine, source := some ⟨0, 6000⟩, target := some ⟨0, 6000⟩ }

-- The same route with a changed docking surface must not reuse the old outline.
#guard dockRequest.outline != { dockRequest with source := some ⟨2000, 6000⟩ }.outline
#guard dockRequest.outline != { dockRequest with target := some ⟨0, 3000⟩ }.outline
#guard let cache := (Connector.cached {} dockRequest).2
  let changed := { dockRequest with target := some ⟨-1000, 3000⟩ }
  (Connector.cached cache changed).1 == changed.outline

/-- Equal-rank points form an admitted horizontal route. -/
def horizontalFixture : Laid := {
  placed := #[{ key := "a", x := 0, y := 0, w := 16 },
    { key := "b", x := 40, y := 0, w := 16 }],
  routes := #[.down "a→b" ["a", "b"]], width := 80, height := 16 }

-- The renderer must retain this admitted route even though a vertical flare does not apply.
#guard (GraphCheck.laid horizontalFixture).isOk
#guard match horizontalFixture.calls {} 0 0 with
  | [⟨"a→b", .shape .ink 1000 [path]⟩] => !path.isEmpty
  | _ => false

/-- A laid graph whose two places share a key. -/
def twice : Laid := { placed := #[{ key := "k", x := 0, y := 0, w := 8 }, { key := "k", x := 40, y := 0, w := 8 }] }

-- The control of the index's order: `Laid.find` answers a key's first place, as the index does;
-- an index put first first answers the last place.
#guard ((Laid.Ix.of twice).find "k").map (·.x) == some 0
#guard (((twice.placed.toList.foldl (fun m p => m.insert p.key p) ({} : KeyMap Key Placed)).get? "k").map (·.x)) ==
  some 40

/-- Two points on bars, with an organic connector between them. -/
def dockFixture : Laid := {
  placed := #[{ key := "a", x := 12, y := 8, w := 16 },
    { key := "b", x := 12, y := 32, w := 16 }]
  marks := #[.bar "top" 0 40 8, .bar "bottom" 0 40 32]
  routes := #[.down "e" ["a", "b"]]
  width := 40, height := 36 }

/-- Read the two transverse faces of one emitted connector perimeter. -/
def connectorFaces (calls : List (Keyed Call)) : Option (Int × Int) := do
  match calls with
  | [⟨_, .shape _ _ [path]⟩] =>
    return ((← path.head?).p0.2, (← path[(path.length - 2) / 2]?).p0.2)
  | _ => none

-- The odd-height bar occupies [7, 10] and [31, 34]. Both collars meet those painted surfaces.
-- The pre-change target face is 30500, leaving a half-pixel slit above the second bar.
#guard [0, 19, -7].all fun dy =>
  let cs := (Laid.routeCalls {} dockFixture.find dockFixture.onBar 40 11 dy {}
    (.down "e" ["a", "b"])).1
  connectorFaces cs == some (1000 * (dy + 10), 1000 * (dy + 31))

-- A growing connector has no target collar. Its source still meets the painted bar.
#guard [250, 500, 750].all fun reveal =>
  let cs := (Laid.routeCalls {} dockFixture.find dockFixture.onBar 40 0 0 {}
    (.down "e" ["a", "b"] reveal)).1
  match connectorFaces cs with
  | some (source, tip) => source == 10000 && 10000 < tip && tip < 31000
  | none => false

/-- A node during its entrance. The painted top is twelve pixels below its final top. -/
def growingTarget : Placed :=
  { key := "b", x := 0, y := 72, w := 80,
    node := some { key := "b", line1 := "b" }, grow := 483 }

#guard Laid.entryAt growingTarget == (40, 84)
#guard Laid.exitAt growingTarget == (40, 107)

-- Side routes dock on the growing side, including the loop's two attachment points.
#guard
  let cs := Laid.segments {} (fun _ => some growingTarget) 140 (.back "back" "b" "b" 0)
  (cs.head?.map (·.p0)) == some (59, 95) && (cs.getLast?.map (·.p3.1)) == some 59
#guard
  let cs := Laid.segments {} (fun _ => some growingTarget) 140 (.loop "loop" "b")
  cs.all fun c => c.p0.1 == 59 && c.p3.1 == 59 &&
    84 ≤ c.p0.2 && c.p3.2 ≤ 107

-- A collar stays behind a short growing tip. Before the fix, its end reaches 54000.
#guard
  let source : Placed :=
    { key := "a", x := 0, y := 0, w := 80, node := some { key := "a", line1 := "a" } }
  let cs : List (Keyed Call) := (Laid.organicCalls (fun _ => some source) (fun _ => false)
    {} {} "e" ["a", "b"] 1000000 [⟨(40, 48), (40, 49), (40, 50), (40, 51)⟩] false).1
  match cs with
  | [⟨_, Call.shape _ _ [path]⟩] => path.all fun c =>
    [c.p0, c.p1, c.p2, c.p3].all fun p => 48000 ≤ p.2 && p.2 ≤ 51000
  | _ => false

/-! ## LV-3: the layout in linear time -/

/-- Every intermediate program of a build: each answered request's sketch. -/
def sketchesOf (p : NativeEff) : List NativeEff :=
  match requests p with
  | none => []
  | some reqs => (reqs.foldl (fun (acc : Tools.Session.State × List NativeEff) r =>
      let (st, _) := Tools.Session.answer acc.1 r
      (st, acc.2 ++ (st.session.map (·.sketch.program)).toList)) ({}, [])).2

/-- Kahn's order by tables is Kahn's order on a flow's edges and accepted waits, as `orderFor`
takes it. -/
def kahnAgrees (f : Flow.Flow) : Bool :=
  let b := Flow.lay f
  let dag := (Flow.acceptWaits b.items.length b.edges b.waitEdges).1
  Flow.kahnTable b.items.length dag == Flow.kahn b.items.length dag

-- On the flow of every sketch of every build, and on every program at once as one flow in
-- parallel. A finite evaluation: no law reads the order, since `orderFor` checks it, but the
-- picture does.
#guard programs.all fun p => (sketchesOf p).all fun q => kahnAgrees (Flow.ofProgram q)
#guard kahnAgrees (Flow.Flow.par .fork "[]" (programs.map Flow.ofProgram))

-- The controls of the order's check. An order with a repeat serves no edge, though its first
-- positions stand in the edge's direction; a cycle has no order, so the check falls back.
#guard Flow.ordersTable [0, 1, 0] [{ fr := 0, to := 1 }] == false
#guard Flow.posBefore (Flow.firstAt (Flow.positionsOf [0, 1, 0]) 0) (Flow.firstAt (Flow.positionsOf [0, 1, 0]) 1)
#guard Flow.kahnTable 2 [{ fr := 0, to := 1 }, { fr := 1, to := 0 }] == []
#guard Flow.ordersTable (Flow.kahnTable 2 [{ fr := 0, to := 1 }, { fr := 1, to := 0 }])
  [{ fr := 0, to := 1 }, { fr := 1, to := 0 }] == false

/-! ## The definition block's flow -/

/-- A definition block (decisions row 328): one definition, whose body answers its request, a main
program of two steps, and no module layer. -/
def defsBlock : NativeEff :=
  .defs [{ name := "echo", request := .nat, answer := .nat }] (.cons (.succeed (.var 0)) .nil)
    (.bind (.yieldNow 0) (.succeed (.lit (.nat 1)))) .nil

-- The control of the block's arm of `Flow.flowOf`: a block has three children (the bodies, the
-- main program and the module's layers), and its flow is the region `definitions` around the main
-- program's flow, its two steps at `[1 0]` and `[1 1]`. An arm of another arity draws the block's
-- own node, then the bodies, then the main program, in series.
#guard match Flow.ofProgram defsBlock with
  | .region "definitions" "[]" (.seq [.node "[1 0]" _ _ _, .node "[1 1]" _ _ _]) => true
  | _ => false

/-! ## LV-4: the folds along an edit -/

/-- A line as the checks compare it: its address, depth, text and operation. -/
def lineView (n : Program.Node) : List Nat × Nat × String × Option NativeOp := (n.path, n.depth, n.text, n.op)

/-- At every step of a build, the lines along the edit are the fresh lines, and the flow along the
edit is the fresh flow. -/
def incAgrees (p : NativeEff) : Bool :=
  match requests p with
  | none => false
  | some reqs =>
    (reqs.foldl (fun (acc : Bool × Tools.Session.State × Inc.Memo) r =>
      let (ok, st, memo) := acc
      let (st', _) := Tools.Session.answer st r
      match st'.session with
      | none => (ok, st', memo)
      | some l =>
        let prog := l.sketch.program
        let edited := if r.op == "fill" || r.op == "omit" then some r.path else none
        let ls := Inc.lines memo edited prog
        (ok && ls.map lineView == (Program.lines prog).map lineView &&
          Inc.flow memo edited prog == Flow.ofProgram prog, st', Inc.Memo.next ls)) (true, {}, {})).1

-- The text law (`Inc.linesWith_eq`) and the memo's (`Inc.next_valid`), read at every step of every
-- build, where `ownText` stands for the text: the lines along each edit are the fresh lines. The
-- flow along each edit is the fresh flow: a finite evaluation that no theorem covers.
#guard programs.all incAgrees

/-- Codex's sibling edit (LV-OW-01): a fork, then an await of it, at the address `[1]`. -/
def siblingSource : NativeEff := .withFiber (.fork (.succeed (.lit .unit)) later)
def siblingOld : NativeEff := .bind siblingSource (.awaitFiber (.var 0) .awaitValue)
def siblingFill : NativeEff := .bind (.yieldNow 0) siblingSource
def siblingNew : NativeEff := .bind siblingFill (.awaitFiber (.var 0) .awaitValue)

-- The edit keeps its focus's type and splices the table; the await stays at `[1]`.
#guard match ((EditSession.open {} { program := siblingOld }).feedStep (.fill [0] siblingFill)).2.delta with
  | .spliced _ => true
  | _ => false
#guard ((EditSession.open {} { program := siblingOld }).feedStep (.fill [0] siblingFill)).1.sketch.program ==
  siblingNew

/-- A program's flow drawn with given waits, for the controls. -/
def flowWithWaits (program : NativeEff) (ws : List (Key × List Key)) : Flow.Flow :=
  let part := cata_eff (EffAlgebra.ofLayer (Flow.flowLayer fun k => (ws.lookup k).getD [])) program []
  part.flow.closing part.releases

-- The controls: the await's wait reads the fork beside it, outside the edited subtree. A wait kept
-- from the old program is a stale edge in the new one; a wait kept from the new program misses the
-- edge in the old one.
#guard Flow.waits siblingOld == [("[1]", ["[0 0]"])]
#guard Flow.waits siblingNew == []
#guard flowWithWaits siblingNew (Flow.waits siblingOld) != Flow.ofProgram siblingNew
#guard flowWithWaits siblingOld (Flow.waits siblingNew) != Flow.ofProgram siblingOld

-- The flow along the edit computes the waits fresh: it is the fresh flow, both ways; and the text
-- memo stays valid across the same edit.
#guard Inc.flow (Inc.Memo.next (Program.lines siblingOld)) (some [0]) siblingNew == Flow.ofProgram siblingNew
#guard Inc.flow (Inc.Memo.next (Program.lines siblingNew)) (some [0]) siblingOld == Flow.ofProgram siblingOld
#guard (Inc.lines (Inc.Memo.next (Program.lines siblingOld)) (some [0]) siblingNew).map lineView ==
  (Program.lines siblingNew).map lineView

-- The control of the text law's premise: a memo kept from another program answers its own texts
-- outside the edit, and the lines along the edit are then not the fresh lines.
#guard (Inc.lines (Inc.Memo.next (Program.lines siblingNew)) (some [1]) siblingOld).map lineView !=
  (Program.lines siblingOld).map lineView

/-! ## LV-5: the retained scene -/

/-- The pictures of a program's frames, at the page width the driver uses. -/
def picturesOf (p : NativeEff) : List (List (Keyed Call)) := (framesOf p).map fun f => pageCalls {} 1280 f.page

-- The two laws of the retained scene, read at every picture and every two consecutive pictures of
-- every build: a picture read as objects and flattened is the picture (`Retained.of_flatten`), and
-- the scene of one picture patched by the diff to the next flattens to the next
-- (`Retained.apply_diff`, whose premise every scene read from one group meets, `ofGroups_wf`).
#guard programs.all fun p => (picturesOf p).all fun cs => (Retained.Scene.of cs).flatten == cs
#guard programs.all fun p =>
  let ps := picturesOf p
  (ps.zip (ps.drop 1)).all fun (a, b) =>
    let (sa, sb) := (Retained.Scene.of a, Retained.Scene.of b)
    (sa.apply (Retained.diff sa sb)).flatten == b

-- The ranks: a key that returns after another key starts a second run, so a second object.
#guard (Retained.Scene.of [⟨"k", .uncut⟩, ⟨"j", .uncut⟩, ⟨"k", .uncut⟩]).order.map (·.nth) == [0, 0, 1]

/-- A scene of one object in the group `g`, with the origin `o`, its groups listed `n` times. -/
def oneObject (o : Int × Int) (n : Nat) : Retained.Scene :=
  let s := Retained.Scene.ofGroups [{ name := "g", origin := o, calls := [⟨"k", .hit 0 0 8 8⟩] }]
  { s with groups := List.replicate n "g" }

-- The control of the premise that a scene lists each group once: a scene listing its group twice
-- takes its shift twice, and the patched scene stands twice as far off.
#guard ((oneObject (0, 0) 1).apply (Retained.diff (oneObject (0, 0) 1) (oneObject (5, 0) 1))).flatten ==
  (oneObject (5, 0) 1).flatten
#guard ((oneObject (0, 0) 1).apply (Retained.diff (oneObject (0, 0) 1) (oneObject (5, 0) 2))).flatten !=
  (oneObject (5, 0) 2).flatten

/-! ## LV-6: the live step -/

/-- The pages a live session draws over a build's requests, at the columns it holds, each with its
retained scene and its retained scene's groups' origin for the graph. -/
def livePages (reqs : List Tools.Session.Request) : List (Page × Retained.Scene) :=
  (reqs.foldl (fun (acc : Live.State × List (Page × Retained.Scene)) r =>
    let (st, out) := acc
    let (st', ans, rows) := Live.step {} "t" st r
    if rows.isEmpty then (st', out) else
    match st'.tool.session with
    | none => (st', out)
    | some l =>
      let g := (Live.page "t" r st'.tool ans l st.memo).1
      (st', out ++ [({ g with gutter := st'.gutter, codeAt := st'.codeAt }, st'.scene)])) ({}, [])).2

-- After every step of every build, the retained scene flattened is the tree's picture of the page
-- the step drew (`pageCalls`), and that page, at the batch's columns and place, draws the batch's
-- frame. A finite evaluation: the page's groups and the graph at its panel's origin are checked,
-- not proved, to draw as `pageCalls` does.
#guard programs.all fun p =>
  match requests p with
  | none => false
  | some reqs =>
    let batch := frames "t" reqs
    let pages := livePages reqs
    pages.length == batch.length &&
      (pages.zip batch).all fun ((g, sc), f) =>
        sc.flatten == pageCalls {} 1280 g &&
          pageCalls {} 1280 { g with gutter := f.page.gutter, codeAt := f.page.codeAt, place := f.page.place } ==
            pageCalls {} 1280 f.page

-- The control of the graph's panel: drawn at the origin of the page, its group unmoved, the graph
-- does not stand where `pageCalls` draws it.
#guard match requests Effect4.Program.Wire.Corpus.pFork with
  | none => false
  | some reqs => match (livePages reqs).getLast? with
    | none => false
    | some (g, _) =>
      let (groups, _) := Live.pageGroups {} 1280 g {}
      let unmoved := groups.map fun gr => { gr with origin := (0, 0) }
      (Retained.Scene.ofGroups unmoved).flatten != pageCalls {} 1280 g

end Tools.View.LiveChecks
