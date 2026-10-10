import Tools.View.Build
import Tools.View.Inc

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

/-! ## LV-2: the graph's calls on a key index and a stroke cache -/

-- One stroke cache carried along every frame and every moment of motion of a build answers each
-- drawing's calls on a fresh cache: `Laid.cachedStroke_eq`, read at the drawings the driver writes.
#guard programs.all fun p =>
  let L : Look := {}
  ((laidsOf L p).foldl (fun (acc : Bool × Laid.StrokeCache) l =>
    let (cs, c) := l.callsCached L 24 200 acc.2
    (acc.1 && cs == l.calls L 24 200, c)) (true, {})).1

/-- A line for the controls: a bump, then a straight run. -/
def controlLine : List Cubic := [⟨(0, 0), (0, 12), (40, 18), (40, 30)⟩, Grow.line (40, 30) (40, 60)]

-- The controls of the cache's key. A growing stroke is not the whole one, so the key holds the
-- tip; another noise draws another stroke, so the key holds the noise.
#guard Grow.stroke 7 {} 2400 controlLine true != Grow.stroke 7 {} 2400 controlLine false
#guard Grow.stroke 7 {} 2400 controlLine false != Grow.stroke 7 { noise := 100 } 2400 controlLine false

/-- A laid graph whose two places share a key. -/
def twice : Laid := { placed := #[{ key := "k", x := 0, y := 0, w := 8 }, { key := "k", x := 40, y := 0, w := 8 }] }

-- The control of the index's order: `Laid.find` answers a key's first place, as the index does;
-- an index put first first answers the last place.
#guard ((Laid.Ix.of twice).find "k").map (·.x) == some 0
#guard (((twice.placed.toList.foldl (fun m p => m.insert p.key p) ({} : KeyMap Key Placed)).get? "k").map (·.x)) ==
  some 40

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

end Tools.View.LiveChecks
