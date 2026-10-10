import Tools.View.Build

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

end Tools.View.LiveChecks
