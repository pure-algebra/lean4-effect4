import Tools.View.Build

/-!
# Probe: where the program graph's routes cross

For the last frame of a program built by edits, the probe takes each route of the laid graph
(`Laid.segments`), samples each cubic at nine points, and counts the pairs of routes whose
polylines cross properly (a shared end is no crossing). It classifies a pair by its kinds: two
forward routes of the flow (`down`), or a lane route (`back`: a loop's return or a wait).
-/

open Effect4 Effect4.Program Tools.View Tools.View.Build

namespace CrossProbe
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))
def forksThen : Nat → Nat → Nat → NativeEff
  | 0, L, k => awaitsRev k L
  | n + 1, L, k =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (forksThen n (L + 1) k)
where
  awaitsRev : Nat → Nat → NativeEff
    | 0, _ => .succeed (.lit .unit)
    | j + 1, L => .bind (.awaitFiber (.var j) .awaitValue) (awaitsRev j (L + 1))
/-- Forks in order, awaits in the same order: each await waits for an earlier fork. -/
def forksInOrder : Nat → Nat → Nat → NativeEff
  | 0, L, k => awaits k 0 L
  | n + 1, L, k =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (forksInOrder n (L + 1) k)
where
  awaits : Nat → Nat → Nat → NativeEff
    | 0, _, _ => .succeed (.lit .unit)
    | j + 1, i, L => .bind (.awaitFiber (.var i) .awaitValue) (awaits j (i + 1) (L + 1))

abbrev P := Int × Int

def lerp (a b : Int) (t : Int) : Int := a + (b - a) * t / 8
def at3 (c : Cubic) (t : Int) : P :=
  -- de Casteljau at t / 8
  let l (p q : P) : P := (lerp p.1 q.1 t, lerp p.2 q.2 t)
  let a := l c.p0 c.p1; let b := l c.p1 c.p2; let e := l c.p2 c.p3
  let ab := l a b; let be := l b e
  l ab be
def poly (cs : List Cubic) : List P := cs.flatMap fun c => ((List.range 9).map Int.ofNat).map fun i => at3 c i

def orient (a b c : P) : Int := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)
def sgn (x : Int) : Int := if x > 0 then 1 else if x < 0 then -1 else 0
/-- Two segments cross properly: each separates the other's ends strictly. -/
def proper (a b c d : P) : Bool :=
  sgn (orient a b c) * sgn (orient a b d) < 0 && sgn (orient c d a) * sgn (orient c d b) < 0

def segs (ps : List P) : List (P × P) := (ps.zip (ps.drop 1)).filter fun (a, b) => a != b
def crosses (p q : List P) : Bool :=
  (segs p).any fun (a, b) => (segs q).any fun (c, d) => proper a b c d

def kind : Route → String
  | .down .. => "down"
  | .back .. => "back"
  | .loop .. => "loop"

def lastLaid (p : NativeEff) : Option Laid :=
  (requests p).bind fun reqs => ((frames "t" reqs).getLast?).bind (·.page.graph.map (·.laid))

def report (name : String) (p : NativeEff) : IO Unit := do
  match lastLaid p with
  | none => IO.println s!"{name}: none"
  | some l =>
    let L : Look := {}
    let rs := l.routes.toList.map fun r => (kind r, r.key, poly (l.segments L r))
    let pairs := rs.zipIdx.flatMap fun (a, i) => (rs.drop (i + 1)).filterMap fun b =>
      if crosses a.2.2 b.2.2 then some (a.1 ++ "×" ++ b.1, a.2.1, b.2.1) else none
    let count (k : String) := (pairs.filter (·.1 == k)).length
    IO.println s!"{name}: {(l.placed.toList.filter (·.node.isSome)).length} boxes, {(rs.filter (·.1 == "down")).length} down, {(rs.filter (·.1 == "back")).length} lane routes; crossings down×down {count "down×down"}, down×back {count "down×back" + count "back×down"}, back×back {count "back×back"}"
    for (k, a, b) in (pairs.filter (·.1 == "down×down")).take 3 do
      IO.println s!"    {k}: {a} and {b}"
end CrossProbe

open CrossProbe in
#eval show IO Unit from do
  for (name, p) in Effect4.Program.Wire.Corpus.all do report name p
  report "chain 4" (chain 4 0)
  report "forksInOrder 3" (forksInOrder 3 0 3)
  report "forksThen 3" (forksThen 3 0 3)
  report "forksThen 5" (forksThen 5 0 5)
