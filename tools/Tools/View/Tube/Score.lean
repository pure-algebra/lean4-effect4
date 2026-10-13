import Tools.View.Tube.Glyphs
import Tools.View.Decision

/-!
# Tools.View.Tube.Score — a run as a score: a staff for each fiber, its events in trace order

Slice M5 of the motion plan (`docs/research/2026-10-13-motion-everywhere/README.md`, §4.1;
decisions row 371 (1): a run reads left to right, one staff per fiber). A built program runs
through its checked session, one control a beat (`Run.controlOnce`, row 367 (10)), and the
machine's trace orders what happens inside each beat. Each event the score shows takes one column:

- **a staff** is a pipe along time, one for each fiber, in the order the fibers appear. It runs
  from the fiber's birth to its exit, or to the present column while it lives;
- **a fork** (`forked`) starts the child's staff an air gap below the parent's, running down and
  on, as the bond `arrow` does: the child shares none of the parent's fluid;
- **the fiber's unit** stands at the column of its latest event: it appears at the fiber's first
  turn (`started`), is hollow while the fiber is parked (`parkedOn`), and fills where it resumes
  (`resumedWith`): a promise kept;
- **an exit** (`exited`) is the cadence `exitBar`: the staff ends an air gap short of a thin strut
  and a heavy one, the unit before them;
- **a beat** is a tick above the score after its last column, one for each control decision.

Within a beat, each change starts in the order of its event (`STEP` of the beat apart), so cause
comes before effect as the trace records it.

**Simplifications** (row 371 (3)): a dispatcher's tasks, an observer's delivery of an exit, a
frame's push and pop, and a later turn of a running fiber take no column. A failure's exit draws
the same bars as a success; its reasons are not drawn yet. A fork's drop that passes over the
staffs of the rows between is drawn over them, and each is parted round it (`cutOf`), as a
crossing is in the tube language (row 370 (2)).
-/

namespace Tools.View.Tube.Score
open Effect4 Effect4.Program Effect4.Machine
open Tools.View Tools.View.Tube Tools.View.Tube.Glyphs

/-- **What the score draws of one event.** -/
inductive Note where
  | start (fiber : Nat)
  | fork (parent child : Nat)
  | park (fiber : Nat)
  | resume (fiber : Nat)
  | exit (fiber : Nat) (ok : Bool)
deriving Repr, BEq, Inhabited

/-- The fiber a note belongs to. -/
def Note.fiber : Note → Nat
  | .start f | .park f | .resume f | .exit f _ => f
  | .fork _ c => c

/-- **The note of an event**, where the score shows it. -/
def noteOf {ν σ β ε δ ι α χ κ η : Type _} : RunEvent ν σ β ε δ ι α χ κ η → Option Note
  | .forked p c _ => some (.fork p.value c.value)
  | .started f => some (.start f.value)
  | .parkedOn f _ => some (.park f.value)
  | .resumedWith f _ _ => some (.resume f.value)
  | .exited f e => some (.exit f.value (match e with | .success _ => true | .failure _ => false))
  | _ => none

/-- A fiber's later turns take no column: only its first `start` is a note. -/
def firstStarts (ns : List Note) : List Note :=
  (ns.foldl (fun (acc : List Nat × List Note) n => match n with
    | .start f => if acc.1.contains f then acc else (f :: acc.1, acc.2 ++ [n])
    | _ => (acc.1, acc.2 ++ [n])) ([], [])).2

/-- **A recorded run**: its notes in trace order, how many fall in each beat, and each beat's
decision in words. -/
structure Record where
  notes : List Note
  beats : List Nat
  verbs : List String
deriving Inhabited

/-- **A program's run, recorded** for at most `most` controls: each control's new events read as
notes. `none` where the program is not admitted. -/
def record (program : NativeEff) (most : Nat := 40) : Option Record :=
  match Api.Author.Internal.finishBuild program [] [] with
  | .error _ => none
  | .ok built =>
    let rec go (left seen : Nat) (s : Effect4.Run) (acc : List (List Note) × List String) :
        List (List Note) × List String :=
      match left, s.nextControl with
      | k + 1, some d =>
        let s' := s.controlOnce
        go k s'.machine.trace.length s'
          (acc.1 ++ [(s'.machine.trace.drop seen).filterMap noteOf], acc.2 ++ [Run.decisionText d])
      | _, _ => acc
    let s0 := Effect4.Run.open built "score"
    let (per, verbs) := go most s0.machine.trace.length s0 ([], [])
    -- first starts are judged over the whole run, then counted back into their beats
    let all := per.flatten
    let kept := firstStarts all
    let (beats, _) := per.foldl (fun (acc : List Nat × Nat) b =>
      let upto := acc.2 + b.length
      let before := firstStarts (all.take acc.2)
      let after := firstStarts (all.take upto)
      (acc.1 ++ [after.length - before.length], upto)) ([], 0)
    some { notes := kept, beats, verbs }

/-! ## The layout -/

/-- A column's width, a row's height, and the score's margins, in pixels. -/
def COL : Nat := 40
def ROW : Nat := 44
def X0 : Nat := 28
def Y0 : Nat := 40
/-- How far a staff reaches past its last column, and where a tick stands above the score. -/
def TAIL : Nat := 12
def TICK_Y : Nat := 8
/-- The thousandths of a beat between two changes of one beat. -/
def STEP : Nat := 110

/-- A column's abscissa, thousandths of a pixel. -/
def xAt (c : Nat) : Int := px (X0 + c * COL)
/-- A row's ordinate. -/
def yAt (r : Nat) : Int := px (Y0 + r * ROW)

/-- The fibers in the order they appear in the notes: the score's rows. -/
def rows (ns : List Note) : List Nat :=
  (ns.foldl (fun acc n => match n with
    | .fork p c => (if acc.contains p then acc else acc ++ [p]) |> fun a => if a.contains c then a else a ++ [c]
    | n => if acc.contains n.fiber then acc else acc ++ [n.fiber]) [])

/-- A fiber's row. -/
def rowOf (ns : List Note) (f : Nat) : Nat := ((rows ns).findIdx? (· == f)).getD 0

/-- The column of a note: its place in the list. -/
def lastCol (ns : List Note) (p : Note → Bool) : Option Nat :=
  (ns.zipIdx.filter (p ·.1)).getLast?.map (·.2)

/-- Where a child's drop starts: an air gap below its parent's staff, just before its fork's
column. -/
def dropStart (pr c : Nat) : Int × Int := (xAt c - px 6, yAt pr + (apart PIPE PIPE : Nat))

/-- The chord that a drop at an eighth of a turn cuts along a staff it passes over. -/
def CHORD : Nat := body PIPE * 1414 / 1000

/-- **The crossings of a score**: for each child whose drop passes over the staffs of the rows
between its parent's and its own, each row passed over and the abscissa where the drop's
centreline crosses it, on the drop's diagonal. -/
def crossings (shown : List Note) : List (Nat × Int) :=
  shown.zipIdx.flatMap fun (n, c) => match n with
    | .fork p ch =>
      let pr := rowOf shown p
      let (xs, y₀) := dropStart pr c
      ((List.range (rowOf shown ch)).filter (pr < ·)).map fun q => (q, xs + (yAt q - y₀))
    | _ => []

/-- **A staff's tube** to the abscissa `xEnd`: for a root, a straight pipe from its first column;
for a child forked at column `c`, the bond's drop from an air gap below its parent's staff, down
an eighth of a turn and back, then on. -/
def staffTube (parentRow row : Option Nat) (c : Nat) (xEnd : Int) : Tube :=
  match parentRow, row with
  | some pr, some r =>
    let y₀ := yAt pr + (apart PIPE PIPE : Nat)
    let drop : Int := (RADIUS * 292893 / 1000 : Nat)
    let down := ((yAt r - y₀ - drop) * 1414214 / 1000000).toNat
    let bend := tube (dropStart pr c).1 y₀ EIGHTH PIPE [⟨down, 0⟩, arc (-EIGHTH)]
    let ((bx, _), _) := bend.at bend.length
    { bend with pieces := bend.pieces ++ [⟨(xEnd - bx).toNat, 0⟩] }
  | _, _ => tube (xAt c - px TAIL) (yAt (row.getD 0)) E PIPE [⟨(xEnd - (xAt c - px TAIL)).toNat, 0⟩]

/-- Where an abscissa stands along a staff whose last piece runs east to its end. -/
def alongAt (t : Tube) (x : Int) : Int :=
  let ((ex, _), _) := t.at t.length
  (t.length : Int) - (ex - x)

/-- A mark that enters at the `j`-th change of its beat. -/
def at_ (j : Nat) (m : Mark) : Mark :=
  let d := min (j * STEP) 800
  { m with move := { m.move with delay := d, duration := 1000 - d } }

/-- **The score after the first `n` notes**, the notes before `fresh` drawn at rest and the rest
entering in order. -/
def picture (ns : List Note) (n fresh : Nat) : List Mark :=
  let shown := ns.take n
  let late (c : Nat) : Nat := if c < fresh then 0 else c - fresh
  let now := n - 1
  (rows shown).flatMap fun f =>
    let born := (lastCol shown fun | .fork _ c => c == f | _ => false)
    let first := ((shown.zipIdx.find? (·.1.fiber == f)).map (·.2)).getD 0
    let parent := shown.findSome? fun | .fork p c => if c == f then some p else none | _ => none
    let exitAt := lastCol shown fun | .exit g _ => g == f | _ => false
    let endCol := exitAt.getD now
    let row := rowOf shown f
    -- a staff passed over ends an air gap short of the drop while it reaches no further, and is
    -- parted round it once it does
    let over := crossings shown |>.filter (·.1 == row) |>.map (·.2)
    let short (x : Int) : Int := x - (CHORD / 2 + GAP + half PIPE : Nat)
    let xEnd := over.foldl (fun (e x : Int) =>
      if e < x + ((CHORD / 2 + GAP + half PIPE + 4000 : Nat) : Int) && e > short x then short x else e)
      (xAt endCol + px TAIL)
    let t := staffTube (parent.map (rowOf shown)) (some row) (born.getD first) xEnd
    let level := match parent with | some p => if row > rowOf shown p + 1 then 1 else 0 | none => 0
    let cuts := (over.filter fun x => x + ((CHORD / 2 + GAP + half PIPE : Nat) : Int) < xEnd).zipIdx.map fun (x, k) =>
      at_ 0 (cutOf s!"c{f}-{k}" t (alongAt t x) CHORD)
    let staff := (bodyOf s!"s{f}" t (level := level)).map (at_ 0) ++ cuts
    -- the unit: from the first turn, at the column of the fiber's latest event
    let started := lastCol shown fun | .start g => g == f | _ => false
    let latest := lastCol shown fun | .fork _ _ => false | n => n.fiber == f
    let parked := match (shown.filter (fun n => n.fiber == f && match n with | .fork .. => false | _ => true)).getLast? with
      | some (.park _) => true | _ => false
    let unit : List Mark := match started, latest with
      | some _, some c =>
        let x := if exitAt.isSome then xAt c - px COL / 2 else xAt c
        let mid := alongAt t x
        (if parked then hollowAt s!"u{f}" s!"u{f}h" t mid else [unitAt s!"u{f}" t mid]).map fun m =>
          at_ (late c) { m with level }
      | _, _ => []
    -- the exit: a thin strut and a heavy one, the staff an air gap short of them
    let bars : List Mark := match exitAt with
      | some c =>
        let xb := xEnd + (apart PIPE THIN : Nat)
        let y := yAt (rowOf shown f)
        let strut (k : String) (x : Int) (bore : Nat) : List Mark :=
          (bodyOf k (tube x (y - px 16) S bore [run 32])).map fun m => at_ (late c) { m with fill := .ink }
        strut s!"x{f}" xb THIN ++ strut s!"y{f}" (xb + (apart THIN PIPE : Nat)) PIPE
      | none => []
    staff ++ unit ++ bars

/-- The ticks above the score: one after each beat's last column, for the beats done. -/
def ticks (beats : List Nat) (done : Nat) : List Mark :=
  let ends := ((beats.take done).foldl (fun (acc : Nat × List Nat) b => (acc.1 + b, acc.2 ++ [acc.1 + b])) (0, [])).2
  ends.zipIdx.flatMap fun (upto, k) =>
    if upto == 0 then [] else
    (bodyOf s!"t{k}" (tube (xAt (upto - 1) + px COL / 2) (px TICK_Y) S THIN [run 12])).map fun m =>
      { m with fill := .ink }

/-- **The score's pictures**, one a beat: before any control, then after each beat's notes. -/
def pictures (r : Record) : List Picture :=
  let ends := (r.beats.foldl (fun (acc : Nat × List Nat) b => (acc.1 + b, acc.2 ++ [acc.1 + b])) (0, [])).2
  let starts := 0 :: ends
  complete ((starts.zip (0 :: starts)).zipIdx.map fun ((n, before), k) =>
    picture r.notes n before ++ ticks r.beats k)

/-- The score's size, in pixels. -/
def size (r : Record) : Nat × Nat :=
  (X0 + r.notes.length * COL + 2 * TAIL + 24, Y0 + (rows r.notes).length * ROW)

/-! ## Two programs -/

/-- A child that yields once and answers. -/
def child (n : Nat) (yields : Nat) : NativeEff :=
  (List.range yields).foldr (fun _ e => .bind (.yieldNow 0) e) (.succeed (.lit (.nat n)))

/-- **Two children awaited in turn**: the parent forks a child that yields once and one that yields
twice, then awaits the first and the second. -/
def twoChildren : NativeEff :=
  .bind (.withFiber (.fork (child 7 1) Effect4.Program.Wire.Corpus.forkOptions))
    (.bind (.withFiber (.fork (child 8 2) Effect4.Program.Wire.Corpus.forkOptions))
      (.bind (.awaitFiber (.var 1) .awaitValue) (.awaitFiber (.var 1) .awaitValue)))

-- the corpus's fork, recorded: the parent forks, parks on the child, the child parks on its
-- yield and resumes, exits, and the parent resumes and exits; two beats
#guard (record Effect4.Program.Wire.Corpus.pFork).map (fun r => (r.notes, r.beats)) ==
  some ([.start 0, .fork 0 1, .park 0, .start 1, .park 1, .resume 1, .exit 1 true, .resume 0, .exit 0 true], [3, 6])
#guard (record twoChildren).isSome
-- every staff and strut of every picture keeps the bend law, and no picture repeats a key
#guard ((record twoChildren).map pictures).all fun ps => ps.all fun p =>
  p.marks.all (fun m => m.tube.pieces.all fun q => decide q.ok) && (p.marks.map (·.key)).eraseDups.length == p.marks.length

end Tools.View.Tube.Score
