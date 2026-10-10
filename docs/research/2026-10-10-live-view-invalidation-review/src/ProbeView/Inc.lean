import ProbeView.Fast

/-!
# The page's folds along an edit: what an edit at `a` leaves standing

An edit of the session (`fill` or `omit` at the address `a`) replaces the subtree at `a` and
nothing else. So, from the frame before:

- **a node's own text** stands at every address outside the subtree at `a`. It is a function of
  the node's constructor and its arguments that are no child (`Program.ownText`), and the edit
  changes neither at a node outside `a`'s subtree, an ancestor included;
- **an await's targets** stand at every await outside the subtree at `a`. They are a function of
  the binders along the await's address (`Flow.forkOf`), and an edit at `a` adds or removes
  binders only inside its subtree, whose scope does not reach outside it.

So the page's lines (`Program.lines`) and the program's flow (`Flow.ofProgram`) need the texts of
the new subtree and the targets of its awaits alone. This module carries both from frame to
frame (`Memo`) and is checked equal to the fresh folds at every step of every build
(`checks/IncCheck.lean`).
-/

open Effect4 Effect4.Program Tools.View Tools.View.Program

namespace Tools.View.Inc

/-- What one frame leaves for the next: each node's own text by its address, and each await's
forks by its key. -/
structure Memo where
  texts : Std.HashMap (List Nat) String := {}
  waits : List (Key × List Key) := []

/-- A key's address: `[0 1 2]` read back. -/
def addrOf (k : Key) : Option (List Nat) :=
  if k.startsWith "[" && k.endsWith "]" then
    let body := ((k.drop 1).dropEnd 1).toString
    if body.isEmpty then some [] else (body.splitOn " ").mapM String.toNat?
  else none

/-- The address is inside the subtree at `a`. -/
def under (a p : List Nat) : Bool := a.isPrefixOf p

/-- A node's own text at `p`: from the memo outside the edited subtree, else computed. -/
def textAt (memo : Memo) (edited : Option (List Nat)) (p : List Nat) (compute : Unit → String) : String :=
  match edited with
  | some a => if under a p then compute () else (memo.texts[p]?).getD (compute ())
  | none => compute ()

/-- `Program.layerWith (ownText …)`, its text from the memo. -/
def linesLayer (memo : Memo) (edited : Option (List Nat)) (fam : EffFam) (ctor : String)
    (args : List (ArgF NativeOp Program.Lines)) : Program.Lines fam :=
  fun p d =>
    let inner := if Program.spine fam then d else d + 1
    let children := (args.filterMap Program.childLines).zipIdx.flatMap fun (r, i) => r (p ++ [i]) inner
    if Program.spine fam then children
    else ⟨p, d, textAt memo edited p (fun _ => ownText ctor args), args.findSome? Program.argOp⟩ :: children

/-- **The page's lines along an edit**: `Program.lines`, with the texts outside the edited
subtree from the memo. -/
def lines (memo : Memo) (edited : Option (List Nat)) (program : Eff NativeOp) : List Program.Node :=
  cata_eff (EffAlgebra.ofLayer (linesLayer memo edited)) program [] 0

/-- The awaits in the subtree at `a`, with their targets: `Flow.targets` on the subtree's
addresses alone. -/
def targetsUnder (program : NativeEff) (a : List Nat) : List (Key × Flow.Targets) :=
  let root : Node NativeOp := .eff program
  let many (b : List Nat) : Flow.Origin → Flow.Targets
    | .items xs =>
      let ts := xs.map (Flow.fiberTarget root b)
      { forks := (ts.flatMap (·.forks)).eraseDups, unresolved := ts.any (·.unresolved) }
    | _ => { unresolved := true }
  match root.at_ a with
  | none => []
  | some sub => (Node.addresses sub).filterMap fun r =>
    let b := a ++ r
    match sub.at_ r with
    | some (.eff (.awaitFiber t _)) => some (bracket b, Flow.fiberTarget root b (Flow.origin t))
    | some (.action (.awaitAll t)) | some (.action (.awaitAllFailFast t)) => some (bracket b, many b (Flow.origin t))
    | _ => none

/-- **The waits along an edit**: the memo's outside the edited subtree, and the subtree's own. -/
def waits (memo : Memo) (edited : Option (List Nat)) (program : NativeEff) : List (Key × List Key) :=
  match edited with
  | none => Flow.waits program
  | some a =>
    let inside (k : Key) : Bool := match addrOf k with
      | some p => under a p
      | none => false
    (memo.waits.filter fun (k, _) => !inside k) ++
      (targetsUnder program a).filterMap fun (k, t) => if t.forks.isEmpty then none else some (k, t.forks)

/-- `Flow.flowLayer`, its leaf's text from the memo. -/
def flowLayer (memo : Memo) (edited : Option (List Nat)) (waitsOf : Key → List Key) (fam : EffFam)
    (ctor : String) (args : List (ArgF NativeOp Flow.FlowAt)) : Flow.FlowAt fam :=
  fun p =>
    let parts := (args.filterMap Flow.childFlow).zipIdx.map fun (r, i) => r (p ++ [i])
    let key := bracket p
    let leaf := Flow.Flow.node key (textAt memo edited p (fun _ => ownText ctor args)) "" (waitsOf key)
    match fam, ctor, parts with
    | .eff, "acquireRelease", [a, r] => { flow := a.flow, releases := a.releases ++ r.flow :: r.releases }
    | .eff, "scoped", [e] => { flow := .region "scoped" key (e.flow.closing e.releases) }
    | .eff, "provideLayer", [l, e] =>
      { flow := .region "provide" key ((l.flow.andThen e.flow).closing l.releases), releases := e.releases }
    | _, _, _ => { flow := Flow.flowOf fam ctor key leaf (parts.map (·.flow)), releases := parts.flatMap (·.releases) }

/-- **The program's flow along an edit**: `Flow.ofProgram`, on the memo's texts and waits. -/
def flow (memo : Memo) (edited : Option (List Nat)) (program : NativeEff) (ws : List (Key × List Key)) :
    Flow.Flow :=
  let part := cata_eff (EffAlgebra.ofLayer (flowLayer memo edited fun k => (ws.lookup k).getD [])) program []
  part.flow.closing part.releases

/-- The memo a frame leaves: its lines' texts and its waits. -/
def Memo.next (ls : List Program.Node) (ws : List (Key × List Key)) : Memo :=
  { texts := ls.foldl (fun m n => m.insert n.path n.text) {}, waits := ws }

end Tools.View.Inc
