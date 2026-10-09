import Tools.View.Program
import Effect4.Program.Binders

/-!
# A program's flow: its own graph as a fold, and its layout as a fold

Slices D2 and D3 of the program graph's design (`docs/research/2026-10-09-program-graph-design.md`;
decisions row 337, point 9). A program's flow is what must happen before what. `bind` and
statements stand in series. The branches of `raceAll`, and a forked fiber beside its parent's
continuation, stand in parallel. Alternatives (a handler, the branches of `select` and `ifElse`)
stand side by side, one of them taken. A region (a scope, an uninterruptible span, a provided
layer) brackets its part, and a loop returns.

**The flow is a fold** of the program (`ofProgram`, through the generic layer
`EffAlgebra.ofLayer`), keyed by address, as the tree's lines are. So a flow's node, the tree's
line and the code plane's text of one place share one key, and the motion between two frames
joins them.

**The flow is series-parallel**, and each part has one entry and one exit: a fork's branches meet
at a join point. So its layout needs no general graph drawing. The layout is a fold too (`lay`):
each part is laid at the origin, and its parent moves it into place. Series stacks, parallel
stands side by side, a region adds a margin and a label, a loop adds a back edge. An unchanged
part is laid out the same wherever it stands, moved rigidly (the design's frame consistency).
-/

namespace Tools.View.Flow

open Effect4 Effect4.Program Tools.View Tools.View.Program

/-- How branches stand side by side: all of them run (`fork`); a fiber runs beside its parent's
continuation (`spawn`); one of them runs (`choice`). -/
inductive Branching where
  | fork | spawn | choice
deriving DecidableEq

/-- **A program's flow**: a node for each leaf operation, parts in series, branches side by side,
a region around a part, a loop. -/
inductive Flow where
  | node (key : Key) (line1 line2 : String) (waits : List Key := [])
  | seq (parts : List Flow)
  | par (how : Branching) (key : Key) (branches : List Flow)
  | region (name : String) (key : Key) (body : Flow)
  | loop (key : Key) (body : Flow)

/-- A flow's parts in series: a series is its parts; any other flow is one part. -/
def Flow.parts : Flow → List Flow
  | .seq ps => ps
  | f => [f]

/-- A node whose wait for the fork `k` is met by its place: it stands after that fork's join. -/
def Flow.joined (k : Key) : Flow → Flow
  | .node key l1 l2 ws => .node key l1 l2 (ws.filter (· != k))
  | f => f

/-- Whether a flow is a node that waits for the fiber forked at `k`. -/
def Flow.waitsOn (k : Key) : Flow → Bool
  | .node _ _ _ ws => ws.contains k
  | _ => false

/-- **`a`, then `b`.** A spawned fiber whose parent has not yet continued takes `b` as its parent's
branch, beside the fiber: what the parent does next runs in parallel with what it forked. When
the parent's series awaits that fiber, the await and what follows it stand after the join, since
they wait for both: fork and join, as structured concurrency draws them. -/
def Flow.andThen (a b : Flow) : Flow :=
  match a.parts.getLast? with
  | some (.par .spawn k [child]) =>
    let bs := b.parts
    match bs.findIdx? (Flow.waitsOn k) with
    | some i =>
      .seq (a.parts.dropLast ++ [.par .fork k [.seq (bs.take i), child]] ++
        ((bs.drop i).headD (.seq [])).joined k :: bs.drop (i + 1))
    | none => .seq (a.parts.dropLast ++ [.par .spawn k [b, child]])
  | _ => .seq (a.parts ++ b.parts)

/-! ## Which fiber an await waits for

A fiber is a value, bound by the part that forks it. A variable is a position in the environment,
counted from its start (`Effect4.Program.Var`): `var n` names the `n`-th value bound on the way
from the root, a de Bruijn level. The binders along an address come from the program's one binder
table (`Node.binders`, generated from `tools/Effect4Gen/binders.json`), and a closed child starts
an empty environment (`Node.closedChild`). When the binder is a `bind` or a statement's binding
yield whose bound part forks a fiber, the await waits for that fork. -/

/-- The environment at an address, outermost first: for each value, the address of the node that
binds it and the child it is bound for. A closed child starts it empty. -/
def bindersAlong (root : Node NativeOp) (a : List Nat) : List (List Nat × Nat) :=
  (List.range a.length).foldl (fun acc k =>
    let pre := a.take k
    match root.at_ pre, a[k]? with
    | some n, some i =>
      (if Node.closedChild n i then [] else acc) ++ List.replicate (Node.binders n i) (pre, i)
    | _, _ => acc) []

/-- The address of the fork whose fiber the part at `q` answers, when `q` holds `withFiber` of a fork. -/
def spawnAt (root : Node NativeOp) (q : List Nat) : Option (List Nat) :=
  match root.at_ q with
  | some (.eff (.withFiber (.fork ..))) | some (.eff (.withFiber (.forkIn ..)))
  | some (.eff (.withFiber (.forkScoped ..))) => some (q ++ [0])
  | _ => none

/-- The fork that `var n` at the address `a` names, if its binder binds a forked fiber. -/
def forkOf (root : Node NativeOp) (a : List Nat) (n : Nat) : Option (List Nat) :=
  match (bindersAlong root a)[n]? with
  | some (pre, 1) =>
    match root.at_ pre with
    | some (.eff (.bind ..)) => spawnAt root (pre ++ [0])
    | some (.stmts (.cons (.bindYield _) _)) => spawnAt root (pre ++ [0, 0])
    | _ => none
  | _ => none

/-- The variables a term reads from an environment of `level` values: a fold of the term algebra.
A `fold`'s body binds two more, at the levels `level` and `level + 1`, which are its own. -/
def termVarsAlg : TermAlgebra (fun _ => Nat → List Nat) where
  term_var i := fun level => if i < level then [i] else []
  term_lit _ := fun _ => []
  term_app _ args := args
  term_record _ _ args := args
  term_field _ t _ := t
  term_recordSet t _ v := fun level => t level ++ v level
  term_tupleAt t _ := t
  term_fold _ list init body := fun level => list level ++ init level ++ body level
  terms_nil := fun _ => []
  terms_cons t ts := fun level => t level ++ ts level

/-- The variables a term reads from an environment of `level` values. -/
def termVars (t : Term) (level : Nat) : List Nat := cata_term termVarsAlg t level

/-- Each node that waits for fibers, by its key, with the keys of the forks it waits for: an
`awaitFiber` waits for the fiber its term names, and `awaitAll` and `awaitAllFailFast` for every
fiber their targets name. A variable that names no fork (a fiber passed in, or held in a cell)
gives no wait: the static graph shows what the program's binding structure says, and the run's
graph shows the rest. -/
def waits (program : NativeEff) : List (Key × List Key) :=
  let root : Node NativeOp := .eff program
  let named (a : List Nat) (t : Term) : List Key :=
    ((termVars t (bindersAlong root a).length).filterMap fun n => (forkOf root a n).map bracket).eraseDups
  (Node.addresses root).filterMap fun a =>
    let ws := match root.at_ a with
      | some (.eff (.awaitFiber t _)) => named a t
      | some (.action (.awaitAll t)) | some (.action (.awaitAllFailFast t)) => named a t
      | _ => []
    if ws.isEmpty then none else some (bracket a, ws)

/-! ## The flow as a fold of the program -/

/-- The carrier of the fold: a part's flow, given its address. -/
abbrev FlowAt (_ : EffFam) : Type := List Nat → Flow

/-- The flow a child argument holds; a leaf holds none. -/
def childFlow : ArgF NativeOp FlowAt → Option (List Nat → Flow)
  | .child _ r => some r
  | _ => none

/-- **One generic layer of the flow**, by row 337's reading. A child's address counts the child
arguments alone, as `Node.child` does, so a node's key is its line's key. A constructor that this
reading does not name is a node, followed by its children in series. -/
def flowLayer (waitsOf : Key → List Key) (fam : EffFam) (ctor : String) (args : List (ArgF NativeOp FlowAt)) :
    FlowAt fam :=
  fun p =>
    let kids := (args.filterMap childFlow).zipIdx.map fun (r, i) => r (p ++ [i])
    let key := bracket p
    let leaf := Flow.node key (ownText ctor args) "" (waitsOf key)
    match fam, ctor, kids with
    | .eff, "bind", [a, k] => a.andThen k
    | .eff, "gen", [s] | .eff, "suspend", [s] | .eff, "exit", [s] | .eff, "withFiber", [s] => s
    | .eff, "onExit", [a, b] | .eff, "acquireRelease", [a, b] => a.andThen b
    | .eff, "catchCause", [a, h] | .eff, "catchIf", [a, h] => a.andThen (.par .choice key [h, .seq []])
    | .eff, "matchCause", [a, f, s] => a.andThen (.par .choice key [f, s])
    | .eff, "select", [a, b] | .stmt, "ifElse", [a, b] => .par .choice key [a, b]
    | .eff, "uninterruptible", [e] => .region "uninterruptible" key e
    | .eff, "interruptible", [e] => .region "interruptible" key e
    | .eff, "scoped", [e] => .region "scoped" key e
    | .eff, "restore", [e] => .region "restore" key e
    | .eff, "provideLayer", [l, e] => .region "provide" key (l.andThen e)
    | .eff, "provideService", [e] => .region "provide" key e
    | .eff, "defs", [_, body] => .region "definitions" key body
    | .eff, "iterate", [body] | .stmt, "whileTrue", [body] => .loop key (leaf.andThen body)
    | .stmt, "bindYield", [e] | .stmt, "yieldDiscard", [e] => e
    | .stmts, "cons", [h, t] => h.andThen t
    | .effs, "cons", [h, t] | .layers, "cons", [h, t] => .seq (h :: t.parts)
    | .action, "fork", [e] | .action, "forkIn", [e] | .action, "forkScoped", [e] => .par .spawn key [e]
    | .action, "raceAll", [es] => .par .fork key es.parts
    | .layer, "provide", [a, b] | .layer, "provideMerge", [a, b] => b.andThen a
    | .layer, "merge", [a, b] => .par .fork key [a, b]
    | .layer, "mergeAll", [ls] => .par .fork key ls.parts
    | .layer, "effect", [e] | .layer, "effectDiscard", [e] | .layer, "fresh", [e] | .layer, "orDie", [e] => e
    | _, _, [] => if fam = .stmts || fam = .effs || fam = .layers then .seq [] else leaf
    | _, _, ks => leaf.andThen (.seq ks)

/-- **A program's flow**, the fold of its generic layer. -/
def ofProgram (program : NativeEff) : Flow :=
  let ws := waits program
  cata_eff (EffAlgebra.ofLayer (flowLayer fun k => (ws.lookup k).getD [])) program []

mutual
/-- A flow with each node's two lines replaced where `label` gives them, by its key. -/
def Flow.relabel (label : Key → Option (String × String)) : Flow → Flow
  | .node k l1 l2 w => match label k with
    | some (a, b) => .node k a b w
    | none => .node k l1 l2 w
  | .seq ps => .seq (relabelAll label ps)
  | .par how k bs => .par how k (relabelAll label bs)
  | .region n k b => .region n k (b.relabel label)
  | .loop k b => .loop k (b.relabel label)
/-- Flows relabelled. -/
def relabelAll (label : Key → Option (String × String)) : List Flow → List Flow
  | [] => []
  | f :: fs => f.relabel label :: relabelAll label fs
end

/-! ## The layout: places across by a fold, heights by the longest path

A program's waits make its graph more than series-parallel: an await may wait for a fiber forked
in another part. So the layout has two passes. Across, it is a fold of the flow (`lay`): series
centres its parts, parallel stands its branches side by side, a region adds a margin. Down, each
item stands below every item before it, by the longest path over the flow's edges and its waits
(`heights`): so every edge descends, and an await stands below the end of the fiber it waits for.
A wait that closes a cycle is a deadlock, and is drawn as a back edge, so it stands out. A
region's frame is the bounding box of what it holds. -/

/-- A region before its height is known: its key, its name, its place and width across, the items
inside it, and the regions inside it. -/
structure Frame where
  key : Key
  name : String
  x : Int
  w : Int
  items : List Key
  inner : List Key

/-- A laid-out part, across only: its width; its entry and exit; the room its frames need above its
entry and below its exit; its items placed across; its edges, each with the room it needs beyond
the gap and whether it is drawn (an edge that is not only holds a place); its frames; its loops'
back edges; the exit of each fiber it forks; its waits, each an await's key and the key of the fork
it waits for; and its marks, each a bar (`true`) or a diamond, by the keys it spans. -/
structure Box where
  w : Int
  src : Key
  snk : Key
  topPad : Int := 0
  botPad : Int := 0
  placed : List Placed := []
  edges : List (Key × Key × Int × Bool) := []
  frames : List Frame := []
  backs : List (Key × Key) := []
  exits : List (Key × Key) := []
  waits : List (Key × Key) := []
  marks : List (Key × Bool × List Key) := []

/-- A part moved across by whole pixels: every item and frame moved alike. -/
def Box.shift (dx : Int) (b : Box) : Box :=
  { b with placed := b.placed.map (fun p => { p with x := p.x + dx }),
           frames := b.frames.map fun f => { f with x := f.x + dx } }

/-- Two parts' contents together; the first's ends and size stand. -/
def Box.with (s m : Box) : Box :=
  { s with placed := s.placed ++ m.placed, edges := s.edges ++ m.edges, frames := s.frames ++ m.frames,
           backs := s.backs ++ m.backs, exits := s.exits ++ m.exits, waits := s.waits ++ m.waits,
           marks := s.marks ++ m.marks }

/-- The gap between an item and the next one down: one row, so boxes stand three rows apart, as a
graph's ranks do. -/
def VGAP : Int := ROWH

/-- A region's margin, and the row its name takes above its part. -/
def MARGIN : Int := CELL
def LABEL : Int := ROWH

/-- The widest box, in cells. -/
def WIDEST : Nat := 30

/-- A point: no height, where edges meet and part. -/
def point (k : Key) : Box :=
  { w := CELL * GAP, src := k, snk := k, placed := [{ key := k, x := 0, y := 0, w := CELL * GAP }] }

/-- A node's box, with its waits. -/
def nodeBox (k l1 l2 : String) (waits : List Key) : Box :=
  let n : GNode := { key := k, line1 := l1, line2 := l2 }
  let w := CELL * min WIDEST (Graph.boxWidth n)
  { w, src := k, snk := k, placed := [{ key := k, x := 0, y := 0, w, node := some n }],
    waits := waits.map fun f => (k, f) }

/-- Whether a part is empty: no item at all. -/
def Box.empty (b : Box) : Bool := b.placed.isEmpty

/-- **Series**: the parts centred, each part's exit joined to the next part's entry, with the room
their frames need between them. -/
def stack : List Box → Box
  | [] => { w := 0, src := "", snk := "" }
  | first :: rest =>
    let W : Int := (first :: rest).foldl (fun m b => max m b.w) 0
    let centred (b : Box) : Box := b.shift ((W - b.w) / 2)
    rest.foldl (fun s b =>
      let m := centred b
      let joined := s.with m
      { joined with snk := m.snk, botPad := m.botPad, edges := joined.edges ++ [(s.snk, m.src, s.botPad + m.topPad, true)] })
      { centred first with w := W }

/-- The middle across of an item of a part. -/
def Box.middleOf (b : Box) (k : Key) : Int := ((b.placed.find? (·.key == k)).map Laid.middle).getD 0

/-- **Parallel**, in the notation of UML's activity diagrams. Branches that all run (`fork`) drop
from a bar, each from its own port straight down to its entry, and meet at a bar: each branch's
exit drops straight to its port on that bar, and the ports stand at one height below every branch,
so no exit crosses another branch. Branches of which one runs (`choice`) part at a diamond and meet
at a diamond, from ports at one height. A fiber forked beside its parent (`spawn`) that the parent
does not await joins nothing: the parent's line runs on past it. An empty branch is a point of its
own. The exit of a fork's last branch is recorded, so a wait elsewhere can find the fiber. -/
def sideBySide (how : Branching) (k : Key) (bs : List Box) : Box :=
  let bs := bs.zipIdx.map fun (b, i) => if b.empty then point (k ++ "/" ++ toString i) else b
  let W : Int := bs.foldl (fun m b => m + b.w) 0 + CELL * GAP * ((bs.length : Int) - 1)
  let fk := k ++ "/fork"
  let jk := k ++ "/join"
  let mid := W / 2 - CELL
  let pt (key : Key) (x : Int) : Placed := { key, x, y := 0, w := CELL * GAP }
  let laid := (bs.foldl (fun (acc : List Box × Int) b => (acc.1 ++ [b.shift acc.2], acc.2 + b.w + CELL * GAP))
    ([], 0)).1
  let inner := laid.foldl Box.with { w := W, src := fk, snk := jk }
  let exits := if how = .choice then [] else (laid.getLast?.map fun b => [(k, b.snk)]).getD []
  let ports (side : String) : List (Key × Box) := laid.zipIdx.map fun (b, i) => (k ++ side ++ toString i, b)
  -- the top: a bar with a port above each branch, or a diamond
  let top : List Placed × List (Key × Key × Int × Bool) × List (Key × Bool × List Key) :=
    if how = .choice then
      ([pt fk mid], laid.map (fun b => (fk, b.src, b.topPad, true)), [(fk, false, [fk])])
    else
      let ps := ports "/fork/"
      ([pt fk mid] ++ ps.map (fun (pk, b) => pt pk (b.middleOf b.src - CELL)),
       ps.flatMap (fun (pk, b) => [(fk, pk, -VGAP, false), (pk, b.src, b.topPad, true)]),
       [(fk, true, fk :: ps.map (·.1))])
  -- the bottom: ports at one height below every branch, then a bar or a diamond; or, for a fiber
  -- the parent does not await, the parent's line running on past the fiber
  let bottom : Key × List Placed × List (Key × Key × Int × Bool) × List (Key × Bool × List Key) :=
    if how = .spawn then
      let ek := k ++ "/end"
      (ek, [pt ek ((laid.headD inner).middleOf (laid.headD inner).snk - CELL)],
       laid.zipIdx.map (fun (b, i) => (b.snk, ek, b.botPad, i == 0)), [])
    else
      let ps := ports "/join/"
      let aligned := ps.flatMap fun (pk, _) => laid.map fun b => (b.snk, pk, b.botPad, false)
      let drops := ps.map fun (pk, b) => (b.snk, pk, b.botPad, true)
      let toJoin := ps.map fun (pk, _) => if how = .choice then (pk, jk, 0, true) else (pk, jk, -VGAP, false)
      (jk, pt jk mid :: ps.map (fun (pk, b) => pt pk (b.middleOf b.snk - CELL)), aligned ++ drops ++ toJoin,
       if how = .choice then [(jk, false, [jk])] else [(jk, true, jk :: ps.map (·.1))])
  { inner with snk := bottom.1, exits := inner.exits ++ exits,
               placed := top.1 ++ inner.placed ++ bottom.2.1,
               edges := top.2.1 ++ inner.edges ++ bottom.2.2.1,
               marks := top.2.2 ++ inner.marks ++ bottom.2.2.2 }

/-- **A region**: its part inside a margin, under a row for its name; the room above and below is
reserved in the gaps around it. -/
def framed (name k : String) (b : Box) : Box :=
  let m := b.shift MARGIN
  let w := b.w + 2 * MARGIN
  { m with w, topPad := b.topPad + MARGIN + LABEL, botPad := b.botPad + MARGIN,
           frames := { key := k ++ "/region", name, x := 0, w, items := b.placed.map (·.key),
                       inner := b.frames.map (·.key) } :: m.frames }

/-- **A loop**: its part, and a back edge from its exit to its entry. -/
def looped (b : Box) : Box := { b with backs := (b.snk, b.src) :: b.backs }

mutual
/-- **The layout of a flow across**: a fold, each part laid out and then moved into place. -/
def lay : Flow → Box
  | .node k l1 l2 w => nodeBox k l1 l2 w
  | .seq ps => stack ((layAll ps).filter (!·.empty))
  | .par how k bs => sideBySide how k (layAll bs)
  | .region name k body => framed name k (lay body)
  | .loop _ body => looped (lay body)
/-- Flows laid out across. -/
def layAll : List Flow → List Box
  | [] => []
  | f :: fs => lay f :: layAll fs
end

/-- An item's height: a box's rows; a point has none. -/
def itemH (p : Placed) : Int := if p.node.isSome then ROWH * BOXROWS else 0

/-- Whether `v` reaches `u` along the edges, in at most `fuel` steps. -/
def reaches (edges : List (Key × Key × Int × Bool)) : Nat → List Key → List Key → Key → Bool
  | 0, _, _, _ => false
  | fuel + 1, frontier, seen, u =>
    if frontier.contains u then true else
    let next := (edges.filterMap fun (a, b, _) => if frontier.contains a && !seen.contains b then some b else none).eraseDups
    if next.isEmpty then false else reaches edges fuel next (seen ++ next) u

/-- **Heights by the longest path**: in the edges' order (Kahn's), each item at least one gap, and
the room its edge asks, below the bottom of each item before it. An item before none stands at
`start`. -/
def heights (placed : List Placed) (edges : List (Key × Key × Int × Bool)) (start : Int) : List (Key × Int) :=
  let h (k : Key) : Int := ((placed.find? (·.key == k)).map itemH).getD 0
  let indeg (k : Key) (es : List (Key × Key × Int × Bool)) : Nat := (es.filter (·.2.1 == k)).length
  let rec go : Nat → List Key → List (Key × Key × Int × Bool) → List (Key × Int) → List (Key × Int)
    | 0, _, _, ys => ys
    | _ + 1, [], _, ys => ys
    | fuel + 1, k :: queue, es, ys =>
      let yk := (ys.lookup k).getD start
      let out := es.filter (·.1 == k)
      let rest := es.filter (·.1 != k)
      let ys := out.foldl (fun ys (_, v, pad, _) =>
        let want := yk + h k + VGAP + pad
        match ys.lookup v with
        | some yv => if yv < want then (v, want) :: ys.filter (·.1 != v) else ys
        | none => (v, want) :: ys) ys
      let ready := (out.map (·.2.1)).eraseDups.filter fun v => indeg v rest == 0
      go fuel (queue ++ ready) rest ys
  let keys := placed.map (·.key)
  let first := keys.filter fun k => indeg k edges == 0
  go (keys.length + 1) first edges (first.map fun k => (k, start))

/-- **A flow laid out** as the graph view draws it. Across by the fold; down by the longest path
over the flow's edges and its waits. A drawn edge of the flow is a route down; a loop's return and
every wait run in a lane at the right, a wait from the fiber's exit to its await. A wait that would
close a cycle is a deadlock: it constrains nothing, and its lane shows it. -/
def layout (f : Flow) : Laid :=
  let b := lay f
  let n := b.placed.length
  let candidates := b.waits.filterMap fun (await, fork) => (b.exits.lookup fork).map fun ex => (ex, await)
  let (dag, crosses, cycles) := candidates.foldl
    (fun (acc : List (Key × Key × Int × Bool) × List (Key × Key) × List (Key × Key)) (ex, await) =>
      if reaches acc.1 (n + 1) [await] [await] ex then (acc.1, acc.2.1, acc.2.2 ++ [(ex, await)])
      else (acc.1 ++ [(ex, await, 0, false)], acc.2.1 ++ [(ex, await)], acc.2.2)) (b.edges, [], [])
  let ys := heights b.placed dag b.topPad
  let yOf (k : Key) : Int := (ys.lookup k).getD 0
  let placed := b.placed.map fun p => { p with y := yOf p.key }
  let bottomOf (p : Placed) : Int := p.y + itemH p
  let rects := b.frames.reverse.foldl (fun (rs : List (Key × Region)) fr =>
    let mine := placed.filter (fr.items.contains ·.key)
    let inner : List Region := fr.inner.filterMap fun k => rs.lookup k
    let tops := mine.map (·.y) ++ inner.map (·.y)
    let top := tops.foldl min (tops.headD 0)
    let bot := (mine.map bottomOf ++ inner.map fun (r : Region) => r.y + r.h).foldl max 0
    let y := top - MARGIN - LABEL
    (fr.key, { key := fr.key, name := fr.name, x := fr.x, y, w := fr.w, h := bot + MARGIN - y }) :: rs) []
  let at_ (k : Key) : Option Placed := placed.find? (·.key == k)
  let marks : List FlowMark := b.marks.filterMap fun (k, bar, keys) =>
    let ps := keys.filterMap at_
    match ps.head? with
    | none => none
    | some p =>
      if bar then
        let xs := ps.map Laid.middle
        some (.bar k (xs.foldl min (Laid.middle p) - CELL) (xs.foldl max (Laid.middle p) + CELL) p.y)
      else some (.diamond k (Laid.middle p) p.y)
  let lanes := b.backs ++ crosses ++ cycles
  let routes := (b.edges.filter (·.2.2.2)).map (fun (u, v, _) => Route.down (u ++ "→" ++ v) [u, v]) ++
    lanes.zipIdx.map fun ((u, v), lane) =>
      if u == v then Route.loop (u ++ "↺") u else Route.back (u ++ "↺" ++ v) u v lane
  let height := (placed.map bottomOf ++ rects.map fun (p : Key × Region) => p.2.y + p.2.h).foldl max 0
  { placed := placed.toArray, routes := routes.toArray, regions := (rects.map (·.2)).reverse.toArray,
    marks := marks.toArray,
    width := b.w + (if lanes.isEmpty then 0 else CELL * (GAP + 2 * lanes.length)), height }

/-- **A page's program graph**: the program's flow, each node labelled with its line's text and
type on the page, laid out. -/
def ofPage (program : NativeEff) (page : Page) : Laid :=
  let label (k : Key) : Option (String × String) :=
    (page.lines.toList.find? (·.key == k)).map fun l => (l.text, l.type)
  layout ((ofProgram program).relabel label)

end Tools.View.Flow
