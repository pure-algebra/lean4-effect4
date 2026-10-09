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

/-- How branches stand side by side: all of them run, and the part ends when all have ended
(`fork`); all of them start, and the part ends when one has (`race`); a fiber runs beside its
parent's continuation (`spawn`); one of them runs (`choice`). -/
inductive Branching where
  | fork | race | spawn | choice
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
yield whose bound part forks a fiber, the await waits for that fork. Which value an await's term
selects is a fold of the term (`originAlg`), so the item of a tuple names its own fiber, and not
every fiber the tuple holds. -/

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

/-- **What a term's value is**, as far as the program's binding structure says: the value bound
at a variable (a de Bruijn level); a tuple or a list, item by item; or unknown. -/
inductive Origin where
  | bound (level : Nat)
  | items (xs : List Origin)
  | unknown

/-- The `i`-th item of a value whose items are known; else unknown. -/
def Origin.item : Origin → Nat → Origin
  | .items xs, i => xs.getD i .unknown
  | _, _ => .unknown

/-- The carrier of the origin fold: a term's origin, a term list's origins. -/
abbrev OriginAt : TermFam → Type
  | .term => Origin
  | .terms => List Origin

/-- **The origin fold** of the term algebra, by the machine's own evaluation (`evalTerm`,
`src/Effect4/Machine/Term.lean`): a variable is the value bound at its level; `tuple`, `pair`,
`nil`, `cons` and `append` build a list item by item, and `tupleAt`, `fst` and `snd` select an item
(`NativeAtom.eval`). Any other term is unknown, as is a fold's value, since its body reads
variables of its own. -/
def originAlg : TermAlgebra OriginAt where
  term_var i := .bound i
  term_lit _ := .unknown
  term_app atom args := match NativeAtom.ofName? atom, args with
    | some .tuple, xs => .items xs
    | some .pair, [a, b] => .items [a, b]
    | some .listNil, [] => .items []
    | some .listCons, [x, .items xs] => .items (x :: xs)
    | some .listAppend, [.items xs, .items ys] => .items (xs ++ ys)
    | some .fst, [o] => o.item 0
    | some .snd, [o] => o.item 1
    | _, _ => .unknown
  term_record _ _ _ := .unknown
  term_field _ _ _ := .unknown
  term_recordSet _ _ _ := .unknown
  term_tupleAt t i := t.item i
  term_fold _ _ _ _ := .unknown
  terms_nil := []
  terms_cons t ts := t :: ts

/-- A term's origin. -/
def origin (t : Term) : Origin := cata_term originAlg t

/-- **What an await waits for**: the forks it names, and whether some target is unresolved. A
target is resolved when its origin is a value bound by a part that forks a fiber. Any other
target (a fiber passed in, held in a cell, chosen by a test, or built by a term this reading does
not follow) is unresolved: it adds no edge, and it establishes neither that the await waits for
no fiber nor that no deadlock exists. -/
structure Targets where
  forks : List Key := []
  unresolved : Bool := false

/-- The targets of one fiber's origin at the address `a`. -/
def fiberTarget (root : Node NativeOp) (a : List Nat) : Origin → Targets
  | .bound n => match forkOf root a n with
    | some f => { forks := [bracket f] }
    | none => { unresolved := true }
  | _ => { unresolved := true }

/-- Each await by its key, with its targets: an `awaitFiber` waits for the fiber its term names,
and `awaitAll` and `awaitAllFailFast` for each fiber of the list their term builds. -/
def targets (program : NativeEff) : List (Key × Targets) :=
  let root : Node NativeOp := .eff program
  let many (a : List Nat) : Origin → Targets
    | .items xs =>
      let ts := xs.map (fiberTarget root a)
      { forks := (ts.flatMap (·.forks)).eraseDups, unresolved := ts.any (·.unresolved) }
    | _ => { unresolved := true }
  (Node.addresses root).filterMap fun a =>
    match root.at_ a with
    | some (.eff (.awaitFiber t _)) => some (bracket a, fiberTarget root a (origin t))
    | some (.action (.awaitAll t)) | some (.action (.awaitAllFailFast t)) => some (bracket a, many a (origin t))
    | _ => none

/-- Each node that waits for fibers it names, by its key, with the keys of those forks. A static
graph shows what the program's binding structure says; the run's graph shows the rest. -/
def waits (program : NativeEff) : List (Key × List Key) :=
  (targets program).filterMap fun (k, t) => if t.forks.isEmpty then none else some (k, t.forks)

/-- The awaits whose target this reading does not resolve, by key. -/
def unresolvedWaits (program : NativeEff) : List Key :=
  (targets program).filterMap fun (k, t) => if t.unresolved then some k else none

/-! ## The flow as a fold of the program -/

/-- **A part's flow**, with the releases it registers that no scope inside it has run. A release
runs when the scope that holds it closes: after the work it protects, the last registered first
(`scopeCloseFinalizers`, `internal/effect.ts:3805-3826` at the pin). So a release stands at its
scope's close, and not where its acquire is written. -/
structure Part where
  flow : Flow
  releases : List Flow := []

/-- A flow, then the releases its scope runs as it closes, the last registered first. -/
def Flow.closing (f : Flow) : List Flow → Flow
  | [] => f
  | rs => f.andThen (.seq rs.reverse)

/-- The carrier of the fold: a part, given its address. -/
abbrev FlowAt (_ : EffFam) : Type := List Nat → Part

/-- The part a child argument holds; a leaf holds none. -/
def childFlow : ArgF NativeOp FlowAt → Option (List Nat → Part)
  | .child _ r => some r
  | _ => none

/-- **A part's flow from its children's flows**, by row 337's reading. A constructor that this
reading does not name is a node, followed by its children in series. -/
def flowOf (fam : EffFam) (ctor : String) (key : Key) (leaf : Flow) (kids : List Flow) : Flow :=
  match fam, ctor, kids with
  | .eff, "bind", [a, k] => a.andThen k
  | .eff, "gen", [s] | .eff, "suspend", [s] | .eff, "exit", [s] | .eff, "withFiber", [s] => s
  | .eff, "onExit", [a, b] => a.andThen b
  | .eff, "catchCause", [a, h] | .eff, "catchIf", [a, h] => a.andThen (.par .choice key [h, .seq []])
  | .eff, "matchCause", [a, f, s] => a.andThen (.par .choice key [f, s])
  | .eff, "select", [a, b] | .stmt, "ifElse", [a, b] => .par .choice key [a, b]
  | .eff, "uninterruptible", [e] => .region "uninterruptible" key e
  | .eff, "interruptible", [e] => .region "interruptible" key e
  | .eff, "restore", [e] => .region "restore" key e
  | .eff, "provideService", [e] => .region "provide" key e
  | .eff, "defs", [_, body] => .region "definitions" key body
  | .eff, "iterate", [body] | .stmt, "whileTrue", [body] => .loop key (leaf.andThen body)
  | .stmt, "bindYield", [e] | .stmt, "yieldDiscard", [e] => e
  | .stmts, "cons", [h, t] => h.andThen t
  | .effs, "cons", [h, t] | .layers, "cons", [h, t] => .seq (h :: t.parts)
  | .action, "fork", [e] | .action, "forkIn", [e] | .action, "forkScoped", [e] => .par .spawn key [e]
  | .action, "raceAll", [es] => .par .race key es.parts
  | .layer, "provide", [a, b] | .layer, "provideMerge", [a, b] => b.andThen a
  | .layer, "merge", [a, b] => .par .fork key [a, b]
  | .layer, "mergeAll", [ls] => .par .fork key ls.parts
  | .layer, "effect", [e] | .layer, "effectDiscard", [e] | .layer, "fresh", [e] | .layer, "orDie", [e] => e
  | _, _, [] => if fam = .stmts || fam = .effs || fam = .layers then .seq [] else leaf
  | _, _, ks => leaf.andThen (.seq ks)

/-- **One generic layer of the flow.** A child's address counts the child arguments alone, as
`Node.child` does, so a node's key is its line's key. An `acquireRelease` is its acquire, and
registers its release. A scope runs the releases registered inside it as it closes. A provided
layer's own scope closes after the body it serves, and runs the layer's releases; the body's
releases belong to the scope around it (`Effect.provide`, `internal/layer.ts:8-22` at the pin).
Every other part passes its children's releases up, in order. -/
def flowLayer (waitsOf : Key → List Key) (fam : EffFam) (ctor : String) (args : List (ArgF NativeOp FlowAt)) :
    FlowAt fam :=
  fun p =>
    let parts := (args.filterMap childFlow).zipIdx.map fun (r, i) => r (p ++ [i])
    let key := bracket p
    let leaf := Flow.node key (ownText ctor args) "" (waitsOf key)
    match fam, ctor, parts with
    | .eff, "acquireRelease", [a, r] => { flow := a.flow, releases := a.releases ++ r.flow :: r.releases }
    | .eff, "scoped", [e] => { flow := .region "scoped" key (e.flow.closing e.releases) }
    | .eff, "provideLayer", [l, e] =>
      { flow := .region "provide" key ((l.flow.andThen e.flow).closing l.releases), releases := e.releases }
    | _, _, _ => { flow := flowOf fam ctor key leaf (parts.map (·.flow)), releases := parts.flatMap (·.releases) }

/-- **A program's flow**, the fold of its generic layer. The releases no scope of the program
holds run as the scope around the whole program closes, after it. -/
def ofProgram (program : NativeEff) : Flow :=
  let ws := waits program
  let part := cata_eff (EffAlgebra.ofLayer (flowLayer fun k => (ws.lookup k).getD [])) program []
  part.flow.closing part.releases

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
it waits for; its marks, each a bar (`true`) or a diamond, by the keys it spans; and whether it may
end. A part that cannot end (an empty race) reaches nothing after it, so no edge is drawn from its
exit. -/
structure Box where
  w : Int
  src : Key
  snk : Key
  ends : Bool := true
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
their frames need between them. The join is drawn when the part before it may end. -/
def stack : List Box → Box
  | [] => { w := 0, src := "", snk := "" }
  | first :: rest =>
    let W : Int := (first :: rest).foldl (fun m b => max m b.w) 0
    let centred (b : Box) : Box := b.shift ((W - b.w) / 2)
    rest.foldl (fun s b =>
      let m := centred b
      let joined := s.with m
      { joined with snk := m.snk, botPad := m.botPad, ends := s.ends && m.ends,
                    edges := joined.edges ++ [(s.snk, m.src, s.botPad + m.topPad, s.ends)] })
      { centred first with w := W }

/-- The middle across of an item of a part. -/
def Box.middleOf (b : Box) (k : Key) : Int := ((b.placed.find? (·.key == k)).map Laid.middle).getD 0

/-- **Parallel**, in the notation of UML's activity diagrams. Branches that all run (`fork`, `race`)
drop from a bar, each from its own port straight down to its entry, and meet at a bar: each branch's
exit drops straight to its port on that bar, and the ports stand at one height below every branch,
so no exit crosses another branch. Branches of which one runs (`choice`) part at a diamond and meet
at a diamond, from ports at one height. A fiber forked beside its parent (`spawn`) that the parent
does not await joins nothing: the parent's line runs on past it. An empty branch is a point of its
own. The exit of a fork's last branch is recorded, so a wait elsewhere can find the fiber.

**Whether it ends.** A fork ends when every branch has ended, or when one fails; a race when one
branch has ended; a choice when its branch has; a spawn when the parent's line has. So each may end
when some branch may, except that an empty fork ends at once, and an empty race never ends
(`raceAll` of no entrant; its live frontier is the machine's, not a completed merge). A branch's
drop to the join is drawn when that branch may end, and the join's mark when the join is reached.
With no branch, the fork's point and the join's point stand one gap apart, a part as wide as a
point. -/
def sideBySide (how : Branching) (k : Key) (bs : List Box) : Box :=
  let bs := bs.zipIdx.map fun (b, i) => if b.empty then point (k ++ "/" ++ toString i) else b
  let W : Int := if bs.isEmpty then CELL * GAP else
    bs.foldl (fun m b => m + b.w) 0 + CELL * GAP * ((bs.length : Int) - 1)
  let ends : Bool := match how with
    | .fork => bs.isEmpty || bs.any (·.ends)
    | .race | .choice => bs.any (·.ends)
    | .spawn => (bs.head?.map (·.ends)).getD true
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
       laid.zipIdx.map (fun (b, i) => (b.snk, ek, b.botPad, i == 0 && b.ends)), [])
    else
      let ps := ports "/join/"
      let aligned := ps.flatMap fun (pk, _) => laid.map fun b => (b.snk, pk, b.botPad, false)
      let drops := ps.map fun (pk, b) => (b.snk, pk, b.botPad, b.ends)
      let toJoin := ps.map fun (pk, b) => if how = .choice then (pk, jk, 0, b.ends) else (pk, jk, -VGAP, false)
      let across := if ps.isEmpty then [(fk, jk, 0, ends)] else []
      let mark := if !ends then [] else if how = .choice then [(jk, false, [jk])] else [(jk, true, jk :: ps.map (·.1))]
      (jk, pt jk mid :: ps.map (fun (pk, b) => pt pk (b.middleOf b.snk - CELL)), aligned ++ drops ++ toJoin ++ across,
       mark)
  { inner with snk := bottom.1, exits := inner.exits ++ exits, ends,
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
