import Tools.View.Tube.Score
import ProofGraph.AxiomAudit

/-!
# The tube algebra: a finite probe (seat FORMAL, 2026-10-13)

The note is `docs/research/2026-10-13-tube-algebra/README.md`. This file is a **finite probe**: its
`#guard`s evaluate named finite inputs, and they establish nothing beyond those inputs. It lives
outside the tree's library roots, so no gate of the tree reads it. Run it alone from the checkout:

    LEAN_NUM_THREADS=2 lake env lean docs/research/2026-10-13-tube-algebra/Probe.lean

After part 0, which defines the audit command of part 6, it holds eight parts.

1. **The free signature** (`Gen`, `D`): the generators of the tube language and the free terms
   over them, with their wire sorts; the counting reading of the junctions as ℕ-matrices (`count`)
   and the bialgebra laws there (`B1`…`B4`); the ordered reading, where `B1` holds only when both
   merges take one decision.
2. **The fold** over a five-constructor fragment of the real `Eff` (`succeed`, `bind`, a fork,
   `awaitFiber`, `perform` of a cell's make and write): one `EffAlgebra` (`picAlg`) whose carrier
   builds a process diagram, folded by the tree's own `cata_eff`; the words beside it; and an
   algebra into the pen's marks (`marksOf`).
3. **Law 1** (expressiveness): over every fragment program of the enumeration, two programs draw
   alike exactly when their normal forms under `norm` (bind reassociated) are equal, and a reader
   reads every picture back as its program's normal form. Red controls: the geometry alone, a fold
   with no normaliser, a fold that forgets which fiber an await joins, and a misjoined picture.
4. **Law 2** (correspondence): on the real machine, over every tape of `fire` decisions of a few
   programs, the picture of the next state is the picture of this state changed by the step's
   events. Its red result: a cell's make and write, and a deferred's make and completion, leave no
   event, so the store's part of a film needs the state's difference.
5. **Tokens**: a place invariant of a net is kept by every firing (a theorem here, accepted by the
   kernel), the Queue's count net keeps `buffer + free`, and a broadcast's net keeps no such sum.
6. **The audit** of the file's two theorems by the gate's walk.
7. **The vocabulary**: each of the tree's 37 marks classed as a term, a contents state, a region or
   a boundary; each term mark's term, typed; and where the classes cross row 368 (4)'s kinds.
8. **A region is not a functor**: one mask round two writes, against two masks, on the machine.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace TubeProbe

/-! ## 0. The audit of this file's declarations, by the gate's walk

`#axiom_audit` takes imported modules. This file is no module, so `#probe_audit` runs the same walk
(`ProofGraph.reachedAxiomsMany`, with the gate's stop at planned goals) over the names it is given. -/

open Lean Elab Command in
/-- `#probe_audit n₁ n₂ …`: every named declaration within `[propext, Quot.sound]`, by the gate's
exact walk, or an error that names the offender. -/
elab "#probe_audit " ns:ident* : command => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for n in ns do
    names := names.push (← liftCoreM (realizeGlobalConstNoOverloadWithInfo n))
  let (results, _) := ProofGraph.reachedAxiomsMany env names {} (ProofGraph.isGoal env)
  for (n, r) in names.zip results do
    match r with
    | none => throwError m!"{n}: the walk ran out of its step budget"
    | some reached =>
      let outside := reached.filter fun a => !ProofGraph.trustedAxioms.contains a
      unless outside.isEmpty do throwError m!"{n} reaches {outside}"
  logInfo m!"probe audit: {names.size} declarations within [propext, Quot.sound]"

/-! ## 1. The free signature

Five wire sorts and seven generators. The structure (a pipe, the crossing, series, the air gap)
is the symmetric monoidal structure itself, and the region and the loop take a diagram. -/

/-- **The wire sorts.** A value is copied and dropped freely; a handle is copied, and its drop is a
close; a park token and a fiber's control are linear; a vessel is a resource's state, linear. -/
inductive Wire where
  | value | handle | token | control | vessel
deriving DecidableEq, Repr

/-- **The generators**, each with its legs (inputs, then outputs). -/
inductive Gen where
  /-- the solid wye inward: amounts add (a commutative monoid) -/
  | merge
  /-- a sealed start: no amount -/
  | start
  /-- the air-gap header: each tap its own copy (a cocommutative comonoid) -/
  | copy
  /-- a sealed end: what arrives is dropped -/
  | discard
  /-- the solid wye outward: the amount divides, which a decision fixes (relational) -/
  | split
  /-- a valve: open, the pipe; closed, a parting, nothing passes -/
  | valve (open_ : Bool)
  /-- an operation on a fiber's control: the leaf of a program, a row, a module's step -/
  | box (label : String) (ins outs : List Wire)
  /-- a fiber's control born beside its parent's, with the child's handle -/
  | fork
deriving DecidableEq, Repr

/-- A generator's legs: its input sorts and its output sorts. Junctions act on one sort. -/
def Gen.legs (s : Wire) : Gen → List Wire × List Wire
  | .merge => ([s, s], [s])
  | .start => ([], [s])
  | .copy => ([s], [s, s])
  | .discard => ([s], [])
  | .split => ([s], [s, s])
  | .valve _ => ([s], [s])
  | .box _ ins outs => (ins, outs)
  | .fork => ([.control], [.control, .control, .handle])

/-- **The free terms** over the generators: a diagram. -/
inductive D where
  | pipe (ws : List Wire)
  | gen (s : Wire) (g : Gen)
  | cross (a b : List Wire)
  | series (f g : D)
  | gap (f g : D)
  | region (name : String) (f : D)
  | loop (s : Wire) (f : D)
deriving DecidableEq, Repr

/-- **A diagram's type**: its input and output sorts, or `none` where a series joins unequal sorts
or a loop's body has no `s` to return. A loop is the iteration of a body `X → A + X`, drawn with the
returning wire: here its body takes `s :: ins` to `s :: outs`, and the loop drops the `s`. -/
def D.ty : D → Option (List Wire × List Wire)
  | .pipe ws => some (ws, ws)
  | .gen s g => some (g.legs s)
  | .cross a b => some (a ++ b, b ++ a)
  | .series f g => do
    let (a, b) ← f.ty
    let (b', c) ← g.ty
    if b = b' then some (a, c) else none
  | .gap f g => do
    let (a, b) ← f.ty
    let (c, d) ← g.ty
    some (a ++ c, b ++ d)
  | .region _ f => f.ty
  | .loop s f => do
    let (a, b) ← f.ty
    match a, b with
    | s' :: a', s'' :: b' => if s' = s ∧ s'' = s then some (a', b') else none
    | _, _ => none

-- a series of two controls' operations types; a series of a value into a control does not
#guard (D.series (.gen .control (.box "a" [.control] [.control]))
  (.gen .control (.box "b" [.control] [.control]))).ty == some ([.control], [.control])
#guard (D.series (.gen .value .copy) (.gen .control (.box "b" [.control] [.control]))).ty == none

/-! ### The counting reading: junctions as ℕ-matrices

A unit that enters at input `j` arrives `M i j` times at output `i`. Series is the product, the
air gap the block sum (Bonchi, Sobociński and Zanasi, *Interacting Hopf algebras*, JPAA 2017,
§3; Lack, *Composing PROPs*, TAC 13(9) 2004, §5.3: the commutative bialgebras present spans of
finite sets, that is ℕ-matrices). Only the junctions and the crossing have a counting reading. -/

/-- An `r × c` matrix of naturals: `c` inputs, `r` outputs, as rows. -/
structure Mat where
  rows : Nat
  cols : Nat
  e : List (List Nat)
deriving DecidableEq, Repr

def Mat.at (m : Mat) (i j : Nat) : Nat := (m.e.getD i []).getD j 0

def Mat.ident (n : Nat) : Mat :=
  ⟨n, n, (List.range n).map fun i => (List.range n).map fun j => if i = j then 1 else 0⟩

/-- `g` after `f`: the product `g · f`. -/
def Mat.comp (f g : Mat) : Option Mat :=
  if f.rows = g.cols then
    some ⟨g.rows, f.cols, (List.range g.rows).map fun i => (List.range f.cols).map fun j =>
      (List.range f.rows).foldl (fun acc k => acc + g.at i k * f.at k j) 0⟩
  else none

/-- The block sum: side by side. -/
def Mat.sum (f g : Mat) : Mat :=
  ⟨f.rows + g.rows, f.cols + g.cols,
    (List.range (f.rows + g.rows)).map fun i => (List.range (f.cols + g.cols)).map fun j =>
      if i < f.rows then (if j < f.cols then f.at i j else 0)
      else (if j < f.cols then 0 else g.at (i - f.rows) (j - f.cols))⟩

/-- **The counting reading** of a diagram of junctions on one sort, or `none` where it holds a
generator with no counting reading (a box, a fork, a split, whose share a decision fixes). -/
def count : D → Option Mat
  | .pipe ws => some (Mat.ident ws.length)
  | .gen _ .merge => some ⟨1, 2, [[1, 1]]⟩
  | .gen _ .start => some ⟨1, 0, [[]]⟩
  | .gen _ .copy => some ⟨2, 1, [[1], [1]]⟩
  | .gen _ .discard => some ⟨0, 1, []⟩
  | .gen _ (.valve b) => some ⟨1, 1, [[if b then 1 else 0]]⟩
  | .gen _ _ => none
  | .cross a b =>
    let n := a.length + b.length
    some ⟨n, n, (List.range n).map fun i => (List.range n).map fun j =>
      -- output i carries input j: the outputs are b's wires, then a's
      if i < b.length then (if j = a.length + i then 1 else 0)
      else (if j = i - b.length then 1 else 0)⟩
  | .series f g => do
    let mf ← count f
    let mg ← count g
    mf.comp mg
  | .gap f g => do
    let mf ← count f
    let mg ← count g
    some (mf.sum mg)
  | .region _ f => count f
  | .loop _ _ => none

/-- A value wire, and the junctions on it. -/
def v1 : D := .pipe [.value]
def mrg : D := .gen .value .merge
def cpy : D := .gen .value .copy
def stt : D := .gen .value .start
def dsc : D := .gen .value .discard
def x1 : D := .cross [.value] [.value]

/-- **The bialgebra laws** (Lack §1.3's compatibility; Bonchi, Sobociński and Zanasi's A7 to A10),
each as two diagrams. `B1`: a copy after a merge is the merges of the copies, crossed. -/
def B1 : D × D := (.series mrg cpy, .series (.gap cpy cpy) (.series (.gap v1 (.gap x1 v1)) (.gap mrg mrg)))
def B2 : D × D := (.series stt cpy, .gap stt stt)
def B3 : D × D := (.series mrg dsc, .gap dsc dsc)
def B4 : D × D := (.series stt dsc, .pipe [])

-- the four laws hold in the counting reading
#guard [B1, B2, B3, B4].all fun (l, r) => count l == count r && (count l).isSome
-- and the monoid and comonoid laws: associativity, commutativity and the units
#guard count (.series (.gap mrg v1) mrg) == count (.series (.gap v1 mrg) mrg)
#guard count (.series x1 mrg) == count mrg
#guard count (.series (.gap stt v1) mrg) == count v1
#guard count (.series cpy (.gap cpy v1)) == count (.series cpy (.gap v1 cpy))
#guard count (.series cpy x1) == count cpy
#guard count (.series cpy (.gap dsc v1)) == count v1
-- red control: a merge and a copy are not one generator: their readings differ, and no law
-- equates a merge with its mirror
#guard count mrg != count (.series cpy x1)

/-- **A solid junction conserves**: every input's column sums to one, so each unit arrives once. -/
def conserves (m : Mat) : Bool := (List.range m.cols).all fun j =>
  (List.range m.rows).foldl (fun acc i => acc + m.at i j) 0 == 1

/-- How many copies of an input's unit leave a junction. -/
def copies (m : Mat) (j : Nat) : Nat := (List.range m.rows).foldl (fun acc i => acc + m.at i j) 0

-- a tree of merges conserves, and so does an open valve; a copy into three taps sends three units
-- for one, and a closed valve sends none (red controls: neither conserves)
#guard (count (.series (.gap mrg v1) mrg)).all conserves
#guard (count (.gen .value (.valve true))).all conserves
#guard (count (.series cpy (.gap cpy v1))).map (copies · 0) == some 3
#guard !(count (.series cpy (.gap cpy v1))).all conserves
#guard !(count (.gen .value (.valve false))).all conserves

/-! ### The ordered reading: where the bialgebra law needs one decision

A wire carries a sequence of messages. A merge interleaves its two inputs as a decision says,
`true` taking from the left; a copy sends the sequence down each tap. Then `B1`'s left side, one
merge copied, gives both subscribers one order. Its right side merges each subscriber's copies by a
decision of its own. With one decision for both it is the left side; with two it reaches orders the
left side does not: two subscribers that disagree. -/

/-- The interleaving of two sequences that a decision word picks, `true` taking from the left; the
rest of either side follows when the word runs out. -/
def interleave : List Bool → List Nat → List Nat → List Nat
  | true :: d, x :: xs, ys => x :: interleave d xs ys
  | false :: d, xs, y :: ys => y :: interleave d xs ys
  | _ :: d, [], ys => interleave d [] ys
  | _ :: d, xs, [] => interleave d xs []
  | [], xs, ys => xs ++ ys

/-- Every decision word of length `n`. -/
def words : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun w => [true :: w, false :: w]

def xs : List Nat := [1, 2]
def ys : List Nat := [3]

/-- `B1`'s left side: one merge, copied to two subscribers. -/
def lhsOrders : List (List Nat × List Nat) :=
  ((words 3).map fun d => (interleave d xs ys, interleave d xs ys)).eraseDups

/-- `B1`'s right side: each subscriber merges its copies by its own decision. -/
def rhsOrders : List (List Nat × List Nat) :=
  ((words 3).flatMap fun d₁ => (words 3).map fun d₂ => (interleave d₁ xs ys, interleave d₂ xs ys)).eraseDups

-- every order of the left side is an order of the right side
#guard lhsOrders.all rhsOrders.contains
-- red control: the right side reaches two subscribers that disagree, which the left side does not
#guard rhsOrders.any fun (a, b) => a != b
#guard !(rhsOrders.all lhsOrders.contains)
-- with one decision for both subscribers, the right side is the left side
#guard ((words 3).map fun d => (interleave d xs ys, interleave d xs ys)).eraseDups == lhsOrders

def zs : List Nat := [4, 5]

/-- Two lists with the same members, each once. -/
def sameSet (a b : List (List Nat)) : Bool := a.all b.contains && b.all a.contains

-- E3 on ordered values, as sets of outcomes over every decision: a merge is commutative and
-- associative
#guard sameSet ((words 3).map fun d => interleave d xs ys) ((words 3).map fun d => interleave d ys xs)
#guard sameSet ((words 5).flatMap fun d₁ => (words 5).map fun d₂ => interleave d₂ (interleave d₁ xs ys) zs)
  ((words 5).flatMap fun d₁ => (words 5).map fun d₂ => interleave d₂ xs (interleave d₁ ys zs))
-- control: the interleavings of three sequences of two, one and two are thirty
#guard ((words 5).flatMap fun d₁ => (words 5).map fun d₂ => interleave d₂ (interleave d₁ xs ys) zs).eraseDups.length == 30

/-! ## 2. The fold over a fragment of `Eff`

The picture of a program is one algebra over `Eff`'s signature (`EffAlgebra`, the tree's
`src/Effect4/Program/Fold.lean`), folded by the tree's `cata_eff`. Its carrier is a builder: given
the ports of the variables in scope (de Bruijn levels) and the current fiber, it draws a program's
boxes on that fiber's control and answers the port of the program's value. Every node is a box on
its fiber's control, so a fiber's boxes are in the order of its threaded wire, and the diagram
needs no other canonical form: fibers in the order they are forked, boxes in the order of control.

Five constructors are drawn: `succeed`, `bind`, `withFiber` of a `fork`, `awaitFiber`, and
`perform` of a cell's make and write. Every other constructor is an opaque box. -/

open Effect4 Effect4.Program Effect4.Machine

/-- Where a value comes from: box `box` of fiber `fiber`. -/
structure Port where
  fiber : Nat
  box : Nat
deriving DecidableEq, Repr

/-- What a box is. -/
inductive Kind where
  | succeed | make | write | fork | await | other (ctor : String)
deriving DecidableEq, Repr

/-- **A phrase**: the words of a box, before any text: a literal, a socket `•` that a wire fills,
a pair, or another atom by name. The words are a second algebra beside the marks (row 367 (1)). -/
inductive Phrase where
  | lit (l : Lit)
  | socket
  | pair (a b : Phrase)
  | other (name : String)
deriving DecidableEq, Repr

/-- **A box**: its kind, its words (a phrase and a note), its value wires in, the fiber a fork
starts, and the fiber whose exit an await takes, where the program's binders say. -/
structure Box where
  kind : Kind
  phrase : Phrase := .other ""
  note : String := ""
  ins : List Port := []
  child : Option Nat := none
  joins : Option Nat := none
deriving DecidableEq, Repr

/-- **A program's process diagram**: its fibers in the order they are forked, each its boxes in
the order of its control. -/
abbrev Pic := List (List Box)

/-- The builder's state: the fibers drawn so far, and which fiber each fork's handle names. -/
structure BState where
  fibers : Array (Array Box)
  forks : List (Port × Nat)

/-- A box drawn at the end of fiber `f`'s control, and its port. -/
def BState.push (st : BState) (f : Nat) (b : Box) : Port × BState :=
  let fib := st.fibers.getD f #[]
  (⟨f, fib.size⟩, { st with fibers := st.fibers.set! f (fib.push b) })

/-- **The carrier**: the ports in scope and the current fiber, to a builder. -/
abbrev Build := List Port → Nat → BState → Port × BState

mutual
/-- A term's value wires: each variable a wire from its port. -/
def termIns (env : List Port) : Term → List Port
  | .var i => (env[i]?).toList
  | .lit _ => []
  | .app _ args => termsIns env args
  | .record _ _ vs => termsIns env vs
  | .field _ t _ => termIns env t
  | .recordSet t _ v => termIns env t ++ termIns env v
  | .tupleAt t _ => termIns env t
  | .fold _ l i _ => termIns env l ++ termIns env i
def termsIns (env : List Port) : Terms → List Port
  | .nil => []
  | .cons h t => termIns env h ++ termsIns env t
end

def litWord : Lit → String
  | .unit => "()"
  | .nat n => toString n
  | .bool b => toString b
  | .str s => "\"" ++ s ++ "\""

mutual
/-- **A term's phrase**: its literals, a variable as a socket, a pair by its parts. -/
def phraseOf : Term → Phrase
  | .var _ => .socket
  | .lit l => .lit l
  | .app f args => if f == "pair" then pairOf args else .other f
  | _ => .other "term"
def pairOf : Terms → Phrase
  | .cons a (.cons b .nil) => .pair (phraseOf a) (phraseOf b)
  | _ => .other "pair"
end

def modeWord : Supervision.ObserverMode → String
  | .awaitValue => "value"
  | .joinEffect => "join"

def optsWord (o : Supervision.ForkOptions) : String :=
  (if o.startImmediately then "now" else "later") ++ (if o.daemon then ",daemon" else "") ++
    (if o.maskMode = .inherit then "" else ",mask")

/-- An opaque box: a constructor outside the fragment. -/
def blank (name : String) : Build := fun _ f st => st.push f { kind := .other name }

/-- A fork on fiber `f`: the child's control is a new fiber, drawn with the parent's scope. -/
def forkB (child : Build) (o : Supervision.ForkOptions) : Build := fun env f st =>
  let c := st.fibers.size
  let st := { st with fibers := st.fibers.push #[] }
  let (h, st) := st.push f { kind := .fork, note := optsWord o, child := some c }
  let st := { st with forks := st.forks ++ [(h, c)] }
  let (_, st) := child env c st
  (h, st)

/-- An await: its handle's wire in, and the fiber whose exit it takes where the binder says. -/
def awaitB (t : Term) (m : Supervision.ObserverMode) : Build := fun env f st =>
  let joins := match t with
    | .var i => (env[i]?).bind fun p => (st.forks.find? (·.1 == p)).map (·.2)
    | _ => none
  st.push f { kind := .await, phrase := phraseOf t, note := modeWord m, ins := termIns env t, joins }

/-- A row's operation: a cell's make and write are drawn, any other is opaque. -/
def performB (op : NativeOp) (t : Term) : Build := fun env f st =>
  match op with
  | .refMake => st.push f { kind := .make, phrase := phraseOf t, ins := termIns env t }
  | .refSet => st.push f { kind := .write, phrase := phraseOf t, ins := termIns env t }
  | _ => st.push f { kind := .other "perform", phrase := phraseOf t, ins := termIns env t }

/-- **The picture algebra** over `Eff`'s signature: one field per constructor of the seven sorts. -/
def picAlg : EffAlgebra NativeOp (fun _ => Build) where
  eff_succeed t := fun env f st => st.push f { kind := .succeed, phrase := phraseOf t, ins := termIns env t }
  eff_fail _ := blank "fail"
  eff_failCause _ := blank "failCause"
  eff_sync _ := blank "sync"
  eff_suspend _ := blank "suspend"
  eff_perform op t := performB op t
  eff_bind e k := fun env f st => let (p, st) := e env f st; k (env ++ [p]) f st
  eff_gen _ := blank "gen"
  eff_catchCause _ _ := blank "catchCause"
  eff_matchCause _ _ _ := blank "matchCause"
  eff_onExit _ _ := blank "onExit"
  eff_exit _ := blank "exit"
  eff_uninterruptible _ := blank "uninterruptible"
  eff_interruptible _ := blank "interruptible"
  eff_yieldNow _ := blank "yieldNow"
  eff_awaitFiber t m := awaitB t m
  eff_withFiber a := a
  eff_scoped _ := blank "scoped"
  eff_acquireRelease _ _ := blank "acquireRelease"
  eff_provideLayer _ _ _ := blank "provideLayer"
  eff_service _ := blank "service"
  eff_provideService _ _ _ := blank "provideService"
  eff_catchIf _ _ _ := blank "catchIf"
  eff_select _ _ _ _ := blank "select"
  eff_iterate _ _ _ _ _ _ := blank "iterate"
  eff_restore _ _ := blank "restore"
  eff_defs _ _ _ _ := blank "defs"
  eff_invoke _ _ _ := blank "invoke"
  eff_provideContext _ _ := blank "provideContext"
  stmt_bindYield _ := blank "bindYield"
  stmt_yieldDiscard _ := blank "yieldDiscard"
  stmt_ret _ := blank "ret"
  stmt_ifElse _ _ _ := blank "ifElse"
  stmt_whileTrue _ := blank "whileTrue"
  stmt_breakLoop := blank "breakLoop"
  stmts_nil := blank "stmts"
  stmts_cons _ _ := blank "stmts"
  effs_nil := blank "effs"
  effs_cons _ _ := blank "effs"
  action_fork e o := forkB e o
  action_forkIn _ _ _ := blank "forkIn"
  action_forkScoped _ _ := blank "forkScoped"
  action_runIn _ _ := blank "runIn"
  action_interrupt _ := blank "interrupt"
  action_interruptScoped _ := blank "interruptScoped"
  action_interruptAll _ _ := blank "interruptAll"
  action_awaitAll _ := blank "awaitAll"
  action_awaitAllFailFast _ := blank "awaitAllFailFast"
  action_snapshotChildren := blank "snapshotChildren"
  action_awaitNewChildren _ := blank "awaitNewChildren"
  action_raceAll _ := blank "raceAll"
  action_getId := blank "getId"
  action_closeScope _ _ := blank "closeScope"
  action_getInterruptible := blank "getInterruptible"
  action_raceAllFirst _ := blank "raceAllFirst"
  action_context _ := blank "context"
  layer_succeed _ _ := blank "layer"
  layer_effect _ _ := blank "layer"
  layer_effectDiscard _ := blank "layer"
  layer_provide _ _ := blank "layer"
  layer_provideMerge _ _ := blank "layer"
  layer_merge _ _ := blank "layer"
  layer_fresh _ := blank "layer"
  layer_orDie _ := blank "layer"
  layer_ref _ := blank "layer"
  layer_mergeAll _ := blank "layer"
  layers_nil := blank "layers"
  layers_cons _ _ := blank "layers"

/-- **The program's picture**: the fold of `picAlg`, run from the root fiber with nothing in scope. -/
def draw (p : NativeEff) : Pic :=
  let (_, st) := cata_eff picAlg p [] 0 ⟨#[#[]], []⟩
  st.fibers.toList.map (·.toList)

/-! ### The fragment, enumerated -/

def lit (n : Nat) : Term := .lit (.nat n)
def var (i : Nat) : Term := .var i
def pair (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))
/-- A child that the dispatcher starts later. -/
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def fork (p : NativeEff) : NativeEff := .withFiber (.fork p later)

/-- The leaves at a scope of `L` values that are not forks. -/
def bases (L : Nat) : List NativeEff :=
  [.succeed (lit 0), .succeed (lit 1), .perform .refMake (lit 0)] ++
  (List.range L).flatMap fun j =>
    [.succeed (var j), .perform .refSet (pair (var j) (lit 1)), .awaitFiber (var j) .awaitValue]

/-- The leaves at a scope of `L` values: the bases, and a fork of each. -/
def leaves (L : Nat) : List NativeEff := bases L ++ (bases L).map fork

/-- **Every program of the enumeration**: one leaf; two in series; three, nested either way. -/
def programs : List NativeEff :=
  leaves 0 ++
  ((leaves 0).flatMap fun a => (leaves 1).map fun b => .bind a b) ++
  ((leaves 0).flatMap fun a => (leaves 1).flatMap fun b => (leaves 2).map fun c => .bind a (.bind b c)) ++
  ((leaves 0).flatMap fun a => (leaves 1).flatMap fun b => (leaves 1).map fun c => .bind (.bind a b) c)

#guard programs.length == 2238

/-! ### The normaliser: binds reassociated

`bind (bind a b) c` and `bind a (bind b c')` draw one diagram, where `c'` is `c` with a binder
inserted at the outer level: the monad's associativity. With de Bruijn levels, inserting a binder
at level `L` moves every variable at `L` or above up by one, at every depth. -/

mutual
def wkTerm (L : Nat) : Term → Term
  | .var j => .var (if L ≤ j then j + 1 else j)
  | .lit l => .lit l
  | .app f args => .app f (wkTerms L args)
  | t => t
def wkTerms (L : Nat) : Terms → Terms
  | .nil => .nil
  | .cons h t => .cons (wkTerm L h) (wkTerms L t)
end

/-- A binder inserted at level `L` in a fragment program. -/
def wk (L : Nat) : NativeEff → NativeEff
  | .succeed t => .succeed (wkTerm L t)
  | .perform op t => .perform op (wkTerm L t)
  | .awaitFiber t m => .awaitFiber (wkTerm L t) m
  | .withFiber (.fork e o) => .withFiber (.fork (wk L e) o)
  | .bind e k => .bind (wk L e) (wk L k)
  | p => p

/-- The size of a program, a bound for the normaliser's rounds. -/
def size : NativeEff → Nat
  | .bind e k => size e + size k + 1
  | .withFiber (.fork e _) => size e + 1
  | _ => 1

/-- **The normaliser** at scope `L`: every bind's first part is no bind. -/
def normF : Nat → Nat → NativeEff → NativeEff
  | 0, _, p => p
  | n + 1, L, .bind (.bind a b) c => normF n L (.bind a (.bind b (wk L c)))
  | n + 1, L, .bind e k => .bind (normF n L e) (normF n (L + 1) k)
  | n + 1, L, .withFiber (.fork e o) => .withFiber (.fork (normF n L e) o)
  | _ + 1, _, p => p

def norm (p : NativeEff) : NativeEff := normF (4 * size p) 0 p

-- the two nestings of three binds normalise to one program, with the inner binder inserted
#guard norm (.bind (.bind (.succeed (lit 0)) (.succeed (var 0))) (.succeed (var 0))) ==
  .bind (.succeed (lit 0)) (.bind (.succeed (var 0)) (.succeed (var 1)))
-- and draw one diagram
#guard draw (.bind (.bind (.succeed (lit 0)) (.succeed (var 0))) (.succeed (var 0))) ==
  draw (.bind (.succeed (lit 0)) (.bind (.succeed (var 0)) (.succeed (var 1))))
-- a fork's await joins the child's fiber: the root forks fiber 1, and the await names it
#guard draw (.bind (fork (.succeed (lit 7))) (.awaitFiber (var 0) .awaitValue)) ==
  [[{ kind := .fork, note := "later", child := some 1 },
    { kind := .await, phrase := .socket, note := "value", ins := [⟨0, 0⟩], joins := some 1 }],
   [{ kind := .succeed, phrase := .lit (.nat 7) }]]

/-! ## 3. Law 1: the picture expresses the program, and only it, modulo the named normaliser

Mackinlay's two conditions ("encodes all the facts in the set" and "only the facts in the set",
TOG 1986, §5) and Kindlmann and Scheidegger's Unambiguity and Invariance (TVCG 2014, Table 1) read,
for a fold `draw` and a normaliser `norm`, as one statement: `draw p = draw q ↔ norm p = norm q`.
Left to right is no confuser; right to left is no hallucinator. Over the enumeration it holds when
the picture and the normal form cut the programs into the same classes, which is when the pairs
of both cut them into no more classes than either does. -/

/-- The number of classes of a list under equality. -/
def classes {α : Type} [BEq α] (l : List α) : Nat := l.eraseDups.length

/-- Each program of the enumeration, its picture and its normal form. -/
def table1 : List (Pic × NativeEff) := programs.map fun p => (draw p, norm p)

/-- How many normal forms the enumeration holds. -/
def normalForms : Nat := classes (table1.map (·.2))

-- Law 1 on the process diagram: one partition
#guard classes (table1.map (·.1)) == normalForms && classes table1 == normalForms

-- red control: with no normaliser the fold is not injective on programs: the nestings of binds are
-- distinct programs drawn alike
#guard classes programs > classes (table1.map (·.1))

/-- A picture with its words erased: the geometry alone. -/
def unworded (p : Pic) : Pic := p.map (·.map fun b => { b with phrase := .other "", note := "" })

-- red control: the geometry alone confuses programs that differ in a literal; the words are part
-- of the encoding (row 367 (1): the words are a second algebra on the same keys)
#guard classes (table1.map (unworded ·.1)) < normalForms

/-- A fold that forgets which value an await takes: its wire and its join erased. -/
def forgetful (p : Pic) : Pic := p.map (·.map fun b =>
  if b.kind == .await then { b with ins := [], joins := none } else b)

-- red control: that fold confuses an await of one fork with an await of another
#guard classes (table1.map (forgetful ·.1)) < normalForms

/-! ### The algebra into the pen's marks

A layout puts box `k` of fiber `f` at a column and a row: the root's boxes from column 0, a child's
boxes from the column after its fork. Each kind is a figure of the pen (`Tools.View.Tube.Draw`): the
control a pipe (the staff), a value a unit on it, a cell's make a vessel, a write a collar, a fork a
fine tube to the child's staff, an await a promised unit with a fine tube from the exit it takes,
and each value wire a fine tube from its port. Keys name places, so the visible picture is the marks
with their keys erased, and the words beside them in the order of the places. -/

open Tools.View Tools.View.Tube
open Tools.View.Tube.Glyphs (px run arcR tube PIPE VESSEL FINE E W S N unitAt hollowAt)

def COL : Nat := 80
def ROW : Nat := 80
def X0 : Nat := 40
def Y0 : Nat := 40
def RAD : Nat := 24

/-- A fine tube from one point to another (thousandths of a pixel): straight along a row or a
column, else a run, a quarter turn, a run across, a quarter turn back and a run, each turn at the
pen's radius. -/
def link (x₀ y₀ x₁ y₁ : Int) (bore : Nat := FINE) : Tube :=
  let dx := x₁ - x₀
  let dy := y₁ - y₀
  if dy = 0 then tube x₀ y₀ (if dx ≥ 0 then E else W) bore [⟨dx.natAbs, 0⟩]
  else if dx = 0 then tube x₀ y₀ (if dy ≥ 0 then S else N) bore [⟨dy.natAbs, 0⟩]
  else
    let r := px RAD
    let a := (dx.natAbs - 2 * r.natAbs) / 2
    let c := dx.natAbs - 2 * r.natAbs - a
    let b := dy.natAbs - 2 * r.natAbs
    let sgn : Int := if (dx > 0) == (dy > 0) then 1 else -1
    tube x₀ y₀ (if dx > 0 then E else W) bore
      [⟨a, 0⟩, arcR RAD (sgn * HALF_PI), ⟨b, 0⟩, arcR RAD (-(sgn * HALF_PI)), ⟨c, 0⟩]

/-- The first column of each fiber: the root's 0, a child's the column after its fork. -/
def starts (p : Pic) : Array Nat :=
  p.zipIdx.foldl (fun (acc : Array Nat) (bs, f) =>
    bs.zipIdx.foldl (fun (acc : Array Nat) (b, k) =>
      match b.child with
      | some c => acc.set! c (acc.getD f 0 + k + 1)
      | none => acc) acc) (Array.replicate p.length 0)

/-- **The pen's marks of a picture**, and its words in the order of the places. -/
def marksOf (p : Pic) : List Mark × List (Phrase × String) :=
  let st := starts p
  let xAt (f k : Nat) : Int := px (X0 + (st.getD f 0 + k) * COL)
  let yAt (f : Nat) : Int := px (Y0 + f * ROW)
  let staffOf (f : Nat) (n : Nat) : Tube :=
    tube (xAt f 0 - px 20) (yAt f) E PIPE [⟨(n - 1) * COL * 1000 + 40000, 0⟩]
  let lastOf (f : Nat) : Nat := (p.getD f []).length - 1
  let marks := p.zipIdx.flatMap fun (bs, f) =>
    if bs.isEmpty then [] else
    let staff := staffOf f bs.length
    let along (k : Nat) : Int := xAt f k - staff.x
    bodyOf s!"s{f}" staff ++ bs.zipIdx.flatMap fun (b, k) =>
      let key := s!"b{f}.{k}"
      let figure : List Mark := match b.kind with
        | .succeed => [unitAt key staff (along k)]
        | .make => bodyOf key (tube (xAt f k - px 14) (yAt f) E VESSEL [run 28])
        | .write => [collarOf key staff (along k - 6000) 12000]
        | .fork => match b.child with
          | some c => bodyOf key (link (xAt f k) (yAt f + px 16) (xAt c 0) (yAt c))
          | none => bodyOf key (tube (xAt f k) (yAt f) E PIPE [run 10])
        | .await => hollowAt key (key ++ "h") staff (along k) ++ match b.joins with
          | some c => bodyOf (key ++ "j") (link (xAt c (lastOf c)) (yAt c) (xAt f k) (yAt f - px 16))
          | none => []
        | .other _ => bodyOf key (tube (xAt f k) (yAt f) E PIPE [run 10])
      let wires := b.ins.zipIdx.flatMap fun (q, i) =>
        bodyOf s!"{key}w{i}" (link (xAt q.fiber q.box) (yAt q.fiber - px 16) (xAt f k) (yAt f - px 16))
      figure ++ wires
  (marks, p.flatMap (·.map fun b => (b.phrase, b.note)))

/-- **What a reader sees** of a program: the marks, keys erased, and the words. -/
def visible (p : NativeEff) : List Mark × List (Phrase × String) :=
  let (ms, ws) := marksOf (draw p)
  (ms.map fun m => { m with key := "" }, ws)

-- every tube of every program's picture keeps the pen's bend law
#guard programs.all fun p => (marksOf (draw p)).1.all fun m => decide m.tube.ok

-- Law 1 on what a reader sees: the marks and words cut the programs as the normal forms do
#guard classes (programs.map visible) == normalForms &&
  classes ((programs.map visible).zip (table1.map (·.2))) == normalForms

-- red control: the marks alone, with no words, confuse programs that differ in a literal
#guard classes (programs.map fun p => (visible p).1) < normalForms

/-! ### A reader: the program read back from its picture

The strongest form of Law 1 is an exact embedding modulo the normaliser: a reader `readPic` with
`readPic (draw p) = some (norm p)` (retraction), which refuses a picture that is the drawing of no
program (exactness, checked by drawing what it reads). The reader walks each fiber's boxes in the
order of its control: a box is a leaf, the boxes after it its continuation, a fork's child the
boxes of the fiber it starts. A socket takes the level of the port its wire comes from. -/

/-- The level of a port in scope. -/
def levelOf (env : List Port) (q : Port) : Option Nat := env.findIdx? (· == q)

/-- A term from a phrase, its sockets filled in order by the box's wires. -/
def termOf (env : List Port) : Phrase → List Port → Option (Term × List Port)
  | .lit l, qs => some (.lit l, qs)
  | .socket, q :: qs => (levelOf env q).map fun i => (.var i, qs)
  | .socket, [] => none
  | .pair a b, qs => do
    let (ta, qs) ← termOf env a qs
    let (tb, qs) ← termOf env b qs
    some (pair ta tb, qs)
  | .other _, _ => none

/-- A box's term, every wire used. -/
def termOfBox (env : List Port) (b : Box) : Option Term :=
  match termOf env b.phrase b.ins with
  | some (t, []) => some t
  | _ => none

def modeOf : String → Option Supervision.ObserverMode
  | "value" => some .awaitValue
  | "join" => some .joinEffect
  | _ => none

/-- **The reader** of fiber `f` from box `i`, with the ports in scope: a leaf, then the rest in a
bind; a fork reads its child's fiber. Fuel bounds the walk. -/
def readFrom (p : Pic) : Nat → List Port → Nat → Nat → Option NativeEff
  | 0, _, _, _ => none
  | n + 1, env, f, i => do
    let bs := p.getD f []
    let b ← bs[i]?
    let leaf ← match b.kind with
      | .succeed => (termOfBox env b).map .succeed
      | .make => (termOfBox env b).map (.perform .refMake ·)
      | .write => (termOfBox env b).map (.perform .refSet ·)
      | .await => do
        let t ← termOfBox env b
        let m ← modeOf b.note
        some (.awaitFiber t m)
      | .fork => do
        let c ← b.child
        guard (b.note == "later")
        let e ← readFrom p n env c 0
        some (fork e)
      | .other _ => none
    if i + 1 = bs.length then some leaf
    else do
      let rest ← readFrom p n (env ++ [⟨f, i⟩]) f (i + 1)
      some (.bind leaf rest)

/-- The number of boxes of a picture, the reader's fuel. -/
def boxes (p : Pic) : Nat := (p.map List.length).foldl (· + ·) 0

/-- **The reader**, checked: a picture that reads, and that is the drawing of what it reads. -/
def readPic (p : Pic) : Option NativeEff := do
  let q ← readFrom p (boxes p + 1) [] 0 0
  if draw q == p then some q else none

-- retraction, over the enumeration: every picture reads back as its program's normal form
#guard programs.all fun p => readPic (draw p) == some (norm p)

/-- A picture changed in one place: the root's first await joins another fiber. -/
def misjoin (p : Pic) : Pic :=
  match p with
  | bs :: rest => (bs.map fun b => if b.kind == .await then { b with joins := b.joins.map (· + 1) } else b) :: rest
  | [] => []

-- exactness has teeth: a picture whose await joins the wrong fiber reads as no program
#guard programs.any fun p => (draw p).headD [] |>.any (·.kind == .await)
#guard programs.all fun p =>
  !(((draw p).headD []).any fun b => b.kind == .await && b.joins.isSome) || readPic (misjoin (draw p)) == none

/-! ## 4. Law 2 on the real machine: drawing then stepping, stepping then drawing

Kindlmann and Scheidegger's Equation (1), `v ∘ r ∘ α = ω ∘ v ∘ r` (TVCG 2014, §3), with the data
change `α` a machine step: the picture of the next state is the picture of this state changed by
`ω`, a change computed from the step. In Alvarez-Picallo and Ong's terms (FoSSaCS 2019, §2) the
picture is a map between change actions, the journal acting on runs and keyed changes acting on
pictures, and `ω` is its derivative. Row 371 (3) asks that fills follow the machine: here `ω` is
read from the step's own events, never from the next state.

The machine is the tree's: `stepDecisionState` over `interpOf`, every tape of enabled `fire`
decisions to a depth, as the battery `Test/Machine/Runtime/ScheduleIndependence.lean` explores. -/

abbrev M := Api.Machine
abbrev Dn := Api.Decision

def fuel : Nat := 400

/-- One decision, with its sufficiency receipt. -/
def stepD (p : NativeEff) (m : M) (d : Dn) : M × Bool :=
  letI := evaluatorFor p []
  stepDecisionState (interpOf p []) fuel m d

/-- **Every run of a program**: the machine loaded, the root started, then every tape of enabled
`fire` decisions to depth `k`, each as the list of machines it passes. -/
def explore (p : NativeEff) : Nat → M → List (List M)
  | 0, m => [[m]]
  | k + 1, m =>
    match m.armed with
    | [] => [[m]]
    | owners => owners.flatMap fun o =>
        let r := stepD p m (.fire o)
        if r.2 then (explore p k r.1).map (m :: ·) else [[m, r.1]]

def runsOf (p : NativeEff) : List (List M) :=
  let m₀ := Api.load p fuel
  (explore p 12 (stepD p m₀ Api.evaluate).1).map (m₀ :: ·)

/-! ### The state's picture: a slice -/

/-- A fiber's state: live, parked on a token, or exited. -/
inductive Status where
  | live | parked | exited
deriving DecidableEq, Repr

def SX : Int := px 40
def SY : Nat := 40
def SROW : Nat := 64

/-- A fiber's staff, and its figure in a state: a unit while it is live, a promised unit while it
is parked, the exit's struts once it has exited. -/
def staffOf (i : Nat) : Tube := tube SX (px (SY + i * SROW)) E PIPE [run 60]

def fiberMarks (i : Nat) (st : Status) : List Mark :=
  bodyOf s!"s{i}" (staffOf i) ++ match st with
  | .live => [unitAt s!"u{i}" (staffOf i) (px 30)]
  | .parked => hollowAt s!"u{i}" s!"u{i}h" (staffOf i) (px 30)
  | .exited => (bodyOf s!"x{i}" (tube (SX + px 70) (px (SY + i * SROW) - px 16) S PIPE [run 32])).map
      fun m => { m with fill := .ink }

/-- A cell's vessel, below the staffs. -/
def cellMarks (j : Nat) : List Mark :=
  bodyOf s!"c{j}" (tube (px (200 + j * 60)) (px 20) E VESSEL [run 28])

/-- A deferred's vessel of one unit: its unit hollow while it is owed, filled once it is kept. -/
def deferredMarks (j : Nat) (kept : Bool) : List Mark :=
  let t := tube (px (200 + j * 60)) (px 80) E VESSEL [run 28]
  bodyOf s!"d{j}" t ++ if kept then [unitAt s!"e{j}" t (px 14)] else hollowAt s!"e{j}" s!"e{j}h" t (px 14)

/-- **A slice picture**: the marks, and the words beside them by key (a cell's value). -/
structure SPic where
  marks : List Mark
  words : List (String × Val)

def statusOf (f : Api.Machine) (i : FiberId) : Status :=
  match f.fiber? i with
  | some fb => if fb.exit.isSome then .exited else match fb.parked with
    | .notParked => .live
    | .withGuard _ => .parked
  | none => .live

/-- **The picture of a state**, read from the state alone: each fiber by its flags, each cell by
its value, each deferred by whether it is kept. -/
def slice (m : M) : SPic :=
  { marks := (m.fibers.flatMap fun f => fiberMarks f.id.value (statusOf m f.id)) ++
      ((List.range m.state.refs.length).flatMap cellMarks) ++
      (m.state.deferreds.cells.zipIdx.flatMap fun (c, j) => deferredMarks j c.completion.isSome)
    words := m.state.refs.zipIdx.map fun (v, j) => (s!"c{j}", v) }

/-! ### The change of a step, read from its events -/

/-- **An edit** of a picture: a mark put by its key (entering, or replacing the mark of its key), a
key dropped, or a word set. -/
inductive Edit where
  | put (m : Mark)
  | drop (key : String)
  | word (key : String) (v : Val)

/-- **A keyed change**: edits in order. Changes compose by concatenation, and act one edit at a
time: the free monoid on edits acting on pictures. -/
abbrev Change := List Edit

def Edit.apply : Edit → SPic → SPic
  | .put m, p => { p with marks := (p.marks.filter (·.key != m.key)) ++ [m] }
  | .drop k, p => { p with marks := p.marks.filter (·.key != k) }
  | .word k v, p => { p with words := (p.words.filter (·.1 != k)) ++ [(k, v)] }

def Change.apply (c : Change) (p : SPic) : SPic := c.foldl (fun p e => e.apply p) p

/-- **The derivative from events**: what each event of a step changes in the picture. A fork
starts a staff with its unit; a park makes the unit hollow; a resume fills it; an exit removes the
unit and draws the struts. The trace has no event for a change of the store: no cell's make or
write, no deferred's make or completion. -/
def ofEvent : RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx
    (Prim EffName EffThunk Val Err Defect FiberId Ann) (FrameEvent EffName EffThunk Val Err Defect FiberId Ann) → Change
  | .forked _ c _ => (fiberMarks c.value .live).map .put
  | .parkedOn f _ => (fiberMarks f.value .parked).map .put
  | .resumedWith f _ _ => .drop s!"u{f.value}h" :: (fiberMarks f.value .live).map .put
  | .exited f _ => [.drop s!"u{f.value}", .drop s!"u{f.value}h"] ++ (fiberMarks f.value .exited).map .put
  | _ => []

/-- The events a step added to the trace. -/
def newEvents (m m' : M) := m'.trace.drop m.trace.length

/-- The change a step's events make. -/
def eventChange (m m' : M) : Change := (newEvents m m').flatMap ofEvent

/-- A store's key: a cell's vessel, a deferred's vessel, or a deferred's unit. -/
def storeKey (k : String) : Bool := k.startsWith "c" || k.startsWith "d" || k.startsWith "e"

/-- The store's part of a picture. -/
def storePart (p : SPic) : SPic := { marks := p.marks.filter (storeKey ·.key), words := p.words }

/-- **The change of the store**, read from the two states: the keyed difference of the store's
marks and words (Cai and others' derivative by difference). -/
def storeChange (m m' : M) : Change :=
  let a := (storePart (slice m)).marks
  let b := (storePart (slice m')).marks
  ((a.filter fun x => !(b.any (·.key == x.key))).map fun x => .drop x.key) ++
    ((b.filter fun y => !(a.contains y)).map .put) ++
    ((slice m').words.filter fun w => !(slice m).words.contains w).map fun (k, v) => .word k v

/-- Two pictures with the same marks, in any order, and the same words. -/
def SPic.same (a b : SPic) : Bool :=
  a.marks.length == b.marks.length && a.marks.all b.marks.contains &&
  a.words.length == b.words.length && a.words.all b.words.contains

/-- A decision leaves the store's picture as it was. -/
def storeSame (m m' : M) : Bool := (storePart (slice m)).same (storePart (slice m'))

/-- The consecutive pairs of a run. -/
def steps (r : List M) : List (M × M) := r.zip r.tail

/-! ### The fragment's programs -/

def seq : List NativeEff → NativeEff
  | [] => .succeed (.lit .unit)
  | [p] => p
  | p :: ps => .bind p (seq ps)

def join (i : Nat) : NativeEff := .awaitFiber (var i) .joinEffect

/-- One fiber: a cell made, written, and a value. -/
def lWrite : NativeEff := seq [.perform .refMake (lit 0), .perform .refSet (pair (var 0) (lit 1)), .succeed (lit 2)]
/-- A child writes the cell; the root joins it. -/
def lChild : NativeEff := seq [.perform .refMake (lit 0), fork (.perform .refSet (pair (var 0) (lit 1))), join 1]
/-- Two children write one cell. With no yield, one `fire` drains the dispatcher, so the fragment's
runs have one schedule. -/
def lRace : NativeEff := seq [.perform .refMake (lit 0),
  fork (.perform .refSet (pair (var 0) (lit 1))), fork (.perform .refSet (pair (var 0) (lit 2))), join 1, join 2]
/-- The battery's `pRaceY`: each child yields before its write, so the schedule decides the last
write. `yieldNow` is outside the five constructors; the slice picture does not draw it. -/
def lRaceY : NativeEff := seq [.perform .refMake (lit 0),
  fork (seq [.yieldNow 0, .perform .refSet (pair (var 0) (lit 1))]),
  fork (seq [.yieldNow 0, .perform .refSet (pair (var 0) (lit 2))]), join 1, join 2]
/-- Two children, each its own cell. -/
def lIndep : NativeEff := seq [.perform .refMake (lit 0), .perform .refMake (lit 0),
  fork (.perform .refSet (pair (var 0) (lit 1))), fork (.perform .refSet (pair (var 1) (lit 2))), join 2, join 3]
/-- Forks within a fork, and no cell. -/
def lNest : NativeEff := seq [fork (seq [fork (.succeed (lit 1)), join 0]), join 0]
/-- `pFork`'s shape in the fragment: a fork and its join. -/
def lFork : NativeEff := seq [fork (.succeed (lit 7)), join 0]
/-- The battery's `pKahnY`: a child keeps a deferred that the root awaits. It leaves the fragment:
a deferred's make, completion and await, and a yield. -/
def lKahn : NativeEff := seq [.perform (.deferredMakeOf .nat .never) (.lit .unit),
  fork (seq [.yieldNow 0, .perform .deferredSucceed (pair (var 0) (lit 5))]),
  .perform .deferredAwait (var 0), join 1, .succeed (var 2)]

def lawPrograms : List NativeEff := [lWrite, lChild, lRace, lRaceY, lIndep, lNest, lFork, lKahn]

/-- Every step of every run of every program. -/
def allSteps : List (M × M) := lawPrograms.flatMap fun p => (runsOf p).flatMap steps

-- every program is admitted by the checker, as the battery's programs are
#guard lawPrograms.all fun p => (typeOf nativeSignature p).isSome
-- the runs end with every fiber exited
#guard lawPrograms.all fun p => (runsOf p).all fun r => (r.getLast?.map (·.finished)).getD false
-- with no yield, lRace has one run; with yields, lRaceY's runs end at two values of its cell
#guard (runsOf lRace).length == 1
#guard ((runsOf lRaceY).filterMap fun r => r.getLast?.map (·.state.refs)).eraseDups.length == 2

/-- **The square, from events alone**: the next state's picture is this state's changed by the
step's events. -/
def squareEvents (m m' : M) : Bool := (Change.apply (eventChange m m') (slice m)).same (slice m')

/-- **The square, with the store's difference**: the events and the store's change. -/
def squareWithStore (m m' : M) : Bool :=
  (Change.apply (eventChange m m' ++ storeChange m m') (slice m)).same (slice m')

-- Law 2 from events holds at every step that leaves the store as it was
#guard allSteps.all fun (m, m') => !storeSame m m' || squareEvents m m'
-- and on the programs with no cell, at every step
#guard ([lNest, lFork].flatMap fun p => (runsOf p).flatMap steps).all fun (m, m') => squareEvents m m'
-- red result: a cell's make and its write leave no event, so the square from events fails there
#guard allSteps.any fun (m, m') => m.state.refs.length < m'.state.refs.length && !squareEvents m m'
#guard allSteps.any fun (m, m') =>
  m.state.refs.length == m'.state.refs.length && m.state.refs != m'.state.refs && !squareEvents m m'
-- and a deferred's make and its completion leave none either
#guard allSteps.any fun (m, m') => m.state.refs == m'.state.refs &&
  m.state.deferreds.cells.length < m'.state.deferreds.cells.length && !squareEvents m m'
#guard allSteps.any fun (m, m') => m.state.refs == m'.state.refs &&
  m.state.deferreds.cells.length == m'.state.deferreds.cells.length &&
  (m.state.deferreds.cells.map (·.completion.isSome)) != (m'.state.deferreds.cells.map (·.completion.isSome)) &&
  !squareEvents m m'
-- with the store's difference added, the square holds at every step of every run
#guard allSteps.all fun (m, m') => squareWithStore m m'

/-- The marks of one key class: the fibers' marks. -/
def fiberKey (k : String) : Bool := k.startsWith "s" || k.startsWith "u" || k.startsWith "x"

/-- The keys a change puts, and the keys it drops. -/
def putKeys (c : Change) : List String := c.filterMap fun | .put m => some m.key | _ => none
def dropKeys (c : Change) : List String := c.filterMap fun | .drop k => some k | _ => none

-- the events' change and the kit's keyed match agree on what enters and what leaves: the fiber keys
-- the step's events put that the state before lacks are the kit's `enter`, and the keys they drop
-- that the state after lacks are its `exit`
#guard allSteps.all fun (m, m') =>
  let a := (slice m).marks.filter (fiberKey ·.key)
  let b := (slice m').marks.filter (fiberKey ·.key)
  let j := Whatwg.Svg.Scene.join (·.key) a b
  let c := eventChange m m'
  let entered := ((putKeys c).filter fun k => !(a.any (·.key == k)) && b.any (·.key == k)).eraseDups
  let left := ((dropKeys c).filter fun k => a.any (·.key == k) && !(b.any (·.key == k))).eraseDups
  (j.enter.map (·.key)).all entered.contains && entered.all (j.enter.map (·.key)).contains &&
  (j.exit.map (·.key)).all left.contains && left.all (j.exit.map (·.key)).contains

-- the agreement is not empty: some step's events enter a key, and some step's events drop one
#guard allSteps.any fun (m, m') => (putKeys (eventChange m m')).any fun k => !((slice m).marks.any (·.key == k))
#guard allSteps.any fun (m, m') => (dropKeys (eventChange m m')).any fun k => (slice m).marks.any (·.key == k)

/-- A derivative that forgets an exit. -/
def forgetExit : RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx
    (Prim EffName EffThunk Val Err Defect FiberId Ann) (FrameEvent EffName EffThunk Val Err Defect FiberId Ann) → Change
  | .exited _ _ => []
  | e => ofEvent e

-- red control: with the exit forgotten, the square from events fails at some step with no cell change
#guard allSteps.any fun (m, m') => m.state.refs == m'.state.refs &&
  !(Change.apply ((newEvents m m').flatMap forgetExit) (slice m)).same (slice m')

-- films compose: the changes of a run's steps, in order, take its first picture to its last
#guard lawPrograms.all fun p => (runsOf p).all fun r =>
  match r.head?, r.getLast? with
  | some m₀, some mₙ =>
    (Change.apply ((steps r).flatMap fun (m, m') => eventChange m m' ++ storeChange m m') (slice m₀)).same (slice mₙ)
  | _, _ => false

/-! ## 5. Tokens: a module's counts as a net, and conservation as a place invariant

A net's marking is a count per place; a transition takes a count from each place and gives a count
to each (Meseguer and Montanari, *Petri nets are monoids*, 1990, read through Baez and Master,
*Open Petri nets*, §2: markings form the free commutative monoid on the places). A weighting `y` is
a place invariant when every transition takes and gives the same weighted sum (Murata 1989, by
name). Then every firing keeps the weighted sum: the theorem below, which the kernel accepts. The
nets are counting readings of a module's cell: they keep counts and forget values and order. -/

/-- A transition fired at a marking: per place, the count less what it takes plus what it gives. -/
def fireL : List Nat → List Nat → List Nat → List Nat
  | m :: ms, t :: ts, g :: gs => (m - t + g) :: fireL ms ts gs
  | _, _, _ => []

/-- The weighted sum of a marking. -/
def wsum : List Nat → List Nat → Nat
  | y :: ys, m :: ms => y * m + wsum ys ms
  | _, _ => 0

/-- A transition is enabled: it takes no more from each place than the place holds. -/
def takes : List Nat → List Nat → Prop
  | t :: ts, m :: ms => t ≤ m ∧ takes ts ms
  | [], [] => True
  | _, _ => False

/-- **A firing moves the weighted sum by what it gives less what it takes.** A step of
`fire_keeps`. -/
theorem fire_sum (y m t g : List Nat) (h : takes t m) (hg : g.length = m.length) :
    wsum y (fireL m t g) + wsum y t = wsum y m + wsum y g := by
  induction m generalizing y t g with
  | nil =>
    cases t with
    | nil =>
      cases g with
      | nil => cases y <;> rfl
      | cons _ _ => simp only [List.length_cons, List.length_nil] at hg; omega
    | cons _ _ => exact absurd h id
  | cons a ms ih =>
    cases t with
    | nil => exact absurd h id
    | cons b ts =>
      cases g with
      | nil => simp only [List.length_nil, List.length_cons] at hg; omega
      | cons c gs =>
        obtain ⟨hb, hts⟩ := h
        cases y with
        | nil => rfl
        | cons w ys =>
          have hl : gs.length = ms.length := by
            simp only [List.length_cons] at hg; omega
          have step := ih ys ts gs hts hl
          have h1 : a - b + c + b = a + c := by omega
          have h2 : w * (a - b + c) + w * b = w * a + w * c := by
            rw [← Nat.mul_add, h1, Nat.mul_add]
          simp only [fireL, wsum]
          omega

/-- **A place invariant is kept by every firing**: where a transition takes and gives one weighted
sum, the marking after it has the weighted sum of the marking before. -/
theorem fire_keeps (y m t g : List Nat) (h : takes t m) (hg : g.length = m.length)
    (inv : wsum y t = wsum y g) : wsum y (fireL m t g) = wsum y m := by
  have := fire_sum y m t g h hg
  omega

/-- A net: its transitions, each a take and a give. -/
abbrev Net := List (List Nat × List Nat)

/-- A weighting is a place invariant of a net. -/
def Invariant (y : List Nat) (n : Net) : Bool := n.all fun (t, g) => wsum y t == wsum y g

/-- **The Queue's counts**: places `free`, `buffer`, offers waiting, takers waiting. An offer takes
a free slot into the buffer; a take frees one; an offer or a take may wait; a waiting offer is
admitted to a freed slot; a waiting offer meets a waiting taker. -/
def queueNet : Net :=
  [([1, 0, 0, 0], [0, 1, 0, 0]), ([0, 1, 0, 0], [1, 0, 0, 0]), ([0, 0, 0, 0], [0, 0, 1, 0]),
   ([0, 0, 0, 0], [0, 0, 0, 1]), ([1, 0, 1, 0], [0, 1, 0, 0]), ([0, 0, 1, 1], [0, 0, 0, 0])]

/-- **The Semaphore's counts**: permits available and held; an acquire and a release. -/
def semaphoreNet : Net := [([1, 0], [0, 1]), ([0, 1], [1, 0])]

/-- **A broadcast's counts**: a header and three taps; a publish gives the header a unit, and the
broadcast copies the header's unit down each tap. -/
def broadcastNet : Net := [([0, 0, 0, 0], [1, 0, 0, 0]), ([1, 0, 0, 0], [0, 1, 1, 1])]

-- the Queue keeps `free + buffer`: its capacity; the Semaphore keeps `available + held`: its circuit
#guard Invariant [1, 1, 0, 0] queueNet
#guard Invariant [1, 1] semaphoreNet
-- red control: the Queue does not keep the count of what waits
#guard !Invariant [0, 0, 1, 1] queueNet
-- red control: a broadcast keeps no plain count, the sum a solid join would claim; with its publish
-- removed it keeps the sum where a header unit weighs as many units as there are taps
#guard !Invariant [1, 1, 1, 1] broadcastNet
#guard Invariant [3, 1, 1, 1] (broadcastNet.drop 1)
#guard !Invariant [3, 1, 1, 1] broadcastNet

-- the theorem at the Queue: a capacity of three, an offer taken in, then a take
#guard wsum [1, 1, 0, 0] (fireL (fireL [3, 0, 0, 0] [1, 0, 0, 0] [0, 1, 0, 0]) [0, 1, 0, 0] [1, 0, 0, 0]) == 3

/-! ## 6. The audit of this file's theorems, by the gate's walk -/

/-- info: probe audit: 2 declarations within [propext, Quot.sound] -/
#guard_msgs in
#probe_audit fire_sum fire_keeps

/-! ## 7. The vocabulary in the algebra

Each of the 37 marks of the tree's `Tools.View.Glyph.Shape` is one of four classes: a term of the
signature, a contents state on a wire, a region round a diagram, or a boundary of a diagram. The
thirteen term marks each get a term of the free signature, typed by `D.ty`; the junction marks are
read as counts. -/

open Tools.View.Glyph (Shape Kind)

/-- The four classes of a mark in the algebra. -/
inductive Class where
  | term | state | region | boundary
deriving DecidableEq, Repr

/-- **The class of each mark**: total over the tree's `Shape`, so a mark added to the vocabulary
is refused here until it is classed. -/
def classOf : Shape → Class
  | .box | .value | .call | .probe | .series | .parallel | .alternative | .loop | .rest | .arrow
  | .spider | .port | .blockedArrow => .term
  | .atom | .tag | .cross | .hash | .reasons | .hollowDot | .filledDot | .hollowBox | .filledBox
  | .slot | .panel | .cells => .state
  | .openBracket | .bracket | .region | .rail | .block | .library => .region
  | .enter | .hole | .barLine | .exitBar | .fermata | .caesura => .boundary

/-- An operation on one fiber's control, with its value legs. -/
def op (name : String) (ins outs : List Wire) : D := .gen .control (.box name (.control :: ins) (.control :: outs))

/-- **The term of each term mark.** -/
def termOf? : Shape → Option D
  | .box => some (op "op" [.value] [.value])
  | .value => some (op "succeed" [] [.value])
  | .call => some (op "invoke" [.value] [.value])
  | .probe => some (op "read" [.vessel] [.vessel, .value])
  | .series => some (.series (op "a" [] [.value]) (op "b" [.value] [.value]))
  | .parallel => some mrg
  | .alternative => some (.series (.gen .value .split) (.gap (.gen .value (.valve true)) (.gen .value (.valve false))))
  | .loop => some (.loop .value (.gen .control (.box "body" [.value, .control] [.value, .control])))
  | .rest => some (.gen .control (.valve false))
  | .arrow => some (.gen .control .fork)
  | .spider => some (.series cpy (.gap cpy v1))
  | .port => some (op "row" [.value] [.value])
  | .blockedArrow => some (.gen .control (.box "interrupt" [.control, .control] [.control, .control]))
  | _ => none

/-- Every shape, in the order of its constructors (the tree's own list). -/
def allShapes : List Shape := Tools.View.Tube.Glyphs.shapes

-- the term marks are exactly the marks with a term, and every term types
#guard allShapes.all fun s => (classOf s == .term) == (termOf? s).isSome
#guard allShapes.all fun s => ((termOf? s).map fun d => d.ty.isSome).getD true
-- the four classes count 13, 12, 6 and 6 of the 37
#guard [Class.term, .state, .region, .boundary].map (fun c => (allShapes.filter (classOf · == c)).length) ==
  [13, 12, 6, 6]

-- the junction marks read as counts: a merge conserves, the spider sends three units for one,
-- and the alternative decided as a copy then one open and one closed valve conserves
#guard ((termOf? .parallel).bind count).all conserves
#guard ((termOf? .spider).bind count).map (copies · 0) == some 3
#guard (count (.series cpy (.gap (.gen .value (.valve true)) (.gen .value (.valve false))))).all conserves
-- red control: the alternative's split has no counting reading until a decision sets its valves
#guard ((termOf? .alternative).bind count).isNone

/-- The marks whose class differs from the class of most marks of their kind. -/
def kindClass : Tools.View.Glyph.Kind → Class
  | .body | .vessel => .state
  | .container => .region
  | .wire | .bond | .force => .term
  | .cadence => .boundary

-- the kinds of row 368 (4) and the classes disagree on eight marks: four bodies that are terms, a
-- body and a vessel that are boundaries, two containers that are states
#guard (allShapes.filter fun s => classOf s != kindClass s.kind) ==
  [.box, .value, .probe, .call, .hole, .enter, .panel, .cells]

/-! ## 8. A region is not a functor: one mask over a series, against two masks, on the machine

E8's refusal, tested on the real machine. A child writes a cell twice inside masks; the parent
interrupts it while it yields. Under one mask round both writes, the recorded interrupt waits for
the mask's end, after the second write. Under two masks, it is delivered where the first ends,
after the first write. The programs leave the fragment: `uninterruptible`, `yieldNow`, an interrupt
and `refGet`. -/

/-- The child's writes, under one mask or under two. -/
def oneMask : NativeEff := .uninterruptible (seq [.yieldNow 0, .perform .refSet (pair (var 0) (lit 1)),
  .yieldNow 0, .perform .refSet (pair (var 0) (lit 2))])
def twoMasks : NativeEff := seq [.uninterruptible (seq [.yieldNow 0, .perform .refSet (pair (var 0) (lit 1))]),
  .uninterruptible (seq [.yieldNow 0, .perform .refSet (pair (var 0) (lit 2))])]

/-- The parent: a cell, the child forked, a yield, the interrupt, the child's exit as a value. -/
def masked (child : NativeEff) : NativeEff := seq [.perform .refMake (lit 0), fork child, .yieldNow 0,
  .withFiber (.interrupt (var 1)), .awaitFiber (var 1) .awaitValue, .perform .refGet (var 0)]

/-- The cell's last value at the end of every run. -/
def lastCells (p : NativeEff) : List (List Val) :=
  ((runsOf p).filterMap fun r => r.getLast?.map (·.state.refs)).eraseDups

-- both programs are admitted, and every run ends with every fiber exited
#guard [masked oneMask, masked twoMasks].all fun p => (typeOf nativeSignature p).isSome
#guard [masked oneMask, masked twoMasks].all fun p => (runsOf p).all fun r => (r.getLast?.map (·.finished)).getD false
-- under one mask the run ends after both writes; under two masks it stops between them
#guard lastCells (masked oneMask) == [[.nat 2]]
#guard lastCells (masked twoMasks) == [[.nat 1]]

end TubeProbe
