import Effect4.Codegen.Template

/-! Probe for R4.2 to R5.1: the table-driven printer as a FOLD of one generic layer function,
and the reader as its one-step inverse.

What the algebra gives: `cata` turns a one-layer function `String → List (ArgF R) → R` into a
function on the whole tree. The generic view of a layer (constructor name, arguments by sort,
children already folded) and its inverse `build` are what a generator emits from the inductive.
The table is first-order data. Nothing else is per constructor. -/

set_option autoImplicit false

namespace TableProbe

open TypeScript
open Effect4.Codegen.Template

/-! ## A leaf sort with its own printer and reader (as `Term` has) -/

inductive Term where
  | lit (b : Bool)
  | num (n : Nat)
deriving DecidableEq, Repr

def printTerm : Term → Expr
  | .lit b => .bool b
  | .num n => .int (Int.ofNat n)

def readTerm : Expr → Option Term
  | .bool b => some (.lit b)
  | .int (.ofNat n) => some (.num n)
  | _ => none

theorem readTerm_printTerm (t : Term) : readTerm (printTerm t) = some t := by
  cases t <;> rfl

/-! ## A miniature of the program family: a binder, a classifier, a string argument, and the
`Effect.suspend` group (two rows sharing a head) -/

inductive Eff where
  | succeed (v : Term)
  | suspend (body : Eff)
  | bind (first rest : Eff)
  | catchIf (test : Term) (body handler : Eff)
  | selectBool (s : Term) (a0 a1 : Eff)
  | selectTag (s : Term) (tag : String) (a0 a1 : Eff)
deriving DecidableEq, Repr

/-! ## What a generator emits from the inductive: the layer view, its inverse, the fold -/

/-- One argument of a constructor, by sort, with children at carrier `R`. -/
inductive ArgF (R : Type) where
  | child (r : R)
  | term (t : Term)
  | str (s : String)

inductive Sort' where
  | child | term | str
deriving DecidableEq

def sorts : String → List Sort'
  | "succeed" => [.term]
  | "suspend" => [.child]
  | "bind" => [.child, .child]
  | "catchIf" => [.term, .child, .child]
  | "selectBool" => [.term, .child, .child]
  | "selectTag" => [.term, .str, .child, .child]
  | _ => []

/-- The fold: a one-layer function becomes a function on the tree. -/
def cata {R : Type} (alg : String → List (ArgF R) → R) : Eff → R
  | .succeed v => alg "succeed" [.term v]
  | .suspend b => alg "suspend" [.child (cata alg b)]
  | .bind f r => alg "bind" [.child (cata alg f), .child (cata alg r)]
  | .catchIf t b h => alg "catchIf" [.term t, .child (cata alg b), .child (cata alg h)]
  | .selectBool s a b => alg "selectBool" [.term s, .child (cata alg a), .child (cata alg b)]
  | .selectTag s t a b =>
    alg "selectTag" [.term s, .str t, .child (cata alg a), .child (cata alg b)]

/-- The inverse of the layer view at the tree itself. -/
def build : String → List (ArgF Eff) → Option Eff
  | "succeed", [.term v] => some (.succeed v)
  | "suspend", [.child b] => some (.suspend b)
  | "bind", [.child f, .child r] => some (.bind f r)
  | "catchIf", [.term t, .child b, .child h] => some (.catchIf t b h)
  | "selectBool", [.term s, .child a, .child b] => some (.selectBool s a b)
  | "selectTag", [.term s, .str t, .child a, .child b] => some (.selectTag s t a b)
  | _, _ => none

/-! ## The table: first-order data -/

structure Row where
  ctor : String
  /-- The classifier: arguments this row fixes. They do not occur in the skeleton; the reader
  supplies them. -/
  fixed : List (Nat × Term)
  /-- Per argument, how many binders it is printed under (the binder table's column). -/
  depth : List Nat
  tpl : Tpl

def call (head : String) (args : List Tpl) : Tpl :=
  .call (.ident head) (args.foldr Tpls.cons .nil)

/-- Hole `i` is the constructor's argument `i`. Order matters where rows share a head: the
conditional before the plain suspension; the fixed-test `catch` before the general `catchIf`. -/
def table : List Row :=
  [ ⟨"succeed", [], [0], call "Effect.succeed" [.hole 0]⟩
  , ⟨"selectBool", [], [0, 0, 0], call "Effect.suspend" [.arrow (.cond (.hole 0) (.hole 1) (.hole 2))]⟩
  , ⟨"suspend", [], [0], call "Effect.suspend" [.arrow (.hole 0)]⟩
  , ⟨"bind", [], [0, 1], call "Effect.flatMap" [.hole 0, .lambda [0] (.hole 1)]⟩
  , ⟨"catchIf", [(0, .lit true)], [0, 0, 1], call "Effect.catch" [.hole 1, .lambda [0] (.hole 2)]⟩
  , ⟨"catchIf", [], [0, 0, 1],
      call "Effect.catchIf" [.hole 1, .lambda [0] (.hole 0), .lambda [0] (.hole 2), .ident "undefined"]⟩
  , ⟨"selectTag", [], [0, 0, 1, 1],
      call "caseTag" [.hole 0, .strHole 1, .lambda [0] (.hole 2), .lambda [0] (.hole 3)]⟩ ]

/-! ## The printer: ONE generic layer function, folded -/

def fixedHolds {R : Type} (fixed : List (Nat × Term)) (args : List (ArgF R)) : Bool :=
  fixed.all fun (i, t) => match args[i]? with
    | some (.term t') => t' == t
    | _ => false

def printArg (n : Nat) (depth : Nat) : ArgF (Nat → Option Expr) → Option Arg
  | .child r => (r (n + depth)).map Arg.expr
  | .term t => some (.expr (printTerm t))
  | .str s => some (.str s)

def printArgs (n : Nat) : List Nat → List (ArgF (Nat → Option Expr)) → Nat → Option Subst
  | d :: ds, a :: as, i => do
    let x ← printArg n d a
    let rest ← printArgs n ds as (i + 1)
    some ((i, x) :: rest)
  | _, _, _ => some []

/-- The whole printer, per layer: choose the row, print the arguments by sort at their depths,
instantiate the skeleton. -/
def printLayer (ctor : String) (args : List (ArgF (Nat → Option Expr))) (n : Nat) : Option Expr := do
  let row ← table.find? fun r => r.ctor == ctor && fixedHolds r.fixed args
  let σ ← printArgs n row.depth args 0
  inst n σ row.tpl

def printT (n : Nat) (e : Eff) : Option Expr := cata printLayer e n

/-! ## The reader: one generic step, iterated -/

/-- One step: the first row whose skeleton matches, and its holes read by sort. A child comes
back as a seed (its depth and its expression). -/
def readArg (n : Nat) (row : Row) (σ : Subst) (i : Nat) (s : Sort') : Option (ArgF (Nat × Expr)) :=
  match row.fixed.find? (·.1 == i) with
  | some (_, t) => some (.term t)
  | none => match s, lookup σ i with
    | .child, some (.expr x) => some (.child (n + row.depth.getD i 0, x))
    | .term, some (.expr x) => (readTerm x).map .term
    | .str, some (.str v) => some (.str v)
    | _, _ => none

def readArgs (n : Nat) (row : Row) (σ : Subst) : List Sort' → Nat → Option (List (ArgF (Nat × Expr)))
  | [], _ => some []
  | s :: ss, i => do
    let a ← readArg n row σ i s
    let rest ← readArgs n row σ ss (i + 1)
    some (a :: rest)

def readLayer (n : Nat) (x : Expr) : Option (String × List (ArgF (Nat × Expr))) :=
  table.findSome? fun row => do
    let σ ← matchT n row.tpl x
    let args ← readArgs n row σ (sorts row.ctor) 0
    some (row.ctor, args)

/-- The unfold, on fuel (the probe's stand-in for recursion on the expression's size). -/
def readT : Nat → Nat → Expr → Option Eff
  | 0, _, _ => none
  | fuel + 1, n, x => do
    let (ctor, seeds) ← readLayer n x
    let args ← seeds.mapM fun
      | .child (d, y) => (readT fuel d y).map ArgF.child
      | .term t => some (.term t)
      | .str s => some (.str s)
    build ctor args

/-! ## It round-trips, classifier and shared head included -/

def ok (e : Eff) : Bool :=
  match printT 0 e with
  | some x => readT 64 0 x == some e
  | none => false

def v : Eff := .succeed (.num 7)

#guard ok v
#guard ok (.bind v (.bind v v))
#guard ok (.suspend (.selectBool (.lit true) v (.suspend v)))
#guard ok (.catchIf (.lit true) v v)          -- prints as `Effect.catch`, reads back with the fixed test
#guard ok (.catchIf (.lit false) v v)         -- prints as `Effect.catchIf`
#guard ok (.selectTag (.num 1) "cons" (.bind v v) v)
#guard ok (.bind (.selectTag (.num 1) "nil" v v) (.catchIf (.lit true) (.suspend v) v))

-- the binder is named from the depth the binder table gives the argument
#guard printT 2 (.bind v v) ==
  some (.call (.ident "Effect.flatMap")
    [.call (.ident "Effect.succeed") [.int 7], .lambda ["a2"] (.call (.ident "Effect.succeed") [.int 7])])

-- red control: the general row's image with the fixed test is NOT what the printer emits, and the
-- reader gives the program back, which prints as the other row (exactness has a domain)
#guard readT 8 0 (.call (.ident "Effect.catchIf")
    [ .call (.ident "Effect.succeed") [.int 7], .lambda ["a0"] (.bool true)
    , .lambda ["a0"] (.call (.ident "Effect.succeed") [.int 7]), .ident "undefined" ])
  == some (.catchIf (.lit true) v v)

end TableProbe
