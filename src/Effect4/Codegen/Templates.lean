import Effect4.Codegen.Template
import Effect4.Codegen.PrintLeaf
import Effect4.Program.LayerView

/-!
# Codegen.Templates — the table of printed clauses, and the printer as its fold (R4.2, R4.3)

One row per (constructor, classifier). A row is first-order data: the family and constructor
name, the classifier (patterns on arguments the row fixes), and the skeleton. **Hole `i` is the
constructor's argument `i`**, so a row carries no separate hole map; and a row states no depth,
because the skeleton shows its own binders (`Template.levelAt`): an argument is printed, and
read, under the binders its hole is under. A layer is closed, which is a fact of the family and
not of a row (`argDepth`).

The printer has no arm per constructor. `tableLayer` is ONE generic layer function: choose the
first row for the constructor whose classifier holds, print each argument by its sort at its
depth, instantiate the skeleton. `EffAlgebra.ofLayer` (generated from the constructor
declarations) makes it an algebra, and the generated fold `cata_eff` does the recursion.

Every constructor of the four row families has a row. One row is not a skeleton: the row call
of `perform` (`RowOut.rowCall`), a codec parametrised by the signature whose inverse is the
signature's `spell`. The three spines (programs, layers, and statements, which thread the
binders a statement declares) are list structure, not clauses; the layer function handles them
by their two constructors, so the printer's algebra is `EffAlgebra.ofLayer` of ONE function with
no field overridden.

`Codegen/Print.lean`'s `print` IS this fold (the hand printer, one clause per constructor, was
deleted once the two agreed on every constructor, classifier and the seeded corpus), and
`Codegen/Read.lean` reads through the same rows. A leaf goes through its own printer
(`Codegen/PrintLeaf.lean`).
-/

set_option autoImplicit false

namespace Effect4.Codegen.Templates

open TypeScript
open Effect4 (ServiceKey)
open Effect4.Program
open Effect4.Codegen.Template

/-! ## Rows -/

/-- A leaf value a classifier fixes. The argument is then no part of the image: the skeleton has
no hole for it, the printer chose the row by it, and a reader supplies it. -/
inductive Fixed where
  | term (t : Term)
  | bool (b : Bool)
  | mode (m : Effect4.Supervision.ObserverMode)
  | decision (d : Decision)
  | noTerm
  | noTy
deriving DecidableEq

/-- A classifier's pattern on one argument: it FIXES the argument (`is`), or it only chooses the
row while a hole still carries the content (the tag's string, the interruptor, the cursor's
annotation, the options object whose `daemon` flag the head spells). The split is in the type,
so what a reader supplies and what the printer tested cannot come apart
(`Fixed.holds_arg`). -/
inductive ArgPat where
  | is (v : Fixed)
  | decisionTag
  | someTerm
  | someTy
  | daemon (b : Bool)
deriving DecidableEq

/-- What a row prints: an expression skeleton, a statement skeleton (the rows of the statement
family), or the refusal of an action with no public export. -/
inductive RowOut where
  | tpl (t : Tpl)
  | stmt (t : StmtTpl)
  /-- The row call of `perform`: printed by the signature's row (`printRow`), read by its
  inverse. It is a codec with its own round trip, parametrised by the signature, and not a
  skeleton; the row says where in the reading order it stands. -/
  | rowCall
  | refuse (name : String)

/-- The binders in scope at argument `i` of a row, read off its skeleton. -/
def RowOut.levelAt : RowOut → Nat → Nat
  | .tpl t, i => Template.levelAt t i
  | .stmt t, i => t.levelAt i
  | .rowCall, _ | .refuse _, _ => 0

structure Row where
  fam : EffFam
  ctor : String
  /-- The classifier: argument index and the pattern it must satisfy. -/
  fixed : List (Nat × ArgPat) := []
  out : RowOut

/-! ## Skeleton shorthands -/

def tpls : List Tpl → Tpls
  | [] => .nil
  | t :: ts => .cons t (tpls ts)

def fieldsOf : List (String × Tpl) → Fields
  | [] => .nil
  | (k, v) :: rest => .cons k v (fieldsOf rest)

def stmtsOf : List StmtTpl → StmtTpls
  | [] => .nil
  | s :: ss => .cons s (stmtsOf ss)

/-- `head(args…)`. -/
def call (head : String) (args : List Tpl) : Tpl := .call (.ident head) (tpls args)

/-- `(a<n>) => body`: the one binder a clause introduces. -/
def lam (body : Tpl) : Tpl := .lambda [0] body

def h (i : Nat) : Tpl := .hole i

/-- The head of a generator. -/
def genHead : String := "Effect.gen"

/-- The loop image (`reduce`'s shape at the pin, `internal/effect.ts:4450-4470`): the cursor
declared at `a<n>`, with its annotation when the row has one (DI-91), the loop, and the loop
mapped to the result over the last cursor. Arguments: 0 the annotation, 1 the initial value,
2 the test, 3 the step, 4 the result, 5 the body. -/
def iterateTpl (ann : Option Nat) : Tpl :=
  call "Effect.suspend"
    [ .arrowBlock []
        (stmtsOf
          [ .letInit 0 (h 1) ann
          , .ret (call "Effect.map"
              [ call "Effect.whileLoop"
                  [ .object (fieldsOf
                      [ ("while", .arrow (h 2))
                      , ("body", .arrow (h 5))
                      , ("step", .arrowBlock [1] (stmtsOf [.assign 0 (h 3)])) ]) ]
              , .arrow (h 4) ]) ]) ]

/-! ## The table

Order is read by the READER only (the printer chooses by constructor and classifier, which never
overlap). First match wins, so where skeletons overlap the more specific comes first: within the
`Effect.suspend` group the conditional and the two loop images come before the plain suspension
(whose body hole would take any of them), and the two transparent rows, a bare hole each
(`withFiber` prints as its action, a layer reference as its name), close their family. The row
call of `perform` is the last program row: a tree is a row call when it is nothing else. -/

def effRows : List Row :=
  [ ⟨.eff, "succeed", [], .tpl (call "Effect.succeed" [h 0])⟩
  , ⟨.eff, "fail", [], .tpl (call "Effect.fail" [h 0])⟩
  , ⟨.eff, "failCause", [], .tpl (call "Effect.failCause" [h 0])⟩
  , ⟨.eff, "sync", [], .tpl (call "Effect.sync" [.arrow (h 0)])⟩
  , ⟨.eff, "bind", [], .tpl (call "Effect.flatMap" [h 0, lam (h 1)])⟩
  , ⟨.eff, "catchCause", [], .tpl (call "Effect.catchCause" [h 0, lam (h 1)])⟩
  , ⟨.eff, "catchIf", [(0, .is (.term (.lit (.bool true))))],
      .tpl (call "Effect.catch" [h 1, lam (h 2)])⟩
  , ⟨.eff, "catchIf", [],
      .tpl (call "Effect.catchIf" [h 1, lam (h 0), lam (h 2), .ident "undefined"])⟩
  , ⟨.eff, "matchCause", [],
      .tpl (call "Effect.matchCauseEffect"
        [h 0, .object (fieldsOf [("onFailure", lam (h 2)), ("onSuccess", lam (h 1))])])⟩
  , ⟨.eff, "onExit", [], .tpl (call "Effect.onExit" [h 0, lam (h 1)])⟩
  , ⟨.eff, "exit", [], .tpl (call "Effect.exit" [h 0])⟩
  , ⟨.eff, "uninterruptible", [], .tpl (call "Effect.uninterruptible" [h 0])⟩
  , ⟨.eff, "interruptible", [], .tpl (call "Effect.interruptible" [h 0])⟩
  , ⟨.eff, "select", [(1, .is (.decision .bool))],
      .tpl (call "Effect.suspend" [.arrow (.cond (h 0) (h 2) (h 3))])⟩
  , ⟨.eff, "select", [(1, .is (.decision .option))],
      .tpl (call "optionCase" [h 0, .arrow (h 2), lam (h 3)])⟩
  , ⟨.eff, "select", [(1, .decisionTag)],
      .tpl (call "caseTag" [h 0, .strHole 1, lam (h 2), lam (h 3)])⟩
  , ⟨.eff, "iterate", [(0, .is .noTy)], .tpl (iterateTpl none)⟩
  , ⟨.eff, "iterate", [(0, .someTy)], .tpl (iterateTpl (some 0))⟩
  , ⟨.eff, "suspend", [], .tpl (call "Effect.suspend" [.arrow (h 0)])⟩
  , ⟨.eff, "yieldNow", [], .tpl (call "Effect.yieldNowWith" [.intHole 0])⟩
  , ⟨.eff, "awaitFiber", [(1, .is (.mode .joinEffect))], .tpl (call "Fiber.join" [h 0])⟩
  , ⟨.eff, "awaitFiber", [(1, .is (.mode .awaitValue))], .tpl (call "Fiber.await" [h 0])⟩
  , ⟨.eff, "scoped", [], .tpl (call "Effect.scoped" [h 0])⟩
  , ⟨.eff, "acquireRelease", [],
      .tpl (call "Effect.acquireRelease" [h 0, .lambda [0, 1] (h 1)])⟩
  , ⟨.eff, "provideLayer", [(1, .is (.bool true))],
      .tpl (call "Effect.provide" [h 2, h 0, .object (fieldsOf [("local", .bool true)])])⟩
  , ⟨.eff, "provideLayer", [(1, .is (.bool false))],
      .tpl (call "Effect.provide" [h 2, h 0])⟩
  , ⟨.eff, "service", [], .tpl (call "Effect.service" [h 0])⟩
  , ⟨.eff, "provideService", [],
      .tpl (call "Effect.provideService" [h 2, h 0, h 1])⟩
  , ⟨.eff, "gen", [], .tpl (call genHead [.generator (.hole 0)])⟩
  , ⟨.eff, "withFiber", [], .tpl (h 0)⟩
  , ⟨.eff, "perform", [], .rowCall⟩ ]

def actionRows : List Row :=
  [ ⟨.action, "fork", [(1, .daemon true)], .tpl (call "Effect.forkDetach" [h 0, h 1])⟩
  , ⟨.action, "fork", [(1, .daemon false)], .tpl (call "Effect.forkChild" [h 0, h 1])⟩
  , ⟨.action, "forkIn", [], .tpl (call "Effect.forkIn" [h 0, h 2, h 1])⟩
  , ⟨.action, "forkScoped", [], .tpl (call "Effect.forkScoped" [h 0, h 1])⟩
  , ⟨.action, "runIn", [],
      .tpl (call "Effect.withFiber"
        [ .arrowBlock []
            (stmtsOf [.exprStmt (call "Fiber.runIn" [h 0, h 1]), .ret (.ident "Effect.void")]) ])⟩
  , ⟨.action, "interrupt", [], .tpl (call "Fiber.interrupt" [h 0])⟩
  , ⟨.action, "interruptScoped", [], .refuse "interruptScoped"⟩
  , ⟨.action, "interruptAll", [(1, .is .noTerm)], .tpl (call "Fiber.interruptAll" [h 0])⟩
  , ⟨.action, "interruptAll", [(1, .someTerm)],
      .tpl (call "Fiber.interruptAllAs" [h 0, h 1])⟩
  , ⟨.action, "awaitAll", [], .tpl (call "Fiber.awaitAll" [h 0])⟩
  , ⟨.action, "awaitAllFailFast", [], .refuse "awaitAllFailFast"⟩
  , ⟨.action, "snapshotChildren", [], .refuse "snapshotChildren"⟩
  , ⟨.action, "awaitNewChildren", [], .refuse "awaitNewChildren"⟩
  , ⟨.action, "raceAll", [], .tpl (call "Effect.raceAll" [.arrHole 0])⟩
  , ⟨.action, "setContext", [], .refuse "setContext"⟩
  , ⟨.action, "getContext", [], .tpl (call "Effect.context" [])⟩
  , ⟨.action, "getId", [], .tpl (.ident "Effect.fiberId")⟩
  , ⟨.action, "closeScope", [], .tpl (call "Scope.close" [h 0, h 1])⟩ ]

def layerRows : List Row :=
  [ ⟨.layer, "succeed", [], .tpl (call "Layer.succeed" [h 0, h 1])⟩
  , ⟨.layer, "effect", [], .tpl (call "Layer.effect" [h 0, h 1])⟩
  , ⟨.layer, "effectDiscard", [], .tpl (call "Layer.effectDiscard" [h 0])⟩
  , ⟨.layer, "provide", [],
      .tpl (.method (h 0) "pipe" (tpls [call "Layer.provide" [h 1]]))⟩
  , ⟨.layer, "provideMerge", [],
      .tpl (.method (h 0) "pipe" (tpls [call "Layer.provideMerge" [h 1]]))⟩
  , ⟨.layer, "merge", [], .tpl (call "Layer.merge" [h 0, h 1])⟩
  , ⟨.layer, "fresh", [], .tpl (call "Layer.fresh" [h 0])⟩
  , ⟨.layer, "orDie", [], .tpl (call "Layer.orDie" [h 0])⟩
  , ⟨.layer, "mergeAll", [], .tpl (.callSpread (.ident "Layer.mergeAll") 0)⟩
  , ⟨.layer, "ref", [], .tpl (h 0)⟩ ]

/-- The statements of a generator. A yielded `const` declares its slot for the statements after
it (`StmtTpl.declares`); the statement list threads that, as the scope rules do. -/
def stmtRows : List Row :=
  [ ⟨.stmt, "bindYield", [], .stmt (.constYield 0 (h 0))⟩
  , ⟨.stmt, "yieldDiscard", [], .stmt (.yieldDiscard (h 0))⟩
  , ⟨.stmt, "ret", [], .stmt (.ret (h 0))⟩
  , ⟨.stmt, "ifElse", [], .stmt (.ifElse (h 0) (.hole 1) (.hole 2))⟩
  , ⟨.stmt, "whileTrue", [], .stmt (.whileTrue (.hole 0))⟩
  , ⟨.stmt, "breakLoop", [], .stmt .breakTo⟩ ]

def table : List Row := effRows ++ actionRows ++ layerRows ++ stmtRows

/-! ## The printer: one generic layer function -/

/-- What a family prints to. A statement comes with the number of binders it leaves in scope
for the rest of its list (`bindYield` leaves one). -/
abbrev Out : EffFam → Type
  | .eff | .action | .layer => Expr
  | .effs | .layers => List Expr
  | .stmts => List Stmt
  | .stmt => Stmt × Nat

/-- The carrier of the fold: the printed form at an environment length. -/
abbrev Carrier (fam : EffFam) : Type := Nat → Except PrintRefusal (Out fam)

variable {Op : Type}

/-- The argument a fixed value is. -/
def Fixed.arg {R : EffFam → Type} : Fixed → ArgF Op R
  | .term t => .term t
  | .bool b => .bool b
  | .mode m => .mode m
  | .decision d => .decision d
  | .noTerm => .optTerm none
  | .noTy => .optTy none

/-- Whether an argument is the fixed value. Fixed values are leaves, so this holds at any
carrier: the printer asks it of folded children, the reader of the arguments it read. -/
def Fixed.holds {R : EffFam → Type} : Fixed → ArgF Op R → Bool
  | .term t, .term t' => decide (t' = t)
  | .bool b, .bool b' => decide (b' = b)
  | .mode m, .mode m' => decide (m' = m)
  | .decision d, .decision d' => decide (d' = d)
  | .noTerm, .optTerm none => true
  | .noTy, .optTy none => true
  | _, _ => false

/-- What a reader supplies, the printer would have tested true. -/
theorem Fixed.holds_arg {R : EffFam → Type} (v : Fixed) :
    v.holds (v.arg (Op := Op) (R := R)) = true := by
  cases v <;> first | rfl | exact decide_eq_true rfl

/-- Whether an argument satisfies a pattern. -/
def ArgPat.holds {R : EffFam → Type} : ArgPat → ArgF Op R → Bool
  | .is v, a => v.holds a
  | .decisionTag, .decision (.tag _) => true
  | .someTerm, .optTerm (some _) => true
  | .someTy, .optTy (some _) => true
  | .daemon b, .forkOptions o => decide (o.daemon = b)
  | _, _ => false

/-- The argument a pattern determines, when it determines one: what a reader supplies for an
argument the skeleton does not carry. -/
def ArgPat.supplies {R : EffFam → Type} : ArgPat → Option (ArgF Op R)
  | .is v => some v.arg
  | _ => none

theorem ArgPat.holds_of_supplies {R : EffFam → Type} {p : ArgPat} {a : ArgF Op R}
    (h : p.supplies = some a) : p.holds a = true := by
  cases p with
  | is v =>
    simp only [ArgPat.supplies, Option.some.injEq] at h
    subst h
    exact v.holds_arg
  | decisionTag => cases h
  | someTerm => cases h
  | someTy => cases h
  | daemon b => cases h

def Row.selects {R : EffFam → Type} (row : Row) (fam : EffFam) (ctor : String)
    (args : List (ArgF Op R)) : Bool :=
  row.fam == fam && row.ctor == ctor &&
    row.fixed.all fun (i, p) => match args[i]? with
      | some a => p.holds a
      | none => false

/-- The environment length an argument is printed and read at, from the binders its hole is
under. A layer is closed (its bodies are typed in the empty scope): every argument of a layer
row, and every argument of a layer family, is at `0` whatever is around it. That is a fact of
the family, so no caller has to arrange it. -/
def argDepth (fam : EffFam) (sort : ArgSort) (n level : Nat) : Nat :=
  match fam, sort with
  | .layer, _ | .layers, _ => 0
  | _, .child .layer | _, .child .layers => 0
  | _, _ => n + level

/-- The sort of an argument, without its value. -/
def argSortOf {R : EffFam → Type} : ArgF Op R → ArgSort
  | .child fam _ => .child fam
  | .term _ => .term | .cause _ => .cause | .op _ => .op | .nat _ => .nat | .mode _ => .mode
  | .bool _ => .bool | .key _ => .key | .decision _ => .decision | .optTy _ => .optTy
  | .forkOptions _ => .forkOptions | .optTerm _ => .optTerm | .lit _ => .lit | .path _ => .path

/-- One argument as what its hole captures, by sort; `none` for an argument that is only a
classifier. A child is its folded printer applied at the row's depth; a leaf goes through its own
printer (`Codegen/PrintLeaf.lean`). -/
def printArg (sig : Signature Op) (d : Nat) :
    ArgF Op Carrier → Except PrintRefusal (Option Arg)
  | .child .eff r | .child .action r | .child .layer r => do return some (.expr (← r d))
  | .child .effs r | .child .layers r => do return some (.exprs (← r d))
  | .child .stmts r => do return some (.stmts (← r d))
  | .child .stmt _ => .ok none
  | .term t => .ok (some (.expr (printTerm t)))
  | .optTerm (some t) => .ok (some (.expr (printTerm t)))
  | .optTerm none => .ok none
  | .cause c => .ok (some (.expr (printCause c)))
  | .lit l => .ok (some (.expr (printLit l)))
  | .key k => do return some (.expr (← printKey sig k))
  | .decision (.tag t) => .ok (some (.str t))
  | .decision _ => .ok none
  | .forkOptions o => .ok (some (.expr (printForkOptions o)))
  | .nat k => .ok (some (.int (Int.ofNat k)))
  | .path p => .ok (some (.expr (.ident (LayerTerm.refName p))))
  | .optTy (some ty) => match Effect4.Codegen.Types.ofTy ty with
    | some target => .ok (some (.type target))
    | none => .error (.typeSpelling ty.render)
  | .optTy none => .ok none
  | .mode _ | .bool _ | .op _ => .ok none

def printArgs (sig : Signature Op) (fam : EffFam) (n : Nat) (out : RowOut) :
    List (ArgF Op Carrier) → Nat → Except PrintRefusal Subst
  | a :: as, i => do
    let x ← printArg sig (argDepth fam (argSortOf a) n (out.levelAt i)) a
    let rest ← printArgs sig fam n out as (i + 1)
    match x with
    | some v => .ok ((i, v) :: rest)
    | none => .ok rest
  | [], _ => .ok []

/-- A table that has no row for a constructor, or a skeleton with a hole no argument fills, is a
defect of the table, not a refusal of the program. It is named so a guard can see it
(`Test/Codegen/TemplatesContract.lean` shows it does not occur). -/
def tableDefect (ctor : String) : PrintRefusal := .internalAction ("table:" ++ ctor)

/-- The whole printer, per layer: the row chosen by constructor and classifier, its arguments
printed by sort at the depth their holes are under, its skeleton instantiated. A statement
comes with the binders it declares for the statements after it, which the statement spine
threads. -/
def tableLayer (sig : Signature Op) :
    (fam : EffFam) → String → List (ArgF Op Carrier) → Carrier fam
  | .eff, ctor, args => fun n => rowPrint sig .eff ctor args n
  | .action, ctor, args => fun n => rowPrint sig .action ctor args n
  | .layer, ctor, args => fun n => rowPrint sig .layer ctor args n
  | .stmt, ctor, args => fun n =>
    match table.find? fun row => row.selects .stmt ctor args with
    | some ⟨_, _, _, .stmt t⟩ => do
      let σ ← printArgs sig .stmt n (.stmt t) args 0
      match instStmt n σ t with
      | some s => .ok (s, t.declares)
      | none => .error (tableDefect ctor)
    | _ => .error (tableDefect ctor)
  -- the three spines are list structure, not clauses: programs and layers item by item at one
  -- depth, statements threading the binders each one declares
  | .effs, "nil", [] => fun _ => .ok []
  | .effs, "cons", [.child .eff head, .child .effs tail] => fun n => do
    return (← head n) :: (← tail n)
  | .layers, "nil", [] => fun _ => .ok []
  | .layers, "cons", [.child .layer head, .child .layers tail] => fun n => do
    return (← head n) :: (← tail n)
  | .stmts, "nil", [] => fun _ => .ok []
  | .stmts, "cons", [.child .stmt head, .child .stmts tail] => fun n => do
    let (s, declared) ← head n
    return s :: (← tail (n + declared))
  | .effs, ctor, _ => fun _ => .error (tableDefect ctor)
  | .layers, ctor, _ => fun _ => .error (tableDefect ctor)
  | .stmts, ctor, _ => fun _ => .error (tableDefect ctor)
where
  rowPrint (sig : Signature Op) (fam : EffFam) (ctor : String) (args : List (ArgF Op Carrier))
      (n : Nat) : Except PrintRefusal Expr :=
    match table.find? fun row => row.selects fam ctor args with
    | none => .error (tableDefect ctor)
    | some row => match row.out with
      | .refuse name => .error (.internalAction name)
      | .stmt _ => .error (tableDefect ctor)
      | .rowCall => match args with
        | [.op op, .term request] => printRow (sig.rowOf op) request
        | _ => .error (tableDefect ctor)
      | .tpl t => do
        let σ ← printArgs sig fam n (.tpl t) args 0
        match inst n σ t with
        | some e => .ok e
        | none => .error (tableDefect ctor)

/-- The printer's algebra IS the table's layer function (`EffAlgebra.ofLayer`): there is no hand
field, so the generated coherence of the fold with `build` (`cata_build`) speaks of the whole
printer. -/
def printAlg (sig : Signature Op) : EffAlgebra Op Carrier :=
  EffAlgebra.ofLayer (tableLayer sig)

/-- The table-driven printer of a program. -/
def printT (sig : Signature Op) (n : Nat) (e : Eff Op) : Except PrintRefusal Expr :=
  cata_eff (printAlg sig) e n

/-- The table-driven printer of a layer (closed: it prints at no environment length). -/
def printLayerT (sig : Signature Op) (l : LayerTerm Op) : Except PrintRefusal Expr :=
  cata_layer (printAlg sig) l 0

end Effect4.Codegen.Templates
