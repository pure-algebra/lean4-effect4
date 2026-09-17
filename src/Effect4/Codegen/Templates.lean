import Effect4.Codegen.Template
import Effect4.Codegen.Print
import Effect4.Program.LayerView

/-!
# Codegen.Templates — the table of printed clauses, and the printer as its fold (R4.2, R4.3)

One row per (constructor, classifier). A row is first-order data: the family and constructor
name, the classifier (patterns on arguments the row fixes), the depth each argument is printed
under (the binder table's column), and the skeleton. **Hole `i` is the constructor's argument
`i`**, so a row carries no separate hole map.

The printer has no arm per constructor. `tableLayer` is ONE generic layer function: choose the
first row for the constructor whose classifier holds, print each argument by its sort at its
depth, instantiate the skeleton. `EffAlgebra.ofLayer` (generated from the constructor
declarations) makes it an algebra, and the generated fold `cata_eff` does the recursion.

What is not a skeleton stays a hand field of the algebra, overriding the table's: the row call of
`perform` (its inverse is the signature's `spell`), `gen` with its statements (a second table over
`TypeScript.Stmt` when it is the largest thing left), and the two spines.

This module stands BESIDE `Codegen/Print.lean` until the agreement is a theorem: the guard
`printT = print` on every constructor and on the corpus is `Test/Codegen/TemplatesContract.lean`.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Templates

open TypeScript
open Effect4 (ServiceKey)
open Effect4.Program
open Effect4.Codegen.Template

/-! ## Rows -/

/-- A classifier's pattern on one argument. A pattern that determines the argument lets a reader
supply it; the others (`decisionTag`, `optTermSome`, `optTySome`, `daemon`) say which row an
argument selects while a hole still carries its content. -/
inductive ArgPat where
  | term (t : Term)
  | bool (b : Bool)
  | mode (m : Effect4.Supervision.ObserverMode)
  | decisionBool
  | decisionOption
  | decisionTag
  | optTermNone
  | optTermSome
  | optTyNone
  | optTySome
  | daemon (b : Bool)
deriving DecidableEq

/-- The depth an argument is printed at: under `k` more binders than the node, or closed (a
layer's body prints at environment length `0`). -/
inductive Depth where
  | rel (k : Nat)
  | closed
deriving DecidableEq, Repr

/-- What a row prints: a skeleton, or the refusal of an action with no public export. -/
inductive RowOut where
  | tpl (t : Tpl)
  | refuse (name : String)

structure Row where
  fam : EffFam
  ctor : String
  /-- The classifier: argument index and the pattern it must satisfy. -/
  fixed : List (Nat × ArgPat) := []
  /-- Per argument, in declaration order, as the scope algebra gives it (`Program/Scoped.lean`).
  The printer reads a child's depth only (a term prints its variables by position); the reader
  reads a term at its depth too, because a binder is in scope only below it. -/
  depth : List Depth
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
(`withFiber` prints as its action, a layer reference as its name), close their family. -/

private def r0 : Depth := .rel 0
private def r1 : Depth := .rel 1

def effRows : List Row :=
  [ ⟨.eff, "succeed", [], [r0], .tpl (call "Effect.succeed" [h 0])⟩
  , ⟨.eff, "fail", [], [r0], .tpl (call "Effect.fail" [h 0])⟩
  , ⟨.eff, "failCause", [], [r0], .tpl (call "Effect.failCause" [h 0])⟩
  , ⟨.eff, "sync", [], [r0], .tpl (call "Effect.sync" [.arrow (h 0)])⟩
  , ⟨.eff, "bind", [], [r0, r1], .tpl (call "Effect.flatMap" [h 0, lam (h 1)])⟩
  , ⟨.eff, "catchCause", [], [r0, r1], .tpl (call "Effect.catchCause" [h 0, lam (h 1)])⟩
  , ⟨.eff, "catchIf", [(0, .term (.lit (.bool true)))], [r0, r0, r1],
      .tpl (call "Effect.catch" [h 1, lam (h 2)])⟩
  , ⟨.eff, "catchIf", [], [r1, r0, r1],
      .tpl (call "Effect.catchIf" [h 1, lam (h 0), lam (h 2), .ident "undefined"])⟩
  , ⟨.eff, "matchCause", [], [r0, r1, r1],
      .tpl (call "Effect.matchCauseEffect"
        [h 0, .object (fieldsOf [("onFailure", lam (h 2)), ("onSuccess", lam (h 1))])])⟩
  , ⟨.eff, "onExit", [], [r0, r1], .tpl (call "Effect.onExit" [h 0, lam (h 1)])⟩
  , ⟨.eff, "exit", [], [r0], .tpl (call "Effect.exit" [h 0])⟩
  , ⟨.eff, "uninterruptible", [], [r0], .tpl (call "Effect.uninterruptible" [h 0])⟩
  , ⟨.eff, "interruptible", [], [r0], .tpl (call "Effect.interruptible" [h 0])⟩
  , ⟨.eff, "select", [(1, .decisionBool)], [r0, r0, r0, r0],
      .tpl (call "Effect.suspend" [.arrow (.cond (h 0) (h 2) (h 3))])⟩
  , ⟨.eff, "select", [(1, .decisionOption)], [r0, r0, r0, r1],
      .tpl (call "optionCase" [h 0, .arrow (h 2), lam (h 3)])⟩
  , ⟨.eff, "select", [(1, .decisionTag)], [r0, r0, r1, r1],
      .tpl (call "caseTag" [h 0, .strHole 1, lam (h 2), lam (h 3)])⟩
  , ⟨.eff, "iterate", [(0, .optTyNone)], [r0, r0, r1, .rel 2, r1, r1], .tpl (iterateTpl none)⟩
  , ⟨.eff, "iterate", [(0, .optTySome)], [r0, r0, r1, .rel 2, r1, r1], .tpl (iterateTpl (some 0))⟩
  , ⟨.eff, "suspend", [], [r0], .tpl (call "Effect.suspend" [.arrow (h 0)])⟩
  , ⟨.eff, "yieldNow", [], [r0], .tpl (call "Effect.yieldNowWith" [.intHole 0])⟩
  , ⟨.eff, "awaitFiber", [(1, .mode .joinEffect)], [r0, r0], .tpl (call "Fiber.join" [h 0])⟩
  , ⟨.eff, "awaitFiber", [(1, .mode .awaitValue)], [r0, r0], .tpl (call "Fiber.await" [h 0])⟩
  , ⟨.eff, "scoped", [], [r0], .tpl (call "Effect.scoped" [h 0])⟩
  , ⟨.eff, "acquireRelease", [], [r0, .rel 2],
      .tpl (call "Effect.acquireRelease" [h 0, .lambda [0, 1] (h 1)])⟩
  , ⟨.eff, "provideLayer", [(1, .bool true)], [r0, r0, r0],
      .tpl (call "Effect.provide" [h 2, h 0, .object (fieldsOf [("local", .bool true)])])⟩
  , ⟨.eff, "provideLayer", [(1, .bool false)], [r0, r0, r0],
      .tpl (call "Effect.provide" [h 2, h 0])⟩
  , ⟨.eff, "service", [], [r0], .tpl (call "Effect.service" [h 0])⟩
  , ⟨.eff, "provideService", [], [r0, r0, r0],
      .tpl (call "Effect.provideService" [h 2, h 0, h 1])⟩
  , ⟨.eff, "withFiber", [], [r0], .tpl (h 0)⟩ ]

def actionRows : List Row :=
  [ ⟨.action, "fork", [(1, .daemon true)], [r0, r0], .tpl (call "Effect.forkDetach" [h 0, h 1])⟩
  , ⟨.action, "fork", [(1, .daemon false)], [r0, r0], .tpl (call "Effect.forkChild" [h 0, h 1])⟩
  , ⟨.action, "forkIn", [], [r0, r0, r0], .tpl (call "Effect.forkIn" [h 0, h 2, h 1])⟩
  , ⟨.action, "forkScoped", [], [r0, r0], .tpl (call "Effect.forkScoped" [h 0, h 1])⟩
  , ⟨.action, "runIn", [], [r0, r0],
      .tpl (call "Effect.withFiber"
        [ .arrowBlock []
            (stmtsOf [.exprStmt (call "Fiber.runIn" [h 0, h 1]), .ret (.ident "Effect.void")]) ])⟩
  , ⟨.action, "interrupt", [], [r0], .tpl (call "Fiber.interrupt" [h 0])⟩
  , ⟨.action, "interruptScoped", [], [r0], .refuse "interruptScoped"⟩
  , ⟨.action, "interruptAll", [(1, .optTermNone)], [r0, r0], .tpl (call "Fiber.interruptAll" [h 0])⟩
  , ⟨.action, "interruptAll", [(1, .optTermSome)], [r0, r0],
      .tpl (call "Fiber.interruptAllAs" [h 0, h 1])⟩
  , ⟨.action, "awaitAll", [], [r0], .tpl (call "Fiber.awaitAll" [h 0])⟩
  , ⟨.action, "awaitAllFailFast", [], [r0], .refuse "awaitAllFailFast"⟩
  , ⟨.action, "snapshotChildren", [], [], .refuse "snapshotChildren"⟩
  , ⟨.action, "awaitNewChildren", [], [r0], .refuse "awaitNewChildren"⟩
  , ⟨.action, "raceAll", [], [r0], .tpl (call "Effect.raceAll" [.arrHole 0])⟩
  , ⟨.action, "setContext", [], [r0], .refuse "setContext"⟩
  , ⟨.action, "getContext", [], [], .tpl (call "Effect.context" [])⟩
  , ⟨.action, "getId", [], [], .tpl (.ident "Effect.fiberId")⟩
  , ⟨.action, "closeScope", [], [r0, r0], .tpl (call "Scope.close" [h 0, h 1])⟩ ]

def layerRows : List Row :=
  [ ⟨.layer, "succeed", [], [r0, r0], .tpl (call "Layer.succeed" [h 0, h 1])⟩
  , ⟨.layer, "effect", [], [r0, .closed], .tpl (call "Layer.effect" [h 0, h 1])⟩
  , ⟨.layer, "effectDiscard", [], [.closed], .tpl (call "Layer.effectDiscard" [h 0])⟩
  , ⟨.layer, "provide", [], [r0, r0],
      .tpl (.method (h 0) "pipe" (tpls [call "Layer.provide" [h 1]]))⟩
  , ⟨.layer, "provideMerge", [], [r0, r0],
      .tpl (.method (h 0) "pipe" (tpls [call "Layer.provideMerge" [h 1]]))⟩
  , ⟨.layer, "merge", [], [r0, r0], .tpl (call "Layer.merge" [h 0, h 1])⟩
  , ⟨.layer, "fresh", [], [r0], .tpl (call "Layer.fresh" [h 0])⟩
  , ⟨.layer, "orDie", [], [r0], .tpl (call "Layer.orDie" [h 0])⟩
  , ⟨.layer, "mergeAll", [], [r0], .tpl (.callSpread (.ident "Layer.mergeAll") 0)⟩
  , ⟨.layer, "ref", [], [r0], .tpl (h 0)⟩ ]

def table : List Row := effRows ++ actionRows ++ layerRows

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

/-- Whether an argument satisfies a pattern. Patterns look at leaf arguments only, so this holds
at any carrier: the printer asks it of folded children, the reader of the arguments it read. -/
def ArgPat.holds {R : EffFam → Type} : ArgPat → ArgF Op R → Bool
  | .term t, .term t' => t' == t
  | .bool b, .bool b' => b' == b
  | .mode m, .mode m' => decide (m' = m)
  | .decisionBool, .decision .bool => true
  | .decisionOption, .decision .option => true
  | .decisionTag, .decision (.tag _) => true
  | .optTermNone, .optTerm none => true
  | .optTermSome, .optTerm (some _) => true
  | .optTyNone, .optTy none => true
  | .optTySome, .optTy (some _) => true
  | .daemon b, .forkOptions o => o.daemon == b
  | _, _ => false

/-- The argument a pattern determines, when it determines one: what a reader supplies for an
argument the skeleton does not carry. The other patterns choose the row while a hole still
carries the content, and a reader checks them against what it read (`Row.selects`). -/
def ArgPat.supplies {R : EffFam → Type} : ArgPat → Option (ArgF Op R)
  | .term t => some (.term t)
  | .bool b => some (.bool b)
  | .mode m => some (.mode m)
  | .decisionBool => some (.decision .bool)
  | .decisionOption => some (.decision .option)
  | .optTermNone => some (.optTerm none)
  | .optTyNone => some (.optTy none)
  | .decisionTag | .optTermSome | .optTySome | .daemon _ => none

def Row.selects {R : EffFam → Type} (row : Row) (fam : EffFam) (ctor : String)
    (args : List (ArgF Op R)) : Bool :=
  row.fam == fam && row.ctor == ctor &&
    row.fixed.all fun (i, p) => match args[i]? with
      | some a => p.holds a
      | none => false

/-- The environment length an argument is printed at. -/
def Depth.at (n : Nat) : Depth → Nat
  | .rel k => n + k
  | .closed => 0

/-- One argument as what its hole captures, by sort; `none` for an argument that is only a
classifier. A child is its folded printer applied at the row's depth; a leaf goes through its own
printer (`Codegen/Print.lean`). -/
def printArg (sig : Signature Op) (n : Nat) (d : Depth) :
    ArgF Op Carrier → Except PrintRefusal (Option Arg)
  | .child .eff r | .child .action r | .child .layer r => do return some (.expr (← r (d.at n)))
  | .child .effs r | .child .layers r => do return some (.exprs (← r (d.at n)))
  | .child .stmts _ | .child .stmt _ => .ok none
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

def printArgs (sig : Signature Op) (n : Nat) :
    List Depth → List (ArgF Op Carrier) → Nat → Except PrintRefusal Subst
  | d :: ds, a :: as, i => do
    let x ← printArg sig n d a
    let rest ← printArgs sig n ds as (i + 1)
    match x with
    | some v => .ok ((i, v) :: rest)
    | none => .ok rest
  | _, _, _ => .ok []

/-- A table that has no row for a constructor, or a skeleton with a hole no argument fills, is a
defect of the table, not a refusal of the program. It is named so a guard can see it; the
agreement with `print` shows it does not occur. -/
def tableDefect (ctor : String) : PrintRefusal := .internalAction ("table:" ++ ctor)

/-- The whole printer of the three skeleton families, per layer. -/
def tableLayer (sig : Signature Op) :
    (fam : EffFam) → String → List (ArgF Op Carrier) → Carrier fam
  | .eff, ctor, args => fun n => rowPrint sig .eff ctor args n
  | .action, ctor, args => fun n => rowPrint sig .action ctor args n
  | .layer, ctor, args => fun n => rowPrint sig .layer ctor args n
  | .effs, ctor, _ => fun _ => .error (tableDefect ctor)
  | .layers, ctor, _ => fun _ => .error (tableDefect ctor)
  | .stmts, ctor, _ => fun _ => .error (tableDefect ctor)
  | .stmt, ctor, _ => fun _ => .error (tableDefect ctor)
where
  rowPrint (sig : Signature Op) (fam : EffFam) (ctor : String) (args : List (ArgF Op Carrier))
      (n : Nat) : Except PrintRefusal Expr :=
    match table.find? fun row => row.selects fam ctor args with
    | none => .error (tableDefect ctor)
    | some row => match row.out with
      | .refuse name => .error (.internalAction name)
      | .tpl t => do
        let σ ← printArgs sig n row.depth args 0
        match inst n σ t with
        | some e => .ok e
        | none => .error (tableDefect ctor)

/-- The algebra: the table's layer function, with the hand fields for what is not a skeleton. -/
def printAlg (sig : Signature Op) : EffAlgebra Op Carrier :=
  { EffAlgebra.ofLayer (tableLayer sig) with
    eff_perform := fun op request _ => printRow (sig.rowOf op) request
    eff_gen := fun body n => do
      let statements ← body n
      .ok (.call (.ident "Effect.gen") [.generator statements])
    stmt_bindYield := fun effect n => do return (.constYield (Var.name n) (← effect n), 1)
    stmt_yieldDiscard := fun effect n => do return (.yieldDiscard (← effect n), 0)
    stmt_ret := fun value _ => .ok (.ret (printTerm value), 0)
    stmt_ifElse := fun test thenB elseB n => do
      return (.ifElse (printTerm test) (← thenB n) (← elseB n), 0)
    stmt_whileTrue := fun body n => do return (.whileTrue none (← body n), 0)
    stmt_breakLoop := fun _ => .ok (.breakTo none, 0)
    stmts_nil := fun _ => .ok []
    stmts_cons := fun head tail n => do
      let (s, k) ← head n
      let rest ← tail (n + k)
      .ok (s :: rest)
    effs_nil := fun _ => .ok []
    effs_cons := fun head tail n => do return (← head n) :: (← tail n)
    layers_nil := fun _ => .ok []
    layers_cons := fun head tail n => do return (← head n) :: (← tail n) }

/-- The table-driven printer of a program. -/
def printT (sig : Signature Op) (n : Nat) (e : Eff Op) : Except PrintRefusal Expr :=
  cata_eff (printAlg sig) e n

/-- The table-driven printer of a layer (closed: it prints at no environment length). -/
def printLayerT (sig : Signature Op) (l : LayerTerm Op) : Except PrintRefusal Expr :=
  cata_layer (printAlg sig) l 0

end Effect4.Codegen.Templates
