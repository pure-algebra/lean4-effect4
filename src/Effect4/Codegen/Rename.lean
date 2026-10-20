import Effect4.Codegen.Templates
import Effect4.Codegen.TsFold
import Effect4.Program.Authoring

/-!
# Codegen.Rename — the reader's named normaliser: binders by lexical scope

The printer names the binder at environment position `i` `Var.name i`: `a0`, `a1`, … An author
names a binder as they like. `Rename.expr names x` renames every binder of `x` to the printer's
name for its level, and every use to the name of the binder it resolves to, nearest binder
first: the rule of the authoring scope reader (`Authoring.Names.resolve`,
`Program/Authoring.lean`), the one resolver of names. The reader reads the printer's text as it
stands and any other text after this renaming (`readEffAt`, `Codegen/Read.lean`). So
`read_print` keeps its statement, and `read_exact` holds under the renaming: a text the reader
accepts is the print of the program it read, or renames to that print.

The lexical scope is TypeScript's, with two differences:

* the clauses of the layer family close the lexical scope. The printer prints a layer at the
  empty environment (`Templates.argDepth`), so under a head of a layer clause (`closedHeads`)
  the renaming starts again from no binder, as the reader does (`readLayerAt`);
* a call's head, a constructed class and a reference applied to type arguments are names, never
  uses. A binder in that place is refused (`ReadRefusal.binder`): the printed fragment calls no
  binder.

A block's binder is in lexical scope over the whole block, as in TypeScript. A use before its
declaration means it, in its temporal dead zone, and is refused (`Binders.later`), as the
source binding analysis refuses it (`SourceBindings`).

A name that no binder declares stays as written, and the reader reads it or refuses it where it
stands (`unknownIdent`, with the path the reader gives). One unbound name is refused here: a name
of the printer's form whose position a binder holds, which the renamed binder would capture. A
declaration that repeats a name its block already declares is refused too
(`ReadRefusal.binder`), as TypeScript refuses it. A refusal here carries the steps down the
target syntax, prefixed by the one prefix rule (`Located.under`): the constructor of
`TypeScript.Expr` or `TypeScript.Stmt` and the child's position.

The renaming is a fold of the target syntax (`TypeScript.cata_expr`, `Codegen/TsFold.lean`).
Nothing here folds over a string: a name of the printer's form is read off its bytes
(`Var.index?`).

The reader's located failure (`ReadFailure`) is defined here, since the renaming is the reader's
first step on a text the printer did not write and refuses with it.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Template

open TypeScript

mutual
  /-- The heads of the calls a skeleton holds, outermost first. -/
  def Tpl.callHeads : Tpl → List String
    | .call (.ident h) args => h :: Tpls.callHeads args
    | .call h args => Tpl.callHeads h ++ Tpls.callHeads args
    | .callSpread (.ident h) _ => [h]
    | .callSpread h _ => Tpl.callHeads h
    | .generic h _ => Tpl.callHeads h
    | .arr items => Tpls.callHeads items
    | .object fields => Fields.callHeads fields
    | .arrow b => Tpl.callHeads b
    | .lambda _ b => Tpl.callHeads b
    | .cond t a b => Tpl.callHeads t ++ Tpl.callHeads a ++ Tpl.callHeads b
    | .method target _ args => Tpl.callHeads target ++ Tpls.callHeads args
    | .arrowBlock _ body => StmtTpls.callHeads body
    | .generator body => StmtTpls.callHeads body
    | .hole _ | .strHole _ | .intHole _ | .arrHole _ | .binderRef _ | .ident _ | .str _
    | .int _ | .bool _ => []
  def Tpls.callHeads : Tpls → List String
    | .nil => []
    | .cons h t => Tpl.callHeads h ++ Tpls.callHeads t
  def Fields.callHeads : Fields → List String
    | .nil => []
    | .cons _ v t => Tpl.callHeads v ++ Fields.callHeads t
  def StmtTpl.callHeads : StmtTpl → List String
    | .letInit _ v _ | .assign _ v | .ret v | .exprStmt v | .constYield _ v | .yieldDiscard v =>
      Tpl.callHeads v
    | .ifElse t a b => Tpl.callHeads t ++ StmtTpls.callHeads a ++ StmtTpls.callHeads b
    | .whileTrue body => StmtTpls.callHeads body
    | .breakTo => []
  def StmtTpls.callHeads : StmtTpls → List String
    | .nil | .hole _ => []
    | .cons h t => StmtTpl.callHeads h ++ StmtTpls.callHeads t
end

end Effect4.Codegen.Template

namespace Effect4.Program

/-- **The reader's located refusal** (`Data/Located.lean`). The site is the constructor and
argument index at each step from the root down to the node that refused, outermost first (a
list's items are its `cons` cells: argument `0` the item, `1` the rest). The reader's steps are
the program's constructors; the renaming's are the target syntax's (`Rename.expr`). A step above
is added by the one prefix rule, `Located.under`. The reason is the refusal, and what the nearest
row expected when a reserved head matched no row: the steps down that row's skeleton to where
the tree parts from it, and what the skeleton has there. The refusal itself stays flat, so
nothing that compares refusals moves. -/
abbrev ReadFailure := Located (List (String × Nat)) (ReadRefusal × Option (List String × String))

/-- A refusal at the node being read. -/
def ReadFailure.here (why : ReadRefusal) : ReadFailure := ⟨[], (why, none)⟩

/-- For a person: `bind.1 > succeed.0: unknownIdent a1`, and what was expected where. -/
def ReadFailure.render (f : ReadFailure) : String :=
  let at_ := " > ".intercalate (f.site.map fun (ctor, i) => ctor ++ "." ++ toString i)
  let why := reprStr f.reason.1
  let expected := match f.reason.2 with
    | some (steps, what) =>
      "; expected " ++ what ++ (if steps.isEmpty then "" else " at " ++ " > ".intercalate steps)
    | none => ""
  (if at_.isEmpty then "" else at_ ++ ": ") ++ why ++ expected

open Effect4.Data.NatDecimal (decodeBytes)

/-- The position a printer's name stands for: `a`, then the decimal spelling of a position, and
nothing else (`Var.name`). Read off the bytes, as `binderNamed` reads them. -/
def Var.index? (s : String) : Option Nat :=
  match s.toByteArray.data.toList with
  | 97 :: rest => if s = Var.name (decodeBytes rest) then some (decodeBytes rest) else none
  | _ => none

end Effect4.Program

namespace Effect4.Codegen.Rename

open Effect4.Program TypeScript

/-- The printer's scope at environment length `n`: its own names, `a0` … `a{n-1}`. -/
def mint (n : Nat) : List String := (List.range n).map Var.name

/-- The heads of the layer family's clauses. The printer prints every argument of a layer clause
at the empty environment (`Templates.argDepth`), so the renaming closes the scope under them. -/
def closedHeads : List String :=
  Templates.table.flatMap fun row =>
    if row.fam = .layer then
      match row.out with
      | .tpl t => t.callHeads
      | _ => []
    else []

/-- Whether a call's head closes the scope of its arguments. -/
def closes (head : Option String) : Bool := head.any closedHeads.contains

/-- What the renaming knows at a point of the text: the binders in lexical scope, and the names
an enclosing block declares later. -/
structure Binders where
  /-- The binders in lexical scope, in level order: level `i` is the `i`-th name. -/
  names : List String
  /-- The names an enclosing block declares at or after the statement that holds this point,
  each with the number of binders in scope at that statement. TypeScript scopes a block's
  binder over the whole block, so a use there before the declaration means it. -/
  later : List (String × Nat) := []

/-- Whether a use of `s` here means a binder that its block declares later, in its temporal dead
zone: no binder of `s` that the statement itself holds is nearer. -/
def Binders.early (b : Binders) (s : String) : Bool :=
  match b.later.foldl (fun acc (t, n) => if t = s then some n else acc) none with
  | none => false
  | some n => (Authoring.Names.resolve b.names s).all (· < n)

/-- A name where it is used: the printer's name of the binder it resolves to, nearest binder
first. A name that no binder declares stays as written. Two uses are refused: one before its
block's declaration of it, and an unbound name of the printer's form whose position a binder in
scope holds, which the renamed binder would capture. -/
def use (b : Binders) (s : String) : Except ReadFailure String :=
  if b.early s then .error (.here (.unknownIdent s)) else
  match Authoring.Names.resolve b.names s with
  | some i => .ok (Var.name i)
  | none =>
    if (Var.index? s).any (· < b.names.length) then .error (.here (.unknownIdent s)) else .ok s

/-- A name in a name's place stays as written. A binder there is refused, unless it is the
printer's own name for its level: a printed atom may carry one. -/
def head (b : Binders) (s : String) : Except ReadFailure String :=
  if b.early s then .error (.here (.binder s)) else
  match Authoring.Names.resolve b.names s with
  | some i => if Var.name i = s then .ok s else .error (.here (.binder s))
  | none => .ok s

/-- The first name a list repeats. -/
def firstRepeat : List String → Option String
  | [] => none
  | s :: rest => if rest.contains s then some s else firstRepeat rest

/-- The parameters as the printer names binders at levels `base`, `base + 1`, …: each keeps its
annotation. -/
def params (base : Nat) : List Parameter → List Parameter
  | [] => []
  | p :: ps => { p with name := Var.name base } :: params (base + 1) ps

/-- A declaration in a block whose declarations start at level `start`: a name the block already
declares is refused, as TypeScript refuses it. -/
def declare (names : List String) (start : Nat) (s : String) : Except ReadFailure Unit :=
  if (names.drop start).contains s then .error (.here (.binder s)) else .ok ()

/-- The renaming's carrier. An expression gives its own name when it is a bare identifier (the
head of a call is a name, and so are the heads that close the scope), and its renaming. A
statement gives the name it declares, and its renaming at the level its block starts at, with
the binders in scope after it. An object entry gives its renaming. -/
abbrev Carrier : ExprFam → Type
  | .expr => Option String × (Binders → Except ReadFailure Expr)
  | .stmt => Option String × (Binders → Nat → Except ReadFailure (Stmt × List String))
  | .objectentry => Binders → Except ReadFailure ObjectEntry

/-- The items of a list, located at their positions from `j` under `step`. -/
def items (step : String) (b : Binders) :
    Nat → List (Carrier .expr) → Except ReadFailure (List Expr)
  | _, [] => .ok []
  | j, x :: xs => do
    let y ← (x.2 b).mapError (Located.under [(step, j)])
    let ys ← items step b (j + 1) xs
    .ok (y :: ys)

/-- The fields of an object: each value renamed, its key as written. -/
def fields (step : String) (b : Binders) :
    Nat → List (String × Carrier .expr) → Except ReadFailure (List (String × Expr))
  | _, [] => .ok []
  | j, (key, x) :: xs => do
    let y ← (x.2 b).mapError (Located.under [(step, j)])
    let ys ← fields step b (j + 1) xs
    .ok ((key, y) :: ys)

/-- The entries of an object built from entries. -/
def entries (b : Binders) :
    Nat → List (Carrier .objectentry) → Except ReadFailure (List ObjectEntry)
  | _, [] => .ok []
  | j, x :: xs => do
    let y ← (x b).mapError (Located.under [("objectWith", j)])
    let ys ← entries b (j + 1) xs
    .ok (y :: ys)

/-- A block's statements, each among the binders the statements before it leave, the block's
declarations starting at level `start`. A statement sees the names that it and the statements
after it declare as later (`Binders.later`), beside those of the blocks around (`outer`). -/
def block (step : String) (start : Nat) (outer : List (String × Nat)) :
    List String → Nat → List (Carrier .stmt) → Except ReadFailure (List Stmt)
  | _, _, [] => .ok []
  | names, j, s :: ss => do
    let later := outer ++ ((s :: ss).filterMap (·.1)).map (·, names.length)
    let (s', after) ← (s.2 { names, later } start).mapError (Located.under [(step, j)])
    let ss' ← block step start outer after (j + 1) ss
    .ok (s' :: ss')

/-- A nested block: its declarations start at the binders in scope. -/
def nested (step : String) (b : Binders) (body : List (Carrier .stmt)) :
    Except ReadFailure (List Stmt) :=
  block step b.names.length b.later b.names 0 body

/-- The cases of a switch, each body a block of its own, located after the scrutinee. -/
def cases (b : Binders) :
    Nat → List (Nat × List (Carrier .stmt)) → Except ReadFailure (List (Nat × List Stmt))
  | _, [] => .ok []
  | j, (tag, body) :: rest => do
    let c ← (nested "case" b body).mapError (Located.under [("switch", j)])
    let cs ← cases b (j + 1) rest
    .ok ((tag, c) :: cs)

/-- A callee: a bare identifier is a name; any other callee is renamed. -/
def callee (step : String) (b : Binders) (fn : Carrier .expr) : Except ReadFailure Expr :=
  match fn.1 with
  | some s => ((head b s).mapError (Located.under [(step, 0)])).map .ident
  | none => (fn.2 b).mapError (Located.under [(step, 0)])

/-- A parameter list binds its names in order; one that names a binder twice is refused. -/
def bindParams (ps : List Parameter) : Except ReadFailure (List String) :=
  match firstRepeat (ps.map (·.name)) with
  | some s => .error (.here (.binder s))
  | none => .ok (ps.map (·.name))

/-- The binders inside a function: its parameters after those in scope. -/
def Binders.bind (b : Binders) (bound : List String) : Binders := { b with names := b.names ++ bound }

/-- The renaming, one constructor at a time. -/
def alg : ExprAlgebra Carrier where
  expr_ident s := (some s, fun b => (use b s).map .ident)
  expr_str v := (none, fun _ => .ok (.str v))
  expr_int v := (none, fun _ => .ok (.int v))
  expr_float64Bits v := (none, fun _ => .ok (.float64Bits v))
  expr_bool v := (none, fun _ => .ok (.bool v))
  expr_jsNull := (none, fun _ => .ok .jsNull)
  expr_call fn args := (none, fun b => do
    let h ← callee "call" b fn
    let as ← items "call" (if closes fn.1 then { names := [] } else b) 1 args
    .ok (.call h as))
  expr_object fs := (none, fun b => (fields "object" b 0 fs).map .object)
  expr_objectML fs := (none, fun b => (fields "objectML" b 0 fs).map .objectML)
  expr_objectQuoted fs := (none, fun b => (fields "objectQuoted" b 0 fs).map .objectQuoted)
  expr_objectQuotedML fs := (none, fun b =>
    (fields "objectQuotedML" b 0 fs).map .objectQuotedML)
  expr_objectFromEntries fs := (none, fun b =>
    (fields "objectFromEntries" b 0 fs).map .objectFromEntries)
  expr_arr xs := (none, fun b => (items "arr" b 0 xs).map .arr)
  expr_arrow ty body := (none, fun b =>
    ((body.2 b).mapError (Located.under [("arrow", 0)])).map (.arrow ty))
  expr_generic fn types := (none, fun b =>
    (callee "generic" b fn).map (.generic · types))
  expr_lambda ps body ty := (none, fun b => do
    let bound ← bindParams ps
    let r ← (body.2 (b.bind bound)).mapError (Located.under [("lambda", 0)])
    .ok (.lambda (params b.names.length ps) r ty))
  expr_method target name args := (none, fun b => do
    let t ← (target.2 b).mapError (Located.under [("method", 0)])
    let as ← items "method" b 1 args
    .ok (.method t name as))
  expr_member target name := (none, fun b =>
    ((target.2 b).mapError (Located.under [("member", 0)])).map (.member · name))
  expr_generator body := (none, fun b => (nested "generator" b body).map .generator)
  expr_cond t x y := (none, fun b => do
    let t' ← (t.2 b).mapError (Located.under [("cond", 0)])
    let x' ← (x.2 b).mapError (Located.under [("cond", 1)])
    let y' ← (y.2 b).mapError (Located.under [("cond", 2)])
    .ok (.cond t' x' y'))
  expr_arrowBlock ps body ty := (none, fun b => do
    let bound ← bindParams ps
    let r ← block "arrowBlock" b.names.length b.later (b.names ++ bound) 0 body
    .ok (.arrowBlock (params b.names.length ps) r ty))
  expr_index target key := (none, fun b => do
    let t ← (target.2 b).mapError (Located.under [("index", 0)])
    let k ← (key.2 b).mapError (Located.under [("index", 1)])
    .ok (.index t k))
  expr_new c args := (none, fun b => do
    let c' ← callee "new" b c
    let as ← items "new" b 1 args
    .ok (.new c' as))
  expr_objectWith keys es := (none, fun b => (entries b 0 es).map (.objectWith keys))
  stmt_constYield name value ty := (some name, fun b start => do
    declare b.names start name
    let v ← (value.2 b).mapError (Located.under [("constYield", 0)])
    .ok (.constYield (Var.name b.names.length) v ty, b.names ++ [name]))
  stmt_ret value := (none, fun b _ => do
    let v ← (value.2 b).mapError (Located.under [("ret", 0)])
    .ok (.ret v, b.names))
  stmt_yieldDiscard value := (none, fun b _ => do
    let v ← (value.2 b).mapError (Located.under [("yieldDiscard", 0)])
    .ok (.yieldDiscard v, b.names))
  stmt_letDefinite name ty := (some name, fun b start => do
    declare b.names start name
    .ok (.letDefinite (Var.name b.names.length) ty, b.names ++ [name]))
  stmt_letInit name value ty := (some name, fun b start => do
    declare b.names start name
    let v ← (value.2 b).mapError (Located.under [("letInit", 0)])
    .ok (.letInit (Var.name b.names.length) v ty, b.names ++ [name]))
  stmt_assign name value := (none, fun b _ => do
    let target ← use b name
    let v ← (value.2 b).mapError (Located.under [("assign", 0)])
    .ok (.assign target v, b.names))
  stmt_whileTrue label body := (none, fun b _ => do
    let r ← nested "whileTrue" b body
    .ok (.whileTrue label r, b.names))
  stmt_switch scrutinee cs := (none, fun b _ => do
    let s ← (scrutinee.2 b).mapError (Located.under [("switch", 0)])
    let c ← cases b 1 cs
    .ok (.switch s c, b.names))
  stmt_ifElse test yes no := (none, fun b _ => do
    let t ← (test.2 b).mapError (Located.under [("ifElse", 0)])
    let y ← nested "then" b yes
    let n ← nested "else" b no
    .ok (.ifElse t y n, b.names))
  stmt_labelled label body := (none, fun b _ => do
    let r ← nested "labelled" b body
    .ok (.labelled label r, b.names))
  stmt_scopedGen name body onExit := (some name, fun b start => do
    declare b.names start name
    let r ← nested "scopedGen" b body
    let e ← (onExit.2 b).mapError (Located.under [("onExit", 0)])
    .ok (.scopedGen (Var.name b.names.length) r e, b.names ++ [name]))
  stmt_scopedGenMasked name body onExit := (some name, fun b start => do
    declare b.names start name
    let r ← nested "scopedGenMasked" b body
    let e ← (onExit.2 b).mapError (Located.under [("onExit", 0)])
    .ok (.scopedGenMasked (Var.name b.names.length) r e, b.names ++ [name]))
  stmt_breakTo label := (none, fun b _ => .ok (.breakTo label, b.names))
  stmt_continueTo label := (none, fun b _ => .ok (.continueTo label, b.names))
  stmt_exprStmt value := (none, fun b _ => do
    let v ← (value.2 b).mapError (Located.under [("exprStmt", 0)])
    .ok (.exprStmt v, b.names))
  objectentry_property name value := fun b =>
    ((value.2 b).mapError (Located.under [("property", 0)])).map (.property name)
  objectentry_spread value := fun b =>
    ((value.2 b).mapError (Located.under [("spread", 0)])).map .spread

/-- **The renaming of binders to the printer's names**, the binders in scope being `names`: the
reader's named normaliser. -/
def expr (names : List String) (x : Expr) : Except ReadFailure Expr :=
  (cata_expr alg x).2 { names }

end Effect4.Codegen.Rename
