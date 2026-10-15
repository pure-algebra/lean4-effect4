import OCaml5.Ml.Syntax
import OCaml5.Ml.Fold

/-!
# OCaml5.Ml.Render

Deterministic rendering of `OCaml5.Ml.Syntax` to OCaml 5 source text. Each sort's printer is an
algebra of the generated fold (`OCaml5.Ml.Fold`): `renderTyAlg`, `renderPatAlg`,
`renderExprAlg` and `renderDeclAlg`. No hand recursion over the syntax is left here.

Precedent: `TypeScript.Render` — syntax in one module, rendering in another, and the rendering is
a total function of the syntax alone. Two properties follow, and they are the whole contract:

* **Equal syntax gives equal bytes.** `render` is a `Module → String`; there is no configuration,
  no environment, no ordering by a hash, and no wall clock. Two runs of the same generator on the
  same day and on different machines produce the same file, which is what makes a byte diff
  against a committed artefact meaningful.
* **Fixed layout.** Where a line break goes is a property of the *form*, not of a width budget:
  a record or variant with `wideAt` or more members is one member per line, everything else is
  one line, and nested expressions are indented by their `ind` depth. There is no reflowing pass,
  so a one-field change moves one line.

## Precedence, and why the table is safe

Each form renders at a level and asks each operand for a minimum level; when the operand's level
is lower, it is parenthesised. Every level here is the manual's (§11.7, the operator table) or
*lower* than the manual's, and a level that is too low only ever adds a parenthesis. So a bug in
this table is a redundant parenthesis, never a reparse.

Levels, tightest last, are the manual's table read upwards:

| level | forms |
| --- | --- |
| 0 | `let`, `match`, `fun` — extend as far right as they can |
| 2 | `if … then … else …` |
| 4 | `,` (tuple) |
| 5 | `||` (right) |
| 6 | `&&` (right) |
| 7 | `=` `<` `>` `|` `$` `!=` (left) |
| 8 | `@…` `^…` (right) |
| 9 | `::` (right) |
| 10 | `+…` `-…` (left) |
| 11 | `*…` `/…` `%…` `mod` `land` `lor` `lxor` (left) |
| 12 | `**…` `lsl` `lsr` `asr` (right) |
| 14 | application, constructor application, `assert` (left) |
| 15 | `.field` |
| 17 | atomic: a literal, a name, `( … )`, `{ … }`, `[ … ]` |

An operator's level is read off its **first character**, which is exactly OCaml's own rule
(§11.7, "the precedence of an operator is determined by its first character"), so a generator may
invent an operator and the renderer will place it correctly.

Types have their own three levels: `->` (right) below `*` below postfix application.
-/

namespace OCaml5.Ml

/-- `( … )` around a rendered form whose level is below the one its context needs. -/
private def paren (wrap : Bool) (body : String) : String :=
  if wrap then "(" ++ body ++ ")" else body

/-! ## Types -/

/-- The type printer: a type renders at a required minimum level. Levels: `0` an arrow, `1` a
`*`-tuple, `2` a postfix application, `3` atomic. -/
def renderTyAlg : TyAlgebra (fun _ => Nat → String) where
  ty_var n := fun _ => "'" ++ n
  ty_con n args := fun need =>
    match args with
    | [] => n
    | [a] => paren (2 < need) (a 2 ++ " " ++ n)
    | _ => paren (2 < need) ("(" ++ String.intercalate ", " (args.map (· 0)) ++ ") " ++ n)
  ty_arrow a b := fun need => paren (0 < need) (a 1 ++ " -> " ++ b 0)
  ty_tuple ps := fun need => paren (1 < need) (String.intercalate " * " (ps.map (· 2)))
  ty_anon := fun _ => "_"
  ty_labelled l a b := fun need => paren (0 < need) (l ++ ":" ++ a 1 ++ " -> " ++ b 0)

/-- One type at a required minimum level. -/
def renderTyAt (need : Nat) (t : Ty) : String := cata_ty renderTyAlg t need

/-- One type, at the outermost level: no parentheses the form does not need. -/
def renderTy (t : Ty) : String := renderTyAt 0 t

/-! ## Patterns -/

/-- The pattern printer, at a required minimum level. Levels: `2` a `::` or `,`, `3` a
constructor application, `4` atomic. -/
def renderPatAlg : PatAlgebra (fun _ => Nat → String) where
  pat_wild := fun _ => "_"
  pat_var n := fun _ => n
  pat_ctor n args := fun need =>
    match args with
    | [] => n
    | [a] => paren (3 < need) (n ++ " " ++ a 4)
    | _ => paren (3 < need) (n ++ " (" ++ String.intercalate ", " (args.map (· 2)) ++ ")")
  pat_record fs := fun _ =>
    "{ " ++ String.intercalate "; " (fs.map fun (n, p) => n ++ " = " ++ p 1) ++ " }"
  pat_recordOpen fs := fun _ =>
    "{ " ++ String.intercalate "; " (fs.map fun (n, p) => n ++ " = " ++ p 1) ++ "; _ }"
  pat_tuple ps := fun need => paren (2 < need) (String.intercalate ", " (ps.map (· 3)))
  pat_cons hd tl := fun need => paren (2 < need) (hd 3 ++ " :: " ++ tl 2)
  pat_int n := fun _ => toString n

/-- One pattern, at the outermost level. -/
def renderPat (p : Pat) : String := cata_pat renderPatAlg p 0

/-! ## Expressions -/

/-- The level and associativity of an infix operator, read off its first character exactly as
§11.7 does. `true` is right-associative. The named operators (`mod`, `land`, `lor`, `lxor`,
`lsl`, `lsr`, `asr`, `or`) and the three fixed ones (`::`, `:=`, `!=`) are matched first, because
their first character would otherwise send them to the wrong row. -/
def opInfo (op : String) : Nat × Bool :=
  if op == "::" then (9, true)
  else if op == ":=" then (3, true)
  else if op == "!=" then (7, false)
  else if op == "||" || op == "or" then (5, true)
  else if op == "&&" || op == "&" then (6, true)
  else if op == "lsl" || op == "lsr" || op == "asr" then (12, true)
  else if op == "mod" || op == "land" || op == "lor" || op == "lxor" then (11, false)
  else if op.startsWith "**" then (12, true)
  else
    match op.toList with
    | [] => (7, false)
    | c :: _ =>
        if c == '*' || c == '/' || c == '%' then (11, false)
        else if c == '+' || c == '-' then (10, false)
        else if c == '@' || c == '^' then (8, true)
        else if c == '&' then (6, true)
        else if c == '|' then (7, false)
        else if c == '=' || c == '<' || c == '>' || c == '$' || c == '!' then (7, false)
        else (7, false)

/-- Two spaces per indentation step. -/
private def indentOf (n : Nat) : String := "".pushn ' ' (2 * n)

/-- An expression's printer: the rendering at indentation `ind` and a required minimum level
`need`. `ind` only affects where a newline is indented to; `need` is the only thing that decides
a parenthesis. Both are parameters rather than state, so rendering a subterm is independent of
everything around it. -/
abbrev Rendered : ExprFam → Type := fun _ => Nat → Nat → String

/-- The expression printer (levels in the module docstring). A hole renders its filling at the
level asked of the hole and prefixes a comment, which is whitespace, so it is exactly as tight as
its filling. -/
def renderExprAlg : ExprAlgebra Rendered where
  expr_var n := fun _ _ => n
  expr_int n := fun _ _ => toString n
  expr_str s := fun _ _ => "\"" ++ escString s ++ "\""
  expr_bool b := fun _ _ => if b then "true" else "false"
  expr_unit := fun _ _ => "()"
  expr_ctor n args := fun ind need =>
    match args with
    | [] => n
    | [a] => paren (14 < need) (n ++ " " ++ a ind 15)
    | _ => paren (14 < need) (n ++ " (" ++ String.intercalate ", " (args.map (· ind 5)) ++ ")")
  -- The head at 15: an application there is parenthesised, so `(f x) y` keeps its tree, which
  -- OCaml parses apart from `f x y`.
  expr_app f args := fun ind need =>
    paren (14 < need) (f ind 15 ++ " " ++ String.intercalate " " (args.map (· ind 15)))
  expr_appL f args := fun ind need =>
    let arg : ArgLabel × (Nat → Nat → String) → String
      | (.nolabel, e) => e ind 15
      | (.lbl n, e) => "~" ++ n ++ ":" ++ e ind 15
    paren (14 < need) (f ind 15 ++ " " ++ String.intercalate " " (args.map arg))
  expr_binop op l r := fun ind need =>
    let (lvl, right) := opInfo op
    paren (lvl < need)
      (l ind (if right then lvl + 1 else lvl) ++ " " ++ op ++ " "
        ++ r ind (if right then lvl else lvl + 1))
  expr_fn ps b := fun ind need =>
    paren (0 < need) ("fun " ++ String.intercalate " " ps ++ " -> " ++ b ind 0)
  expr_letIn n v b := fun ind need =>
    paren (0 < need) ("let " ++ n ++ " = " ++ v ind 0 ++ " in\n" ++ indentOf ind ++ b ind 0)
  expr_letRec f ps v b := fun ind need =>
    paren (0 < need)
      ("let rec " ++ f ++ (if ps.isEmpty then "" else " " ++ String.intercalate " " ps) ++ " = "
        ++ v (ind + 1) 0 ++ " in\n" ++ indentOf ind ++ b ind 0)
  expr_ifThen c t e := fun ind need =>
    paren (2 < need) ("if " ++ c ind 2 ++ " then " ++ t (ind + 1) 3 ++ " else " ++ e (ind + 1) 2)
  -- One arm per line, at `ind + 1`. The body is at level 1: a bare `match` may not stand in an
  -- arm, because it would swallow the arms that follow.
  expr_matchE s arms := fun ind need =>
    paren (0 < need)
      ("match " ++ s ind 2 ++ " with"
        ++ String.join (arms.map fun (p, b) =>
          "\n" ++ indentOf (ind + 1) ++ "| " ++ renderPat p ++ " -> " ++ b (ind + 2) 1))
  -- A field value may not contain a bare `;`.
  expr_record fs := fun ind _ =>
    "{ " ++ String.intercalate "; " (fs.map fun (n, e) => n ++ " = " ++ e ind 2) ++ " }"
  expr_field e n := fun ind need => paren (15 < need) (e ind 15 ++ "." ++ n)
  expr_tuple ps := fun ind need => paren (4 < need) (String.intercalate ", " (ps.map (· ind 5)))
  expr_listLit items := fun ind _ => "[" ++ String.intercalate "; " (items.map (· ind 5)) ++ "]"
  expr_annot e ty := fun ind _ => "(" ++ e ind 0 ++ " : " ++ renderTy ty ++ ")"
  expr_hole note fill := fun ind need => "(* HOLE: " ++ note ++ " *) " ++ fill ind need
  expr_assertE e := fun ind need => paren (14 < need) ("assert " ++ e ind 15)
  -- `function`, like `match`, takes every arm that follows: level 0.
  expr_fnMatch arms := fun ind need =>
    paren (0 < need)
      ("function"
        ++ String.join (arms.map fun (p, b) =>
          "\n" ++ indentOf (ind + 1) ++ "| " ++ renderPat p ++ " -> " ++ b (ind + 2) 1))
  -- `;` binds below `if` and above `let`, `match` and `fun`, and to the right: level 1, the left
  -- operand at 2 (an `if` there is whole, a `let` or a `match` would take the rest).
  expr_seq a b := fun ind need => paren (1 < need) (a ind 2 ++ "; " ++ b ind 1)
  expr_letPat p v b := fun ind need =>
    paren (0 < need) ("let " ++ renderPat p ++ " = " ++ v ind 0 ++ " in\n" ++ indentOf ind ++ b ind 0)
  -- its branch at 3, as `ifThen`'s: a nested `if` there is parenthesised, so no `else` can
  -- attach to it
  expr_ifUnit c t := fun ind need => paren (2 < need) ("if " ++ c ind 2 ++ " then " ++ t (ind + 1) 3)
  expr_commented e note := fun ind need => e ind need ++ " (* " ++ note ++ " *)"
  expr_pack m s := fun _ _ => "(module " ++ m ++ " : " ++ s ++ ")"

/-- One expression, at indentation `ind` and a required minimum level `need`. -/
def renderExprAt (ind : Nat) (need : Nat) (e : Expr) : String := cata_expr renderExprAlg e ind need

/-- One expression, at indentation `ind` and the outermost level. -/
def renderExpr (ind : Nat) (e : Expr) : String := renderExprAt ind 0 e

/-! ## Declarations -/

/-- The parameter block of a type declaration: `'a `, `('a, 'b) `, or nothing. -/
def renderParams (params : List String) : String :=
  match params.map ("'" ++ ·) with
  | [] => ""
  | [p] => p ++ " "
  | ps => "(" ++ String.intercalate ", " ps ++ ") "

private def renderField (f : Field) : String := f.name ++ " : " ++ renderTy f.ty

/-- One variant constructor: `| C of t * u`. -/
private def renderCtor (c : Ctor) : String :=
  "| " ++ c.name
    ++ (if c.args.isEmpty then "" else " of " ++ String.intercalate " * " (c.args.map (renderTyAt 2)))

/-- A record or variant with four or more members is laid out one member per line; three or
fewer stay on one line. -/
def wideAt : Nat := 4

private def renderTyBody (b : TyBody) : String :=
  match b with
  | .record fs =>
      if fs.length < wideAt then "{ " ++ String.intercalate "; " (fs.map renderField) ++ " }"
      else "{\n" ++ String.join (fs.map fun f => "  " ++ renderField f ++ ";\n") ++ "}"
  | .variant cs =>
      if cs.length < wideAt then
        " " ++ String.intercalate " | " (cs.map fun c => (renderCtor c).drop 2 |>.toString)
      else
        "\n" ++ String.join (cs.map fun c => "  " ++ renderCtor c ++ "\n") |>.dropEnd 1 |>.toString
  | .alias t => renderTy t
  | .abstract => ""

private def renderTypeDecl (d : TypeDecl) : String :=
  let priv := if d.isPrivate then " private" else ""
  renderParams d.params ++ d.name
    ++ (match d.body with
        | .abstract => ""
        -- a variant body starts on its own line, so no space before it
        | .variant cs => " =" ++ priv ++ renderTyBody (.variant cs)
        | b => " =" ++ priv ++ " " ++ renderTyBody b)

/-- One item of a module type: `val name : ty`, or `type …`. -/
private def renderSigItem : SigItem → String
  | .value name ty => "val " ++ name ++ " : " ++ renderTy ty
  | .type d => "type " ++ renderTypeDecl d

private def renderBind (b : Bind) : String :=
  b.name
    ++ String.join (b.params.map fun p =>
        match p.2 with
        | none => " " ++ p.1
        | some t => " (" ++ p.1 ++ " : " ++ renderTy t ++ ")")
    ++ (match b.result with
        | none => ""
        | some t => " : " ++ renderTy t)
    ++ " =\n  " ++ renderExpr 1 b.body

/-- The structure-item printer, at an indentation (a functor body is one step in). -/
def renderDeclAlg : DeclAlgebra (fun _ => Nat → String) where
  decl_types group := fun _ => "type " ++ String.intercalate "\nand " (group.map renderTypeDecl)
  decl_letD isRec binds := fun _ =>
    "let " ++ (if isRec then "rec " else "") ++ String.intercalate "\n\nand " (binds.map renderBind)
  decl_comment t := fun _ => "(* " ++ t ++ " *)"
  decl_rawD t := fun _ => t
  decl_moduleD n params body := fun ind =>
    "module " ++ n
      ++ String.join (params.map fun p => " (" ++ p.1 ++ " : " ++ p.2 ++ ")")
      ++ " = struct\n"
      ++ String.join (body.map fun d =>
          let s := d (ind + 1)
          (if s.isEmpty then "" else indentOf (ind + 1)) ++ s ++ "\n")
      ++ indentOf ind ++ "end"
  decl_floatingAttrD t := fun _ => "[@@@" ++ t ++ "]"
  decl_blank := fun _ => ""
  decl_openD path := fun _ => "open " ++ path
  decl_moduleTypeD n items := fun ind =>
    "module type " ++ n ++ " = sig\n"
      ++ String.join (items.map fun i => indentOf (ind + 1) ++ renderSigItem i ++ "\n")
      ++ indentOf ind ++ "end"

/-- One declaration, as a top-level structure item. -/
def renderDecl (d : Decl) : String := cata_decl renderDeclAlg d 0

/-- The bytes of a `.ml` file: the header comment, then the structure items.

This is the one entry point a generator needs. It is a total function of its argument, so equal
syntax gives equal bytes. -/
def render (m : Module) : String :=
  (match m.header with
   | none => ""
   | some h => "(* " ++ h ++ " *)\n\n")
    ++ String.join (m.items.map fun d => renderDecl d ++ "\n\n")

/-! ## Checks

The rendering is checked by `#guard` here on the shapes whose bytes are pinned, by the
regeneration of the LCNF group (no byte of a committed artefact moves), and by `ocamlopt` in
`make check-ocaml`. Only the last can say the text is *OCaml*; the first two say it is the text
this file is supposed to produce. -/

-- Types: postfix application, the arrow's right associativity, and the one parenthesis a
-- `*`-tuple of arrows needs.
#guard renderTy (.con "pending" [.var "nu", .var "b"]) == "('nu, 'b) pending"
#guard renderTy (.arrow Ty.unit (Ty.list (.con "bucket" [.var "b"]))) == "unit -> 'b bucket list"
#guard renderTy (.arrow (.arrow Ty.int Ty.int) Ty.int) == "(int -> int) -> int"
#guard renderTy (.arrow Ty.int (.arrow Ty.int Ty.int)) == "int -> int -> int"
#guard renderTy (.tuple [.arrow Ty.int Ty.int, Ty.bool]) == "(int -> int) * bool"
#guard renderTy (.list (.tuple [Ty.int, Ty.bool])) == "(int * bool) list"
#guard renderTy .anon == "_"
-- a labelled arrow, its domain an arrow
#guard renderTy (.labelled "exit_of" (.arrow (.var "a") (Ty.option (.var "x"))) (.var "a"))
  == "exit_of:('a -> 'x option) -> 'a"

-- Expressions: the operator table, and the parentheses it does *not* emit.
#guard renderExpr 0 (.binop "+" (.binop "*" (.int 1) (.int 2)) (.int 3)) == "1 * 2 + 3"
#guard renderExpr 0 (.binop "*" (.binop "+" (.int 1) (.int 2)) (.int 3)) == "(1 + 2) * 3"
#guard renderExpr 0 (.binop "-" (.binop "-" (.int 1) (.int 2)) (.int 3)) == "1 - 2 - 3"
#guard renderExpr 0 (.binop "-" (.int 1) (.binop "-" (.int 2) (.int 3))) == "1 - (2 - 3)"
#guard renderExpr 0 (.binop "::" (.int 1) (.binop "::" (.int 2) Expr.nil)) == "1 :: 2 :: []"
#guard renderExpr 0 (.binop "&&" (.binop "=" (.var "a") (.var "b")) (.var "c"))
  == "a = b && c"
#guard renderExpr 0 (Expr.call "f" [.var "a", Expr.call "g" [.var "b"]]) == "f a (g b)"
-- an application in head position keeps its tree
#guard renderExpr 0 (.app (Expr.call "f" [.var "x"]) [.var "y"]) == "(f x) y"
#guard renderExpr 0 (.field (.field (.var "f") "frame") "control") == "f.frame.control"
#guard renderExpr 0 (.tuple [.int 1, .tuple [.int 2, .int 3]]) == "1, (2, 3)"
#guard renderExpr 0 (.listLit [.tuple [.int 1, .int 2]]) == "[(1, 2)]"
#guard renderExpr 0 (.app (.var "f") [.matchE (.var "x") [(.wild, .int 1)]])
  == "f (match x with\n  | _ -> 1)"
#guard renderExpr 0 (.assertE (.bool false)) == "assert false"
#guard renderExpr 0 (.appL (.var "f") [(.lbl "x", .int 1), (.nolabel, .unit)]) == "f ~x:1 ()"
#guard renderExpr 0 (.letRec "go" ["n"] (.var "n") (.app (.var "go") [.int 1]))
  == "let rec go n = n in\ngo 1"

-- Patterns.
#guard renderPat (.cons (.var "hd") (.var "tl")) == "hd :: tl"
#guard renderPat (.ctor "Some" [.var "x"]) == "Some x"
#guard renderPat (.ctor "C" [.var "a", .var "b"]) == "C (a, b)"
#guard renderPat (.recordOpen [("x", .var "x")]) == "{ x = x; _ }"

-- Declarations: the shapes whose bytes other files diff against.
#guard renderDecl (.types [{ name := "fiber_id", body := .alias Ty.int }]) == "type fiber_id = int"
#guard renderDecl (.types [{ name := "t", params := ["a"], body := .abstract }]) == "type 'a t"
#guard renderDecl (.moduleD "M" [] [.comment "x"]) == "module M = struct\n  (* x *)\nend"
#guard renderDecl (.moduleD "M" [] [.blank, .comment "x", .blank])
  == "module M = struct\n\n  (* x *)\n\nend"
#guard renderDecl (.moduleD "F" [("X", "S")] []) == "module F (X : S) = struct\nend"

-- A module is its header and its items.
#guard render { name := "m", header := some "Generated.", items := [.comment "x"] }
  == "(* Generated. *)\n\n(* x *)\n\n"

-- The `eff/` emitter's forms: an integer pattern, `function`, a sequence, a pattern `let`, an
-- `if` without `else` and a trailing comment.
#guard renderPat (.tuple [.ctor "Eff" [], .int 4]) == "Eff, 4"
#guard renderExpr 0 (.fnMatch [(.ctor "A" [], .int 0), (.wild, .int 1)])
  == "function\n  | A -> 0\n  | _ -> 1"
#guard renderExpr 0 (.seq (Expr.call "f" [.var "x"]) (Expr.call "g" [.var "x"])) == "f x; g x"
-- a `match` left of `;` is parenthesised, or its last arm would take the right operand
#guard renderExpr 0 (.seq (.matchE (.var "x") [(.wild, .unit)]) .unit)
  == "(match x with\n  | _ -> ()); ()"
-- a sequence in a branch is parenthesised; a sequence in an arm is not
#guard renderExpr 0 (.ifThen (.var "c") (.seq .unit .unit) .unit) == "if c then ((); ()) else ()"
#guard renderExpr 0 (.matchE (.var "x") [(.wild, .seq .unit .unit)]) == "match x with\n  | _ -> (); ()"
#guard renderExpr 0 (.letPat (.tuple [.var "a", .var "b"]) (.var "p") (.var "a"))
  == "let a, b = p in\na"
#guard renderExpr 0 (.ifUnit (.var "c") (Expr.call "f" [.unit])) == "if c then f ()"
-- an `if` without `else` in the branch of one with `else` is parenthesised: no dangling `else`
#guard renderExpr 0 (.ifThen (.var "a") (.ifUnit (.var "b") .unit) .unit)
  == "if a then (if b then ()) else ()"
#guard renderExpr 0 (.commented (.int 1) "one") == "1 (* one *)"

-- The module language: a packed module, `open`, a module type, private bodies.
#guard renderExpr 0 (Expr.call "run" [.pack "E4_table" "TABLE"]) == "run (module E4_table : TABLE)"
#guard renderDecl (.openD "Eff_types") == "open Eff_types"
#guard renderDecl (.moduleTypeD "TABLE"
    [.type { name := "t", params := ["a"], body := .abstract }, .value "empty" (.con "t" [.var "a"])])
  == "module type TABLE = sig\n  type 'a t\n  val empty : 'a t\nend"
#guard renderDecl (.types [{ name := "nat", body := .alias Ty.int, isPrivate := true }])
  == "type nat = private int"
#guard renderDecl (.types [{ name := "t", body := .variant [{ name := "A" }], isPrivate := true }])
  == "type t = private A"

end OCaml5.Ml
