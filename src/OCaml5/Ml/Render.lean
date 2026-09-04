import OCaml5.Ml.Syntax

/-!
# OCaml5.Ml.Render

Deterministic rendering of `OCaml5.Ml.Syntax` to OCaml 5 source text.

Precedent: `TypeScript.Render` — syntax in one module, rendering in another, and the rendering is
a total function of the syntax alone. Two properties follow, and they are the whole contract:

* **Equal syntax gives equal bytes.** `render` is a `Module → String`; there is no configuration,
  no environment, no ordering by a hash, and no wall clock. Two runs of the same generator on the
  same day and on different machines produce the same file, which is what makes
  `tools/fuzz.sh avatar`'s byte diff against a hand-written file meaningful.
* **Fixed layout.** Where a line break goes is a property of the *form*, not of a width budget:
  a record or variant with `wideAt` or more members is one member per line, everything else is
  one line, and nested expressions are indented by their `ind` depth. There is no reflowing pass,
  so a one-field change moves one line.

## Precedence, and why the table is safe

Round two of the P5 spike parenthesised aggressively and said why: "`ocamlc` accepts redundant
parentheses everywhere and a wrong precedence table is a silent miscompile". The table below
replaces that, and the reason it is safe to is that it is **conservative in one direction**. Each
form renders at a level and asks each operand for a minimum level; when the operand's level is
lower, it is parenthesised. Every level here is the manual's (§11.7, the operator table) or
*lower* than the manual's, and a level that is too low only ever adds a parenthesis. So a bug in
this table is a redundant parenthesis, never a reparse.

Levels, tightest last, are the manual's table read upwards:

| level | forms |
| --- | --- |
| 0 | `let`, `match`, `fun`, `function`, `try`, `let open` — extend as far right as they can |
| 1 | `;` |
| 2 | `if … then … else …`, `while`, `for` |
| 3 | `<-`, `:=` (right) |
| 4 | `,` (tuple) |
| 5 | `||`, `or` (right) |
| 6 | `&&`, `&` (right) |
| 7 | `=` `<` `>` `|` `&` `$` `!=` (left) |
| 8 | `@…` `^…` (right) |
| 9 | `::` (right) |
| 10 | `+…` `-…` (left) |
| 11 | `*…` `/…` `%…` `mod` `land` `lor` `lxor` (left) |
| 12 | `**…` `lsl` `lsr` `asr` (right) |
| 14 | application, constructor application, `assert`, `lazy` (left) |
| 15 | `.field`, `.(i)` |
| 16 | prefix `!` |
| 17 | atomic: a literal, a name, `( … )`, `{ … }`, `[ … ]`, `begin … end` |

An operator's level is read off its **first character**, which is exactly OCaml's own rule
(§11.7, "the precedence of an operator is determined by its first character"), so a generator may
invent an operator and the renderer will place it correctly.

Types have their own three levels: `->` (right) below `*` below postfix application.
-/

namespace OCaml5.Ml

/-! ## Types -/

/-- Type levels: `0` an arrow, `1` a `*`-tuple, `2` a postfix application, `3` atomic. -/
private def tyLevel : Ty → Nat
  | .var _ => 3
  | .anon => 3
  | .con _ [] => 3
  | .con _ _ => 2
  | .arrow _ _ => 0
  | .larrow _ _ _ => 0
  | .tuple _ => 1
  | .polyVariant _ _ => 3
  | .asVar _ _ => 3

private def labelPrefix : ArgLabel → String
  | .nolabel => ""
  | .lbl n => n ++ ":"
  | .opt n => "?" ++ n ++ ":"

mutual

/-- One type at a required minimum level; parenthesised when it does not reach it. -/
def renderTyAt (need : Nat) (t : Ty) : String :=
  let body : String :=
    match t with
    | .var n => "'" ++ n
    | .anon => "_"
    | .con n [] => n
    | .con n [a] => renderTyAt 2 a ++ " " ++ n
    | .con n args => "(" ++ String.intercalate ", " (renderTysAt 0 args) ++ ") " ++ n
    | .arrow a b => renderTyAt 1 a ++ " -> " ++ renderTyAt 0 b
    | .larrow l a b => labelPrefix l ++ renderTyAt 1 a ++ " -> " ++ renderTyAt 0 b
    | .tuple ps => String.intercalate " * " (renderTysAt 2 ps)
    | .polyVariant k rows =>
        (match k with | .exact => "[ " | .atLeast => "[> " | .atMost => "[< ")
          ++ String.intercalate " | " (renderRows rows) ++ " ]"
    | .asVar inner n => "(" ++ renderTyAt 0 inner ++ " as '" ++ n ++ ")"
  if tyLevel t < need then "(" ++ body ++ ")" else body

def renderTysAt (need : Nat) : List Ty → List String
  | [] => []
  | t :: rest => renderTyAt need t :: renderTysAt need rest

def renderRows : List (String × List Ty) → List String
  | [] => []
  | (tag, []) :: rest => ("`" ++ tag) :: renderRows rest
  | (tag, ts) :: rest =>
      ("`" ++ tag ++ " of " ++ String.intercalate " * " (renderTysAt 2 ts)) :: renderRows rest

end

/-- One type, at the outermost level: no parentheses the form does not need. -/
def renderTy (t : Ty) : String := renderTyAt 0 t

/-- A list of types, each at the outermost level. -/
def renderTys (ts : List Ty) : List String := renderTysAt 0 ts

/-! ## Patterns -/

/-- Pattern levels: `0` an `|`-alternative, `1` an `as`, `2` a `::` or `,`, `3` a constructor
application, `4` atomic. Patterns are parenthesised on the same rule as expressions. -/
private def patLevel : Pat → Nat
  | .wild => 4
  | .var _ => 4
  | .int _ => 4
  | .str _ => 4
  | .char _ => 4
  | .float _ => 4
  | .ctor _ [] => 4
  | .ctor _ _ => 3
  | .record _ => 4
  | .recordOpen _ => 4
  | .tuple _ => 2
  | .listPat _ => 4
  | .cons _ _ => 2
  | .alias _ _ => 1
  | .orPat _ _ => 0
  | .constrained _ _ => 4
  | .exnPat _ => 3
  | .polyPat _ (some _) => 3
  | .polyPat _ none => 4
  | .lazyPat _ => 3

mutual

/-- One pattern at a required minimum level. -/
def renderPatAt (need : Nat) (p : Pat) : String :=
  let body : String :=
    match p with
    | .wild => "_"
    | .var n => n
    | .int n => toString n
    | .str s => "\"" ++ escString s ++ "\""
    | .char c => "'" ++ escChar c ++ "'"
    | .float r => r
    | .ctor n [] => n
    | .ctor n [a] => n ++ " " ++ renderPatAt 4 a
    | .ctor n args => n ++ " (" ++ String.intercalate ", " (renderPatsAt 2 args) ++ ")"
    | .record fs => "{ " ++ String.intercalate "; " (renderPatFieldsAt fs) ++ " }"
    | .recordOpen fs => "{ " ++ String.intercalate "; " (renderPatFieldsAt fs) ++ "; _ }"
    | .tuple ps => String.intercalate ", " (renderPatsAt 3 ps)
    | .listPat ps => "[" ++ String.intercalate "; " (renderPatsAt 2 ps) ++ "]"
    | .cons hd tl => renderPatAt 3 hd ++ " :: " ++ renderPatAt 2 tl
    | .alias inner n => renderPatAt 2 inner ++ " as " ++ n
    | .orPat a b => renderPatAt 1 a ++ " | " ++ renderPatAt 0 b
    | .constrained inner ty => "(" ++ renderPatAt 0 inner ++ " : " ++ renderTy ty ++ ")"
    | .exnPat inner => "exception " ++ renderPatAt 4 inner
    | .polyPat tag none => "`" ++ tag
    | .polyPat tag (some a) => "`" ++ tag ++ " " ++ renderPatAt 4 a
    | .lazyPat inner => "lazy " ++ renderPatAt 4 inner
  if patLevel p < need then "(" ++ body ++ ")" else body

def renderPatsAt (need : Nat) : List Pat → List String
  | [] => []
  | p :: rest => renderPatAt need p :: renderPatsAt need rest

def renderPatFieldsAt : List (String × Pat) → List String
  | [] => []
  | (n, p) :: rest => (n ++ " = " ++ renderPatAt 1 p) :: renderPatFieldsAt rest

end

/-- One pattern, at the outermost level. -/
def renderPat (p : Pat) : String := renderPatAt 0 p
/-- A list of patterns, each at the outermost level. -/
def renderPats (ps : List Pat) : List String := renderPatsAt 0 ps
/-- The `f = p` entries of a record pattern. -/
def renderPatFields (fs : List (String × Pat)) : List String := renderPatFieldsAt fs

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

private def exprLevelOfBinop (op : String) : Nat := (opInfo op).1

/-- The level a form renders at. Lower binds looser; see the table in the module docstring. -/
private def exprLevel : Expr → Nat
  | .var _ => 17
  | .int _ => 17
  | .str _ => 17
  | .bool _ => 17
  | .unit => 17
  | .char _ => 17
  | .float r => if r.startsWith "-" then 17 else 17
  | .intOf n => if n < 0 then 17 else 17
  | .ctor _ [] => 17
  | .ctor _ _ => 14
  | .polyCtor _ none => 17
  | .polyCtor _ (some _) => 14
  | .app _ _ => 14
  | .appL _ _ => 14
  | .binop op _ _ => exprLevelOfBinop op
  | .fn _ _ => 0
  | .lam _ _ => 0
  | .functionE _ => 0
  | .letIn _ _ _ => 0
  | .letPat _ _ _ => 0
  | .letRecIn _ _ => 0
  | .openIn _ _ => 0
  | .seq _ _ => 1
  | .ifThen _ _ _ => 2
  | .ifThenOnly _ _ => 2
  | .whileE _ _ => 2
  | .forE _ _ _ _ _ => 2
  | .matchE _ _ => 0
  | .tryWith _ _ => 0
  | .record _ => 17
  | .recordWith _ _ => 17
  | .field _ _ => 15
  | .setField _ _ _ => 3
  | .tuple _ => 4
  | .listLit _ => 17
  | .arrayLit _ => 17
  | .arrayGet _ _ => 15
  | .arraySet _ _ _ => 3
  | .mkRef _ => 14
  | .deref _ => 16
  | .assign _ _ => 3
  | .raiseE _ => 14
  | .assertE _ => 14
  | .lazyE _ => 14
  | .perform _ => 14
  | .continueK _ _ => 14
  | .discontinueK _ _ => 14
  | .shallowContinue _ _ _ => 14
  | .shallowDiscontinue _ _ _ => 14
  | .reperform _ _ _ => 14
  | .matchWith _ _ _ _ _ _ _ => 14
  | .tryWithEff _ _ _ _ => 14
  | .matchWithK _ _ _ _ => 14
  | .handler _ _ _ _ _ => 17
  | .annot _ _ => 17
  -- a hole renders its filling at the level asked of the hole, and prefixes a comment;
  -- a comment is whitespace, so the result is exactly as tight as the filling.
  | .hole _ _ => 17
  -- verbatim text: the caller owns its parenthesisation, as with `Decl.rawD`.
  | .raw _ => 17

/-- Two spaces per indentation step. -/
private def indentOf (n : Nat) : String := "".pushn ' ' (2 * n)

mutual

/-- One expression, at indentation `ind` and a required minimum level `need`.

`ind` only affects where a newline is indented to; `need` is the only thing that decides a
parenthesis. Both are parameters rather than state, so rendering a subterm is independent of
everything around it. -/
def renderExprAt (ind : Nat) (need : Nat) (e : Expr) : String :=
  let body : String :=
    match e with
    | .var n => n
    | .int n => toString n
    | .str s => "\"" ++ escString s ++ "\""
    | .bool b => if b then "true" else "false"
    | .unit => "()"
    | .char c => "'" ++ escChar c ++ "'"
    | .float r => if r.startsWith "-" then "(" ++ r ++ ")" else r
    | .intOf n => if n < 0 then "(" ++ toString n ++ ")" else toString n
    | .ctor n [] => n
    | .ctor n [a] => n ++ " " ++ renderExprAt ind 15 a
    | .ctor n args => n ++ " (" ++ String.intercalate ", " (renderExprsAt ind 5 args) ++ ")"
    | .polyCtor tag none => "`" ++ tag
    | .polyCtor tag (some a) => "`" ++ tag ++ " " ++ renderExprAt ind 15 a
    | .app f args =>
        renderExprAt ind 14 f ++ " " ++ String.intercalate " " (renderExprsAt ind 15 args)
    | .appL f args =>
        renderExprAt ind 14 f ++ " " ++ String.intercalate " " (renderLabelledAt ind args)
    | .binop op l r =>
        let (lvl, right) := opInfo op
        renderExprAt ind (if right then lvl + 1 else lvl) l ++ " " ++ op ++ " "
          ++ renderExprAt ind (if right then lvl else lvl + 1) r
    | .fn ps b => "fun " ++ String.intercalate " " ps ++ " -> " ++ renderExprAt ind 0 b
    | .lam ps b =>
        "fun " ++ String.intercalate " " (renderParamsAt ind ps) ++ " -> " ++ renderExprAt ind 0 b
    | .functionE arms => "function" ++ renderArmsAt (ind + 1) arms
    | .letIn n v b =>
        "let " ++ n ++ " = " ++ renderExprAt ind 0 v ++ " in\n" ++ indentOf ind
          ++ renderExprAt ind 0 b
    | .letPat p v b =>
        "let " ++ renderPat p ++ " = " ++ renderExprAt ind 0 v ++ " in\n" ++ indentOf ind
          ++ renderExprAt ind 0 b
    | .letRecIn binds b =>
        "let rec " ++ String.intercalate ("\n" ++ indentOf ind ++ "and ")
            (renderLocalBindsAt ind binds)
          ++ " in\n" ++ indentOf ind ++ renderExprAt ind 0 b
    | .openIn path b =>
        "let open " ++ path ++ " in\n" ++ indentOf ind ++ renderExprAt ind 0 b
    | .seq a b => renderExprAt ind 2 a ++ ";\n" ++ indentOf ind ++ renderExprAt ind 1 b
    | .ifThen c t f =>
        "if " ++ renderExprAt ind 2 c ++ " then " ++ renderExprAt (ind + 1) 3 t ++ " else "
          ++ renderExprAt (ind + 1) 2 f
    | .ifThenOnly c t => "if " ++ renderExprAt ind 2 c ++ " then " ++ renderExprAt (ind + 1) 3 t
    | .whileE c b =>
        "while " ++ renderExprAt ind 1 c ++ " do " ++ renderExprAt (ind + 1) 1 b ++ " done"
    | .forE n lo hi down b =>
        "for " ++ n ++ " = " ++ renderExprAt ind 1 lo ++ (if down then " downto " else " to ")
          ++ renderExprAt ind 1 hi ++ " do " ++ renderExprAt (ind + 1) 1 b ++ " done"
    | .matchE s arms =>
        "match " ++ renderExprAt ind 2 s ++ " with" ++ renderArmsAt (ind + 1) arms
    | .tryWith b arms =>
        "try " ++ renderExprAt (ind + 1) 1 b ++ " with" ++ renderArmsAt (ind + 1) arms
    | .record fs => "{ " ++ String.intercalate "; " (renderFieldsAt ind fs) ++ " }"
    | .recordWith base fs =>
        "{ " ++ renderExprAt ind 2 base ++ " with "
          ++ String.intercalate "; " (renderFieldsAt ind fs) ++ " }"
    | .field inner n => renderExprAt ind 15 inner ++ "." ++ n
    | .setField inner n v =>
        renderExprAt ind 15 inner ++ "." ++ n ++ " <- " ++ renderExprAt ind 3 v
    | .tuple ps => String.intercalate ", " (renderExprsAt ind 5 ps)
    | .listLit items => "[" ++ String.intercalate "; " (renderExprsAt ind 5 items) ++ "]"
    | .arrayLit items => "[|" ++ String.intercalate "; " (renderExprsAt ind 5 items) ++ "|]"
    | .arrayGet a i => renderExprAt ind 15 a ++ ".(" ++ renderExprAt ind 0 i ++ ")"
    | .arraySet a i v =>
        renderExprAt ind 15 a ++ ".(" ++ renderExprAt ind 0 i ++ ") <- "
          ++ renderExprAt ind 3 v
    | .mkRef inner => "ref " ++ renderExprAt ind 15 inner
    | .deref inner => "!" ++ renderExprAt ind 16 inner
    | .assign r v => renderExprAt ind 4 r ++ " := " ++ renderExprAt ind 3 v
    | .raiseE inner => "raise " ++ renderExprAt ind 15 inner
    | .assertE inner => "assert " ++ renderExprAt ind 15 inner
    | .lazyE inner => "lazy " ++ renderExprAt ind 15 inner
    | .perform inner => "Effect.perform " ++ renderExprAt ind 15 inner
    | .continueK k v =>
        "Effect.Deep.continue " ++ renderExprAt ind 15 k ++ " " ++ renderExprAt ind 15 v
    | .discontinueK k inner =>
        "Effect.Deep.discontinue " ++ renderExprAt ind 15 k ++ " " ++ renderExprAt ind 15 inner
    | .shallowContinue k v h =>
        "Effect.Shallow.continue_with " ++ renderExprAt ind 15 k ++ " " ++ renderExprAt ind 15 v
          ++ " " ++ renderExprAt ind 15 h
    | .shallowDiscontinue k inner h =>
        "Effect.Shallow.discontinue_with " ++ renderExprAt ind 15 k ++ " "
          ++ renderExprAt ind 15 inner ++ " " ++ renderExprAt ind 15 h
    | .reperform eff k lf =>
        "reperform " ++ renderExprAt ind 15 eff ++ " " ++ renderExprAt ind 15 k ++ " "
          ++ renderExprAt ind 15 lf
    | .matchWith comp arg answer retcVar retc exnc effc =>
        "Effect.Deep.match_with " ++ renderExprAt ind 15 comp ++ " "
          ++ renderExprAt ind 15 arg ++ "\n"
          ++ indentOf (ind + 1) ++ "{ retc = (fun " ++ retcVar ++ " -> "
          ++ renderExprAt (ind + 2) 0 retc ++ ");\n"
          ++ indentOf (ind + 1) ++ "  exnc = (function" ++ renderArmsAt (ind + 2) exnc
          ++ "\n" ++ indentOf (ind + 2) ++ "| e -> raise e);\n"
          ++ indentOf (ind + 1) ++ "  effc = (fun (type a) (eff : a Effect.t) ->\n"
          ++ indentOf (ind + 2) ++ "match eff with" ++ renderEffcClausesAt (ind + 2) answer effc
          ++ "\n" ++ indentOf (ind + 2) ++ "| _ -> None) }"
    | .tryWithEff comp arg answer effc =>
        "Effect.Deep.try_with " ++ renderExprAt ind 15 comp ++ " "
          ++ renderExprAt ind 15 arg ++ "\n"
          ++ indentOf (ind + 1) ++ "{ effc = (fun (type a) (eff : a Effect.t) ->\n"
          ++ indentOf (ind + 2) ++ "match eff with" ++ renderEffcClausesAt (ind + 2) answer effc
          ++ "\n" ++ indentOf (ind + 2) ++ "| _ -> None) }"
    | .matchWithK kind comp arg h =>
        kind.path ++ ".match_with " ++ renderExprAt ind 15 comp ++ " "
          ++ renderExprAt ind 15 arg ++ " " ++ renderExprAt ind 15 h
    -- A handler record on its own: one field per line at `ind + 1`, which is the same shape
    -- `matchWith` inlines but aligned to this record rather than to a call around it.
    | .handler kind answer retc exnc effc =>
        "{ "
          ++ (match retc with
              | none => ""
              | some (v, r) =>
                  "retc = (fun " ++ v ++ " -> " ++ renderExprAt (ind + 2) 0 r ++ ");\n"
                    ++ indentOf (ind + 1) ++ "exnc = (function" ++ renderArmsAt (ind + 2) exnc
                    ++ "\n" ++ indentOf (ind + 2) ++ "| e -> raise e);\n"
                    ++ indentOf (ind + 1))
          ++ "effc = (fun (type a) (eff : a Effect.t) ->\n"
          ++ indentOf (ind + 2) ++ "match eff with"
          ++ renderEffcClausesKindAt (ind + 2) kind answer effc
          ++ "\n" ++ indentOf (ind + 2) ++ "| _ -> None) }"
    | .annot inner ty => "(" ++ renderExprAt ind 0 inner ++ " : " ++ renderTy ty ++ ")"
    | .hole note fill => "(* HOLE: " ++ note ++ " *) " ++ renderExprAt ind need fill
    | .raw t => t
  if exprLevel e < need then "(" ++ body ++ ")" else body

def renderExprsAt (ind : Nat) (need : Nat) : List Expr → List String
  | [] => []
  | e :: rest => renderExprAt ind need e :: renderExprsAt ind need rest

/-- The arguments of a labelled application: `~x:e`, `?y:e`, `e`. -/
def renderLabelledAt (ind : Nat) : List (ArgLabel × Expr) → List String
  | [] => []
  | (.nolabel, e) :: rest => renderExprAt ind 15 e :: renderLabelledAt ind rest
  | (.lbl n, e) :: rest => ("~" ++ n ++ ":" ++ renderExprAt ind 15 e) :: renderLabelledAt ind rest
  | (.opt n, e) :: rest => ("?" ++ n ++ ":" ++ renderExprAt ind 15 e) :: renderLabelledAt ind rest

/-- The `f = e` entries of a record literal: a field value may not contain a bare `;`. -/
def renderFieldsAt (ind : Nat) : List (String × Expr) → List String
  | [] => []
  | (n, e) :: rest => (n ++ " = " ++ renderExprAt ind 2 e) :: renderFieldsAt ind rest

def renderLocalBindsAt (ind : Nat) : List (String × List String × Expr) → List String
  | [] => []
  | (n, ps, b) :: rest =>
      (n ++ (if ps.isEmpty then "" else " " ++ String.intercalate " " ps) ++ " = "
        ++ renderExprAt (ind + 1) 0 b) :: renderLocalBindsAt ind rest

/-- One arm per line. The body is at level 1: a `;` may appear in an arm body, a bare `match`
may not, because it would swallow the arms that follow. -/
def renderArmsAt (ind : Nat) : List Arm → String
  | [] => ""
  | .mk p g b :: rest =>
      "\n" ++ indentOf ind ++ "| " ++ renderPat p
        ++ (match g with
            | none => ""
            | some ge => " when " ++ renderExprAt ind 1 ge)
        ++ " -> " ++ renderExprAt (ind + 1) 1 b
        ++ renderArmsAt ind rest

/-- The clauses of the `effc` field of `Effect.Deep.handler` (`stdlib/effect.ml:66-68`). The
continuation is annotated `(a, answer) Effect.Deep.continuation`, which is what makes the `'c.`
polymorphism of the field check. -/
def renderEffcClausesAt (ind : Nat) (answer : Ty) : List Effc → String
  | [] => ""
  | .mk name args k body :: rest =>
      -- `a` and not `'a`: the annotation must name the *locally abstract* type the
      -- `(type a)` binder introduced, or the GADT match does not refine it and the clause
      -- bodies are all forced to one answer type.
      "\n" ++ indentOf ind ++ "| " ++ renderPat (.ctor name args) ++ " -> Some (fun ("
        ++ k ++ " : " ++ renderTy (Ty.cont (.named "a") answer) ++ ") -> "
        ++ renderExprAt (ind + 1) 0 body ++ ")"
        ++ renderEffcClausesAt ind answer rest

/-- As `renderEffcClausesAt`, with the continuation type of the handler family: a shallow
handler's is `('a, 'b) Effect.Shallow.continuation` (`effect.ml:100`). -/
def renderEffcClausesKindAt (ind : Nat) (kind : HandlerKind) (answer : Ty) : List Effc → String
  | [] => ""
  | .mk name args k body :: rest =>
      let contTy := match kind with
        | .deep => Ty.cont (.named "a") answer
        | .shallow => Ty.shallowCont (.named "a") answer
      "\n" ++ indentOf ind ++ "| " ++ renderPat (.ctor name args) ++ " -> Some (fun ("
        ++ k ++ " : " ++ renderTy contTy ++ ") -> "
        ++ renderExprAt (ind + 1) 0 body ++ ")"
        ++ renderEffcClausesKindAt ind kind answer rest

/-- One `fun` parameter (§11.7, "parameter"). -/
def renderParamsAt (ind : Nat) : List Param → List String
  | [] => []
  | .mk label pat ty default :: rest =>
      let one : String :=
        match label, ty, default with
        | .nolabel, none, _ => renderPatAt 4 pat
        | .nolabel, some t, _ => "(" ++ renderPat pat ++ " : " ++ renderTy t ++ ")"
        | .lbl n, none, _ =>
            (match pat with
             | .var m => if m == n then "~" ++ n else "~" ++ n ++ ":" ++ m
             | _ => "~" ++ n ++ ":" ++ renderPatAt 4 pat)
        | .lbl n, some t, _ =>
            "~" ++ n ++ ":(" ++ renderPat pat ++ " : " ++ renderTy t ++ ")"
        | .opt n, none, none =>
            (match pat with
             | .var m => if m == n then "?" ++ n else "?" ++ n ++ ":" ++ m
             | _ => "?" ++ n ++ ":" ++ renderPatAt 4 pat)
        | .opt n, some t, none => "?" ++ n ++ ":(" ++ renderPat pat ++ " : " ++ renderTy t ++ ")"
        | .opt n, none, some d => "?(" ++ n ++ " = " ++ renderExprAt ind 2 d ++ ")"
        | .opt n, some t, some d =>
            "?(" ++ n ++ " : " ++ renderTy t ++ " = " ++ renderExprAt ind 2 d ++ ")"
      one :: renderParamsAt ind rest

end

/-- One expression, at indentation `ind` and the outermost level. -/
def renderExpr (ind : Nat) (e : Expr) : String := renderExprAt ind 0 e
/-- A list of expressions, each at the outermost level. -/
def renderExprs (ind : Nat) (es : List Expr) : List String := renderExprsAt ind 0 es
/-- The `f = e` entries of a record literal. -/
def renderFields (ind : Nat) (fs : List (String × Expr)) : List String := renderFieldsAt ind fs
/-- The bindings of a local `let rec … and …`. -/
def renderLocalBinds (ind : Nat) (bs : List (String × List String × Expr)) : List String :=
  renderLocalBindsAt ind bs
/-- The arms of a `match` or `try`. -/
def renderArms (ind : Nat) (arms : List Arm) : String := renderArmsAt ind arms
/-- The clauses of a deep `effc` table. -/
def renderEffcClauses (ind : Nat) (answer : Ty) (cs : List Effc) : String :=
  renderEffcClausesAt ind answer cs
/-- The parameters of a `fun`. -/
def renderParams' (ind : Nat) (ps : List Param) : List String := renderParamsAt ind ps

/-! ## Declarations -/

/-- Single-`@` attributes, which is the form a field or a constructor takes. -/
private def renderItemAttrs (attrs : List String) : String :=
  String.join (attrs.map fun a => " [@" ++ a ++ "]")

/-- `[@@deriving a, b, c]`, or nothing. One attribute with a comma-separated payload, which is
what `ppxlib` parses and what `ppx_jane` expects. -/
def renderDerivers (ds : List String) : String :=
  if ds.isEmpty then "" else " [@@deriving " ++ String.intercalate ", " ds ++ "]"

private def renderVariance : Variance → String
  | .invariant => ""
  | .covariant => "+"
  | .contravariant => "-"

private def renderTyParam (p : TyParam) : String :=
  renderVariance p.variance ++ (if p.injective then "!" else "") ++ "'" ++ p.name

/-- The parameter block of a type declaration: `'a `, `('a, 'b) `, or nothing. `tparams` takes
the place of `params` when it is non-empty; only `tparams` can carry a variance, and only a
variance makes a phantom parameter legal. -/
def renderParams (params : List String) (tparams : List TyParam := []) : String :=
  let ps := if tparams.isEmpty then params.map (fun p => "'" ++ p) else tparams.map renderTyParam
  match ps with
  | [] => ""
  | [p] => p ++ " "
  | _ => "(" ++ String.intercalate ", " ps ++ ") "

private def renderField (f : Field) : String :=
  (if f.isMutable then "mutable " else "") ++ f.name ++ " : " ++ renderTy f.ty
    ++ renderItemAttrs f.attrs

private def renderInlineRecord (fs : List Field) : String :=
  "{ " ++ String.intercalate "; " (fs.map renderField) ++ " }"

/-- One variant constructor. Three shapes: an ordinary `| C of t * u`, an inline record
`| C of { x : int }`, and the GADT `| C : t -> u` that an extensible variant's entries and an
effect declaration are made of. -/
private def renderCtor (c : Ctor) : String :=
  "| " ++ c.name
    ++ (match c.result with
        | some res =>
            " : " ++ String.join ((renderTysAt 1 c.args).map (· ++ " -> ")) ++ renderTy res
        | none =>
            match c.inlineRecord with
            | some fs => " of " ++ renderInlineRecord fs
            | none =>
                if c.args.isEmpty then ""
                else " of " ++ String.intercalate " * " (renderTysAt 2 c.args))
    ++ renderItemAttrs c.attrs

private def trailing : Option String → String
  | none => ""
  | some t => "  (* " ++ t ++ " *)"

/-- A record or variant with four or more members is laid out one member per line, which is
the shape `ocaml/avatar/deep_fibers.ml` is written in; three or fewer stay on one
line. Below the threshold a comment has nowhere to go and is dropped. -/
def wideAt : Nat := 4

private def renderTyBody (b : TyBody) : String :=
  match b with
  | .record fs =>
      if fs.length < wideAt then "{ " ++ String.intercalate "; " (fs.map renderField) ++ " }"
      else
        "{\n" ++ String.join (fs.map fun f =>
          String.join (f.leading.map fun l => "  " ++ l ++ "\n")
            ++ "  " ++ renderField f ++ ";" ++ trailing f.comment ++ "\n") ++ "}"
  | .variant cs =>
      if cs.length < wideAt then
        " " ++ String.intercalate " | " (cs.map fun c =>
          (renderCtor c).drop 2 |>.toString)
      else
        "\n" ++ String.join (cs.map fun c => "  " ++ renderCtor c ++ trailing c.comment ++ "\n")
          |>.dropEnd 1 |>.toString
  | .alias t => renderTy t
  | .abstract => ""
  | .extensible => ".."

private def renderAttrs (attrs : List String) : String :=
  String.join (attrs.map fun a => " [@@" ++ a ++ "]")


private def renderTypeDecl (d : TypeDecl) : String :=
  renderParams d.params d.tparams ++ d.name
    ++ (match d.body with
        | .abstract => ""
        -- a variant body starts on its own line, so no space before it
        | .variant cs => " =" ++ renderTyBody (.variant cs)
        | b => " = " ++ renderTyBody b)
    ++ renderDerivers d.derivers ++ renderAttrs d.attrs

private def renderBind (b : Bind) : String :=
  b.name
    ++ (if b.abstractTys.isEmpty then ""
        else " : type " ++ String.intercalate " " b.abstractTys ++ ".")
    ++ (if b.lparams.isEmpty then
          String.join (b.params.map fun p =>
            match p.2 with
            | none => " " ++ p.1
            | some t => " (" ++ p.1 ++ " : " ++ renderTy t ++ ")")
        else " " ++ String.intercalate " " (renderParamsAt 1 b.lparams))
    ++ (match b.result with
        | none => ""
        | some t => " : " ++ renderTy t)
    ++ " =\n  " ++ renderExpr 1 b.body
    ++ renderAttrs b.attrs

/-! ### Module types -/

mutual

/-- One module type (§11.9). -/
def renderModTy (ind : Nat) : ModTy → String
  | .path n => n
  | .sig items =>
      "sig\n" ++ String.join ((renderSigItems (ind + 1) items).map
        (fun s => indentOf (ind + 1) ++ s ++ "\n")) ++ indentOf ind ++ "end"
  | .functor arg argTy res =>
      "functor (" ++ arg ++ " : " ++ renderModTy ind argTy ++ ") -> " ++ renderModTy ind res
  | .withType base name params ty =>
      renderModTy ind base ++ " with type " ++ renderParams params ++ name ++ " = " ++ renderTy ty

def renderSigItems (ind : Nat) : List SigItem → List String
  | [] => []
  | it :: rest => renderSigItem ind it :: renderSigItems ind rest

/-- One signature item (§11.10). -/
def renderSigItem (ind : Nat) : SigItem → String
  | .val n ty => "val " ++ n ++ " : " ++ renderTy ty
  | .types group => "type " ++ String.intercalate "\nand " (group.map renderTypeDecl)
  | .exn n args =>
      "exception " ++ n
        ++ (if args.isEmpty then "" else " of " ++ String.intercalate " * " (renderTysAt 2 args))
  | .ext n ty prim attrs =>
      "external " ++ n ++ " : " ++ renderTy ty ++ " = \"" ++ prim ++ "\"" ++ renderAttrs attrs
  | .modS n mt => "module " ++ n ++ " : " ++ renderModTy ind mt
  | .modTypeS n mt => "module type " ++ n ++ " = " ++ renderModTy ind mt
  | .includeS mt => "include " ++ renderModTy ind mt
  | .openS n => "open " ++ n
  | .commentS t => "(* " ++ t ++ " *)"
  | .rawS t => t

end

/-! ### Structure items -/

mutual

/-- One declaration, as a top-level structure item (§11.11). -/
def renderDeclAt (ind : Nat) : Decl → String
  | .types group =>
      "type " ++ String.intercalate "\nand " (group.map renderTypeDecl)
  | .exn n args =>
      "exception " ++ n
        ++ (if args.isEmpty then ""
            else " of " ++ String.intercalate " * " (renderTysAt 2 args))
  | .effects ctors =>
      "type _ Effect.t +=\n  "
        ++ String.intercalate "\n  " (ctors.map fun c =>
             "| " ++ c.1 ++ " : "
               ++ String.join ((renderTysAt 1 c.2.1).map (· ++ " -> "))
               ++ renderTy (Ty.effect c.2.2))
  | .letD isRec binds =>
      "let " ++ (if isRec then "rec " else "")
        ++ String.intercalate "\n\nand " (binds.map renderBind)
  | .ext n ty prim attrs =>
      "external " ++ n ++ " : " ++ renderTy ty ++ " = \"" ++ prim ++ "\""
        ++ String.join (attrs.map fun a => " [@@" ++ a ++ "]")
  | .openM n => "open " ++ n
  | .comment t => "(* " ++ t ++ " *)"
  | .rawD t => t
  | .typeExt path params ctors isPrivate =>
      "type " ++ renderParams [] params ++ path ++ " +=" ++ (if isPrivate then " private" else "")
        ++ "\n  " ++ String.intercalate "\n  " (ctors.map fun c => renderCtor c ++ trailing c.comment)
  | .includeD mt => "include " ++ renderModTy ind mt
  | .moduleD n params ascribe body =>
      "module " ++ n
        ++ String.join (params.map fun p => " (" ++ p.1 ++ " : " ++ renderModTy ind p.2 ++ ")")
        ++ (match ascribe with | none => "" | some mt => " : " ++ renderModTy ind mt)
        ++ " = struct\n"
        ++ String.join ((renderDecls (ind + 1) body).map
             (fun s => indentOf (ind + 1) ++ s ++ "\n"))
        ++ indentOf ind ++ "end"
  | .moduleAliasD n target => "module " ++ n ++ " = " ++ target
  | .moduleTypeD n mt => "module type " ++ n ++ " = " ++ renderModTy ind mt
  | .attrD attrs d => renderDeclAt ind d ++ renderAttrs attrs
  | .floatingAttrD t => "[@@@" ++ t ++ "]"
  | .letPatD p v => "let " ++ renderPat p ++ " =\n  " ++ renderExpr 1 v
  | .blank => ""

def renderDecls (ind : Nat) : List Decl → List String
  | [] => []
  | d :: rest => renderDeclAt ind d :: renderDecls ind rest

end

/-- One declaration, as a top-level structure item. -/
def renderDecl (d : Decl) : String := renderDeclAt 0 d

/-- A whole compilation unit, as a list of structure items. -/
def moduleText (decls : List Decl) : String :=
  String.join (decls.map fun d => renderDecl d ++ "\n\n")

/-- The bytes of a `.ml` file: the header comment, then the structure items.

This is the one entry point a generator needs. It is a total function of its argument, so equal
syntax gives equal bytes. -/
def render (m : Module) : String :=
  (match m.header with
   | none => ""
   | some h => "(* " ++ h ++ " *)\n\n")
    ++ moduleText m.items

/-- The file name a `Module` belongs in. -/
def Module.fileName (m : Module) : String := m.name ++ ".ml"

/-! ## Checks

The rendering is checked three ways: by `#guard` here on the shapes whose bytes are pinned, by
`OCaml5.MlTest` on a fixture that exercises every constructor, and by `tools/ml-check.sh`, which
compiles that fixture with `ocamlc`. Only the last can say the text is *OCaml*; the first two say
it is the text this file is supposed to produce. -/

-- Types: postfix application, the arrow's right associativity, and the one parenthesis a
-- `*`-tuple of arrows needs.
#guard renderTy (Ty.cont (.var "a") Ty.int) == "('a, int) Effect.Deep.continuation"
#guard renderTy (.con "pending" [.var "nu", .var "b"]) == "('nu, 'b) pending"
#guard renderTy (.arrow Ty.unit (Ty.list (.con "bucket" [.var "b"]))) == "unit -> 'b bucket list"
#guard renderTy (.arrow (.arrow Ty.int Ty.int) Ty.int) == "(int -> int) -> int"
#guard renderTy (.arrow Ty.int (.arrow Ty.int Ty.int)) == "int -> int -> int"
#guard renderTy (.tuple [.arrow Ty.int Ty.int, Ty.bool]) == "(int -> int) * bool"
#guard renderTy (.list (.tuple [Ty.int, Ty.bool])) == "(int * bool) list"
#guard renderTy (.larrow (.lbl "x") Ty.int Ty.bool) == "x:int -> bool"
#guard renderTy (.larrow (.opt "x") Ty.int Ty.bool) == "?x:int -> bool"
#guard renderTy (.polyVariant .exact [("A", []), ("B", [Ty.int])]) == "[ `A | `B of int ]"
#guard renderTy .anon == "_"

-- Expressions: the operator table, and the parentheses it does *not* emit.
#guard renderExpr 0 (.binop "+" (.binop "*" (.int 1) (.int 2)) (.int 3)) == "1 * 2 + 3"
#guard renderExpr 0 (.binop "*" (.binop "+" (.int 1) (.int 2)) (.int 3)) == "(1 + 2) * 3"
#guard renderExpr 0 (.binop "-" (.binop "-" (.int 1) (.int 2)) (.int 3)) == "1 - 2 - 3"
#guard renderExpr 0 (.binop "-" (.int 1) (.binop "-" (.int 2) (.int 3))) == "1 - (2 - 3)"
#guard renderExpr 0 (.binop "::" (.int 1) (.binop "::" (.int 2) Expr.nil)) == "1 :: 2 :: []"
#guard renderExpr 0 (.binop "&&" (.binop "=" (.var "a") (.var "b")) (.var "c"))
  == "a = b && c"
#guard renderExpr 0 (Expr.call "f" [.var "a", Expr.call "g" [.var "b"]]) == "f a (g b)"
#guard renderExpr 0 (.field (.field (.var "f") "frame") "control") == "f.frame.control"
#guard renderExpr 0 (.setField (.field (.var "f") "frame") "control" (.var "c"))
  == "f.frame.control <- c"
#guard renderExpr 0 (.deref (.var "r")) == "!r"
#guard renderExpr 0 (.assign (.var "r") (.binop "+" (.deref (.var "r")) (.int 1)))
  == "r := !r + 1"
#guard renderExpr 0 (.tuple [.int 1, .tuple [.int 2, .int 3]]) == "1, (2, 3)"
#guard renderExpr 0 (.listLit [.tuple [.int 1, .int 2]]) == "[(1, 2)]"
#guard renderExpr 0 (.app (.var "f") [.matchE (.var "x") [.mk .wild none (.int 1)]])
  == "f (match x with\n  | _ -> 1)"
#guard renderExpr 0 (.intOf (-3)) == "(-3)"
#guard renderExpr 0 (.char 'a') == "'a'"
#guard renderExpr 0 (.float "0x1.8p1") == "0x1.8p1"
#guard renderExpr 0 (.assertE (.bool false)) == "assert false"
#guard renderExpr 0 (.lam [Param.named "x", Param.optionalD "y" (.int 0), Param.unit] (.var "x"))
  == "fun ~x ?(y = 0) () -> x"
#guard renderExpr 0 (.polyCtor "A" (some (.int 1))) == "`A 1"
#guard renderExpr 0 (.appL (.var "f") [(.lbl "x", .int 1), (.nolabel, .unit)]) == "f ~x:1 ()"
#guard renderExpr 0 (.arrayGet (.var "a") (.int 0)) == "a.(0)"
#guard renderExpr 0 (.whileE (.bool true) .unit) == "while true do () done"
#guard renderExpr 0 (.forE "i" (.int 0) (.int 9) false .unit) == "for i = 0 to 9 do () done"

-- Patterns.
#guard renderPat (.cons (.var "hd") (.var "tl")) == "hd :: tl"
#guard renderPat (.ctor "Some" [.var "x"]) == "Some x"
#guard renderPat (.ctor "C" [.var "a", .var "b"]) == "C (a, b)"
#guard renderPat (.orPat (.ctor "A" []) (.ctor "B" [])) == "A | B"
#guard renderPat (.recordOpen [("x", .var "x")]) == "{ x = x; _ }"
#guard renderPat (.exnPat (.ctor "Not_found" [])) == "exception Not_found"

-- Declarations: the shapes whose bytes other files diff against.
#guard renderDecl (.types [{ name := "fiber_id", body := .alias Ty.int }]) == "type fiber_id = int"
#guard renderDecl (.exn "Stuck" [.named "fiber_id"]) == "exception Stuck of fiber_id"
#guard renderDecl (.effects [("Fork", [.arrow Ty.unit Ty.unit], .named "fiber_id")])
  == "type _ Effect.t +=\n  | Fork : (unit -> unit) -> fiber_id Effect.t"
#guard renderDecl (.types [{ name := "t", tparams := [{ name := "a", variance := .covariant }],
                             body := .abstract }]) == "type +'a t"
#guard renderDecl (.types [{ name := "t", body := .extensible }]) == "type t = .."
#guard renderDecl (.types [{ name := "t", body := .alias Ty.int, derivers := ["show"] }])
  == "type t = int [@@deriving show]"
#guard renderDecl (.types [{ name := "t", body := .alias Ty.int,
                             derivers := janeRecordDerivers, attrs := ["warning \"-37\""] }])
  == "type t = int [@@deriving sexp, compare, equal, hash, fields] [@@warning \"-37\"]"
#guard renderDecl (.types [{ name := "t",
                             body := .record [{ name := "x", ty := Ty.int,
                                                attrs := ["default 0"] }] }])
  == "type t = { x : int [@default 0] }"
#guard renderDecl (.moduleTypeD "S" (.sig [.val "f" (.arrow Ty.int Ty.int)]))
  == "module type S = sig\n  val f : int -> int\nend"
#guard renderDecl (.moduleD "M" [] none [.openM "Effect"])
  == "module M = struct\n  open Effect\nend"
#guard renderDecl (.typeExt "Effect.t" [] [{ name := "E", args := [Ty.int],
                                             result := some (Ty.effect Ty.unit) }])
  == "type Effect.t +=\n  | E : int -> unit Effect.t"

-- A module is its header and its items.
#guard render { name := "m", header := some "Generated.", items := [.openM "Effect"] }
  == "(* Generated. *)\n\nopen Effect\n\n"
#guard (Module.fileName { name := "deep_fibers", items := [] }) == "deep_fibers.ml"

end OCaml5.Ml
