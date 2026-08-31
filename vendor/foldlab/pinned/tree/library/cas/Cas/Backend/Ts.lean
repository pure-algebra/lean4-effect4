/-!
# The TypeScript fragment, L2 — and the printer, L3

The closed expression/declaration fragment the backend emits, grown
only with a real consumer (EFFECTS-BACKEND R6). First consumer: the
generated canonical-schema mirrors (slice 1) — module header, star
imports, doc-commented exported consts, and the expression forms
constructor calls need.

Rendering is fixed-layout under a `Style` value (the ratified
Substance/Denotation/Style split): no width-adaptive grouping, ever —
stable bytes and stable diffs are the point. `house0` transcribes the
effects package's existing look; it is the first inhabitant, not a
default to drift from.
-/

namespace Cas.Backend.Ts

/-- Declared, digestable aesthetic values. Fixed layout; these are the
knobs the house look actually uses. -/
structure Style where
  indent : Nat := 2
  quote : Char := '"'

/-- The effects package's look, transcribed. -/
def house0 : Style := {}

/-- Expressions: exactly what constructor-call emission needs. -/
inductive Expr where
  /-- A (possibly dotted) reference: `Schema.Struct`, `refSchema`. -/
  | ident (name : String)
  | str (value : String)
  | int (value : Int)
  | bool (value : Bool)
  | jsNull
  | call (fn : Expr) (args : List Expr)
  | object (fields : List (String × Expr))
  /-- An object the emitter chose to lay out one field per line —
  layout is the emitter's explicit choice, never a width heuristic. -/
  | objectML (fields : List (String × Expr))
  /-- `[a, b, …]`. -/
  | arr (items : List Expr)
  /-- A zero-parameter arrow, `() => body`, with an optional declared
  return type: `(): T => body`. The declared type is a raw string for
  the same reason `ConstDecl.type` is — a generated expression sometimes
  has to arrive at a type the reader expects, and inference would widen
  it.

  First consumer: the `Suspend` lowering. Effect's own printer writes
  `Schema.suspend((): Schema.Codec<Objects_ | null> => …)`, so the form
  is the target's, not a choice — a zero-parameter arrow whose return
  type is declared when the emitter has one to declare. -/
  | arrow (returnType : Option String) (body : Expr)
  deriving Inhabited

/-- One statement of a generator body — exactly the forms straight-line
store programs need. -/
inductive Stmt where
  /-- `const name = yield* value`. -/
  | constYield (name : String) (value : Expr)
  /-- `return value`. -/
  | ret (value : Expr)

/-- One exported `const` with its doc comment. `type` is the optional
declared type — additive, so an emitter that has no type to declare
constructs the same three fields it always did. It exists because a
generated TABLE has to arrive in TypeScript at the type the hand-written
reader expects (a `Refusal` union, not a widened `string`); inference
would widen every literal column and push a cast onto the consumer. -/
structure ConstDecl where
  doc : List String
  name : String
  value : Expr
  type : Option String := none

/-- An exported straight-line store program:
`export const name = (store: ParamType) => Effect.gen(function* () { … })`. -/
structure ProgDecl where
  doc : List String
  name : String
  paramName : String
  paramType : String
  stmts : List Stmt

/-- A module declaration. -/
inductive Decl where
  | const (d : ConstDecl)
  | prog (d : ProgDecl)
  /-- A verbatim preamble block (a generated local helper). -/
  | raw (text : String)

/-- An import: star, or named values/types. -/
inductive Import where
  | all (name : String) (path : String)
  | named (names : List String) (path : String)
  | types (names : List String) (path : String)

/-- A generated module: header doc block, imports, declarations. -/
structure Module where
  header : List String
  imports : List Import
  decls : List Decl

namespace Render

def indentOf (style : Style) (depth : Nat) : String :=
  String.ofList (List.replicate (style.indent * depth) ' ')

/-- String-literal escaping: the delimiter, the escape character, and
the three control characters a source line cannot hold. Everything else
— accents, dashes, the whole of the non-ASCII plane — travels verbatim,
because the emitted file is UTF-8 and so is TypeScript's grammar.

Escaping lives in the PRINTER, not in the emitters: a string that has to
be pre-escaped by its producer is a string every future producer will
forget to escape. Nothing already emitted carries a delimiter or a
backslash, so the house bytes are unchanged. -/
def escapeString (style : Style) (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++
      (if c == style.quote then "\\" ++ String.singleton c
       else if c == '\\' then "\\\\"
       else if c == '\n' then "\\n"
       else if c == '\r' then "\\r"
       else if c == '\t' then "\\t"
       else String.singleton c)

def quoted (style : Style) (s : String) : String :=
  String.singleton style.quote ++ escapeString style s ++
    String.singleton style.quote

mutual

/-- Fixed-layout rendering. Objects and arrays render inline when every
member renders newline-free (a layout function of the substance, never
of a width budget); otherwise one member per line, trailing commas. -/
def expr (style : Style) (depth : Nat) : Expr → String
  | .ident name => name
  | .str value => quoted style value
  | .int value => toString value
  | .bool value => if value then "true" else "false"
  | .jsNull => "null"
  | .call fn args => expr style depth fn ++ "(" ++
      String.intercalate ", " (exprs style depth args) ++ ")"
  | .object fields =>
    if fields.isEmpty then "{}"
    else
      let rendered := objectFields style (depth + 1) fields
      if rendered.all (fun f => !f.2.any (· == '\n')) then
        "{ " ++
          String.intercalate ", " (rendered.map fun (n, v) => n ++ ": " ++ v) ++
          " }"
      else
        "{\n" ++
          String.intercalate "\n"
            (rendered.map fun (n, v) =>
              indentOf style (depth + 1) ++ n ++ ": " ++ v ++ ",") ++
          "\n" ++ indentOf style depth ++ "}"
  | .objectML fields =>
    if fields.isEmpty then "{}"
    else
      "{\n" ++
        String.intercalate "\n"
          ((objectFields style (depth + 1) fields).map fun (n, v) =>
            indentOf style (depth + 1) ++ n ++ ": " ++ v ++ ",") ++
        "\n" ++ indentOf style depth ++ "}"
  | .arr items =>
    if items.isEmpty then "[]"
    else
      let rendered := exprs style (depth + 1) items
      if rendered.all (fun s => !s.any (· == '\n')) then
        "[" ++ String.intercalate ", " rendered ++ "]"
      else
        "[\n" ++
          String.intercalate "\n"
            (rendered.map fun s => indentOf style (depth + 1) ++ s ++ ",") ++
          "\n" ++ indentOf style depth ++ "]"
  -- The body renders at THIS depth, not one deeper: an arrow is an
  -- expression on one line, and the layout of whatever it wraps is that
  -- expression's own decision.
  | .arrow returnType body =>
    "()" ++ (match returnType with | none => "" | some t => ": " ++ t) ++
      " => " ++ expr style depth body

def exprs (style : Style) (depth : Nat) : List Expr → List String
  | [] => []
  | e :: rest => expr style depth e :: exprs style depth rest

def objectFields (style : Style) (depth : Nat) :
    List (String × Expr) → List (String × String)
  | [] => []
  | (name, value) :: rest =>
    (name, expr style depth value) :: objectFields style depth rest

end

def docBlock (lines : List String) : String :=
  match lines with
  | [] => ""
  | [one] => "/** " ++ one ++ " */\n"
  | first :: rest =>
    "/** " ++ first ++ "\n" ++
      String.intercalate "\n" (rest.map (" * " ++ ·)) ++ " */\n"

def constDecl (style : Style) (d : ConstDecl) : String :=
  docBlock d.doc ++ "export const " ++ d.name ++
    (match d.type with | none => "" | some t => ": " ++ t) ++ " = " ++
    expr style 0 d.value ++ "\n"

def stmt (style : Style) (depth : Nat) : Stmt → String
  | .constYield name value =>
    indentOf style depth ++ "const " ++ name ++ " = yield* " ++
      expr style depth value
  | .ret value =>
    indentOf style depth ++ "return " ++ expr style depth value

def progDecl (style : Style) (d : ProgDecl) : String :=
  docBlock d.doc ++ "export const " ++ d.name ++ " = (" ++ d.paramName ++
    ": " ++ d.paramType ++ ") =>\n" ++
    indentOf style 1 ++ "Effect.gen(function* () {\n" ++
    String.intercalate "\n" (d.stmts.map (stmt style 2)) ++ "\n" ++
    indentOf style 1 ++ "})\n"

def decl (style : Style) : Decl → String
  | .const d => constDecl style d
  | .prog d => progDecl style d
  | .raw text => text ++ "\n"

def import_ (style : Style) : Import → String
  | .all name path =>
    "import * as " ++ name ++ " from " ++ quoted style path ++ "\n"
  | .named names path =>
    "import { " ++ String.intercalate ", " names ++ " } from " ++
      quoted style path ++ "\n"
  | .types names path =>
    "import type { " ++ String.intercalate ", " names ++ " } from " ++
      quoted style path ++ "\n"

/-- The whole module, house layout: header block, imports, one blank
line between declarations. An empty header line prints as a bare `" *"`
— the house look has no trailing whitespace, so a paragraph break in a
header block cannot smuggle any in. -/
def module (style : Style) (m : Module) : String :=
  "/**\n" ++ String.intercalate "\n"
      (m.header.map fun line => if line.isEmpty then " *" else " * " ++ line) ++
    "\n */\n" ++
    String.join (m.imports.map (import_ style)) ++ "\n" ++
    String.intercalate "\n" (m.decls.map (decl style))

end Render

end Cas.Backend.Ts
