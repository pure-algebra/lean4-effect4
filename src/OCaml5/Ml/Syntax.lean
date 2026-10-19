import OCaml5.Ml.Identifier

/-!
# OCaml5.Ml.Syntax

The part of the OCaml 5 surface that the estate prints, as first-order data. This module owns
**syntax only**: no rendering, no checking. Every constructor is one a producer builds: the LCNF
route (`OCaml5.Lcnf.Translate`, `OCaml5.Lcnf.Types`, the builtin table's forms, `OCaml5.Lcnf.Gen`)
and the `eff/` library's emitter (`OCaml5.Eff.Emit`), whose forms `fnMatch`, `seq`, `letPat`,
`ifUnit`, `commented` and `Pat.int` are. Three module-language forms land ahead of their
producers, the interop plan's P1 and P2 (`docs/research/2026-10-15-interop-plan/README.md`,
decisions row 393): `pack`, `SigItem` with `Decl.moduleTypeD`, and `TypeDecl.isPrivate`. The
program types' owner (`ocaml/eff/eff_types.ml`) builds `Decl.moduleD` and `Decl.moduleRecD`, one
module per type (slice 1.2a of the OCaml estate refactor). The public facade
(`OCaml5.Lcnf.Public`) builds `Decl.moduleAliasD`, and a consumer's facade (`OCaml5.Lcnf.Gen`)
builds `Decl.includeD`. A form no producer builds is not here otherwise. The cut of 2026-10-15 (LC-3 of
`docs/research/2026-10-14-lowering-cleanup/prompt.md`) measured each removal by a build: the
avatar's surface of 55 expression constructors became 22. The `eff/` emitter added 6, and verbatim
expression text went once the prelude's three primitives were structured. The join point's
attributed `let` (`letAttr`) came on 2026-10-17, slice 0.2 of the OCaml estate refactor.

Precedent: `TypeScript.Syntax` in the estate's TypeScript target package — syntax in one module,
rendering in another. The traversals of the four sorts (`Ty`, `Pat`, `Expr`, `Decl`) are algebras
of one generated fold (`OCaml5.Ml.Fold`, `make gen-derived`, the group `MlFold`): the printer
(`OCaml5.Ml.Render`), the checker (`OCaml5.Ml.Check`), the builtin table's uses and substitution
(`OCaml5.Lcnf.Builtins`) and the conformance reader (`Conform.Effect4.LcnfMl`).

Every constructor names the section of the OCaml 5.1.1 manual it renders.

## Two properties this data has, and one it does not

* **First order.** No binders as Lean functions: a value of `Expr` is a tree of strings, so it
  can be compared, printed, diffed and stored.
* **Untyped.** The surface can describe a module `ocamlc` rejects. `OCaml5.Ml.Check` narrows that:
  it decides scoping, constructor arity, duplicate labels and the shadowing rule, and the rest is
  `ocamlopt`'s (`make check-ocaml`).
-/

namespace OCaml5.Ml

/-! ## Argument labels (§11.7, "labeled arguments") -/

/-- A function-argument label at a call site: `~x:e` is `lbl`, and an unlabelled argument is
`nolabel`. The name is stored without its `~`. -/
inductive ArgLabel where
  /-- An ordinary positional argument. -/
  | nolabel
  /-- `~name:` — a labelled argument (§11.7). -/
  | lbl (name : String)
deriving Repr, Inhabited, DecidableEq

/-! ## Types (§11.2, *Type expressions*) -/

/-- An OCaml type expression (§11.2). Type application is postfix, as OCaml writes it. -/
inductive Ty where
  /-- `'a` — a type variable (§11.2, "'ident"). Rendered with its `'`. -/
  | var (name : String)
  /-- A type constructor applied to its arguments, postfix: `int`, `'a list`,
  `('a, 'b) result`. The name may be qualified (§11.4). -/
  | con (name : String) (args : List Ty)
  /-- `t -> u` (§11.2, "typexpr -> typexpr"). -/
  | arrow (dom cod : Ty)
  /-- `t1 * t2 * …` (§11.2, "typexpr * typexpr"). -/
  | tuple (parts : List Ty)
  /-- `_` — the anonymous type (§11.2, "_"): an annotation that says nothing. -/
  | anon
  /-- `label:t -> u` (§11.2, "typexpr -> typexpr" with a label): the engine's carrier signatures
  take the fiber table's projection as `exit_of:`. -/
  | labelled (label : String) (dom cod : Ty)
deriving Repr, Inhabited, BEq

namespace Ty
def int : Ty := .con "int" []
def bool : Ty := .con "bool" []
def unit : Ty := .con "unit" []
def string : Ty := .con "string" []
def named (n : String) : Ty := .con n []
def list (t : Ty) : Ty := .con "list" [t]
def option (t : Ty) : Ty := .con "option" [t]
end Ty

/-! ## Patterns (§11.6, *Patterns*) -/

/-- An OCaml pattern (§11.6). -/
inductive Pat where
  /-- `_` (§11.6, "_"). -/
  | wild
  /-- A variable binding (§11.6, "value-name"). -/
  | var (name : String)
  /-- A constructor pattern (§11.6, "constr pattern"); `≥ 2` arguments are rendered as one
  tuple, as OCaml requires. `[]`, `()`, `true` and `false` are constructors here. -/
  | ctor (name : String) (args : List Pat)
  /-- `{ f = p; … }` (§11.6, "{ field = pattern }"). -/
  | record (fields : List (String × Pat))
  /-- `{ f = p; _ }` — a record pattern that does not name every field (§11.6). The `_` is what
  keeps `warning 9` quiet on a record the generator only partly reads. -/
  | recordOpen (fields : List (String × Pat))
  /-- `(p1, p2, …)` (§11.6, "pattern , pattern"). -/
  | tuple (parts : List Pat)
  /-- `hd :: tl`, which `Pat.ctor` cannot spell because `::` is infix. -/
  | cons (hd tl : Pat)
  /-- A non-negative integer literal (§11.6, "constant"): the wire decoders' tag arms. -/
  | int (n : Nat)
deriving Repr, Inhabited

namespace Pat
def unit : Pat := .ctor "()" []
def nil : Pat := .ctor "[]" []
def true_ : Pat := .ctor "true" []
def false_ : Pat := .ctor "false" []
def none_ : Pat := .ctor "None" []
def some_ (p : Pat) : Pat := .ctor "Some" [p]
end Pat

/-! ## Expressions (§11.7, *Expressions*) -/

/-- An OCaml expression (§11.7). -/
inductive Expr where
  /-- A value path (§11.4): `x`, `M.f`. -/
  | var (name : String)
  /-- A non-negative integer literal (§11.1). -/
  | int (n : Nat)
  /-- A string literal (§11.1). -/
  | str (s : String)
  /-- `true` / `false`. -/
  | bool (b : Bool)
  /-- `()` (§11.7, "( )"). -/
  | unit
  /-- A constructor applied to its arguments (§11.7, "constr expr"); `≥ 2` arguments become one
  tuple, as OCaml requires. -/
  | ctor (name : String) (args : List Expr)
  /-- Function application (§11.7, "expr { argument }+"), left-associative. -/
  | app (fn : Expr) (args : List Expr)
  /-- Application with labelled arguments (§11.7, "argument"): `f ~x:e e`. `app` is the
  all-`nolabel` case. -/
  | appL (fn : Expr) (args : List (ArgLabel × Expr))
  /-- An infix application `l op r` (§11.7, "expr infix-op expr"). The operator's precedence and
  associativity are read off its first character, exactly as OCaml's grammar does. -/
  | binop (op : String) (l r : Expr)
  /-- `fun p1 p2 -> body` over plain parameter names; a parameter named `()` renders as the unit
  pattern. -/
  | fn (params : List String) (body : Expr)
  /-- `let x = v in body` (§11.7, "let … in"). -/
  | letIn (name : String) (value body : Expr)
  /-- `let[@attr] x = v in body` (§11.13): `letIn` with an attribute on its binding, which the
  manual reads as `let x = v [@@attr] in body`. The attribute is text, as `Decl.floatingAttrD`'s
  is. The LCNF route marks each join point `local always` (`OCaml5.Lcnf.localFun`). -/
  | letAttr (attr : String) (name : String) (value body : Expr)
  /-- A local `let rec f ps = v in body` (§11.7): one recursive local function. -/
  | letRec (name : String) (params : List String) (value body : Expr)
  /-- `if c then t else e` (§11.7). -/
  | ifThen (cond thenE elseE : Expr)
  /-- `match e with | p -> b …` (§11.7), one arm per pattern and body. -/
  | matchE (scrut : Expr) (arms : List (Pat × Expr))
  /-- `{ f = e; … }` (§11.7, "{ field = expr }"). -/
  | record (fields : List (String × Expr))
  /-- `e.f` (§11.7, "expr . field"). -/
  | field (e : Expr) (name : String)
  /-- `(e1, e2, …)` (§11.7, "expr , expr"). -/
  | tuple (parts : List Expr)
  /-- `[e1; e2; …]` (§11.7, "[ expr ; … ]"). -/
  | listLit (items : List Expr)
  /-- `(e : t)` (§11.7, "( expr : typexpr )"). -/
  | annot (e : Expr) (ty : Ty)
  /-- A place the translator has no rule for. `note` says what the Lean side had; `fill` is what
  stands in its place. Rendered as a comment followed by `fill`, so a hole is visible in the
  output. -/
  | hole (note : String) (fill : Expr)
  /-- `assert e` (§11.7, "assert expr"). `assert false` is the idiom for an unreachable arm and
  is the one expression OCaml types at any type. -/
  | assertE (e : Expr)
  /-- `function | p -> e …` (§11.7, "function pattern-matching"): a match on the one argument
  of a function, as the `eff/` library's constructor tables write it. -/
  | fnMatch (arms : List (Pat × Expr))
  /-- `e1; e2` (§11.7, "expr ; expr"): `e1` evaluated for its effect, then `e2`. -/
  | seq (first rest : Expr)
  /-- `let p = v in body` with a pattern (§11.7, "let … in"): `letIn` is the variable case. -/
  | letPat (pat : Pat) (value body : Expr)
  /-- `if c then e` with no `else` (§11.7): `e` has type `unit`. -/
  | ifUnit (cond thenE : Expr)
  /-- `e (* note *)`: an expression with a trailing comment. The comment is whitespace to
  OCaml, so the form is exactly as tight as `e`. -/
  | commented (e : Expr) (note : String)
  /-- `(module M : S)` (§11.7, "first-class modules"): the module `M` packed at the module type
  `S`, both paths. -/
  | pack (module_ : String) (signature : String)
deriving Repr, Inhabited

namespace Expr
/-- `f a b …` with `f` a name. -/
def call (f : String) (args : List Expr) : Expr := .app (.var f) args
def none_ : Expr := .ctor "None" []
def some_ (e : Expr) : Expr := .ctor "Some" [e]
def nil : Expr := .ctor "[]" []
end Expr

/-! ## Type declarations (§11.6, *Type and exception definitions*) -/

/-- One record field (§11.6, "field-decl"). -/
structure Field where
  name : String
  ty : Ty
deriving Repr, Inhabited

/-- One variant constructor (§11.6, "constr-decl"): `| C of t1 * t2`. -/
structure Ctor where
  name : String
  args : List Ty := []
deriving Repr, Inhabited

/-- The right-hand side of a `type` declaration (§11.6, "type-representation"). -/
inductive TyBody where
  /-- `{ f : t; g : u }`. -/
  | record (fields : List Field)
  /-- `| A | B of t`. -/
  | variant (ctors : List Ctor)
  /-- `type t = u` — an abbreviation (§11.6, "type-equation"). -/
  | alias (ty : Ty)
  /-- `type t` — an abstract type. -/
  | abstract
deriving Repr, Inhabited

/-- One `type` declaration (§11.6, "typedef"). A Lean `structure` becomes a `record`, a Lean
`inductive` a `variant`, and a group of them joined by `and` is a `Decl.types`. -/
structure TypeDecl where
  name : String
  params : List String := []
  body : TyBody
  /-- `= private …` (§11.6, "private types"): outside its module the type's values can be read
  and matched but not built. An abstract type has no body to make private. -/
  isPrivate : Bool := false
deriving Repr, Inhabited

/-- One item of a module type (§11.10, "module types"). -/
inductive SigItem where
  /-- `val name : ty`. -/
  | value (name : String) (ty : Ty)
  /-- `type …`: one type declaration, abstract or with its body. -/
  | type (decl : TypeDecl)
deriving Repr, Inhabited

/-- One `let` binding, possibly a function (§11.6, "value definition"). -/
structure Bind where
  name : String
  params : List (String × Option Ty) := []
  result : Option Ty := none
  body : Expr
deriving Repr, Inhabited

/-! ## Structure items (§11.11, *Module implementations*) -/

/-- One structure item: what a compilation unit is a list of (§11.11). -/
inductive Decl where
  /-- `type a = … and b = …` (§11.6). -/
  | types (group : List TypeDecl)
  /-- `let [rec] f … and g …` (§11.11, "definition"). -/
  | letD (isRec : Bool) (binds : List Bind)
  /-- `(* text *)`. -/
  | comment (text : String)
  /-- Verbatim text: the hand prelude of the engine's seam (`--prelude`), the one item no
  structured form covers, since it is hand OCaml until the carriers are Lean data. -/
  | rawD (text : String)
  /-- `module F (X : S) … = struct … end` — the functor definition (§11.11), each parameter
  with the path of its module type. -/
  | moduleD (name : String) (params : List (String × String)) (body : List Decl)
  /-- A floating attribute, `[@@@warning "-32"]` (§11.13). -/
  | floatingAttrD (text : String)
  /-- One blank line. Layout, not syntax; here so that a generated unit's paragraphing is data
  like everything else. -/
  | blank
  /-- `open M` (§11.11, "open"): the unit `M`'s names in scope. The checker reads it as a scope
  when it is handed `M`'s interface (`OCaml5.Ml.checkModule`). -/
  | openD (path : String)
  /-- `module type S = sig … end` (§11.10). -/
  | moduleTypeD (name : String) (items : List SigItem)
  /-- `module rec A : sig … end = A and B : sig … end = B` (§12.2, recursive modules): each member
  is its own signature and its own implementation. The program types' owner declares a cycle of
  types so (`Eff`–`Stmt`–`Stmts`), since a sequential signature cannot name it. A member holds
  types only: OCaml evaluates such a group safely, and `Ml.checkModule` refuses a `val`. -/
  | moduleRecD (members : List (String × List SigItem))
  /-- `module M = P` (§11.11, "module-name = module-expr" with a module path; §12.13, "module
  aliases"): `M` is another name for the module at `P`, its types equal and its constructors and
  fields reachable through `M`. The public facade re-exports each program type's module at its
  owner so (`OCaml5.Lcnf.Public`), since OCaml re-exports constructors only with their module. -/
  | moduleAliasD (name : String) (path : String)
  /-- `include P` (§11.11, "include"): the items of the module at `P`, re-exported. A consumer's
  facade includes the unit that implements its roots (`OCaml5.Lcnf.Gen`), and its inferred
  interface keeps the consumer's roots and the types they name. -/
  | includeD (path : String)
deriving Repr, Inhabited

/-! ## The root -/

/-- A compilation unit: a name, an optional header comment, and its structure items (§11.11).
`OCaml5.Ml.render` turns one into the bytes of a `.ml` file. The name is the unit's module name
and is *not* rendered into the file; OCaml takes a unit's module name from its file name. -/
structure Module where
  name : String
  /-- A header comment, emitted first, without the `(* *)`. -/
  header : Option String := none
  items : List Decl

end OCaml5.Ml
