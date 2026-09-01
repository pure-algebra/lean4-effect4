/-!
# Target.TypeScript.Expr

The first-order TypeScript syntax retained from Foldlab's target backend.
This module owns syntax only. Deterministic source rendering lives in
`Effect4.Target.TypeScript.Render`; typing, lowering, decoding, and simulation
remain separate target layers.

The fragment is intentionally small and grows only for an admitted Effect4
consumer. It is target data, never the denotation or identity of an Effect4
program.
-/

namespace Effect4.Target.TypeScript

/-- Expressions in the retained target fragment. Names and optional type
annotations are target spellings; later typed lowering is responsible for
constructing them from checked Effect4 content. -/
inductive Expr where
  /-- A possibly qualified target reference, such as `Schema.Struct`. -/
  | ident (name : String)
  | str (value : String)
  | int (value : Int)
  | bool (value : Bool)
  | jsNull
  | call (fn : Expr) (args : List Expr)
  | object (fields : List (String × Expr))
  /-- An object whose multiline layout is an explicit syntax choice. -/
  | objectML (fields : List (String × Expr))
  | arr (items : List Expr)
  /-- A zero-parameter arrow with an optional declared result type. -/
  | arrow (returnType : Option String) (body : Expr)
  deriving Inhabited

/-- One statement in the retained straight-line generator fragment. -/
inductive Stmt where
  /-- `const name = yield* value`. -/
  | constYield (name : String) (value : Expr)
  /-- `return value`. -/
  | ret (value : Expr)

/-- An exported constant declaration with an optional target type spelling. -/
structure ConstDecl where
  doc : List String
  name : String
  value : Expr
  type : Option String := none

/-- An exported straight-line Effect generator declaration. -/
structure ProgDecl where
  doc : List String
  name : String
  paramName : String
  paramType : String
  stmts : List Stmt

/-- One declaration in a generated TypeScript module. `raw` is retained only
as the Foldlab compatibility escape hatch for generated local helpers. It is
not admitted as checked Effect4 target syntax and receives no lowering rule. -/
inductive Decl where
  | const (decl : ConstDecl)
  | prog (decl : ProgDecl)
  | raw (text : String)

/-- An import declaration in the retained target fragment. -/
inductive Import where
  | all (name : String) (path : String)
  | named (names : List String) (path : String)
  | types (names : List String) (path : String)

/-- A generated TypeScript module. -/
structure Module where
  header : List String
  imports : List Import
  decls : List Decl

end Effect4.Target.TypeScript
