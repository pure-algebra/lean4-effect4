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
  /-- A JavaScript number reconstructed from an exact IEEE-754 binary64 bit
  pattern. This avoids lossy decimal formatting in generated raw data. -/
  | float64Bits (bits : UInt64)
  | bool (value : Bool)
  | jsNull
  | call (fn : Expr) (args : List Expr)
  | object (fields : List (String × Expr))
  /-- An object whose multiline layout is an explicit syntax choice. -/
  | objectML (fields : List (String × Expr))
  /-- An object whose property names are data and are therefore always quoted. -/
  | objectQuoted (fields : List (String × Expr))
  /-- A quoted-key object whose multiline layout is explicit syntax. -/
  | objectQuotedML (fields : List (String × Expr))
  /-- A data-keyed object built from retained entries. Used when JavaScript
  object-literal semantics would reinterpret a key such as `__proto__`. -/
  | objectFromEntries (fields : List (String × Expr))
  | arr (items : List Expr)
  /-- A zero-parameter arrow with an optional declared result type. -/
  | arrow (returnType : Option String) (body : Expr)
  deriving Inhabited

-- Keep the existing equality API total. Lean's BEq deriving handler uses a
-- partial helper for nested inductives; these four structural recursions
-- traverse the expression and its nested lists without that trust boundary.
mutual
  def instBEqExpr.beq (self other : Expr) : Bool :=
    match self, other with
    | .ident a, .ident b | .str a, .str b => a == b
    | .int a, .int b => a == b
    | .float64Bits a, .float64Bits b => a == b
    | .bool a, .bool b => a == b
    | .jsNull, .jsNull => true
    | .call f xs, .call g ys => instBEqExpr.beq f g && beqExprList xs ys
    | .object xs, .object ys | .objectML xs, .objectML ys
    | .objectQuoted xs, .objectQuoted ys | .objectQuotedML xs, .objectQuotedML ys
    | .objectFromEntries xs, .objectFromEntries ys => beqExprFields xs ys
    | .arr xs, .arr ys => beqExprList xs ys
    | .arrow ty a, .arrow ty' b => ty == ty' && instBEqExpr.beq a b
    | _, _ => false
  termination_by structural self

  private def beqExprList (self other : List Expr) : Bool :=
    match self, other with
    | [], [] => true
    | a :: xs, b :: ys => instBEqExpr.beq a b && beqExprList xs ys
    | _, _ => false
  termination_by structural self

  private def beqExprFields (self other : List (String × Expr)) : Bool :=
    match self, other with
    | [], [] => true
    | a :: xs, b :: ys => beqExprField a b && beqExprFields xs ys
    | _, _ => false
  termination_by structural self

  private def beqExprField (self other : String × Expr) : Bool :=
    self.1 == other.1 && instBEqExpr.beq self.2 other.2
  termination_by structural self
end

instance instBEqExpr : BEq Expr := ⟨instBEqExpr.beq⟩

/-- One statement in the retained straight-line generator fragment. -/
inductive Stmt where
  /-- `const name = yield* value`. -/
  | constYield (name : String) (value : Expr)
  /-- `return value`. -/
  | ret (value : Expr)
  deriving BEq

/-- An exported constant declaration with an optional target type spelling. -/
structure ConstDecl where
  doc : List String
  name : String
  value : Expr
  type : Option String := none
  deriving BEq

/-- An exported straight-line Effect generator declaration. -/
structure ProgDecl where
  doc : List String
  name : String
  paramName : String
  paramType : String
  stmts : List Stmt
  deriving BEq

/-- One checked effectful Schema field API. This target-only node retains all
directional types needed by the Effect v4 renderer without storing host
functions or falling back to raw source text. -/
structure EffectfulFieldDecl where
  fieldName : String
  sourceType : String
  fieldType : String
  readService : String
  readMethod : String
  readError : String
  writeService : String
  writeMethod : String
  writeError : String
  deriving BEq

/-- One declaration in a generated TypeScript module. `raw` is retained only
as the Foldlab compatibility escape hatch for generated local helpers. It is
not admitted as checked Effect4 target syntax and receives no lowering rule. -/
inductive Decl where
  | const (decl : ConstDecl)
  | prog (decl : ProgDecl)
  | effectfulField (declaration : EffectfulFieldDecl)
  | raw (text : String)
  deriving BEq

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
