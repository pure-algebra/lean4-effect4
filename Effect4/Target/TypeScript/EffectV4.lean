import TypeScript
import Effects.Family

/-!
# Target.TypeScript.EffectV4

The pinned Effect v4 target profile: how a Lean `Effects.Family` becomes a
`Context.Service` class, how a first-order straight-line script becomes an
`Effect.gen` program, and what an LLM is told about both. Everything here is
a pure function over first-order rows; the rows are what `effect_signature`
and `effect_program` (`Effect4/Meta/Derive.lean`) emit beside the algebra.

Idiom pins, stated once:

| Algebra | Effect v4 |
| --- | --- |
| `Family` | `class X extends Context.Service<X, Shape>()("X") {}` |
| `Family.perform name param` | `yield* x.name(param)`; nullary: `yield* x.name` (an Effect value) |
| `Handler.sum` | `Layer.merge` |
| `Handler.mapHom (interpretHom lower)` (= `through`) | `Layer.provide` |
| `StateT` transport | `Ref` |

Host pin: `hostPin` below; generated modules cite it in their header.
-/

open TypeScript

namespace Effect4.Target.EffectV4

/-- The exact host this profile is checked against. -/
def hostPin : HostPin :=
  { typescript := "7.0.2"
    languageService := some "@effect/tsgo@0.38.0"
    runtime := "node 22 --experimental-strip-types"
    libraries := ["effect@4.0.0-rc.112"] }

/-! ## First-order rows -/

/-- One operation as data: Lean and TypeScript spellings side by side, and
the natural-language cues bound to it. -/
structure OpRow where
  name : String
  index : Nat
  /-- binder, Lean type spelling -/
  params : List (String × String)
  /-- binder, TypeScript type spelling -/
  tsParams : List (String × String)
  answer : String
  tsAnswer : String
  cues : List String := []
  deriving Repr, BEq, Inhabited

/-- One family as data. The Lean name is the Effect service class name. -/
structure ServiceRow where
  name : String
  ops : List OpRow
  deriving Repr, BEq, Inhabited

namespace ServiceRow

def row? (rows : ServiceRow) (op : String) : Option OpRow :=
  rows.ops.find? fun row => row.name == op

/-- The receiver a lowered program binds the service to. -/
def receiver (rows : ServiceRow) : String :=
  rows.name.decapitalize

/-- `(params) => Effect.Effect<Answer>`; a nullary operation is an Effect
value, `Effect.Effect<Answer>`, because Effect is already lazy (tsgo rule
`lazyEffect`). -/
def methodType (row : OpRow) : String :=
  if row.tsParams.isEmpty then "Effect.Effect<" ++ row.tsAnswer ++ ">"
  else
    let params := String.intercalate ", " (row.tsParams.map fun (x, t) => x ++ ": " ++ t)
    "(" ++ params ++ ") => Effect.Effect<" ++ row.tsAnswer ++ ">"

/-- The service shape, one readonly method per operation. -/
def shapeType (rows : ServiceRow) : String :=
  "{\n" ++
    String.intercalate "\n"
      (rows.ops.map fun row => "  readonly " ++ row.name ++ ": " ++ methodType row) ++
    "\n}"

/-- `export class X extends Context.Service<X, Shape>()("X") {}`. -/
def classDecl (rows : ServiceRow) : Decl :=
  .classDecl
    { doc := ["Service `" ++ rows.name ++ "`: one method per operation of the Lean family."]
      name := rows.name
      heritage := some (.call (.call (.generic (.ident "Context.Service")
        [rows.name, rows.shapeType]) []) [.str rows.name]) }

/-- What an LLM is told, rendered from the rows it will be checked against. -/
def sheet (rows : ServiceRow) : String :=
  let recv := rows.receiver
  let opLine (row : OpRow) : String :=
    let args := String.intercalate ", " (row.tsParams.map (·.1))
    let cue := String.intercalate ", " row.cues
    "- `" ++ row.name ++ "` (operation " ++ toString row.index ++ "; say: " ++ cue ++
      "): `const x = yield* " ++ recv ++ "." ++ row.name ++ "(" ++ args ++ ")` returns `" ++
      row.tsAnswer ++ "`."
  String.intercalate "\n"
    ([ "# Writing programs over `" ++ rows.name ++ "`"
     , ""
     , "Acquire the service once at the top of an `Effect.gen` block: `const " ++ recv ++
         " = yield* " ++ rows.name ++ "`."
     , "Perform operations only through that receiver, only with `yield*`, one per statement."
     , "Pure work goes in named atoms already in scope; no inline arithmetic, no `await`, no `try`, no casts."
     , ""
     , "Operations:" ] ++ rows.ops.map opLine ++
     [ ""
     , "Every program is checked back: each `yield*` is tagged against these operations, unknown"
     , "tokens are refused, and the order of tags must match the declared script." ])

end ServiceRow

/-! ## Straight-line scripts -/

/-- The admitted pure fragment at the lowering face: variables, literals, and
named pure atoms. No inline arithmetic; an atom is a name already in scope. -/
inductive PureTerm where
  | var (name : String)
  | nat (value : Nat)
  | str (value : String)
  | app (atom : String) (args : List PureTerm)
  deriving Inhabited

-- `PureTerm` is a nested inductive; Lean's `BEq` and `Repr` deriving handlers
-- use a partial helper for it, which the source trust gate refuses. These
-- structural recursions keep both instances total.
mutual
  def instBEqPureTerm.beq (self other : PureTerm) : Bool :=
    match self, other with
    | .var a, .var b | .str a, .str b => a == b
    | .nat a, .nat b => a == b
    | .app f xs, .app g ys => f == g && beqPureTermList xs ys
    | _, _ => false
  termination_by structural self

  private def beqPureTermList (self other : List PureTerm) : Bool :=
    match self, other with
    | [], [] => true
    | a :: xs, b :: ys => instBEqPureTerm.beq a b && beqPureTermList xs ys
    | _, _ => false
  termination_by structural self
end

instance instBEqPureTerm : BEq PureTerm := ⟨instBEqPureTerm.beq⟩

mutual
  def PureTerm.render : PureTerm → String
    | .var name => name
    | .nat value => toString value
    | .str value => "\"" ++ value ++ "\""
    | .app atom args => atom ++ "(" ++ PureTerm.renderList args ++ ")"
  termination_by structural t => t

  def PureTerm.renderList : List PureTerm → String
    | [] => ""
    | [one] => PureTerm.render one
    | first :: rest => PureTerm.render first ++ ", " ++ PureTerm.renderList rest
  termination_by structural ts => ts
end

instance : Repr PureTerm := ⟨fun term _ => Std.Format.text term.render⟩

namespace PureTerm

def lower : PureTerm → Expr
  | .var name => .ident name
  | .nat value => .int value
  | .str value => .str value
  | .app atom args => .call (.ident atom) (lowerAll args)
where
  lowerAll : List PureTerm → List Expr
    | [] => []
    | first :: rest => lower first :: lowerAll rest

end PureTerm

/-- One step: bind (or discard) the answer of an operation, or return. -/
inductive Step where
  | perform (bind : String) (op : String) (args : List PureTerm)
  | ret (value : PureTerm)
  deriving Repr, BEq, Inhabited

/-- A first-order straight-line program over one family. -/
structure Script where
  family : String
  name : String
  /-- binder, TypeScript type spelling -/
  param : String × String
  steps : List Step
  deriving Repr, BEq, Inhabited

namespace Script

/-- Refuse unknown operations and arity mismatches at the first-order face;
otherwise lower into the straight-line generator fragment. A bind spelled
with a leading underscore discards its answer. -/
def lower (rows : ServiceRow) (script : Script) : Option ProgDecl := do
  guard (script.family == rows.name)
  let recv := rows.receiver
  let mut stmts : List Stmt := [.constYield recv (.ident rows.name)]
  for step in script.steps do
    match step with
    | .perform bind op args =>
        let row ← rows.row? op
        guard (row.params.length == args.length)
        let call : Expr :=
          if row.params.isEmpty then .ident (recv ++ "." ++ op)
          else .call (.ident (recv ++ "." ++ op)) (args.map PureTerm.lower)
        stmts := stmts ++ [if bind.startsWith "_" then .yieldDiscard call else .constYield bind call]
    | .ret value =>
        stmts := stmts ++ [.ret value.lower]
  pure { doc := ["Lowered from `" ++ script.name ++ "` over `" ++ script.family ++ "`."]
         name := script.name
         paramName := script.param.1
         paramType := script.param.2
         stmts }

end Script

/-! ## Modules -/

/-- The generated module: header with the host pin, the `effect` import, the
service class, and the lowered programs. -/
def module (rows : ServiceRow) (programs : List ProgDecl)
    (atoms : List Import := []) : Module :=
  { header := ["Generated by Effect4 (Effect v4 profile).", ""] ++ hostPin.headerLines ++
      ["", "Do not edit."]
    imports := .named ["Context", "Effect"] "effect" :: atoms
    decls := rows.classDecl :: programs.map Decl.prog }

/-- Lower every script; `none` if any script is refused. `atoms` imports the
named pure atoms the scripts call. -/
def module? (rows : ServiceRow) (scripts : List Script)
    (atoms : List Import := []) : Option Module := do
  let programs ← scripts.mapM (Script.lower rows)
  pure (module rows programs atoms)

def source? (rows : ServiceRow) (scripts : List Script)
    (atoms : List Import := []) (style : Style := house0) : Option String :=
  (module? rows scripts atoms).map (Render.module style)

end Effect4.Target.EffectV4
