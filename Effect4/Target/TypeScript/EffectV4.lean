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
  /-- A pure atom: lowered as a plain call, excluded from traces by mask. -/
  pure : Bool := false
  /-- The aborting error reading: Lean and TypeScript spellings of `E`. -/
  error : Option (String × String) := none
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

/-- `export const XRows = { "get": { params: 0 }, "put": { params: 1 } }`: the
operation rows as data, read by the trace harness for arities. -/
def rowsDecl (rows : ServiceRow) : Decl :=
  .const
    { doc := ["Operation rows of `" ++ rows.name ++ "`, for the trace harness."]
      name := rows.name ++ "Rows"
      value := .objectQuoted (rows.ops.map fun row =>
        (row.name, .object [("params", .int row.params.length)])) }

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

/-! ## Lowering rules

One definition per rule, each tagged `lowering: rule.<name>` in its docstring.
`docs/LOWERING-COVERAGE.md` owns the vocabulary; the ledger joins evidence to
these tags, so a rule is exactly the code below its tag. -/

namespace Lowering

/-- Acquire the service once at the top of the generator:
`const cell = yield* Cell`. lowering: rule.service-acquire -/
def serviceAcquire (rows : ServiceRow) : Stmt :=
  .constYield rows.receiver (.ident rows.name)

/-- A pure atom applied to lowered arguments: `succ(x)`.
lowering: rule.atom-call -/
def atomCall (atom : String) (args : List Expr) : Expr :=
  .call (.ident atom) args

/-- A nullary operation is an Effect value, `cell.get`, not a call.
lowering: rule.nullary-value -/
def nullaryValue (recv op : String) : Expr :=
  .ident (recv ++ "." ++ op)

/-- An operation with arguments is a method call, `cell.put(n)`.
lowering: rule.perform-call -/
def performCall (recv op : String) (args : List Expr) : Expr :=
  .call (.ident (recv ++ "." ++ op)) args

/-- Bind an operation's answer: `const x = yield* cell.get`.
lowering: rule.perform-bind -/
def performBind (bind : String) (call : Expr) : Stmt :=
  .constYield bind call

/-- Discard an operation's answer: `yield* cell.put(n)`.
lowering: rule.perform-discard -/
def performDiscard (call : Expr) : Stmt :=
  .yieldDiscard call

/-- Return the program's value: `return y`. lowering: rule.ret -/
def ret (value : Expr) : Stmt :=
  .ret value

end Lowering

namespace PureTerm

/-- Whether a pure term applies an atom anywhere. -/
def hasApp : PureTerm → Bool
  | .app .. => true
  | _ => false

def lower : PureTerm → Expr
  | .var name => .ident name
  | .nat value => .int value
  | .str value => .str value
  | .app atom args => Lowering.atomCall atom (lowerAll args)
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
  let mut stmts : List Stmt := [Lowering.serviceAcquire rows]
  for step in script.steps do
    match step with
    | .perform bind op args =>
        let row ← rows.row? op
        guard (row.params.length == args.length)
        let call : Expr :=
          if row.params.isEmpty then Lowering.nullaryValue recv op
          else Lowering.performCall recv op (args.map PureTerm.lower)
        stmts := stmts ++
          [if bind.startsWith "_" then Lowering.performDiscard call else Lowering.performBind bind call]
    | .ret value =>
        stmts := stmts ++ [Lowering.ret value.lower]
  pure { doc := ["Lowered from `" ++ script.name ++ "` over `" ++ script.family ++ "`."]
         name := script.name
         paramName := script.param.1
         paramType := script.param.2
         stmts }

/-- The lowering rule ids a script exercises, in first-use order. The ledger
(`docs/LOWERING-COVERAGE.md`) joins goldens to rules through this list. -/
def rules (rows : ServiceRow) (script : Script) : List String :=
  let step (acc : List String) (id : String) : List String :=
    if acc.contains id then acc else acc ++ [id]
  let atoms (acc : List String) (term : PureTerm) : List String :=
    if term.hasApp then step acc "atom-call" else acc
  script.steps.foldl (init := ["service-acquire"]) fun acc s =>
    match s with
    | .perform bind op args =>
        let nullary := (rows.row? op).map (·.params.isEmpty) |>.getD false
        let acc := step acc (if nullary then "nullary-value" else "perform-call")
        let acc := step acc (if bind.startsWith "_" then "perform-discard" else "perform-bind")
        args.foldl atoms acc
    | .ret value => atoms (step acc "ret") value

end Script

/-! ## Modules -/

/-- The generated module: header with the host pin, the `effect` import, the
service class, and the lowered programs. -/
def module (rows : ServiceRow) (programs : List ProgDecl)
    (atoms : List Import := []) : Module :=
  { header := ["Generated by Effect4 (Effect v4 profile).", ""] ++ hostPin.headerLines ++
      ["", "Do not edit."]
    imports := .named ["Context", "Effect"] "effect" :: atoms
    decls := rows.classDecl :: rows.rowsDecl :: programs.map Decl.prog }

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
