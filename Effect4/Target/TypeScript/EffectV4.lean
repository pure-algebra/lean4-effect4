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

namespace Lowering

/-- An aborting operation's method carries its error in `E`:
`Effect.Effect<A, E>`. The family's answer stays `A`; the handler kind is
`X.Service (ExceptT E M)`. lowering: rule.error-abort -/
def errorAbort (answer error : String) : String :=
  "Effect.Effect<" ++ answer ++ ", " ++ error ++ ">"

end Lowering

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
  let effect := match row.error with
    | some (_, e) => Lowering.errorAbort row.tsAnswer e
    | none => "Effect.Effect<" ++ row.tsAnswer ++ ">"
  if row.tsParams.isEmpty then effect
  else
    let params := String.intercalate ", " (row.tsParams.map fun (x, t) => x ++ ": " ++ t)
    "(" ++ params ++ ") => " ++ effect

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

/-- `export const XRows = { "get": { params: 0, answer: "number" }, … }`: the
operation rows as data. The trace harness reads arities from it and records
answers *as typed*: a `void` answer encodes as unit whatever the host returns
(rc.112's `Ref.set` returns the mutable ref at runtime under a `void` type). -/
def rowsDecl (rows : ServiceRow) : Decl :=
  .const
    { doc := ["Operation rows of `" ++ rows.name ++ "`, for the trace harness."]
      name := rows.name ++ "Rows"
      value := .objectQuoted (rows.ops.map fun row =>
        (row.name, .object [("params", .int row.params.length), ("answer", .str row.tsAnswer)])) }

/-- Whether any spelling names `Result.Result`, so the module imports it. -/
def usesResult (rows : ServiceRow) : Bool :=
  rows.ops.any fun row =>
    row.tsAnswer.startsWith "Result." || row.tsParams.any fun p => p.2.startsWith "Result."

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

/-- One step: bind the answer of an operation (`some name`), discard it
(`none`), or return. -/
inductive Step where
  | perform (bind : Option String) (op : String) (args : List PureTerm)
  | ret (value : PureTerm)
  deriving Repr, BEq, Inhabited

/-- A first-order straight-line program over one family. -/
structure Script where
  family : String
  name : String
  /-- binder, TypeScript type spelling -/
  param : String × String
  /-- TypeScript spelling of the result -/
  result : String := "unknown"
  steps : List Step
  deriving Repr, BEq, Inhabited

namespace Script

/-- The operations a script performs, in order. This is the script's half of
the per-program receipt `effect_program` emits (`Effect4/Meta/Derive.lean`):
the elaborator builds a program and a script from the same steps, and nothing
else relates the two. -/
def operationNames (script : Script) : List String :=
  script.steps.filterMap fun step =>
    match step with
    | .perform _ op _ => some op
    | .ret _ => none

end Script

/-- The operations a first-order program performs, in order, read off the
program itself. Every operation is answered by `answer`, which the
straight-line fragment `effect_program` admits never branches on: it has no
`if`, no `match`, and no operation whose continuation depends on the answer
except through the pure terms of later requests.

This is the program's half of the per-program receipt. It is not a claim about
programs in general: a program that branched on an answer would perform other
operations under another answer, and the receipt would say only what this
`answer` sees. -/
def performedNames {F : Effects.Family.{0, 0, 0}} {A : Type}
    (spelling : F.Name → String) (answer : (name : F.Name) → F.Answer name) :
    Effects.Program F.toSignature A → List String
  | .pure _ => []
  | .vis operation next =>
      spelling operation.1 :: performedNames spelling answer (next (answer operation.1))
  termination_by structural program => program

namespace Script

/-- Refuse unknown operations and arity mismatches at the first-order face;
otherwise lower into the straight-line generator fragment. A step without a
bind discards its answer. -/
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
          [match bind with
           | none => Lowering.performDiscard call
           | some name => Lowering.performBind name call]
    | .ret value =>
        stmts := stmts ++ [Lowering.ret value.lower]
  pure { doc := ["Lowered from `" ++ script.name ++ "` over `" ++ script.family ++ "`."]
         name := script.name
         paramName := script.param.1
         paramType := script.param.2
         stmts }

/-- The error channel of a script: the union of the error spellings of the
operations it performs, in first-use order; `never` when none. -/
def errorChannel (rows : ServiceRow) (script : Script) : String :=
  let spellings := script.steps.foldl (init := ([] : List String)) fun acc step =>
    match step with
    | .perform _ op _ =>
        match (rows.row? op).bind (·.error) with
        | some (_, e) => if acc.contains e then acc else acc ++ [e]
        | none => acc
    | .ret _ => acc
  if spellings.isEmpty then "never" else String.intercalate " | " spellings

/-- The declaration line the pinned compiler must emit for the lowered
program: its A, E and R channels as `tsc --declaration` prints them. This is
the type receipt a golden carries (`docs/LOWERING-COVERAGE.md`). -/
def declarationLine (rows : ServiceRow) (script : Script) : String :=
  "export declare const " ++ script.name ++ ": (" ++ script.param.1 ++ ": " ++ script.param.2 ++
    ") => Effect.Effect<" ++ script.result ++ ", " ++ script.errorChannel rows ++ ", " ++
    script.family ++ ">;"

end Script

/-! ## Modules -/

/-- The generated module: header with the host pin, the `effect` import, the
service class, and the lowered programs. -/
def module (rows : ServiceRow) (programs : List ProgDecl)
    (atoms : List Import := []) : Module :=
  { header := ["Generated by Effect4 (Effect v4 profile).", ""] ++ hostPin.headerLines ++
      ["", "Do not edit."]
    imports := .named (["Context", "Effect"] ++ (if rows.usesResult then ["Result"] else [])) "effect" :: atoms
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

/-- One module declaring several families, each with its scripts. -/
def modules? (families : List (ServiceRow × List Script))
    (atoms : List Import := []) (style : Style := house0) : Option String := do
  let decls ← families.mapM fun (rows, scripts) => do
    let programs ← scripts.mapM (Script.lower rows)
    pure (rows.classDecl :: rows.rowsDecl :: programs.map Decl.prog)
  let result := families.any fun (rows, _) => rows.usesResult
  let target : Module :=
    { header := ["Generated by Effect4 (Effect v4 profile).", ""] ++ hostPin.headerLines ++
        ["", "Do not edit."]
      imports := .named (["Context", "Effect"] ++ (if result then ["Result"] else [])) "effect" :: atoms
      decls := decls.flatten }
  pure (Render.module style target)

end Effect4.Target.EffectV4
