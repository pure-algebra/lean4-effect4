import TypeScript
import Effects.Family
import Effects.Trace

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

/-! ## The answer-type profile

The type spellings both faces know, reified. `effect_signature` parses Lean
type syntax into a `Spelling` (`Effect4/Meta/Derive.lean`) and every face reads
it from here: `render` is the TypeScript spelling, `wireDefault` the wire
inhabitant, `depth` the admission measure. Nothing outside this inductive is a
legal parameter, answer or atom type, so the host decoder in
`harness/trace/tracer.ts` is a finite case analysis over the same grammar.

Frozen by `test/contracts/answer-profile.contract.md`. -/

/-- One admitted type spelling. rc.112 has no `Either`: an `Except E A` answer
is the data reading `Result.Result<A, E>`. `handle` is an opaque host object
(`Effect4.Meta.Handle`), whose wire value is a stable index and whose target
spelling is carried verbatim. -/
inductive Spelling where
  | nat
  | int
  | string
  | bool
  | unit
  | handle (target : String)
  | option (inner : Spelling)
  | list (inner : Spelling)
  | except (error value : Spelling)
  | prod (left right : Spelling)
  deriving DecidableEq, Repr, Inhabited

namespace Spelling

/-- The TypeScript spelling. -/
def render : Spelling → String
  | .nat | .int => "number"
  | .string => "string"
  | .bool => "boolean"
  | .unit => "void"
  | .handle target => target
  | .option inner => "Option.Option<" ++ render inner ++ ">"
  | .list inner => "ReadonlyArray<" ++ render inner ++ ">"
  | .except error value => "Result.Result<" ++ render value ++ ", " ++ render error ++ ">"
  | .prod left right => "readonly [" ++ render left ++ ", " ++ render right ++ "]"

/-- Constructor nesting: a base type, a handle included, is depth one. -/
def depth : Spelling → Nat
  | .nat | .int | .string | .bool | .unit | .handle _ => 1
  | .option inner | .list inner => 1 + depth inner
  | .except left right | .prod left right => 1 + max (depth left) (depth right)

/-- The arity of a spelling read as a tuple: a right-nested product of `n`
components has arity `n`, and everything else arity one. This is what an
operation of `n` parameters packs its request into and what the host call
unpacks again; the tracer needs it on an answer because an opaque `Handle`
target is outside the wire grammar, so `readonly [JobQueue, number]` cannot be
parsed back into a pair on that face. -/
def arity : Spelling → Nat
  | .prod _ right => 1 + arity right
  | _ => 1

/-- The deepest nesting the profile admits. Depth three is
`Option (Except E A)`, `Except E (Option A)`, `List (A × B)`, `Option (A × B)`
and `A × Except E B`; depth four is refused. -/
def profileDepth : Nat := 3

/-- Whether the profile admits this spelling. -/
def admitted (spelling : Spelling) : Bool := spelling.depth <= profileDepth

/-- The wire inhabitant of a spelling: what a face answers when it has nothing
else to answer. `Effects.Trace.ToVal` of the `Inhabited` default of the Lean
type with this spelling is exactly this value, which is what makes the
per-program receipt's `X.answerDefault` and this agree. -/
def wireDefault : Spelling → Effects.Trace.Val
  | .nat | .handle _ => .nat 0
  | .int => .int 0
  | .string => .str ""
  | .bool => .bool false
  | .unit => .unit
  | .option _ => .none
  | .list _ => .unit
  -- Lean's `Inhabited (Except ε α)` is `Except.error default`, so the wire
  -- inhabitant of a `Result` spelling is its failure side.
  | .except error _ => .pair (.bool false) (wireDefault error)
  | .prod left right => .pair (wireDefault left) (wireDefault right)

/-- Whether a rendered spelling mentions a namespace of the `effect` package,
at any nesting depth. `Option.Option<Result.Result<number, string>>` mentions
both, so a module carrying it imports both. -/
def mentions (needle haystack : String) : Bool := (haystack.splitOn needle).length > 1

/-- The `effect` namespaces a list of rendered spellings needs, in import
order.

The needle list is fixed and alphabetical, so the import line is a function of
the spellings and nothing else. `Exit` and `Fiber` join `Option` and `Result`
here because the region rows spell `Exit.Exit<unknown, unknown>`
(`RegionLower.lean`, `regionsRows`) and the fiber profile spells
`Fiber.Fiber<A, E>` (`FiberProfile.lean`, `handleTy`); before this they were
added by hand at the module emitter, or not at all. Adding one is safe for a
module that does not name it -- the test is by occurrence -- and a caller that
already binds the name in its own imports subtracts it through
`neededNamespaces`, which is how the harness's `Fibers` and `Deferreds`
fixtures import `Fiber`, `Option` and `Result` as types only. -/
def namespacesOf (spellings : List String) : List String :=
  ["Exit", "Fiber", "Option", "Result"].filter fun name =>
    spellings.any (mentions (name ++ "."))

end Spelling

/-! ## The binding profile

`TypeScript.reservedIdentifiers` (lean4-typescript v0.4.2) is the shared list;
these are the words it does not carry and this profile still refuses. They are
checked here rather than in the pinned package so the DSL can refuse them
today. -/

/-- Reserved and predefined names missing from
`TypeScript.reservedIdentifiers`. -/
def reservedExtra : List String :=
  ["arguments", "eval", "undefined", "NaN", "Infinity"]

/-- A legal generated binding name for an operation or an atom. -/
def bindingName (name : String) : Bool :=
  TypeScript.targetIdentifier name && !(reservedExtra.contains name)

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
  /-- `Spelling.arity` of the answer: `1` unless the answer is a product. A row
  that answers a tuple carries it to the host tracer, which cannot always read
  the arity back out of the spelling. -/
  answerArity : Nat := 1
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
(rc.112's `Ref.set` returns the mutable ref at runtime under a `void` type).

`answerArity` is written only when the answer is a tuple, so a row that answers
one value is spelled exactly as it was before the field existed and every
pre-existing fixture stays byte-identical. -/
def rowsDecl (rows : ServiceRow) : Decl :=
  .const
    { doc := ["Operation rows of `" ++ rows.name ++ "`, for the trace harness."]
      name := rows.name ++ "Rows"
      value := .objectQuoted (rows.ops.map fun row =>
        (row.name, .object ([("params", .int row.params.length), ("answer", .str row.tsAnswer)] ++
          (if row.answerArity > 1 then [("answerArity", .int row.answerArity)] else [])))) }

/-- Every TypeScript spelling the rows mention, answers and parameters. -/
def spellings (rows : ServiceRow) : List String :=
  rows.ops.flatMap fun row => row.tsAnswer :: row.tsParams.map (·.2)

/-- The `effect` namespaces the module needs beside `Context` and `Effect`. A
depth-three spelling nests them, so this is a substring test, not a prefix
test: `Option.Option<Result.Result<number, string>>` needs both. -/
def namespaces (rows : ServiceRow) : List String :=
  Spelling.namespacesOf rows.spellings

/-- Whether any spelling names `Result.Result`, at any depth. -/
def usesResult (rows : ServiceRow) : Bool :=
  rows.namespaces.contains "Result"

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

/-- The names a supplied import list already binds. The module's own `effect`
import must not re-bind one of them: a caller that already imports `Option` as
a type-only binding would otherwise get a duplicate identifier. -/
def importedNames : List Import → List String
  | [] => []
  | .all name _ :: rest => name :: importedNames rest
  | .named names _ :: rest => names ++ importedNames rest
  | .types names _ :: rest => names ++ importedNames rest

/-- The `effect` namespaces a module must import for its own rows, minus the
ones the supplied imports already bind. -/
def neededNamespaces (spellings : List String) (atoms : List Import) : List String :=
  let bound := importedNames atoms
  (Spelling.namespacesOf spellings).filter fun name => !bound.contains name

/-- The `effect` namespaces a generated *flow* module needs: the ones the rows
it declares actually spell, minus the ones its supplied imports already bind.

`declared` is every `ServiceRow` the module emits a class for -- the families,
and `Decisions`, `Regions` and `Interrupts` exactly when they are declared. That
is what makes the import line a function of the module's own text: `Exit` arrives
with the `Regions` class, which is the only row that spells it, rather than from
a separate `if regions` at the emitter; `Result`, `Option` and `Fiber` arrive
with whichever family row spells them. A module that names none of them imports
`Context` and `Effect` and nothing else, exactly as before. -/
def moduleNamespaces (declared : List ServiceRow) (atoms : List Import) : List String :=
  neededNamespaces (declared.flatMap ServiceRow.spellings) atoms

/-- The generated module: header with the host pin, the `effect` import, the
service class, and the lowered programs. -/
def module (rows : ServiceRow) (programs : List ProgDecl)
    (atoms : List Import := []) : Module :=
  { header := ["Generated by Effect4 (Effect v4 profile).", ""] ++ hostPin.headerLines ++
      ["", "Do not edit."]
    imports := .named (["Context", "Effect"] ++ neededNamespaces rows.spellings atoms) "effect" :: atoms
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
  let needed := neededNamespaces (families.flatMap fun (rows, _) => rows.spellings) atoms
  let target : Module :=
    { header := ["Generated by Effect4 (Effect v4 profile).", ""] ++ hostPin.headerLines ++
        ["", "Do not edit."]
      imports := .named (["Context", "Effect"] ++ needed) "effect" :: atoms
      decls := decls.flatten }
  pure (Render.module style target)

/-! ## Pure atoms

An atom is declared once, by `effect_atoms` (`Effect4/Meta/Derive.lean`), and
both faces are projections of the row: the Lean function and the wire
dispatcher on one side, `atoms.ts` on the other. Declaring an atom in one face
only is `E4-TARGET-CE-025`. -/

/-- One pure atom as data: the binder and its two type spellings, the Lean
answer spelling, and the host body as a single TypeScript expression over the
binder. -/
structure AtomRow where
  name : String
  binder : String
  /-- Lean type spelling of the argument -/
  request : String
  /-- TypeScript type spelling of the argument -/
  tsRequest : String
  /-- Lean type spelling of the answer -/
  answer : String
  /-- TypeScript type spelling of the answer -/
  tsAnswer : String
  /-- One TypeScript expression over `binder`. -/
  body : String
  /-- A multi-parameter atom's parameters, name and TypeScript spelling each;
  empty for the one-parameter form, whose parameter is `binder : tsRequest`. -/
  params : List (String × String) := []
  deriving Repr, BEq, Inhabited

namespace AtomRow

/-- `export const succ = (n: number): number => n + 1`. -/
def constSource (row : AtomRow) : String :=
  "/** Host body of the pure atom `" ++ row.name ++ "`; its Lean model is `" ++
    row.name ++ "`. */\n" ++
  "export const " ++ row.name ++ " = (" ++
    (if row.params.isEmpty then row.binder ++ ": " ++ row.tsRequest
     else String.intercalate ", " (row.params.map fun (name, ty) => name ++ ": " ++ ty)) ++ "): " ++
    row.tsAnswer ++ " => " ++ row.body ++ "\n"

/-- The row as the flow embedding reads it: name, request, answer. -/
def entry (row : AtomRow) : String × String × String :=
  (row.name, row.tsRequest, row.tsAnswer)

end AtomRow

/-- The generated `atoms.ts`: the same header and import layout as `module`,
then one exported constant per row. `hostTypes` are the opaque host types an
atom's spelling names: a `Handle "T"` target is outside the `effect`
namespaces, so the declaration site says which module it comes from. -/
def atomsModule (rows : List AtomRow) (hostTypes : List Import := [])
    (style : Style := house0) : String :=
  let needed := neededNamespaces
    (rows.flatMap fun row => [row.tsRequest, row.tsAnswer] ++ row.params.map (·.2)) hostTypes
  let header := ["Generated by Effect4 (Effect v4 profile).", ""] ++ hostPin.headerLines ++
    ["", "The pure atoms of the harness, declared by `effect_atoms`.", "", "Do not edit."]
  "/**\n" ++ String.intercalate "\n"
      (header.map fun line => if line.isEmpty then " *" else " * " ++ line) ++
    "\n */\n" ++
    (if needed.isEmpty then ""
     else "import { " ++ String.intercalate ", " needed ++ " } from \"effect\"\n") ++
    String.join (hostTypes.map (Render.import_ style)) ++
    "\n" ++ String.intercalate "\n" (rows.map AtomRow.constSource)

/-! ## Decoding the wire

`Effects.Trace.ToVal` encodes; this decodes, so a generated atom dispatcher can
run a Lean atom on a wire value. Every instance is the exact inverse of the
`ToVal` instance for the same type. This is the encoding's converse the DSL had
no carrier for (row `E4-TARGET-CE-016`); it is a partial function, so it closes
nothing about `denoteScript` on its own. -/

/-- Read a wire value back at a profile type. -/
class OfVal (α : Type) where
  ofVal : Effects.Trace.Val → Option α

namespace OfVal

instance : OfVal Effects.Trace.Val := ⟨Option.some⟩
instance : OfVal Unit := ⟨fun value => match value with | .unit => Option.some () | _ => Option.none⟩
instance : OfVal Nat := ⟨fun value => match value with | .nat n => Option.some n | _ => Option.none⟩
instance : OfVal Int := ⟨fun value => match value with | .int i => Option.some i | _ => Option.none⟩
instance : OfVal Bool := ⟨fun value => match value with | .bool b => Option.some b | _ => Option.none⟩
instance : OfVal String := ⟨fun value => match value with | .str s => Option.some s | _ => Option.none⟩

instance [OfVal α] [OfVal β] : OfVal (α × β) :=
  ⟨fun value => match value with
    | .pair left right => do
        let a ← OfVal.ofVal left
        let b ← OfVal.ofVal right
        Option.some (a, b)
    | _ => Option.none⟩

instance [OfVal α] : OfVal (Option α) :=
  ⟨fun value => match value with
    | .none => Option.some Option.none
    | .some inner => (OfVal.ofVal inner).map Option.some
    | _ => Option.none⟩

instance [OfVal ε] [OfVal α] : OfVal (Except ε α) :=
  ⟨fun value => match value with
    | .pair (.bool false) error => (OfVal.ofVal error).map Except.error
    | .pair (.bool true) ok => (OfVal.ofVal ok).map Except.ok
    | _ => Option.none⟩

/-- A list is right-nested pairs closed by `unit`, exactly as `ToVal` writes
it. -/
def ofValList [OfVal α] : Effects.Trace.Val → Option (List α)
  | .unit => Option.some []
  | .pair head tail => do
      let a ← OfVal.ofVal head
      let rest ← ofValList tail
      Option.some (a :: rest)
  | _ => Option.none

instance [OfVal α] : OfVal (List α) := ⟨ofValList⟩

end OfVal

end Effect4.Target.EffectV4
