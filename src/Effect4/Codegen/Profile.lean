import TypeScript

/-!
# Codegen.Profile — the pinned Effect v4 host, and a service as rows

The exact host every generated module is checked against (`hostPin`), the generated-binding
profile the pinned package does not carry, and the one first-order description of an Effect
service that survives from the archived family DSL: `ServiceRow`, a class name and its
operation rows, rendered as `class X extends Context.Service<X, Shape>()("X") {}`.

Idiom pins, stated once:

| Lean | Effect v4 |
| --- | --- |
| a service row | `class X extends Context.Service<X, Shape>()("X") {}` |
| an operation with parameters | `readonly name: (params) => Effect.Effect<Answer, E>` |
| a nullary operation | `readonly name: Effect.Effect<Answer, E>` (Effect is lazy; tsgo rule `lazyEffect`) |

What was here and is gone (`docs/research/2026-09-04-codegen-api-design.md`, F5): the
straight-line `Script`/`PureTerm`/`Lowering` fragment, the `AtomRow` and its module, the
wire decoder `OfVal`, and the `Spelling` type language — all of the archived
`effect_program`/`effect_atoms` route. `Effect4.Program.Ty` is the type language now, and
its `render` is the TypeScript spelling.

The three string-traversing helpers (`mentions`, `namespacesOf`, `neededNamespaces`) and the
two renderers that reach them (`ServiceRow.receiver` through `String.decapitalize`,
`ServiceRow.sheet`) reach `Classical.choice` and are admitted by exact name in the axiom
gate; the rows themselves are `String`-free data.
-/

open TypeScript

namespace Effect4.Codegen.Profile

/-- The exact host this profile is checked against. -/
def hostPin : HostPin :=
  { typescript := "7.0.2"
    languageService := some "@effect/tsgo@0.38.0"
    runtime := "node 22 --experimental-strip-types"
    libraries := ["effect@4.0.0-rc.112"] }

/-! ## The binding profile

`TypeScript.reservedIdentifiers` (lean4-typescript) is the shared list; these are the words
it does not carry and this profile still refuses. -/

/-- Reserved and predefined names missing from `TypeScript.reservedIdentifiers`. -/
def reservedExtra : List String :=
  ["arguments", "eval", "undefined", "NaN", "Infinity"]

/-- A legal generated binding name for an operation or an atom. -/
def bindingName (name : String) : Bool :=
  TypeScript.targetIdentifier name && !(reservedExtra.contains name)

/-! ## The `effect` namespaces a spelling mentions -/

/-- Whether a rendered spelling mentions a namespace of the `effect` package, at any nesting
depth. `Option.Option<Result.Result<number, string>>` mentions both, so a module carrying it
imports both. -/
def mentions (needle haystack : String) : Bool := (haystack.splitOn needle).length > 1

/-- The `effect` namespaces a list of rendered spellings needs, in import order. The needle
list is fixed and alphabetical, so the import line is a function of the spellings and
nothing else. -/
def namespacesOf (spellings : List String) : List String :=
  ["Exit", "Fiber", "Option", "Result"].filter fun name =>
    spellings.any (mentions (name ++ "."))

/-- The names a supplied import list already binds. The module's own `effect` import must
not re-bind one of them: a caller that already imports `Option` as a type-only binding would
otherwise get a duplicate identifier. -/
def importedNames : List Import → List String
  | [] => []
  | .all name _ :: rest => name :: importedNames rest
  | .named names _ :: rest => names ++ importedNames rest
  | .types names _ :: rest => names ++ importedNames rest

/-- The `effect` namespaces a module must import for its own rows, minus the ones the
supplied imports already bind. -/
def neededNamespaces (spellings : List String) (atoms : List Import) : List String :=
  let bound := importedNames atoms
  (namespacesOf spellings).filter fun name => !bound.contains name

/-! ## Rows -/

/-- One operation as data: Lean and TypeScript spellings side by side, and the
natural-language cues bound to it. -/
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
  /-- A pure atom: lowered as a plain call. -/
  pure : Bool := false
  /-- The aborting error reading: Lean and TypeScript spellings of `E`. -/
  error : Option (String × String) := none
  /-- The arity of the answer read as a tuple: `1` unless the answer is a product. -/
  answerArity : Nat := 1
  deriving Repr, BEq, Inhabited

/-- An aborting operation's method carries its error in `E`: `Effect.Effect<A, E>`. -/
def errorAbort (answer error : String) : String :=
  "Effect.Effect<" ++ answer ++ ", " ++ error ++ ">"

/-- One service as data. The name is the Effect service class name. -/
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

/-- `(params) => Effect.Effect<Answer>`; a nullary operation is an Effect value,
`Effect.Effect<Answer>`, because Effect is already lazy (tsgo rule `lazyEffect`). -/
def methodType (row : OpRow) : String :=
  let effect := match row.error with
    | some (_, e) => errorAbort row.tsAnswer e
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
    { doc := ["Service `" ++ rows.name ++ "`: one method per operation."]
      name := rows.name
      heritage := some (.call (.call (.generic (.ident "Context.Service")
        [rows.name, rows.shapeType]) []) [.str rows.name]) }

/-- `export const XRows = { "get": { params: 0, answer: "number" }, … }`: the operation rows
as data, so a harness can read arities and answer spellings off the module. `answerArity` is
written only when the answer is a tuple. -/
def rowsDecl (rows : ServiceRow) : Decl :=
  .const
    { doc := ["Operation rows of `" ++ rows.name ++ "`."]
      name := rows.name ++ "Rows"
      value := .objectQuoted (rows.ops.map fun row =>
        (row.name, .object ([("params", .int row.params.length), ("answer", .str row.tsAnswer)] ++
          (if row.answerArity > 1 then [("answerArity", .int row.answerArity)] else [])))) }

/-- Every TypeScript spelling the rows mention, answers and parameters. -/
def spellings (rows : ServiceRow) : List String :=
  rows.ops.flatMap fun row => row.tsAnswer :: row.tsParams.map (·.2)

/-- The `effect` namespaces the module needs beside `Context` and `Effect`. -/
def namespaces (rows : ServiceRow) : List String :=
  namespacesOf rows.spellings

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

end Effect4.Codegen.Profile
