import Effect4.Codegen.Checked
import Effect4.Codegen.SchemaCode

/-!
# Codegen.Surface: an emitted module's typed surface (CR-4; decisions rows 373 (11), 378 (20))

An application exports one service, its methods the entries, with its layer (row 378 (20)). The
program module holds them as the printer writes them, and the reading boundary reads them back
(`admitModule`). The **surface** is a second module beside it, which a consumer imports. For each
data service of the program's block, it holds two declarations:

- `SSchemas`: for each method `m`, `{ input, answer, error }`, the typed Schema code
  (`Codegen.SchemaCode.ofTy`) of the method's arguments as one tuple, of its answer and of its
  error;
- `SLive`: `Layer.provide(Layer.effect(S, Effect.map(S, (a0) => { return { m: … } })), SLayer)`,
  the service from the program's own layer, each method decoding its arguments with
  `Schema.decodeUnknownEffect(SSchemas.m.input)` before it calls the program's method.

A failed decode dies (`Effect.orDie`). So an entry's declared type stays the model's, and the
surface refuses an input outside its type at run time, as the face refuses a literal outside its
profile (DI-56; `E4-PRINT-CE-003`). A method's program parameters pass as they are.

A service is a **data service** when every argument, answer and error of its methods has typed
Schema code. A generic service's method takes its caller's type, which no Schema fixes. A method
that takes a handle takes a value that no decode checks; row 373 (11) brands a `Ref` argument
instead. The surface holds neither kind of service.

The surface is no program syntax. It is a function of the checked program's types, so the reading
boundary does not read it. tsgo 7 checks it against the program module, and rc.112 runs it
(`make check-host-protocol`). This module states no law of it.
-/

set_option autoImplicit false

namespace Effect4.Codegen

open Effect4.Program

/-- One entry of a service: the method's name, its arguments' types, and its definition's
declaration, which holds its answer, its error and its program parameters. -/
structure Entry where
  method : String
  args : List Ty
  definition : DefDecl

/-- A service's entries, in method order: each method's arguments read off its definition's
request (`methodArgs`); `none` where a definition is missing or its request is not the state and
its arguments, which `serviceFault` refuses before any service prints. -/
def entriesOf (defs : List DefDecl) (sv : Service) : Option (List Entry) := do
  let init ← defs[sv.init]?
  sv.methods.mapM fun (m, j, n) => do
    let d ← defs[j]?
    let args ← methodArgs init.answer d n
    pure { method := m, args, definition := d }

/-- An entry's three Schemas, `{ input, answer, error }`; `none` where one of its types has no
typed Schema code. -/
def entrySchemas (e : Entry) : Option TypeScript.Expr := do
  let input ← (SchemaCode.ofTy (.tuple e.args)).toOption
  let answer ← (SchemaCode.ofTy e.definition.answer).toOption
  let error ← (SchemaCode.ofTy e.definition.error).toOption
  pure (.objectWith .plain
    [.property "input" input, .property "answer" answer, .property "error" error])

/-- The name of a service's Schemas: `SSchemas`. -/
def schemasName (service : String) : String := service ++ "Schemas"

/-- The name of a service's decoding layer: `SLive`. -/
def liveName (service : String) : String := service ++ "Live"

/-- An entry's closure in the decoding layer: `(a1: T1, …, p, …) =>
Effect.flatMap(Effect.orDie(Schema.decodeUnknownEffect(SSchemas.m.input)([a1, …])), (an+1) =>
a0.m(an+1[0], …, p, …))`, and `() => a0.m(p, …)` with no argument. The argument types are the
program's closure's (`methodClosure`); a program parameter passes as it is, typed by
`paramType`. -/
def entryClosure (sig : Signature NativeOp) (service : String) (e : Entry) :
    Except PrintRefusal (String × TypeScript.Expr) := do
  let n := e.args.length
  let params ← ((argNames n).zip e.args).mapM fun (a, t) => do
    let r ← typeRefOf t sig.keyNames
    pure ({ name := a, type := some r } : TypeScript.Parameter)
  let fns ← e.definition.params.mapM (paramType sig)
  let programs := (e.definition.params.zip fns).map fun (q, f) =>
    ({ name := q.name, type := some f } : TypeScript.Parameter)
  let call (args : List TypeScript.Expr) : TypeScript.Expr :=
    .method (.ident (Var.name 0)) e.method (args ++ e.definition.params.map fun q => .ident q.name)
  let decoded := Var.name (n + 1)
  let body := match n with
    | 0 => call []
    | _ => .call (.ident "Effect.flatMap")
        [.call (.ident "Effect.orDie")
          [.call (.call (.ident "Schema.decodeUnknownEffect")
              [.member (.member (.ident (schemasName service)) e.method) "input"])
            [.arr ((argNames n).map .ident)]],
         .lambda [{ name := decoded }]
          (call ((List.range n).map fun i => .index (.ident decoded) (.int (Int.ofNat i))))]
  pure (e.method, .lambda (params ++ programs) body)

/-- **A data service's surface**: its Schemas and its decoding layer (`SSchemas`, `SLive`); `none`
when the service is no data service, or its entries do not resolve. -/
def serviceSurface (sig : Signature NativeOp) (defs : List DefDecl) (sv : Service) :
    Except PrintRefusal (Option (List TypeScript.ConstDecl)) := do
  let some entries := entriesOf defs sv | pure none
  let some schemas := entries.mapM entrySchemas | pure none
  let closures ← entries.mapM (entryClosure sig sv.name)
  pure (some
    [{ doc := ["The Schemas of " ++ sv.name ++ "'s methods: each method's arguments as one tuple, " ++
          "its answer and its error."]
       name := schemasName sv.name
       value := .objectWith .plain ((entries.zip schemas).map fun (e, s) => .property e.method s) },
     { doc := [sv.name ++ " from its program's layer, each method's arguments decoded at entry by " ++
          "its Schema; a failed decode dies."]
       name := liveName sv.name
       value := .call (.ident "Layer.provide")
        [.call (.ident "Layer.effect") [.ident sv.name,
          .call (.ident "Effect.map") [.ident sv.name,
            .arrowBlock [{ name := Var.name 0 }] [.ret (.object closures)]]],
         .ident (sv.name ++ "Layer")] }])

/-- **The surface's imports, from Lean data**: its free names, each in byte order. A name comes
from `effect` when it is one of `effect`'s names (`fromEffect`) or `Schema`, from the prelude at
`prelude` when it is a prelude name, and from the program module at `program` otherwise: a
service's key and layer, and a payload class that a type names. -/
def surfaceImports (prelude program : String) (decls : List TypeScript.Decl) :
    List TypeScript.Import :=
  let free := (freeNames { header := [], imports := [], decls }).mergeSort fun a b =>
    bytesLe a.1.toUTF8.data.toList b.1.toUTF8.data.toList
  let binding (p : String × Bool) : TypeScript.ImportBinding :=
    { imported := p.1, localName := p.1, typeOnly := p.2 }
  let ofEffect := free.filter fun p => fromEffect p.1 || p.1 == "Schema"
  let ofPrelude := free.filter fun p => !(fromEffect p.1 || p.1 == "Schema") &&
    preludeNames.contains p.1
  let ofProgram := free.filter fun p => !(fromEffect p.1 || p.1 == "Schema") &&
    !preludeNames.contains p.1
  let named (ps : List (String × Bool)) (path : String) : List TypeScript.Import :=
    if ps.isEmpty then [] else [.named (ps.map binding) path false]
  named ofEffect "effect" ++ named ofProgram program ++ named ofPrelude prelude

/-- **An emission's surface**: the surface of each data service of its program's block, in the
order of the services' initial programs, with its imports from Lean data (`surfaceImports`): the
program module at `path`, the prelude at `prelude`. A program with no data service has an empty
surface. Refused where a type of an entry's closure has no TypeScript type, by its spelling. -/
def ModuleEmission.surface {program : NativeEff} {table : RowTable} {name : String}
    (_emission : ModuleEmission program table name) (prelude path : String) :
    Except PrintRefusal TypeScript.Module := do
  let defs := program.defsOf
  let groups ← (servicesOf defs).mapM (serviceSurface (nativeSignature table) defs)
  let decls := (groups.filterMap id).flatten.map TypeScript.Decl.const
  pure { header := [], imports := surfaceImports prelude path decls, decls }

end Effect4.Codegen
