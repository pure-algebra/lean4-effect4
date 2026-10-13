import Effect4.Codegen.Print

/-!
# Codegen.RowServices — a row namespace as an Effect service (decisions row 378 (19), slice E3)

Each row namespace is an rc.112 service key, and each of its rows is a method of that service. A
row is a service row when its requirement column names exactly one key and its spelling is
`Ns.method` (`Row.serviceCall?`): the column says that the call needs the key, and the spelling
names the service and the method. Nothing new is stored.

The call site prints as it did, `Ns.method(x)`. The module declares `Ns` as the key with one
accessor per method, and each accessor is the ruled call `NsKey.use((r) => r.method(x))`
(option A of the seat ROWS receipt, `docs/research/2026-10-13-seat-rows-receipt.md`, accepted by
the coordinator on 2026-10-13). So the call's printed requirement is the key that the column
names, and a person provides the service by a layer, `Layer.succeed(Ns, impl)`. The printer, the
readers and their laws do not move.

The module envelope calls `rowServiceDecls` where a table becomes a module, and refuses the
module by a row's spelling where it refuses (`rowServiceFault`). This module states no target
typing and no execution claim: tsgo 7 and rc.112 are the receipt's evidence.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4.Machine.Env (Requirement)

variable {Op : Type}

/-- The bytes before the one dot of a spelling and the bytes after it; `none` unless the bytes
hold exactly one dot (byte `46`). -/
def splitDot : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: rest =>
    if b = 46 then (if rest.contains 46 then none else some ([], rest))
    else (splitDot rest).map fun p => (b :: p.1, p.2)

/-- **A spelling `Ns.method` as its namespace and its method**: a binding name, one dot, and a
property name, which may be a keyword (`TodoRepo.delete`, as `Effect.catch`;
`SourceBindings.identifierBytes`). It reads the spelling's bytes and decodes the two parts
(`Store.decodeString`), so no traversal of a `String` enters the proof graph. -/
def serviceParts (spelling : String) : Option (String × String) :=
  match splitDot spelling.toByteArray.data.toList with
  | some (pre, post) =>
    match Effect4.Store.decodeString pre, Effect4.Store.decodeString post with
    | some ns, some m =>
      if Effect4.Codegen.Names.binderName ns && Effect4.Codegen.SourceBindings.identifierBytes post
      then some (ns, m)
      else none
    | _, _ => none
  | none => none

/-- **The service a row belongs to**: a call row with no trailing argument and no declared type
argument, whose requirement column names exactly one key and whose spelling is `Ns.method`
(`serviceParts`), is method `method` of the service `Ns`. The column is read first, so a row
whose column names no key is no service row by computation. -/
def Row.serviceCall? (row : Row) : Option (String × String) :=
  match row.requires with
  | [_] =>
    if row.shape = .call ∧ row.trailing = [] ∧ row.typeArgs = [] then serviceParts row.spelling
    else none
  | _ => none

/-- The members of an rc.112 service key, which an accessor on the key would shadow
(`Object.assign`): the `Key` and `Service` interfaces (`Context.ts:64-69`, `:98-103`); the
`Effect` interface's `Pipeable` and `Inspectable` members (`Effect.ts:117`, `Pipeable.ts:44-45`,
`Inspectable.ts:126-129`), which the key's prototype implements (`Context.ts:419-447`,
`internal/core.ts:66-79`, `:100-113`); the key function's own properties (`Context.ts:395-410`:
`function KeyClass() {}`, its `key`, a reference's `defaultValue` and `make`); and the members of
`Object.prototype`, which ends the key's prototype chain (`Context.ts:397`). Paths are under
`vendor/effect-4.0.0-rc.112/src/`. -/
def serviceKeyMembers : List String :=
  [ "Service", "Identifier", "key", "of", "context", "use", "useSync", "pipe", "toString",
    "toJSON", "length", "name", "prototype", "defaultValue", "make", "constructor",
    "hasOwnProperty", "isPrototypeOf", "propertyIsEnumerable", "toLocaleString", "valueOf",
    "__proto__", "__defineGetter__", "__defineSetter__", "__lookupGetter__", "__lookupSetter__" ]

/-- A row namespace's service: the namespace, its key, and its methods with their rows, in table
order. -/
structure RowService where
  ns : String
  key : ServiceKey
  methods : List (String × Row)

/-- The services of a table's service rows, one for each namespace, in the order of the
namespace's first row. A service's key is its first row's. -/
def rowServices (table : List Row) : List RowService :=
  let rows := table.filterMap fun row =>
    match row.serviceCall?, row.requires with
    | some (ns, m), [key] => some (ns, key, m, row)
    | _, _ => none
  (rows.map (·.1)).eraseDups.filterMap fun ns =>
    match rows.find? (·.1 == ns) with
    | some (_, key, _, _) =>
      some ⟨ns, key, (rows.filter (·.1 == ns)).map fun r => (r.2.2.1, r.2.2.2)⟩
    | none => none

/-- Whether one row of a table breaks its services (`rowServiceFault`): a row whose requirement
column names a key and that is no service row (its spelling is no `Ns.method`, it is no plain
call, or it names several keys); a row of a service's namespace that names another key or none;
a method whose name is a member of the key (`serviceKeyMembers`), which its accessor would
shadow; two methods of one name; two services of one key, which one slot of a context holds; and
a service whose key's name, `NsKey`, is another service's name. -/
def rowBreaksServices (services : List RowService) (row : Row) : Bool :=
  match row.serviceCall?, row.requires with
  | some (ns, m), [key] =>
    serviceKeyMembers.contains m ||
      services.any (fun s => s.ns == ns &&
        (s.key != key || (s.methods.filter (·.1 == m)).length != 1)) ||
      services.any (fun s => s.ns != ns && (s.key == key || s.ns == ns ++ "Key"))
  | none, [] =>
    match serviceParts row.spelling with
    | some (ns, _) => services.any (·.ns == ns)
    | none => false
  | _, _ => true

/-- **Why a table's services do not print**: the first row that breaks them
(`rowBreaksServices`), named by its spelling. -/
def rowServiceFault (table : List Row) : Option String :=
  (table.find? (rowBreaksServices (rowServices table))).map (·.spelling)

/-- A method's field in its service's shape: `readonly m: (a0: Request) => Effect.Effect<A, E,
never>`, and `() => …` on a `unit` request, each column through the type printer. The method
requires nothing: the layer that builds the service provides what it needs. -/
def rowMethodField (sig : Signature Op) (m : String) (row : Row) :
    Except PrintRefusal TypeScript.TypeRef.Field := do
  let params ← if row.request = Ty.unit then pure [] else do
    let request ← typeRefOf row.request
    pure [(Var.name 0, request)]
  match ← declarationType ⟨row.answer, row.error, Requirement.empty⟩ sig.scopeKey with
  | some result => .ok { name := m, readonly := true, type := .function params result }
  | none => .error (.typeSpelling row.spelling)

/-- A method's accessor on its key: `m: (a0: Request) => NsKey.use((a1) => a1.m(a0))`, and
`m: () => NsKey.use((a0) => a0.m())` on a `unit` request. It is the ruled call of a service's
method, `Key.use((r) => r.method(x))` (decisions row 378 (19); rc.112 `Context.ts:101`,
`:442-444`: `use` reads the service from the fiber's context and applies the function to it). -/
def rowAccessor (keyName m : String) (row : Row) :
    Except PrintRefusal (String × TypeScript.Expr) :=
  if row.request = Ty.unit then
    .ok (m, .lambda [] (.method (.ident keyName) "use"
      [.lambda [{ name := Var.name 0 }] (.method (.ident (Var.name 0)) m [])]))
  else do
    let request ← typeRefOf row.request
    .ok (m, .lambda [{ name := Var.name 0, type := some request }] (.method (.ident keyName) "use"
      [.lambda [{ name := Var.name 1 }] (.method (.ident (Var.name 1)) m [.ident (Var.name 0)])]))

/-- **The row namespaces' services**: for each service of the table (`rowServices`), its key,
`export const NsKey = Context.Service<"k…", { readonly m: … }>("k…")` (`serviceKeyDecl`; its
identifier is its key's spelling `keyText`, which is what a requirement row prints), and the
namespace, `export const Ns = Object.assign(NsKey, { m: … })`, the key with one accessor for each
method (`rowAccessor`). A program's call `Ns.m(x)` is its accessor's call, and a consumer may
provide either name. Both are exported, so the reading boundary's envelope admits them as it
admits a layer (`envelopeCheck`, `Codegen/Admit.lean`). Refused by a row's spelling where
`rowServiceFault` names one, and by the namespace where its key is the signature's scope, which
prints as `Scope.Scope` and has no shape of methods. -/
def rowServiceDecls (sig : Signature Op) (table : List Row) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  match rowServiceFault table with
  | some spelling => .error (.unsafeName spelling)
  | none => do
    let groups ← (rowServices table).mapM fun s =>
      if s.key = sig.scopeKey then .error (.unsafeName s.ns) else do
        let fields ← s.methods.mapM fun (m, row) => rowMethodField sig m row.normalizeTypes
        let accessors ← s.methods.mapM fun (m, row) =>
          rowAccessor (s.ns ++ "Key") m row.normalizeTypes
        .ok [serviceKeyDecl (s.ns ++ "Key") (keyText s.key) fields,
             { doc := [], name := s.ns,
               value := .call (.ident "Object.assign")
                 [.ident (s.ns ++ "Key"), .object accessors] }]
    .ok groups.flatten

end Effect4.Program
