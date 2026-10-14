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
names, and a person provides the service by a layer, `Layer.succeed(Ns, impl)`. The call site's
printer and reader do not move. The key prints by the service's name, `"TodoRepo"`, in every
requirement row and as the key's runtime identity (`keySpelling` under the native signature's
key names, `rowKeyNames`; decisions row 378 (22)).

The module's file declares the services after its payload classes (`ModuleEmission.file`,
`Codegen/Checked.lean`), and refuses the module by a row's spelling where `rowServiceFault`
refuses. The file reader reads them back exactly (`readRowServices`): the declarations are a
function of the table, so it checks each against the table's services, piece by piece. This
module states no target typing and no execution claim: tsgo 7 and rc.112 are the receipts'
evidence.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4.Machine.Env (Requirement)

variable {Op : Type}

/-- **A spelling `Ns.method` as its namespace and its method**: a binding name, one dot
(`splitDot`, `Program/Native.lean`), and a property name, which may be a keyword
(`TodoRepo.delete`, as `Effect.catch`; `SourceBindings.identifierBytes`). It reads the
spelling's bytes and decodes the two parts (`Store.decodeString`), so no traversal of a `String`
enters the proof graph. -/
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

/-- **The service a row belongs to**: a row that names its key by a namespace
(`Row.keyNamespace?`, `Program/Native.lean`: a call row with no trailing argument and no declared
type argument, whose requirement column names exactly one key and whose spelling holds one dot)
and whose spelling is `Ns.method` (`serviceParts`) is method `method` of the service `Ns`. The
column is read first, so a row whose column names no key is no service row by computation, and
a service's key prints by the service's name (`rowKeyNames`). -/
def Row.serviceCall? (row : Row) : Option (String × String) :=
  row.keyNamespace?.bind fun _ => serviceParts row.spelling

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
    let request ← typeRefOf row.request sig.keyNames
    pure [(Var.name 0, request)]
  match ← declarationType ⟨row.answer, row.error, Requirement.empty⟩ sig.scopeKey sig.keyNames with
  | some result => .ok { name := m, readonly := true, type := .function params result }
  | none => .error (.typeSpelling row.spelling)

/-- A method's accessor on its key, as an expression: `(a0: T) => NsKey.use((a1) => a1.m(a0))` at
the request's type `T`, and `() => NsKey.use((a0) => a0.m())` on a `unit` request (`none`). It is
the ruled call of a service's method, `Key.use((r) => r.method(x))` (decisions row 378 (19);
rc.112 `Context.ts:101`, `:442-444`: `use` reads the service from the fiber's context and applies
the function to it). -/
def accessorExpr (keyName m : String) : Option TypeScript.TypeRef → TypeScript.Expr
  | none => .lambda [] (.method (.ident keyName) "use"
      [.lambda [{ name := Var.name 0 }] (.method (.ident (Var.name 0)) m [])])
  | some request => .lambda [{ name := Var.name 0, type := some request }]
      (.method (.ident keyName) "use"
        [.lambda [{ name := Var.name 1 }] (.method (.ident (Var.name 1)) m [.ident (Var.name 0)])])

/-- A method's request in its accessor: `none` on a `unit` request, which the accessor drops, and
the request's type through the type printer under the module's key names otherwise. -/
def accessorRequest (names : KeyNames) (row : Row) :
    Except PrintRefusal (Option TypeScript.TypeRef) :=
  if row.request = Ty.unit then .ok none else (typeRefOf row.request names).map some

/-- **What a row namespace's two declarations print** (`rowServiceDecls`): the namespace, its
key's runtime identity, the fields of the key's shape, and each method with its accessor's
request. -/
structure RowServiceData where
  ns : String
  identity : String
  fields : List TypeScript.TypeRef.Field
  methods : List (String × Option TypeScript.TypeRef)

/-- The name of a service's key: `NsKey`. -/
def RowServiceData.keyName (d : RowServiceData) : String := d.ns ++ "Key"

/-- A service's two declarations: its key, `NsKey = Context.Service<"identity", { fields }>(
"identity")` (`serviceKeyDecl`), and the namespace, `Ns = Object.assign(NsKey, { m: … })`, the
key with one accessor for each method (`accessorExpr`). -/
def RowServiceData.decls (d : RowServiceData) : List TypeScript.ConstDecl :=
  [serviceKeyDecl d.keyName d.identity d.fields,
   { doc := [], name := d.ns,
     value := .call (.ident "Object.assign") [.ident d.keyName,
       .object (d.methods.map fun (m, request) => (m, accessorExpr d.keyName m request))] }]

/-- **The data of a table's services**, for each service of the table (`rowServices`): its key's
identity is its key's spelling under the signature's key names (`keySpelling`), which is what a
requirement row prints: at the native signature, the service's own name (`rowKeyNames`,
decisions row 378 (22)). Each method's field and request go through the type printer. Refused
by a row's spelling where `rowServiceFault` names one, and by the namespace where its key is the
signature's scope, which prints as `Scope.Scope` and has no shape of methods. -/
def rowServiceData (sig : Signature Op) (table : List Row) :
    Except PrintRefusal (List RowServiceData) :=
  match rowServiceFault table with
  | some spelling => .error (.unsafeName spelling)
  | none => (rowServices table).mapM fun s =>
    if s.key = sig.scopeKey then .error (.unsafeName s.ns) else do
      let fields ← s.methods.mapM fun (m, row) => rowMethodField sig m row.normalizeTypes
      let methods ← s.methods.mapM fun (m, row) =>
        (accessorRequest sig.keyNames row.normalizeTypes).map fun request => (m, request)
      .ok ⟨s.ns, keySpelling sig.keyNames s.key, fields, methods⟩

/-- **The row namespaces' services**: for each service of the table, its two declarations
(`RowServiceData.decls`), the key and the namespace. A program's call `Ns.m(x)` is its accessor's
call, and a consumer may provide either name. Both are exported, so the reading boundary's
envelope admits them as it admits a layer (`envelopeCheck`, `Codegen/Admit.lean`). The module
declares them after its payload classes and before every other declaration (`readModule`,
`Codegen/Read.lean`). -/
def rowServiceDecls (sig : Signature Op) (table : List Row) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  (rowServiceData sig table).map fun data => data.flatMap RowServiceData.decls

/-! ## The declarations read back

The declarations are a function of the table, so the reader takes the table and accepts exactly
what `rowServiceDecls` prints of it: each declaration is compared with the service's data piece by
piece, each piece by a decision (strings, binders, types), never by a traversal of a `String`.
The laws are `readRowServices_rowServiceDecls` and `readRowServices_exact`
(`Laws/Codegen/RowServices.lean`). -/

/-- Whether an expression is exactly a method's accessor (`accessorExpr`). -/
def isAccessor (keyName m : String) : Option TypeScript.TypeRef → TypeScript.Expr → Bool
  | none, .lambda ps (.method (.ident k) u [.lambda qs (.method (.ident r) m' []) rt']) rt =>
    decide (ps = [] ∧ k = keyName ∧ u = "use" ∧ qs = [{ name := Var.name 0 }] ∧
      r = Var.name 0 ∧ m' = m ∧ rt' = none ∧ rt = none)
  | some request, .lambda ps (.method (.ident k) u
      [.lambda qs (.method (.ident r) m' [.ident a]) rt']) rt =>
    decide (ps = [{ name := Var.name 0, type := some request }] ∧ k = keyName ∧ u = "use" ∧
      qs = [{ name := Var.name 1 }] ∧ r = Var.name 1 ∧ m' = m ∧ a = Var.name 0 ∧ rt' = none ∧
      rt = none)
  | _, _ => false

/-- Whether an object's entries are exactly a service's accessors, in order. -/
def isAccessors (keyName : String) :
    List (String × TypeScript.Expr) → List (String × Option TypeScript.TypeRef) → Bool
  | [], [] => true
  | (m', e) :: es, (m, request) :: ms =>
    decide (m' = m) && isAccessor keyName m request e && isAccessors keyName es ms
  | _, _ => false

/-- Whether two declarations are exactly a service's (`RowServiceData.decls`). -/
def RowServiceData.isDecls (d : RowServiceData) :
    TypeScript.ConstDecl → TypeScript.ConstDecl → Bool
  | ⟨doc, name, .call (.generic (.ident h) targs) [.str i], type, exported⟩,
    ⟨doc', name', .call (.ident h') [.ident k, .object es], type', exported'⟩ =>
    decide (doc = [] ∧ name = d.keyName ∧ h = "Context.Service" ∧
      targs = [.literal d.identity, .object d.fields] ∧ i = d.identity ∧ type = none ∧
      exported = true ∧ doc' = [] ∧ name' = d.ns ∧ h' = "Object.assign" ∧ k = d.keyName ∧
      type' = none ∧ exported' = true) && isAccessors d.keyName es d.methods
  | _, _ => false

/-- The leading declarations that are exactly the services' of `data`, two for each service in
order, and the declarations after them. -/
def readServiceDecls : List RowServiceData → List TypeScript.Decl → Option (List TypeScript.Decl)
  | [], rest => some rest
  | d :: ds, decls =>
    match decls with
    | .const key :: .const ns :: rest => if d.isDecls key ns then readServiceDecls ds rest else none
    | _ => none

/-- **The row services read back**: the declarations after a module's payload classes that are
exactly the declarations of the table's services (`rowServiceDecls`), two for each service in
table order, and the declarations after them. `none` when the table's services do not print, or
the declarations do not begin with theirs. A table with no service row has none, and every
declaration list begins with them. -/
def readRowServices (sig : Signature Op) (table : List Row) (decls : List TypeScript.Decl) :
    Option (List TypeScript.Decl) :=
  match rowServiceData sig table with
  | .ok data => readServiceDecls data decls
  | .error _ => none

end Effect4.Program
