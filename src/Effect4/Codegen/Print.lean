import Effect4.Codegen.Templates
import Effect4.Codegen.ClassTable
import Effect4.Program.Definitions

/-!
# Codegen.Print — `Eff` into TypeScript: the generated fold over the table of printed clauses

`print` has no clause of its own. It is `cata_eff` of ONE table-driven layer function
(`Templates.printAlg`): choose the row of `Codegen/Templates.lean` for the constructor and its
classifier, print each argument by sort at the depth the row gives it, instantiate the row's
skeleton. Every constructor has a row; the row call of `perform` is the one row that is a codec
and not a skeleton (`printRow`, `Codegen/PrintLeaf.lean`), and the three spines are the
algebra's only hand fields. The reader (`Codegen/Read.lean`) runs the same rows the other way.

The target is the pinned lean4-typescript fragment (`TypeScript.Expr`, `TypeScript.Stmt`), which
`TypeScript.Render.expr house0 0` renders at a fixed layout: equal syntax is equal bytes, so the
printer is byte-deterministic without a width heuristic anywhere in it.

What the table refuses, the printer refuses by name rather than by a fallback spelling: the five
internal fiber actions (`interruptScoped`, `awaitAllFailFast`, `snapshotChildren`,
`awaitNewChildren`, `setContext`) have no public rc.112 export with the same frame shape.
`PrintRefusal` is the closed refusal alphabet; a refusal is data, never a printed guess.

The hand printer this replaced (one clause per constructor, six mutual functions) agreed with
the fold on a sample of every constructor and classifier and on the 400 seeded programs before
it was deleted (2026-09-17); the printed bytes are pinned independently by
`Test/Codegen/PrintContract.lean`, the corpus goldens and the truth harness's modules.
-/

namespace Effect4.Program

open Effect4.Machine.Env (Requirement)

variable {Op : Type}

/-- `print sig n e` is `e` as one TypeScript expression, with `n` the environment's length.
Every binder a clause introduces is `Var.name` of the position it occupies, as its row's depth
column says. -/
def print (sig : Signature Op) (n : Nat) (e : Eff Op) : Except PrintRefusal TypeScript.Expr :=
  Effect4.Codegen.Templates.printT sig n e

/-- A layer as one TypeScript expression. A layer is closed: its bodies print at environment
length `0`. -/
def printLayer (sig : Signature Op) (l : LayerTerm Op) : Except PrintRefusal TypeScript.Expr :=
  Effect4.Codegen.Templates.printLayerT sig l

/-- A row's invocation prints as its row call: the table's `rowCall` row, by computation, the
row's call on the request and after it the operation's binder term as a function of the current
value (`printPerform`, `Codegen/PrintLeaf.lean`). -/
theorem print_perform (sig : Signature Op) (n : Nat) (op : Op) (request : Term) :
    print sig n (.perform op request) = printPerform sig n op request := rfl

/-- The complete requirement row as target syntax. The empty union is `never`. -/
def requirementType (scopeKey : ServiceKey) (requires : Requirement) : TypeScript.TypeRef :=
  match requires.elems.map (keyIdentifier scopeKey) with
  | [] => .name ["never"] []
  | [one] => one
  | many => .union many

/-- The complete declared type `Effect.Effect<A, E, R>`. The native API defaults to
its reserved scope key; generic module printing passes the signature's scope key.
This is structural annotation evidence, not a general target typing theorem. A payload type in
either column prints as its class name (`Types.ofTy`, decisions row 120), and a union by its
members: `Effect.Effect<never, NotFound | Unauthorized, never>`. -/
def declarationType (ty : EffTy) (scopeKey : ServiceKey := Effect4.Machine.Env.scopeKey) :
    Except PrintRefusal (Option TypeScript.TypeRef) := do
  let answer ← match Effect4.Codegen.Types.ofTy ty.answer with
    | some target => .ok target
    | none => .error (.typeSpelling ty.answer.render)
  let error ← match Effect4.Codegen.Types.ofTy ty.error with
    | some target => .ok target
    | none => .error (.typeSpelling ty.error.render)
  .ok (some (.name ["Effect", "Effect"] [answer, error, requirementType scopeKey ty.requires]))

/-- The printed program as an exported constant carrying `declarationType`'s annotation. -/
def printDecl (name : String) (ty : EffTy) (body : TypeScript.Expr)
    (scopeKey : ServiceKey := Effect4.Machine.Env.scopeKey) :
    Except PrintRefusal TypeScript.ConstDecl := do
  let annotation ← declarationType ty scopeKey
  .ok { doc := [], name := name, value := body, type := annotation }

/-- Answer and error types must both be representable; a nonempty requirement row never
bypasses that check. Requirement identifiers have a total structural spelling. -/
def declarationTypeRepresentable (ty : EffTy) : Bool :=
  (Effect4.Codegen.Types.ofTy ty.answer).isSome && (Effect4.Codegen.Types.ofTy ty.error).isSome

/-- Representability suffices for a complete annotation at every scope identity. -/
theorem declarationType_ok {ty : EffTy} (hr : declarationTypeRepresentable ty = true)
    (scopeKey : ServiceKey := Effect4.Machine.Env.scopeKey) :
    ∃ annotation, declarationType ty scopeKey = .ok annotation := by
  simp only [declarationTypeRepresentable, Bool.and_eq_true, Option.isSome_iff_exists] at hr
  obtain ⟨⟨answer, ha⟩, ⟨error, he⟩⟩ := hr
  exact ⟨_, by simp only [declarationType, ha, he, bind, Except.bind]; rfl⟩

/-- A successful declaration always retains all three slots, including the complete
requirement row. Consumer: checked module production and its annotation admission check. -/
theorem declarationType_complete {ty : EffTy} {scopeKey : ServiceKey}
    {annotation : Option TypeScript.TypeRef} (h : declarationType ty scopeKey = .ok annotation) :
    ∃ answer error, annotation = some (.name ["Effect", "Effect"]
      [answer, error, requirementType scopeKey ty.requires]) := by
  unfold declarationType at h
  cases ha : Effect4.Codegen.Types.ofTy ty.answer with
  | none => simp only [ha, bind, Except.bind] at h; cases h
  | some answer =>
    cases he : Effect4.Codegen.Types.ofTy ty.error with
    | none => simp only [ha, he, bind, Except.bind] at h; cases h
    | some error =>
      simp only [ha, he, bind, Except.bind, Except.ok.injEq] at h
      exact ⟨answer, error, h.symm⟩

/-- Everything a successful declaration retains: its requested name, its body unchanged,
its export flag, and the annotation this type's one owner decided. -/
theorem printDecl_fields {scopeKey : ServiceKey} {name : String} {ty : EffTy} {body : TypeScript.Expr}
    {decl : TypeScript.ConstDecl} (hp : printDecl name ty body scopeKey = .ok decl) :
    decl.name = name ∧ decl.value = body ∧ decl.exported = true ∧
      declarationType ty scopeKey = .ok decl.type := by
  unfold printDecl at hp
  cases h : declarationType ty scopeKey with
  | error why => simp only [h, bind, Except.bind] at hp; cases hp
  | ok annotation =>
    rw [h] at hp
    simp only [bind, Except.bind] at hp
    cases hp
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A successful raw declaration retains its expression exactly. -/
theorem printDecl_value {scopeKey : ServiceKey} {name : String} {ty : EffTy} {body : TypeScript.Expr}
    {decl : TypeScript.ConstDecl} (hp : printDecl name ty body scopeKey = .ok decl) :
    decl.value = body :=
  (printDecl_fields hp).2.1

/-- A representable declaration type prints, at every name and body. -/
theorem printDecl_readable (name : String) (ty : EffTy) (body : TypeScript.Expr)
    (hr : declarationTypeRepresentable ty = true)
    (scopeKey : ServiceKey := Effect4.Machine.Env.scopeKey) :
    ∃ decl, printDecl name ty body scopeKey = .ok decl := by
  obtain ⟨annotation, ha⟩ := declarationType_ok hr scopeKey
  refine ⟨{ doc := [], name := name, value := body, type := annotation }, ?_⟩
  simp only [printDecl, ha, bind, Except.bind]

/-! ## A definition block (decisions row 328, slice PROC-3) -/

/-- A program's definition block, when its root holds one: the declarations, the bodies and the
main program. -/
def Eff.block? : Eff Op → Option (List DefDecl × Effs Op × Eff Op)
  | .defs decls bodies main => some (decls, bodies, main)
  | _ => none

/-- A program type as target syntax, refused by its rendering when it has none. -/
def typeRefOf (ty : Ty) : Except PrintRefusal TypeScript.TypeRef :=
  match Effect4.Codegen.Types.ofTy ty with
  | some target => .ok target
  | none => .error (.typeSpelling ty.render)

/-- A definition's declared type: its answer and error columns, and its requirement row. -/
def DefDecl.effTy (d : DefDecl) : EffTy := ⟨d.answer, d.error, Requirement.ofList d.requires⟩

/-- **A definition as a module constant**: `const name = (a0: Request): Effect.Effect<A, E, R> =>
Effect.suspend(() => body)`. The parameter is the request, the body's one variable, so the body
prints at environment length `1`. The body is a suspension, so an invocation is one
`Effect.suspend`, as the machine's is. The result type is `declarationType` of the declared
columns: a recursive arrow needs it (TS7023). A layer inside a body is refused by name: printed
inside the arrow, rc.112 would build one layer object per invocation, where the machine keeps
one memo entry per path (DB-12). -/
def printDef (sig : Signature Op) (d : DefDecl) (body : Eff Op) :
    Except PrintRefusal TypeScript.ConstDecl :=
  if !(body.layerPaths []).isEmpty then .error (.internalAction "defs:layer")
  else
    typeRefOf d.request >>= fun request =>
    declarationType d.effTy sig.scopeKey >>= fun result =>
    print sig 1 (.suspend body) >>= fun value =>
    .ok { doc := [], name := d.name,
          value := .lambda [{ name := Var.name 0, type := some request }] value result }

/-- The definitions of a block, in order, each against its body. A block whose declarations
and bodies differ in number is refused, as the checker refuses it. -/
def printDefs (sig : Signature Op) : List DefDecl → Effs Op →
    Except PrintRefusal (List TypeScript.ConstDecl)
  | [], .nil => .ok []
  | d :: ds, .cons body rest => do
    let c ← printDef sig d body
    let cs ← printDefs sig ds rest
    .ok (c :: cs)
  | _, _ => .error (.internalAction "defs")

/-! ## A block's services (decisions rows 338 and 339, slice CO-6b)

A block's roles declare its services (`DefRole`). A service prints as two constants after the
definitions: its key, `const S = Context.Service<"S", Shape>("S")`, the form of every service key
the printer writes (`printKey`); and its layer, `const SLayer = Layer.effect(S,
Effect.map(init(), (a0) => { return { m: (a1, …) => d(pair(a0, …)), … } }))`. The layer runs
the initial program once, and each method closes over its answer, the state (rc.112
`Layer.effect`, `vendor/effect-4.0.0-rc.112/src/Layer.ts`). -/

/-- A service of a block: its name, its initial program's position, and its methods, each with
its name, its definition's position and its arity. -/
structure Service where
  name : String
  init : Nat
  methods : List (String × Nat × Nat)
deriving DecidableEq, Repr

/-- The method of service `s` that the definition at position `j` is, if it is one. -/
def methodAt (s : String) (defs : List DefDecl) (j : Nat) : Option (String × Nat × Nat) :=
  match defs[j]? with
  | some d =>
    match d.role with
    | .serviceMethod s' m n => if s' = s then some (m, j, n) else none
    | _ => none
  | none => none

/-- The methods of service `s` in a block, in block order. -/
def serviceMethods (s : String) (defs : List DefDecl) : List (String × Nat × Nat) :=
  (List.range defs.length).filterMap (methodAt s defs)

/-- The service whose initial program is the definition at position `i`, if it is one. -/
def serviceAt (defs : List DefDecl) (i : Nat) : Option Service :=
  match defs[i]? with
  | some d =>
    match d.role with
    | .serviceInit s => some ⟨s, i, serviceMethods s defs⟩
    | _ => none
  | none => none

/-- The services a block's roles declare, in the order of their initial programs. -/
def servicesOf (defs : List DefDecl) : List Service :=
  (List.range defs.length).filterMap (serviceAt defs)

/-- A method's arguments after the state: `arity` types read off the rest of its request. -/
def methodArgTys : Nat → Ty → Option (List Ty)
  | 0, _ => some []
  | 1, t => some [t]
  | n + 2, .prod a b => (methodArgTys (n + 1) b).map (a :: ·)
  | _ + 2, _ => none

/-- A method's arguments, from its definition's request and the service's state type. -/
def methodArgs (state : Ty) (d : DefDecl) (arity : Nat) : Option (List Ty) :=
  match arity, d.request with
  | 0, request => if request = state then some [] else none
  | n + 1, .prod first rest => if first = state then methodArgTys (n + 1) rest else none
  | _ + 1, _ => none

/-- The argument names `a1` to `an`. -/
def argNames (n : Nat) : List String := (List.range n).map fun k => Var.name (k + 1)

/-- The tuple of a method's arguments, as `Authoring.requestOf` builds it. -/
def argTuple : List String → TypeScript.Expr
  | [] => .ident "undefined"
  | [a] => .ident a
  | a :: rest => .call (.ident "pair") [.ident a, argTuple rest]

/-- The request a method's closure passes its definition: the state `a0`, then its arguments. -/
def methodRequest (args : List String) : TypeScript.Expr :=
  match args with
  | [] => .ident (Var.name 0)
  | _ => .call (.ident "pair") [.ident (Var.name 0), argTuple args]

/-- Why one service does not print, if it does not: its initial program is missing or takes a
request other than `unit`; it has no method, or two with one name; its name or its layer's name
is a definition's or carries a layer path; or a method's request is not the state and its
arguments. -/
def serviceFaultOf (defs : List DefDecl) (sv : Service) : Option String :=
  match defs[sv.init]? with
  | none => some sv.name
  | some init =>
    if init.request ≠ .unit then some sv.name
    else if !(sv.methods.map (·.1)).Nodup || sv.methods.isEmpty then some sv.name
    else if defs.any (·.name == sv.name) || defs.any (·.name == sv.name ++ "Layer") ||
        (LayerTerm.readRefName sv.name).isSome ||
        (LayerTerm.readRefName (sv.name ++ "Layer")).isSome then
      some sv.name
    else sv.methods.findSome? fun (m, j, n) =>
      match defs[j]? with
      | some d => if (methodArgs init.answer d n).isSome then none else some (sv.name ++ "." ++ m)
      | none => some (sv.name ++ "." ++ m)

/-- Whether a definition is a method of a service that the block does not declare. -/
def strayMethod (names : List String) (d : DefDecl) : Bool :=
  match d.role with
  | .serviceMethod s _ _ => !names.contains s
  | _ => false

/-- Why a block's services do not print, if they do not: definitions with one name in a block
with a service, two services with one name, a method of no service, or a fault of one service
(`serviceFaultOf`). -/
def serviceFault (defs : List DefDecl) : Option String :=
  if !(servicesOf defs).isEmpty && !decide ((defs.map (·.name)).Nodup) then some "service:names"
  else if !decide (((servicesOf defs).map (·.name)).Nodup) then some "service:twice"
  else if defs.any (strayMethod ((servicesOf defs).map (·.name))) then some "service:method"
  else (servicesOf defs).findSome? (serviceFaultOf defs)

/-- A method's type in the service's shape: `(a1: T1, …) => Effect.Effect<A, E, R>`. -/
def methodType (sig : Signature Op) (state : Ty) (d : DefDecl) (arity : Nat) :
    Except PrintRefusal TypeScript.TypeRef := do
  let some tys := methodArgs state d arity | .error (.internalAction "service")
  let params ← (argNames arity).zip tys |>.mapM fun (a, t) => do
    let r ← typeRefOf t
    .ok (a, r)
  let result ← declarationType d.effTy sig.scopeKey
  match result with
  | some r => .ok (.function params r)
  | none => .error (.internalAction "service")

/-- A method's closure in its service's layer: `(a1: T1, …) => d(pair(a0, …))`. -/
def methodClosure (init : DefDecl) (defs : List DefDecl) (x : String × Nat × Nat) :
    Except PrintRefusal (String × TypeScript.Expr) := do
  let some d := defs[x.2.1]? | .error (.internalAction "service")
  let some tys := methodArgs init.answer d x.2.2 | .error (.internalAction "service")
  let params ← ((argNames x.2.2).zip tys).mapM fun p => do
    let r ← typeRefOf p.2
    .ok ({ name := p.1, type := some r } : TypeScript.Parameter)
  .ok (x.1, TypeScript.Expr.lambda params (.call (.ident d.name) [methodRequest (argNames x.2.2)]))

/-- A method's field in its service's shape. -/
def methodField (sig : Signature Op) (init : DefDecl) (defs : List DefDecl)
    (x : String × Nat × Nat) : Except PrintRefusal TypeScript.TypeRef.Field := do
  let some d := defs[x.2.1]? | .error (.internalAction "service")
  let t ← methodType sig init.answer d x.2.2
  .ok { name := x.1, readonly := true, type := t }

/-- **A service's key and layer.** -/
def printService (sig : Signature Op) (defs : List DefDecl) (sv : Service) :
    Except PrintRefusal (List TypeScript.ConstDecl) := do
  let some init := defs[sv.init]? | .error (.internalAction "service")
  let fields ← sv.methods.mapM (methodField sig init defs)
  let closures ← sv.methods.mapM (methodClosure init defs)
  .ok [{ doc := [], name := sv.name,
         value := .call (.generic (.ident "Context.Service") [.literal sv.name, .object fields])
           [.str sv.name] },
       { doc := [], name := sv.name ++ "Layer",
         value := .call (.ident "Layer.effect") [.ident sv.name,
           .call (.ident "Effect.map") [.call (.ident init.name) [],
             .arrowBlock [{ name := Var.name 0 }] [.ret (.object closures)]]] }]

/-- **A block's services**, each its key and its layer, in the order of their initial
programs; refused by name where `serviceFault` names a fault. -/
def printServices (sig : Signature Op) (defs : List DefDecl) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  match serviceFault defs with
  | some why => .error (.internalAction why)
  | none => do
    let groups ← (servicesOf defs).mapM (printService sig defs)
    .ok groups.flatten

/-- The printed program as a declaration block (the host rows slice): one
`const L_<path> = …` per referenced layer target, in declaration order (`Path.declBefore`: a
target inside another first, then program order), each hoisted out of the program so that
its defining site and every reference print as the one identifier (`Refs.lean` `hoistAll`),
which is one rc.112 layer object and one memo entry; the main declaration last. A program
with no references is `[printDecl name ty (print …)]`. `readModule` (`Codegen/Read.lean`)
is the inverse on what this prints.

A program with a definition block prints its definitions first (`printDef`), each at the
block's signature, so that an invocation prints as the definition's name. They stand before the
layers: a layer's body runs when its constant is evaluated, and it may invoke a definition. The
main declaration is the block's main program. -/
def printModule (sig : Signature Op) (name : String) (ty : EffTy) (e : Eff Op) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  match e.hoistAll with
  | .error target => .error (.layerRef target)
  | .ok (main, decls) =>
    match main.block? with
    | none => do
      let ordered := Path.sortBy Path.declBefore (decls.map (·.1))
      let ds ← ordered.mapM fun t =>
        match decls.find? (·.1 == t) with
        | some (_, l) => do
          let x ← printLayer sig l
          .ok ({ doc := [], name := LayerTerm.refName t, value := x } : TypeScript.ConstDecl)
        | none => .error (.layerRef t)
      let m ← print sig 0 main
      let declaration ← printDecl name ty m sig.scopeKey
      .ok (ds ++ [declaration])
    -- an empty block would print as its main program alone, and read back as it
    | some ([], _, _) => .error (.internalAction "defs")
    | some (d :: ds, bodies, body) => do
      let defs := d :: ds
      let sig' := sig.withDefs defs
      let cs ← printDefs sig' defs bodies
      let svc ← printServices sig' defs
      let ordered := Path.sortBy Path.declBefore (decls.map (·.1))
      let ds ← ordered.mapM fun t =>
        match decls.find? (·.1 == t) with
        | some (_, l) => do
          let x ← printLayer sig' l
          .ok ({ doc := [], name := LayerTerm.refName t, value := x } : TypeScript.ConstDecl)
        | none => .error (.layerRef t)
      let m ← print sig' 0 body
      let declaration ← printDecl name ty m sig.scopeKey
      .ok (cs ++ svc ++ ds ++ [declaration])

variable [ScopedOp Op]

/-- Check stored declarations, including records discarded before the final result and a list
fold's stated accumulator type (decisions row 228). The raw printer retains its exact fallback;
checked entries require a target projection. -/
def annotationRefusal (program : Eff Op) : Option PrintRefusal :=
  (Formation.programAnnotations program).findSome? fun (_, type) =>
    match Codegen.Types.ofTy type with
    | some _ => none
    | none => some (.typeSpelling type.render)

/-- The first definition name that is no safe module constant, or `none`. A definition's name
is an export name (`exportNameSafe`: a binding, no binder, no reserved head, no layer name, no
helper and no imported name), not the main declaration's, not a row's spelling, and declared
once. A built-in row's spelling holds a dot, so it is no binding. -/
def defsNameFault (table : List Row) (name : String) : List DefDecl → Option String
  | [] => none
  | d :: ds =>
    if !exportNameSafe d.name || d.name == name || table.any (·.spelling == d.name) ||
        ds.any (·.name == d.name) then some d.name
    else defsNameFault table name ds

/-- A service's name and its layer's name, when one is not free: not an export name, the main
declaration's name, or a row's spelling. `serviceFault` checks them against the definitions. -/
def serviceNamesFault (table : List Row) (name : String) (defs : List DefDecl) : Option String :=
  (servicesOf defs).findSome? fun sv =>
    if !exportNameSafe sv.name || !exportNameSafe (sv.name ++ "Layer") || sv.name == name ||
        sv.name ++ "Layer" == name || table.any (fun row => row.spelling == sv.name) then
      some sv.name
    else none

/-- A program with no definitions has no service names to refuse. -/
theorem serviceNamesFault_nil (table : List Row) (name : String) :
    serviceNamesFault table name [] = none := rfl

/-- Print an admitted program against its row table. Refuses by name if the requested
export name is unsafe (a printed binder `a0`, a reserved head, a layer reference name, or
no legal binding at all), then if any row carries an unsafe name, then if the module cannot
declare one of its payload classes (`ClassTable.moduleClasses`, decisions row 120). Refusing
the export name here is what lets the reading boundary compare names at all: a block exporting
`a0` would be read back as a binder. The classes themselves are declared by the module
(`Codegen.ModuleEmission`), before these declarations. -/
def printEntry (table : List Row) (sig : Signature Op) (name : String) (ty : EffTy) (e : Eff Op) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  if !exportNameSafe name then .error (.unsafeName name)
  else
    match table.find? (fun row => !rowNamesSafe row) with
    | some row => .error (.unsafeName row.spelling)
    | none =>
      match defsNameFault table name e.defsOf with
      | some fault => .error (.unsafeName fault)
      | none =>
      match serviceNamesFault table name e.defsOf with
      | some fault => .error (.unsafeName fault)
      | none =>
      match Effect4.Codegen.ClassTable.moduleClasses sig name ty e with
      | .error why => .error why
      | .ok _ =>
      match annotationRefusal e with
      | some why => .error why
      | none => printModule sig name ty e

/-- Shared checks of a successful entry, serving `printed-modules` through module emission.
Stored-annotation support is a target profile fact, not a target execution theorem (R2/R3). -/
theorem printEntry_checks {table : List Row} {sig : Signature Op} {name : String} {ty : EffTy}
    {e : Eff Op} {decls : List TypeScript.ConstDecl}
    (h : printEntry table sig name ty e = .ok decls) :
    exportNameSafe name = true ∧ table.find? (fun row => !rowNamesSafe row) = none ∧
      defsNameFault table name e.defsOf = none ∧ serviceNamesFault table name e.defsOf = none ∧
      (∃ classes, Effect4.Codegen.ClassTable.moduleClasses sig name ty e = .ok classes) ∧
      annotationRefusal e = none ∧ printModule sig name ty e = .ok decls := by
  cases hs : exportNameSafe name with
  | false => simp only [printEntry, hs, Bool.not_false, ↓reduceIte] at h; cases h
  | true =>
    simp only [printEntry, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hr : table.find? (fun row => !rowNamesSafe row) with
    | some row => simp only [hr] at h; cases h
    | none =>
      simp only [hr] at h
      cases hd : defsNameFault table name e.defsOf with
      | some fault => simp only [hd] at h; cases h
      | none =>
      simp only [hd] at h
      cases hn : serviceNamesFault table name e.defsOf with
      | some fault => simp only [hn] at h; cases h
      | none =>
      simp only [hn] at h
      cases hc : Effect4.Codegen.ClassTable.moduleClasses sig name ty e with
      | error why => simp only [hc] at h; cases h
      | ok classes =>
        simp only [hc] at h
        cases ha : annotationRefusal e with
        | some why => simp only [ha] at h; cases h
        | none => exact ⟨rfl, rfl, rfl, rfl, ⟨classes, rfl⟩, rfl, by simpa only [ha] using h⟩

/-- Every successful entry retains safe names and the actual module-printer equation. -/
theorem printEntry_ok {table : List Row} {sig : Signature Op} {name : String} {ty : EffTy}
    {e : Eff Op} {decls : List TypeScript.ConstDecl}
    (h : printEntry table sig name ty e = .ok decls) :
    exportNameSafe name = true ∧ table.find? (fun row => !rowNamesSafe row) = none ∧
      printModule sig name ty e = .ok decls := by
  obtain ⟨safe, rows, _, _, _, _, printed⟩ := printEntry_checks h
  exact ⟨safe, rows, printed⟩

/-- A checked entry contains only representable stored annotations (`printed-modules`, R2/R3).
The exact hypothesis is successful `printEntry`; host execution remains outside this fact. -/
theorem printEntry_annotations {table : List Row} {sig : Signature Op} {name : String} {ty : EffTy}
    {e : Eff Op} {decls : List TypeScript.ConstDecl}
    (h : printEntry table sig name ty e = .ok decls) : annotationRefusal e = none :=
  (printEntry_checks h).2.2.2.2.2.1

end Effect4.Program
