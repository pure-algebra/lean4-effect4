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

/-- The complete declared type `Effect.Effect<A, E, R>`. The native API defaults to
its reserved scope key and no key name (`env : Classes.TypeEnv := {}`); generic module printing
passes the signature's spelling context (`sig.typeEnv`, decisions row 378 (22)), so a named key's
requirement reads `"TodoRepo"`, in `R` and in a context type's row alike. This is structural
annotation evidence, not a general target typing theorem. A payload type in either column prints as
its class name (`Types.ofTy`, decisions row 120), and a union by its members:
`Effect.Effect<never, NotFound | Unauthorized, never>`. -/
def declarationType (ty : EffTy) (env : Effect4.Codegen.Classes.TypeEnv := {}) :
    Except PrintRefusal (Option TypeScript.TypeRef) := do
  let answer ← match Effect4.Codegen.Types.ofTy ty.answer env.names with
    | some target => .ok target
    | none => .error (.typeSpelling ty.answer.render)
  let error ← match Effect4.Codegen.Types.ofTy ty.error env.names with
    | some target => .ok target
    | none => .error (.typeSpelling ty.error.render)
  .ok (some (.name ["Effect", "Effect"]
    [answer, error, requirementType env.scopeKey env.names ty.requires]))

/-- The printed program as an exported constant carrying `declarationType`'s annotation. -/
def printDecl (name : String) (ty : EffTy) (body : TypeScript.Expr)
    (env : Effect4.Codegen.Classes.TypeEnv := {}) :
    Except PrintRefusal TypeScript.ConstDecl := do
  let annotation ← declarationType ty env
  .ok { doc := [], name := name, value := body, type := annotation }

/-- Answer and error types must both be representable; a nonempty requirement row never
bypasses that check. Requirement identifiers have a total structural spelling. -/
def declarationTypeRepresentable (ty : EffTy) : Bool :=
  (Effect4.Codegen.Types.ofTy ty.answer).isSome && (Effect4.Codegen.Types.ofTy ty.error).isSome

/-- Representability suffices for a complete annotation under every spelling context `env`: the
names spell no part whose printed form may be missing (`Types.ofTy_isSome`). -/
theorem declarationType_ok {ty : EffTy} (hr : declarationTypeRepresentable ty = true)
    (env : Effect4.Codegen.Classes.TypeEnv := {}) :
    ∃ annotation, declarationType ty env = .ok annotation := by
  simp only [declarationTypeRepresentable, Bool.and_eq_true] at hr
  rw [← Effect4.Codegen.Types.ofTy_isSome ty.answer env.names,
    ← Effect4.Codegen.Types.ofTy_isSome ty.error env.names] at hr
  simp only [Option.isSome_iff_exists] at hr
  obtain ⟨⟨answer, ha⟩, ⟨error, he⟩⟩ := hr
  exact ⟨_, by simp only [declarationType, ha, he, bind, Except.bind]; rfl⟩

/-- A successful declaration always retains all three slots, including the complete
requirement row. Consumer: checked module production and its annotation admission check. -/
theorem declarationType_complete {ty : EffTy} {env : Effect4.Codegen.Classes.TypeEnv}
    {annotation : Option TypeScript.TypeRef}
    (h : declarationType ty env = .ok annotation) :
    ∃ answer error, annotation = some (.name ["Effect", "Effect"]
      [answer, error, requirementType env.scopeKey env.names ty.requires]) := by
  unfold declarationType at h
  cases ha : Effect4.Codegen.Types.ofTy ty.answer env.names with
  | none => simp only [ha, bind, Except.bind] at h; cases h
  | some answer =>
    cases he : Effect4.Codegen.Types.ofTy ty.error env.names with
    | none => simp only [ha, he, bind, Except.bind] at h; cases h
    | some error =>
      simp only [ha, he, bind, Except.bind, Except.ok.injEq] at h
      exact ⟨answer, error, h.symm⟩

/-- Everything a successful declaration retains: its requested name, its body unchanged,
its export flag, and the annotation this type's one owner decided. -/
theorem printDecl_fields {env : Effect4.Codegen.Classes.TypeEnv} {name : String} {ty : EffTy}
    {body : TypeScript.Expr} {decl : TypeScript.ConstDecl}
    (hp : printDecl name ty body env = .ok decl) :
    decl.name = name ∧ decl.value = body ∧ decl.exported = true ∧
      declarationType ty env = .ok decl.type := by
  unfold printDecl at hp
  cases h : declarationType ty env with
  | error why => simp only [h, bind, Except.bind] at hp; cases hp
  | ok annotation =>
    rw [h] at hp
    simp only [bind, Except.bind] at hp
    cases hp
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A successful raw declaration retains its expression exactly. -/
theorem printDecl_value {env : Effect4.Codegen.Classes.TypeEnv} {name : String} {ty : EffTy}
    {body : TypeScript.Expr} {decl : TypeScript.ConstDecl}
    (hp : printDecl name ty body env = .ok decl) : decl.value = body :=
  (printDecl_fields hp).2.1

/-- A representable declaration type prints, at every name, body and spelling context. -/
theorem printDecl_readable (name : String) (ty : EffTy) (body : TypeScript.Expr)
    (hr : declarationTypeRepresentable ty = true)
    (env : Effect4.Codegen.Classes.TypeEnv := {}) :
    ∃ decl, printDecl name ty body env = .ok decl := by
  obtain ⟨annotation, ha⟩ := declarationType_ok hr env
  refine ⟨{ doc := [], name := name, value := body, type := annotation }, ?_⟩
  simp only [printDecl, ha, bind, Except.bind]

/-! ## A definition block (decisions row 328, slice PROC-3) -/

/-- A program type as target syntax, a context type's row under the key names given (none by
default), refused by its rendering when it has none. -/
def typeRefOf (ty : Ty) (names : KeyNames := []) : Except PrintRefusal TypeScript.TypeRef :=
  match Effect4.Codegen.Types.ofTy ty names with
  | some target => .ok target
  | none => .error (.typeSpelling ty.render)

/-- A definition's declared type: its answer and error columns, and its requirement row. -/
def DefDecl.effTy (d : DefDecl) : EffTy := ⟨d.answer, d.error, Requirement.ofList d.requires⟩

/-! ### A body's own layers (decisions row 341, step 3)

A layer written in a definition's body belongs to one call of the body: rc.112 builds one layer
object per evaluation of the body, and its memo map is keyed by the object
(`vendor/effect-4.0.0-rc.112/src/Layer.ts`, `MemoMapImpl.map`). So a body's hoisted layers print
as constants at the top of the body's suspension, `Effect.suspend(() => { let L_<path> = …;
return body })`, and each run of the body makes its own objects. -/

/-- The definition whose body holds a path of a block: `k` when the path stands under body `k`,
the block's child `0` at position `k`; `none` outside every body. It is `Eff.scopeOf` of a block,
read off the path alone. -/
def Path.bodyIndex : List Nat → Option Nat
  | 0 :: rest => Path.spineIndex rest
  | _ => none

/-- A body's own layer as a constant at the top of its suspension, `let L_<path> = <layer>`,
found by its path among the body's hoisted layers. -/
def printLocal (sig : Signature Op) (locals : List (List Nat × LayerTerm Op)) (t : List Nat) :
    Except PrintRefusal TypeScript.Stmt :=
  match locals.find? (·.1 == t) with
  | some (_, l) => do
    let x ← printLayer sig l
    .ok (.letInit (LayerTerm.refName t) x none)
  | none => .error (.layerRef t)

/-- A definition's suspension: `Effect.suspend(() => body)`, and with the body's own layers
`Effect.suspend(() => { let L_<path> = …; return body })`. The block runs at each run of the
suspension, so each call makes its own layer objects. -/
def suspension : List TypeScript.Stmt → TypeScript.Expr → TypeScript.Expr
  | [], body => .call (.ident "Effect.suspend") [.arrow none body]
  | locals@(_ :: _), body =>
    .call (.ident "Effect.suspend") [.arrowBlock [] (locals ++ [.ret body])]

/-- A parameter's type in its definition's header (decisions row 340, slice HO-3): a function
from its request to an Effect of its declared columns, `(a0: Request) => Effect.Effect<A, E,
never>`. A parameter requires nothing: the passed program's requirements are the call's. -/
def paramType (sig : Signature Op) (q : ParamDecl) : Except PrintRefusal TypeScript.TypeRef :=
  typeRefOf q.request sig.keyNames >>= fun request =>
  declarationType ⟨q.answer, q.error, Requirement.ofList []⟩ sig.typeEnv >>= fun
    | some result => .ok (.function [(Var.name 0, request)] result)
    | none => .error (.typeSpelling q.name)

/-! ### The printer of a module's program pieces

A module prints programs in two places: its main program, and each definition's body. A **piece
printer** prints one of them at its signature and its checked environment. The plain module
prints a piece by the table's fold at the environment's length (`plainPieces`). The module that
ships prints it by the typed print, which writes a call's type arguments where a join needs them
(`shippedPieces`, `Codegen/PrintTyped.lean`; decisions row 373 (11)), or by the fold where the
typed print refuses. Everything else a module prints is the same in both: its classes, its
services, its layers and its declarations' order. So one module printer serves both
(`printModuleWith`), and `printModule` is the plain one. -/

/-- A printer of a module's program pieces, at the piece's signature and environment. -/
abbrev PiecePrint (Op : Type) :=
  Signature Op → TyEnv → Eff Op → Except PrintRefusal TypeScript.Expr

/-- **The plain pieces**: the table's fold at the environment's length. -/
def plainPieces : PiecePrint Op := fun sig env e => print sig env.length e

/-- **A definition as a module constant**: `const name = (a0: Request, p: (a0: B) =>
Effect.Effect<…>, …): Effect.Effect<A, E, R> => Effect.suspend(() => body)`. The first parameter
is the request, the body's one variable, so the body prints at environment length `1`. Each
parameter whose value is a program follows it, named by its declaration and typed by
`paramType`; the body prints at the signature its parameters extend (`Signature.withParams`),
so the run of parameter `i` prints as the row call of its name (slice HO-3). The body is a
suspension, so an invocation is one `Effect.suspend`, as the machine's is. The result type is
`declarationType` of the declared columns: a recursive arrow needs it (TS7023).

The body's own hoisted layers (`locals`) print at the top of the suspension (`suspension`), in
declaration order (`Path.declBefore`), at the body's signature, so a layer may run the body's
parameters. A reference to one prints as its constant's name, and each run of the body makes its
own objects, as the machine keys a body's build by its path and the running call (decisions row
341, step 3). A reference to a module layer prints as the module constant's name (step 2).

The body is a piece (`pp`): at the signature its parameters extend and the environment of its
declared request, as the module check checks it (`Checker.checkBodies`). -/
def printDefWith (pp : PiecePrint Op) (sig : Signature Op) (d : DefDecl) (body : Eff Op)
    (locals : List (List Nat × LayerTerm Op)) : Except PrintRefusal TypeScript.ConstDecl :=
  typeRefOf d.request sig.keyNames >>= fun request =>
  d.params.mapM (paramType sig) >>= fun fns =>
  declarationType d.effTy sig.typeEnv >>= fun result =>
  (Path.sortBy Path.declBefore (locals.map (·.1))).mapM
    (printLocal (sig.withParams d.params) locals) >>= fun ls =>
  pp (sig.withParams d.params) [d.request.normalize] body >>= fun value =>
  .ok { doc := [], name := d.name,
        value := .lambda ({ name := Var.name 0, type := some request } ::
          (d.params.zip fns).map fun p => { name := p.1.name, type := some p.2 })
          (suspension ls value) result }

/-- A definition as a plain module constant: its body by the table's fold. -/
abbrev printDef (sig : Signature Op) (d : DefDecl) (body : Eff Op)
    (locals : List (List Nat × LayerTerm Op)) : Except PrintRefusal TypeScript.ConstDecl :=
  printDefWith plainPieces sig d body locals

/-- The definitions of a block, in order, each against its body, from position `k`. Each takes
into its suspension the hoisted layers of `rest` whose paths stand in its body
(`Path.bodyIndex`), and passes the others on: the answer is the constants and the layers no body
took. A block whose declarations and bodies differ in number is refused at the position where
they part (`PrintRefusal.bodies`), as the checker refuses it. -/
def printDefsWith (pp : PiecePrint Op) (sig : Signature Op) : Nat → List DefDecl → Effs Op →
    List (List Nat × LayerTerm Op) →
    Except PrintRefusal (List TypeScript.ConstDecl × List (List Nat × LayerTerm Op))
  | _, [], .nil, rest => .ok ([], rest)
  | k, d :: ds, .cons body bodies, rest =>
    printDefWith pp sig d body (rest.filter fun e => decide (Path.bodyIndex e.1 = some k)) >>= fun c =>
    printDefsWith pp sig (k + 1) ds bodies
      (rest.filter fun e => !decide (Path.bodyIndex e.1 = some k)) >>= fun out =>
    .ok (c :: out.1, out.2)
  | k, _, _, _ => .error (.bodies k)

/-- The plain definitions of a block: each body by the table's fold. -/
abbrev printDefs (sig : Signature Op) (k : Nat) (defs : List DefDecl) (bodies : Effs Op)
    (rest : List (List Nat × LayerTerm Op)) :
    Except PrintRefusal (List TypeScript.ConstDecl × List (List Nat × LayerTerm Op)) :=
  printDefsWith plainPieces sig k defs bodies rest

/-! ## A block's services (decisions rows 338 and 339, slice CO-6b)

A block's roles declare its services (`DefRole`). A service prints as two constants after the
definitions: its key, `const S = Context.Service<"S", Shape>("S")`, the form of every service key
the printer writes (`printKey`); and its layer, `const SLayer = Layer.effect(S,
Effect.map(init(), (a0) => { return { m: (a1, …) => d(pair(a0, …)), … } }))`. The layer runs
the initial program once, and each method closes over its answer, the state (rc.112
`Layer.effect`, `vendor/effect-4.0.0-rc.112/src/Layer.ts`). A method whose definition takes
programs takes them after its arguments and passes them on: `m: (a1, …, p, …) => d(pair(a0, …),
p, …)` (slice HO-5, decisions row 340). -/

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

/-- A method's name, written as a plain key of the layer's object and a plain member of the
key's shape: a target identifier other than `__proto__`, which a literal would read as the
prototype (the record policy's plain key, `Codegen.Record.keyForm`; Codex's CO6B-KEYS). -/
def plainMethodName (m : String) : Bool := TypeScript.targetIdentifier m && m != "__proto__"

/-- Every name that a block's services declare: each service's key and its layer. -/
def serviceNames (services : List Service) : List String :=
  services.flatMap fun sv => [sv.name, sv.name ++ "Layer"]

/-- Why one service does not print, if it does not: its initial program is missing, takes a
request other than `unit`, or takes a program, which the layer has none to pass; it has no
method, two with one name, or one whose name is no plain key (`plainMethodName`); its name or its
layer's name is a definition's or carries a layer path; or a method's request is not the state and
its arguments. A method that takes programs prints, and its closure passes them on (slice HO-5).
The refusal names the service (`PrintRefusal.service`), or the service and the method at fault
(`PrintRefusal.serviceMethod`). -/
def serviceFaultOf (defs : List DefDecl) (sv : Service) : Option PrintRefusal :=
  match defs[sv.init]? with
  | none => some (.service sv.name)
  | some init =>
    -- the layer runs the initial program with no caller, so none passes it a program
    if init.request ≠ .unit || !init.params.isEmpty then some (.service sv.name)
    else if !(sv.methods.map (·.1)).Nodup || sv.methods.isEmpty ||
        sv.methods.any (fun x => !plainMethodName x.1) then some (.service sv.name)
    else if defs.any (·.name == sv.name) || defs.any (·.name == sv.name ++ "Layer") ||
        (LayerTerm.readRefName sv.name).isSome ||
        (LayerTerm.readRefName (sv.name ++ "Layer")).isSome then
      some (.service sv.name)
    else sv.methods.findSome? fun (m, j, n) =>
      match defs[j]? with
      | some d =>
        if (methodArgs init.answer d n).isSome then none
        else some (.serviceMethod sv.name m)
      | none => some (.serviceMethod sv.name m)

/-- Whether a definition is a method of a service that the block does not declare. -/
def strayMethod (names : List String) (d : DefDecl) : Bool :=
  match d.role with
  | .serviceMethod s _ _ => !names.contains s
  | _ => false

/-- The first name of a list that a later one repeats, if one does. -/
def repeatOf : List String → Option String
  | [] => none
  | n :: rest => if rest.contains n then some n else repeatOf rest

/-- The refusal of the first definition that is a method of a service the block does not
declare (`strayMethod`), by the definition and the service it names. -/
def strayOf (names : List String) : List DefDecl → Option PrintRefusal
  | [] => none
  | d :: ds =>
    match d.role with
    | .serviceMethod s _ _ => if names.contains s then strayOf names ds else some (.strayMethod d.name s)
    | _ => strayOf names ds

/-- Why a block's services do not print, if they do not: definitions with one name in a block
with a service, two of the names the services declare that are one (a key and another service's
layer among them, Codex's CO6B-NAMES), a method of no service, or a fault of one service
(`serviceFaultOf`). Each refusal names the name, the definition, the service or the method at
fault. -/
def serviceFault (defs : List DefDecl) : Option PrintRefusal :=
  match (if (servicesOf defs).isEmpty then none else repeatOf (defs.map (·.name))) with
  | some n => some (.serviceName n)
  | none =>
  match repeatOf (serviceNames (servicesOf defs)) with
  | some n => some (.serviceName n)
  | none =>
  match strayOf ((servicesOf defs).map (·.name)) defs with
  | some why => some why
  | none => (servicesOf defs).findSome? (serviceFaultOf defs)

/-- A method's type in the service's shape: `(a1: T1, …, p: (a0: B) => Effect.Effect<…>, …) =>
Effect.Effect<A, E, R>`. The definition's program parameters follow the arguments, each named by
its declaration and typed by `paramType` (slice HO-5). Refused by the service and the method,
`service.method`, where its request is not the state and its arguments. -/
def methodType (sig : Signature Op) (service method : String) (state : Ty) (d : DefDecl)
    (arity : Nat) : Except PrintRefusal TypeScript.TypeRef := do
  let some tys := methodArgs state d arity | .error (.serviceMethod service method)
  let params ← (argNames arity).zip tys |>.mapM fun (a, t) => do
    let r ← typeRefOf t sig.keyNames
    .ok (a, r)
  let fns ← d.params.mapM (paramType sig)
  let result ← declarationType d.effTy sig.typeEnv
  match result with
  | some r => .ok (.function (params ++ (d.params.map (·.name)).zip fns) r)
  | none => .error (.serviceMethod service method)

/-- A method's closure in its service's layer: `(a1: T1, …, p: …, …) => d(pair(a0, …), p, …)`.
The closure takes the definition's programs after its arguments and passes them on unchanged
(slice HO-5): a method that takes none is `(a1: T1, …) => d(pair(a0, …))`. Refused by the
service and the method where its definition is missing or its request is not the state and its
arguments. -/
def methodClosure (sig : Signature Op) (service : String) (init : DefDecl) (defs : List DefDecl)
    (x : String × Nat × Nat) : Except PrintRefusal (String × TypeScript.Expr) := do
  let some d := defs[x.2.1]? | .error (.serviceMethod service x.1)
  let some tys := methodArgs init.answer d x.2.2 | .error (.serviceMethod service x.1)
  let params ← ((argNames x.2.2).zip tys).mapM fun p => do
    let r ← typeRefOf p.2 sig.keyNames
    .ok ({ name := p.1, type := some r } : TypeScript.Parameter)
  let fns ← d.params.mapM (paramType sig)
  .ok (x.1, TypeScript.Expr.lambda
    (params ++ (d.params.zip fns).map fun q => ({ name := q.1.name, type := some q.2 } :
      TypeScript.Parameter))
    (.call (.ident d.name) (methodRequest (argNames x.2.2) :: d.params.map fun q => .ident q.name)))

/-- A method's field in its service's shape, refused by the service and the method where its
definition is missing. -/
def methodField (sig : Signature Op) (service : String) (init : DefDecl) (defs : List DefDecl)
    (x : String × Nat × Nat) : Except PrintRefusal TypeScript.TypeRef.Field := do
  let some d := defs[x.2.1]? | .error (.serviceMethod service x.1)
  let t ← methodType sig service x.1 init.answer d x.2.2
  .ok { name := x.1, readonly := true, type := t }

/-- **A service's key**: `const name = Context.Service<"identity", { fields }>("identity")`, the
one form of a service key that a module declares. rc.112's `Context.Service<Identifier, Shape>`
takes the identifier type first and the shape second, and its string argument is the key's
runtime identity (`vendor/effect-4.0.0-rc.112/src/Context.ts:252`). A block's service names its
key by its own name (`printService`); a row namespace's key carries its `ServiceKey`'s spelling
(`keyText`), so that its identifier is the one a requirement row prints (decisions row 378 (19),
slice E3). -/
def serviceKeyDecl (name identity : String) (fields : List TypeScript.TypeRef.Field) :
    TypeScript.ConstDecl :=
  { doc := [], name := name,
    value := .call (.generic (.ident "Context.Service") [.literal identity, .object fields])
      [.str identity] }

/-- **A service's key and layer**, refused by the service's name where its initial program is
missing. -/
def printService (sig : Signature Op) (defs : List DefDecl) (sv : Service) :
    Except PrintRefusal (List TypeScript.ConstDecl) := do
  let some init := defs[sv.init]? | .error (.service sv.name)
  let fields ← sv.methods.mapM (methodField sig sv.name init defs)
  let closures ← sv.methods.mapM (methodClosure sig sv.name init defs)
  .ok [serviceKeyDecl sv.name sv.name fields,
       { doc := [], name := sv.name ++ "Layer",
         value := .call (.ident "Layer.effect") [.ident sv.name,
           .call (.ident "Effect.map") [.call (.ident init.name) [],
             .arrowBlock [{ name := Var.name 0 }] [.ret (.object closures)]]] }]

/-- **A block's services**, each its key and its layer, in the order of their initial
programs; refused where `serviceFault` names a fault, by the name, the definition, the service or
the method at fault. -/
def printServices (sig : Signature Op) (defs : List DefDecl) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  match serviceFault defs with
  | some why => .error why
  | none => do
    let groups ← (servicesOf defs).mapM (printService sig defs)
    .ok groups.flatten

/-- **The module's layers** (decisions row 341, step 2): one `const L_<path> = …` per layer, the
`k`-th named by `Path.layerPath k`, in order. They stand after the definitions and the services,
which a layer's body may invoke, and before the hoisted layers, which may name them. -/
def printModuleLayers (sig : Signature Op) (layers : LayerTerms Op) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  layers.toList.zipIdx.mapM (printModuleLayer sig)
where
  /-- The module's layer `k`: `const L_<Path.layerPath k> = <layer>`. -/
  printModuleLayer (sig : Signature Op) (p : LayerTerm Op × Nat) :
      Except PrintRefusal TypeScript.ConstDecl := do
    let x ← printLayer sig p.1
    .ok { doc := [], name := LayerTerm.refName (Path.layerPath p.2), value := x }

/-- The printed program as a declaration block (the host rows slice): one
`const L_<path> = …` per referenced layer target, in declaration order (`Path.declBefore`: a
target inside another first, then program order), each hoisted out of the program so that
its defining site and every reference print as the one identifier (`Refs.lean` `hoistAll`),
which is one rc.112 layer object and one memo entry; the main declaration last. A program
with no references is `[printDecl name ty (print …)]`. `readModule` (`Codegen/Read.lean`)
is the inverse on what this prints.

A program with a definition block prints its definitions first (`printDef`), each at the
block's signature, so that an invocation prints as the definition's name. They stand before the
layers: a layer's body runs when its constant is evaluated, and it may invoke a definition. A
body's own hoisted layers stand at the top of its suspension (`printDefs`, decisions row 341,
step 3). The module's layers come next (`printModuleLayers`), then the hoisted ones no body took,
which may name them. The main declaration is the block's main program.

A block's references must stand in their scopes (`Eff.inScope`, decisions row 341): a body names
its own layers, declared in its suspension, and the module's; the main program names its own and
the module's. Otherwise a printed name would be declared where its site cannot see it, so the
first reference out of its scope is refused by its target.

The main program is a piece (`pp`), at the empty environment and the block's signature. -/
def printModuleWith (pp : PiecePrint Op) (sig : Signature Op) (name : String) (ty : EffTy)
    (e : Eff Op) :
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
      let m ← pp sig [] main
      let declaration ← printDecl name ty m sig.typeEnv
      .ok (ds ++ [declaration])
    -- an empty block would print as its main program alone, and read back as it
    | some ([], _, _, _) => .error .emptyBlock
    | some (d :: ds, bodies, body, layers) =>
      match (e.refSites []).find? fun x => !e.inScope x.1 x.2 with
      | some x => .error (.layerRef x.2)
      | none => do
        let defs := d :: ds
        let sig' := sig.withDefs defs
        let out ← printDefsWith pp sig' 0 defs bodies decls
        let svc ← printServices sig' defs
        let ms ← printModuleLayers sig' layers
        let ordered := Path.sortBy Path.declBefore (out.2.map (·.1))
        let ds ← ordered.mapM fun t =>
          match out.2.find? (·.1 == t) with
          | some (_, l) => do
            let x ← printLayer sig' l
            .ok ({ doc := [], name := LayerTerm.refName t, value := x } : TypeScript.ConstDecl)
          | none => .error (.layerRef t)
        let m ← pp sig' [] body
        let declaration ← printDecl name ty m sig.typeEnv
        .ok (out.1 ++ svc ++ ms ++ ds ++ [declaration])

/-- The plain module: each program piece by the table's fold. -/
abbrev printModule (sig : Signature Op) (name : String) (ty : EffTy) (e : Eff Op) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  printModuleWith plainPieces sig name ty e

variable [ScopedOp Op]

/-- Check stored declarations, including records discarded before the final result and a list
fold's stated accumulator type (decisions row 228). The raw printer retains its exact fallback;
checked entries require a target projection. -/
def annotationRefusal (program : Eff Op) : Option PrintRefusal :=
  (Formation.programAnnotations program).findSome? fun (_, type) =>
    match Codegen.Types.ofTy type with
    | some _ => none
    | none => some (.typeSpelling type.render)

/-- **The names a row table uses in printed code** (Codex's HO3-NAME-01): each row's spelling,
the root of a qualified one (`Widget` of `Widget.run`, `SourceBindings.qualifiedRoot`), and each
trailing name. A definition or a parameter named so would capture what the row's call names. -/
def rowNameUses (table : List Row) : List String :=
  table.flatMap fun row =>
    row.spelling :: ((Effect4.Codegen.SourceBindings.qualifiedRoot row.spelling).toList ++ RowArg.names row.trailing)

/-- A row's spelling is a name its table uses. A step of `defsNamed_of_fault`. -/
theorem spelling_mem_rowNameUses {table : List Row} {row : Row} (h : row ∈ table) :
    row.spelling ∈ rowNameUses table :=
  List.mem_flatMap.mpr ⟨row, h, List.mem_cons_self⟩

/-- The first definition name that is no safe module constant, or `none`. A definition's name
is an export name (`exportNameSafe`: a binding, no binder, no reserved head, no layer name, no
helper and no imported name), not the main declaration's, not a row's spelling, and declared
once. A built-in row's spelling holds a dot, so it is no binding. -/
def defsNameFault (table : List Row) (name : String) : List DefDecl → Option String
  | [] => none
  | d :: ds =>
    if !exportNameSafe d.name || d.name == name || (rowNameUses table).contains d.name ||
        ds.any (·.name == d.name) then some d.name
    else defsNameFault table name ds

/-- The first parameter name that is no safe binding in its definition's arrow, or `none`
(slice HO-3). A parameter's name is an export name (`exportNameSafe`), so it shadows no binder,
reserved head or imported name; it is not the main declaration's, not a row's spelling, not a
definition's, which the body calls by name, and declared once in its definition. -/
def paramsNameFault (table : List Row) (name : String) (defs : List DefDecl) :
    List ParamDecl → Option String
  | [] => none
  | q :: qs =>
    if !exportNameSafe q.name || q.name == name || (rowNameUses table).contains q.name ||
        defs.any (·.name == q.name) || qs.any (·.name == q.name) then some q.name
    else paramsNameFault table name defs qs

/-- The first parameter name of a block that is no safe binding (`paramsNameFault`). -/
def blockParamsFault (table : List Row) (name : String) (defs : List DefDecl) : Option String :=
  defs.findSome? fun d => paramsNameFault table name defs d.params

/-- The first definition or parameter name that is a payload class the module declares, or
`none` (Codex's HO3-NAME-01): a definition so named would declare the name twice, and a
parameter so named would capture the class's constructor in its body. -/
def classNameFault (classes : Effect4.Codegen.Classes.Classes) (defs : List DefDecl) :
    Option String :=
  defs.findSome? fun d =>
    ((d.name :: d.params.map (·.name)).find? fun s => classes.any (·.1 == s))

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
def printEntryWith (pp : PiecePrint Op) (table : List Row) (sig : Signature Op) (name : String)
    (ty : EffTy) (e : Eff Op) : Except PrintRefusal (List TypeScript.ConstDecl) :=
  if !exportNameSafe name then .error (.unsafeName name)
  else
    match table.find? (fun row => !rowNamesSafe row) with
    | some row => .error (.unsafeName row.spelling)
    | none =>
      match defsNameFault table name e.defsOf with
      | some fault => .error (.unsafeName fault)
      | none =>
      match blockParamsFault table name e.defsOf with
      | some fault => .error (.unsafeName fault)
      | none =>
      match serviceNamesFault table name e.defsOf with
      | some fault => .error (.unsafeName fault)
      | none =>
      match Effect4.Codegen.ClassTable.moduleClasses sig name ty e with
      | .error why => .error why
      | .ok (classes, _) =>
      match classNameFault classes e.defsOf with
      | some fault => .error (.unsafeName fault)
      | none =>
      match annotationRefusal e with
      | some why => .error why
      | none => printModuleWith pp sig name ty e

/-- A plain entry: the module's program pieces by the table's fold. -/
abbrev printEntry (table : List Row) (sig : Signature Op) (name : String) (ty : EffTy) (e : Eff Op) :
    Except PrintRefusal (List TypeScript.ConstDecl) :=
  printEntryWith plainPieces table sig name ty e

/-- Shared checks of a successful entry, serving `printed-modules` through module emission.
Stored-annotation support is a target profile fact, not a target execution theorem (R2/R3). -/
theorem printEntry_checks {pp : PiecePrint Op} {table : List Row} {sig : Signature Op}
    {name : String} {ty : EffTy} {e : Eff Op} {decls : List TypeScript.ConstDecl}
    (h : printEntryWith pp table sig name ty e = .ok decls) :
    exportNameSafe name = true ∧ table.find? (fun row => !rowNamesSafe row) = none ∧
      defsNameFault table name e.defsOf = none ∧ blockParamsFault table name e.defsOf = none ∧
      serviceNamesFault table name e.defsOf = none ∧
      (∃ classes, Effect4.Codegen.ClassTable.moduleClasses sig name ty e = .ok classes) ∧
      annotationRefusal e = none ∧ printModuleWith pp sig name ty e = .ok decls := by
  cases hs : exportNameSafe name with
  | false => simp only [printEntryWith, hs, Bool.not_false, ↓reduceIte] at h; cases h
  | true =>
    simp only [printEntryWith, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hr : table.find? (fun row => !rowNamesSafe row) with
    | some row => simp only [hr] at h; cases h
    | none =>
      simp only [hr] at h
      cases hd : defsNameFault table name e.defsOf with
      | some fault => simp only [hd] at h; cases h
      | none =>
      simp only [hd] at h
      cases hp : blockParamsFault table name e.defsOf with
      | some fault => simp only [hp] at h; cases h
      | none =>
      simp only [hp] at h
      cases hn : serviceNamesFault table name e.defsOf with
      | some fault => simp only [hn] at h; cases h
      | none =>
      simp only [hn] at h
      cases hc : Effect4.Codegen.ClassTable.moduleClasses sig name ty e with
      | error why => simp only [hc] at h; cases h
      | ok pair =>
        obtain ⟨classes, classDecls⟩ := pair
        simp only [hc] at h
        cases hcf : classNameFault classes e.defsOf with
        | some fault => simp only [hcf] at h; cases h
        | none =>
        simp only [hcf] at h
        cases ha : annotationRefusal e with
        | some why => simp only [ha] at h; cases h
        | none =>
          exact ⟨rfl, rfl, rfl, rfl, rfl, ⟨(classes, classDecls), rfl⟩, rfl,
            by simpa only [ha] using h⟩

/-- Every successful entry retains safe names and the actual module-printer equation, at any
piece printer. -/
theorem printEntry_ok {pp : PiecePrint Op} {table : List Row} {sig : Signature Op} {name : String}
    {ty : EffTy} {e : Eff Op} {decls : List TypeScript.ConstDecl}
    (h : printEntryWith pp table sig name ty e = .ok decls) :
    exportNameSafe name = true ∧ table.find? (fun row => !rowNamesSafe row) = none ∧
      printModuleWith pp sig name ty e = .ok decls := by
  obtain ⟨safe, rows, _, _, _, _, _, printed⟩ := printEntry_checks h
  exact ⟨safe, rows, printed⟩

/-- A checked entry contains only representable stored annotations (`printed-modules`, R2/R3).
The exact hypothesis is successful `printEntry`; host execution remains outside this fact. -/
theorem printEntry_annotations {pp : PiecePrint Op} {table : List Row} {sig : Signature Op}
    {name : String} {ty : EffTy} {e : Eff Op} {decls : List TypeScript.ConstDecl}
    (h : printEntryWith pp table sig name ty e = .ok decls) : annotationRefusal e = none :=
  (printEntry_checks h).2.2.2.2.2.2.1

end Effect4.Program
