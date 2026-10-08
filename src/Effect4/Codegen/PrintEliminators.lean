import Effect4.Codegen.Print
import Effect4.Program.Typing.Annotate

/-!
# Print the checked arguments of eliminators

This printer serves `exact-codecs`, R8, through typed-print reconstruction after the named erasure.
The generated term fold retains source terms and reads their checked slot environments.
The template printer retains its table and changes term slots and named generic heads.
`NoJoin` excludes added generic arguments at these sites and at row calls.
The reconstruction laws live in `Effect4.Laws.Codegen.PrintTyped`.
TypeScript typing and execution require separate compiler and runtime evidence.
-/

set_option autoImplicit false

namespace Effect4.Codegen.PrintEliminators

open Effect4.Program TypeScript

variable {Op : Type}

/-- Refuse missing typing evidence instead of inventing a column. -/
def need {α : Type} (name : String) : Option α → Except PrintRefusal α
  | some value => .ok value
  | none => .error (.internalAction ("typed:" ++ name))

/-- A proper union in the checker, before target spellings identify members. -/
def proper (ty : Ty) : Bool := decide (1 < ty.normalize.members.length)

/-- An effect column or row has more than one retained member. -/
def columnsJoin (ty : EffTy) : Bool :=
  proper ty.answer || proper ty.error || decide (1 < ty.requires.elems.length)

/-- Refusing structural target projection; no fallback to any or unknown. -/
def target (ty : Ty) : Except PrintRefusal TypeRef :=
  match Types.ofTy ty with
  | some value => .ok value
  | none => .error (.typeSpelling ty.render)

/-- The actual three columns, in the target's A,E,R order. -/
def «columns» (sig : Signature Op) (ty : EffTy) : Except PrintRefusal (List TypeRef) := do
  return [← target ty.answer, ← target ty.error, requirementType sig.scopeKey ty.requires]

/-- A whole effect type, for target heads whose one parameter is the complete effect. -/
def effectTarget (sig : Signature Op) (ty : EffTy) : Except PrintRefusal TypeRef := do
  return .name ["Effect", "Effect"] (← «columns» sig ty)

/-- The original term plus its environment-dependent print. Literal flags follow `argTy`. -/
def TermCarrier : TermFam → Type
  | .term => Term × (TyEnv → Bool → Except PrintRefusal Expr)
  | .terms => Terms × (TyEnv → Bool → Except PrintRefusal (List Expr))

/-- Repeat the checked stored accumulator type on the first callback parameter.
Erasure verifies equality with the generic head before retaining its stored accumulator.
The inferred form instead annotates both callback parameters on a bare fold. -/
def storedFoldStep (n : Nat) (acc : TypeRef) (body : Expr) : Expr :=
  .lambda [{ name := Template.varName n, type := some acc },
    { name := Template.varName (n + 1) }] body

/-- The checked term fold. Raw declarations remain raw; projected annotations refuse when unavailable. -/
def termAlg (sig : Signature Op) : TermAlgebra TermCarrier where
  term_var index := (.var index, fun _ _ => .ok (.ident (Var.name index)))
  term_lit value := (.lit value, fun _ _ => .ok (printLit value))
  term_app name args := (.app name args.1, fun env _ => do
    let values ← args.2 env (sig.constAtom name)
    let plain : Expr := .call (.ident name) values
    if ["causeIsFail", "causeIsDie", "causeIsInterrupt", "causeError"].contains name then
      match args.1 with
      | .cons input .nil =>
        let inputTy ← need name (termTy sig env input)
        if proper inputTy then
          let error ← need name (causeInputError? inputTy)
          -- `causeInputError_upper` proves the two-family input is below this exact upper.
          withHeadTypes name [← target .unknown, ← target error] plain
        else return plain
      | _ => return plain
    else return plain)
  term_record fields names values := (.record fields names values.1, fun env _ => do
    let children ← values.2 env true
    match Classes.classTag? fields names values.1 with
    | some tag => return Classes.writeClass tag names.tail children.tail
    | none => return Record.writeRecord fields names children)
  term_field mode receiver name := (.field mode receiver.1 name, fun env _ => do
    let value ← receiver.2 env false
    let ty ← need "record field" (termTy sig env receiver.1)
    let plain := Record.writeField (decide (mode = .optional)) name value
    if proper ty then
      match plain with
      | .call head args => return .call (.generic head [← target ty]) args
      | _ => throw (.internalAction "typed:record field shape")
    else return plain)
  term_recordSet receiver name replacement := (.recordSet receiver.1 name replacement.1, fun env _ => do
    let value ← receiver.2 env false
    let newValue ← replacement.2 env true
    let receiverTy ← need "record set receiver" (termTy sig env receiver.1)
    let valueTy ← need "record set value" (argTy sig env true replacement.1)
    if proper receiverTy || proper valueTy then
      let key : Expr := .call (.generic (.ident "recordSet") [.literal name]) [.str name]
      let applied : Expr := .call (.generic key [← target receiverTy]) [value]
      return .call (.generic applied [← target valueTy]) [newValue]
    else return Record.writeSet name value newValue)
  term_tupleAt receiver index := (.tupleAt receiver.1 index, fun env _ => do
    return Tuple.writeAt index (← receiver.2 env false))
  term_fold stored list init body := (.fold stored list.1 init.1 body.1, fun env _ => do
    let listTy ← need "fold list" (termTy sig env list.1)
    let item ← need "fold item" (Checker.listOf? listTy)
    let initTy ← need "fold initial" (termTy sig env init.1)
    let acc := stored.getD initTy
    let listExpr ← list.2 env false
    let initExpr ← init.2 env false
    let bodyExpr ← body.2 (env ++ [acc, item]) false
    if proper listTy || proper acc || proper item then
      let accTarget ← target acc
      let itemTarget ← target item
      match stored with
      | some _ =>
        return .call (.generic (.ident "fold") [accTarget, itemTarget])
          [listExpr, initExpr, storedFoldStep env.length accTarget bodyExpr]
      | none => return .call (.ident "fold") [listExpr, initExpr,
          .lambda [{ name := Template.varName env.length, type := some accTarget },
            { name := Template.varName (env.length + 1), type := some itemTarget }] bodyExpr]
    else
      -- Preserve the existing raw print exactly. `annotationRefusal` excludes its unsupported
      -- stored-type fallback from the checked target profile; the typed branch never invents one.
      return ListFold.write env.length (stored.map ListFold.typeArg) listExpr initExpr bodyExpr)
  terms_nil := (.nil, fun _ _ => .ok [])
  terms_cons head tail := (.cons head.1 tail.1, fun env const => do
    return (← head.2 env const) :: (← tail.2 env const))

/-- The generated fold at a term's checked slot environment. -/
def term (sig : Signature Op) (env : TyEnv) (const : Bool) (t : Term) : Except PrintRefusal Expr :=
  (cata_term (termAlg sig) t).2 env const

/-- Cause construction keeps its existing spelling and uses typed terms at its leaves. -/
def causeAlg (sig : Signature Op) : CauseTermAlgebra (fun _ => TyEnv → Except PrintRefusal Expr) where
  cause_fail t env := do return .call (.ident "Cause.fail") [← term sig env false t]
  cause_die t env := do return .call (.ident "Cause.die") [← term sig env false t]
  cause_interrupt who env := do
    let args ← who.toList.mapM (term sig env false)
    return .call (.ident "Cause.interrupt") args
  cause_both left right env := do return .call (.ident "Cause.combine") [← left env, ← right env]

/-- A node and its actual environment from the checker's address rule. -/
structure Context (Op : Type) where
  node : Node Op
  env : TyEnv
  path : List Nat := []
  entries : Option (List Table.Entry) := none

/-- Address lookup for every node sort, including actions and statements. -/
def contextAt (sig : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) : Option (Context Op) := do
  let node ← (Node.eff p).at_ path
  let env ← (Node.eff p).envAt sig (.env env0) path
  return ⟨node, env.tyEnv, path, none⟩

/-- Read a context from the existing annotation table, retaining its checked child answers. -/
def contextAtTable (entries : List Table.Entry) (p : Eff Op) (path : List Nat) :
    Option (Context Op) := do
  let node ← (Node.eff p).at_ path
  let entry ← entries.find? fun entry => decide (entry.path = path)
  let env ← entry.env
  return ⟨node, env.tyEnv, path, some entries⟩

/-- A child's checked answer from the shared annotation table, when that table is supplied. -/
def childTy (sig : Signature Op) (ctx : Context Op) (index : Nat) : Option EffTy :=
  match ctx.entries with
  | some entries => do
    let entry ← entries.find? fun entry => decide (entry.path = ctx.path ++ [index])
    let result ← entry.result
    result.toOption
  | none => do
    let child ← ctx.node.child index
    let childEnv ← ctx.node.childEnv sig (.env ctx.env) index
    match child with
    | .eff p => effTy sig childEnv.tyEnv p
    | _ => none

/-- Extended slots use the checker-defined environment, never an inferred binder count. -/
def slotEnv (sig : Signature Op) (ctx : Context Op) (index : Nat) : Option TyEnv :=
  match ctx.node, index with
  | .eff (.catchIf _ _ _), 0 => (childTy sig ctx 0).map fun body => ctx.env ++ [body.error]
  | .eff (.iterate _ _ _ _ _ _), 2 => ctx.node.extSlotEnv sig ctx.env .iterateTest
  | .eff (.iterate cursorTy initial _ _ _ _), 3 => do
    let c0 ← termTy sig ctx.env initial
    let body ← childTy sig ctx 0
    return ctx.env ++ [cursorTy.getD c0, body.answer]
  | .eff (.iterate _ _ _ _ _ _), 4 => ctx.node.extSlotEnv sig ctx.env .iterateResult
  | _, _ => some ctx.env

/-- A leaf argument's typed print. The template still owns its structural binder depth. -/
def printArg (sig : Signature Op) (ctx : Context Op) (index depth : Nat) :
    ArgF Op Templates.Carrier → Except PrintRefusal (Option Template.Arg)
  | .term t => do
    let env ← need "term slot" (slotEnv sig ctx index)
    if env.length = depth then return some (.expr (← term sig env false t))
    else throw (.internalAction "typed:term slot depth")
  | .optTerm (some t) => do
    let env ← need "optional term slot" (slotEnv sig ctx index)
    if env.length = depth then return some (.expr (← term sig env false t))
    else throw (.internalAction "typed:optional term slot depth")
  | .cause c => do
    if ctx.env.length = depth then return some (.expr (← cata_cause (causeAlg sig) c ctx.env))
    else throw (.internalAction "typed:cause slot depth")
  | other => Templates.printArg sig depth other

/-- Instantiate the existing template with typed term leaves. -/
def printArgs (sig : Signature Op) (ctx : Context Op) (fam : EffFam) (n : Nat) (out : Templates.RowOut) :
    List (ArgF Op Templates.Carrier) → Nat → Except PrintRefusal Template.Subst
  | [], _ => .ok []
  | arg :: rest, index => do
    let value ← printArg sig ctx index
      (Templates.argDepth fam (Templates.argSortOf arg) n (out.levelAt index)) arg
    let tail ← printArgs sig ctx fam n out rest (index + 1)
    match value with
    | some value => return (index, value) :: tail
    | none => return tail

/-- Typed row shape printing. It keeps row-declared and operation-carried arguments intact. -/
def row (sig : Signature Op) (env : TyEnv) (r : Effect4.Program.Row) (request : Term) : Except PrintRefusal Expr := do
  let trailing := r.trailing.map Expr.ident
  let tupleArgs (q : Term) : Except PrintRefusal (List Expr) := do
    match pairArgs? q with
    | some (a, b) => return [← term sig env false a, ← term sig env false b]
    | none =>
      let value ← term sig env false q
      return [.call (.ident "fst") [value], .call (.ident "snd") [value]]
  match r.shape with
  | .value => return .ident r.spelling
  | .call =>
    let head ← printRowHead r
    if r.request = .unit then return .call head trailing
    else return .call head ((← term sig env false request) :: trailing)
  | .tupleCall => return .call (← printRowHead r) ((← tupleArgs request) ++ trailing)
  | .method =>
    let (receiver, args) := (pairArgs? request).getD
      (.app "fst" (.cons request .nil), .app "snd" (.cons request .nil))
    let targetExpr ← term sig env false receiver
    let argsRow := methodArgsRow r
    let argsExpr ← if argsRow.shape = .tupleCall then tupleArgs args
      else if argsRow.request = .unit then pure []
      else do pure [← term sig env false args]
    let declared ← need r.spelling (rowTypeArgs r)
    if declared.isEmpty then return .method targetExpr r.spelling (argsExpr ++ trailing)
    else return .call (.generic (.member targetExpr r.spelling) declared) (argsExpr ++ trailing)

/-- Typed request and operation term, with independent inferred row arguments. -/
def perform (sig : Signature Op) (ctx : Context Op) (op : Op) (request : Term)
    (inferred : Option (List Ty)) : Except PrintRefusal Expr := do
  let base ← row sig ctx.env (sig.rowOf op) request
  let owned := sig.typeArgsOf op
  let call ← match inferred with
    | some (ty :: tys) => do
        if owned.isEmpty && (sig.rowOf op).typeArgs.isEmpty then
          withHeadTypes (sig.rowOf op).spelling (← (ty :: tys).mapM target) base
        else throw (.typeSpelling (sig.rowOf op).spelling)
    | _ => do
        if owned.isEmpty then pure base
        else withHeadTypes (sig.rowOf op).spelling (← owned.mapM target) base
  match sig.termOf op with
  | none => return call
  | some b =>
    let env ← need "operation term" (ctx.node.extSlotEnv sig ctx.env .opTerm)
    withFunction (sig.rowOf op).spelling (Binders.write ctx.env.length [0] (← term sig env false b.term)) call

/-- Join arguments for the supported program and action heads, in each target's declared order. -/
def decorate (sig : Signature Op) (ctx : Context Op) (plain : Expr) : Except PrintRefusal Expr := do
  let input (t : Term) := need "eliminator input" (termTy sig ctx.env t)
  let fiber (t : Term) := do
    let ty ← input t
    let pair ← need "fiber columns" (fiberTy ty)
    pure (ty, pair)
  let apply (name : String) (types : List TypeRef) := withHeadTypes name types plain
  match ctx.node with
  | .eff (.select _ .bool _ _) => return plain
  | .eff (.select scrutinee decision _ _) =>
    let source ← input scrutinee
    let left ← need "select first child" (childTy sig ctx 0)
    let right ← need "select second child" (childTy sig ctx 1)
    if proper source || columnsJoin left || columnsJoin right then
      let branches := (← «columns» sig left) ++ (← «columns» sig right)
      match decision with
      | .option =>
        let payload ← need "option payload" (optionTy source)
        apply "optionCase" ((← target payload) :: branches)
      | .tag tag => apply "caseTag" ((← target source) :: .literal tag :: branches)
      | .recordTag tag => apply "caseTagR" ((← target source) :: .literal tag :: branches)
      | .bool => return plain
    else return plain
  | .eff (.awaitFiber receiver mode) =>
    let (source, pair) ← fiber receiver
    if proper source then
      apply (match mode with | .joinEffect => "Fiber.join" | .awaitValue => "Fiber.await")
        [← target pair.1, ← target pair.2]
    else return plain
  | .eff (.scoped _) =>
    let body ← need "scoped child" (childTy sig ctx 0)
    if columnsJoin body then apply "Effect.scoped" (← «columns» sig body) else return plain
  | .eff (.acquireRelease _ _) =>
    let acquire ← need "acquire child" (childTy sig ctx 0)
    let release ← need "release child" (childTy sig ctx 1)
    if columnsJoin acquire || columnsJoin release then
      apply "Effect.acquireRelease" ((← «columns» sig acquire) ++ [requirementType sig.scopeKey release.requires])
    else return plain
  | .action (.fork _ _) | .action (.forkScoped _ _) =>
    let body ← need "fork child" (childTy sig ctx 0)
    if columnsJoin body then apply "fork" [← effectTarget sig body] else return plain
  | .action (.forkIn _ _ _) =>
    let body ← need "forkIn child" (childTy sig ctx 0)
    if columnsJoin body then apply "Effect.forkIn" (← «columns» sig body) else return plain
  | .action (.interrupt receiver) =>
    let (source, pair) ← fiber receiver
    if proper source then apply "Fiber.interrupt" [← target pair.1, ← target pair.2] else return plain
  | .action (.runIn receiver _) =>
    let (source, pair) ← fiber receiver
    if proper source then
      -- Only the inner call takes A,E; the outer Effect.withFiber call does not.
      match plain with
      | .call head [.arrowBlock params [.exprStmt call, .ret result] resultTy] =>
        return .call head [.arrowBlock params
          [.exprStmt (← withHeadTypes "Fiber.runIn" [← target pair.1, ← target pair.2] call), .ret result] resultTy]
      | _ => throw (.internalAction "typed:runIn shape")
    else return plain
  | .action (.interruptAll receivers _) =>
    let source ← input receivers
    let item ← need "interruptAll list" (Checker.listOf? source)
    let _ ← need "interruptAll fibers" (fiberTy item)
    if proper source || proper item then apply "interruptAll" [← target source] else return plain
  | .action (.awaitAll receivers) =>
    let source ← input receivers
    let item ← need "awaitAll list" (Checker.listOf? source)
    let pair ← need "awaitAll fibers" (fiberTy item)
    if proper source || proper item then apply "Fiber.awaitAll" [← target (.fiberOf pair.1 pair.2)] else return plain
  | .action (.closeScope _ exit) =>
    let source ← input exit
    let pair ← need "closeScope exit" (Checker.exitOf? source)
    if proper source then apply "Scope.close" [← target pair.1, ← target pair.2] else return plain
  | _ => return plain

/-- The table layer with typed leaves and actual checked columns. Existing profile refusals run first. -/
def layer (sig : Signature Op) (ctx : Context Op) (inferred : Option (List Ty))
    (fam : EffFam) (ctor : String) (args : List (ArgF Op Templates.Carrier)) : Templates.Carrier fam :=
  match fam with
  | .eff | .action | .layer => fun n => do
    match Templates.table.find? fun row => row.selects fam ctor args with
    | none => throw (Templates.tableDefect ctor)
    | some row => match row.out with
      | .refuse name => throw (.internalAction name)
      | .stmt _ => throw (Templates.tableDefect ctor)
      | .rowCall => match args with
        | [.op op, .term request] => perform sig ctx op request inferred
        | _ => throw (Templates.tableDefect ctor)
      | .tpl tpl =>
        let subst ← printArgs sig ctx fam n (.tpl tpl) args 0
        let printed ← need ctor (Template.inst n subst tpl)
        decorate sig ctx printed
  | .stmt => fun n =>
    match Templates.table.find? fun row => row.selects .stmt ctor args with
    | some ⟨_, _, _, .stmt tpl⟩ => do
      let subst ← printArgs sig ctx .stmt n (.stmt tpl) args 0
      let statement ← need ctor (Template.instStmt n subst tpl)
      return (statement, tpl.declares)
    | _ => .error (Templates.tableDefect ctor)
  | .effs => Templates.tableLayer sig .effs ctor args
  | .layers => Templates.tableLayer sig .layers ctor args
  | .stmts => Templates.tableLayer sig .stmts ctor args

/-- Missing checked context is a print refusal at every node sort. -/
def missing : (fam : EffFam) → Templates.Carrier fam
  | .eff => fun _ => .error (.internalAction "typed:missing context")
  | .action => fun _ => .error (.internalAction "typed:missing context")
  | .layer => fun _ => .error (.internalAction "typed:missing context")
  | .effs => fun _ => .error (.internalAction "typed:missing context")
  | .layers => fun _ => .error (.internalAction "typed:missing context")
  | .stmt => fun _ => .error (.internalAction "typed:missing context")
  | .stmts => fun _ => .error (.internalAction "typed:missing context")

/-! The P2b annotation-absence detector. It excludes the parent's row-call detector. -/

def JoinCarrier : TermFam → Type
  | .term => Term × (TyEnv → Bool → Bool)
  | .terms => Terms × (TyEnv → Bool → Bool)

/-- Missing typing at an existing site prevents a NoJoin claim. -/
def properAt (sig : Signature Op) (env : TyEnv) (const : Bool) (t : Term) : Bool :=
  ((argTy sig env const t).map proper).getD true

/-- The same term fold's exact insertion conditions and extended fold-body environment. -/
def termJoinAlg (sig : Signature Op) : TermAlgebra JoinCarrier where
  term_var index := (.var index, fun _ _ => false)
  term_lit value := (.lit value, fun _ _ => false)
  term_app name args := (.app name args.1, fun env _ =>
    let children := args.2 env (sig.constAtom name)
    if ["causeIsFail", "causeIsDie", "causeIsInterrupt", "causeError"].contains name then
      match args.1 with
      | .cons input .nil => children || properAt sig env false input
      | _ => children
    else children)
  term_record fields names values := (.record fields names values.1, fun env _ => values.2 env true)
  term_field mode receiver name := (.field mode receiver.1 name, fun env _ =>
    receiver.2 env false || properAt sig env false receiver.1)
  term_recordSet receiver name replacement := (.recordSet receiver.1 name replacement.1, fun env _ =>
    receiver.2 env false || replacement.2 env true ||
      properAt sig env false receiver.1 || properAt sig env true replacement.1)
  term_tupleAt receiver index := (.tupleAt receiver.1 index, fun env _ => receiver.2 env false)
  term_fold stored list init body := (.fold stored list.1 init.1 body.1, fun env _ =>
    match termTy sig env list.1, termTy sig env init.1 with
    | some listTy, some initTy =>
      match Checker.listOf? listTy with
      | some item =>
        let acc := stored.getD initTy
        list.2 env false || init.2 env false || body.2 (env ++ [acc, item]) false ||
          proper listTy || proper acc || proper item
      | none => true
    | _, _ => true)
  terms_nil := (.nil, fun _ _ => false)
  terms_cons head tail := (.cons head.1 tail.1, fun env const => head.2 env const || tail.2 env const)

def termJoin (sig : Signature Op) (env : TyEnv) (const : Bool) (t : Term) : Bool :=
  (cata_term (termJoinAlg sig) t).2 env const

def causeJoinAlg (sig : Signature Op) : CauseTermAlgebra (fun _ => TyEnv → Bool) where
  cause_fail t env := termJoin sig env false t
  cause_die t env := termJoin sig env false t
  cause_interrupt who env := who.toList.any (termJoin sig env false)
  cause_both left right env := left env || right env

def nodeArgs : Node Op → List (ArgF Op (EffSelfCarrier Op))
  | .eff p => (view_eff p).2
  | .action a => (view_action a).2
  | .stmt s => (view_stmt s).2
  | .stmts ss => (view_stmts ss).2
  | .effs es => (view_effs es).2
  | .layer l => (view_layer l).2
  | .layers ls => (view_layers ls).2

/-- Node-head insertion conditions match `decorate`, including each target's arity. -/
def nodeJoin (sig : Signature Op) (ctx : Context Op) : Bool :=
  match ctx.node with
  | .eff (.select _ .bool _ _) => false
  | .eff (.select t _ _ _) =>
    properAt sig ctx.env false t ||
      ((childTy sig ctx 0).map columnsJoin).getD true ||
      ((childTy sig ctx 1).map columnsJoin).getD true
  | .eff (.awaitFiber t _) => properAt sig ctx.env false t
  | .eff (.scoped _) => ((childTy sig ctx 0).map columnsJoin).getD true
  | .eff (.acquireRelease _ _) =>
    ((childTy sig ctx 0).map columnsJoin).getD true ||
      ((childTy sig ctx 1).map columnsJoin).getD true
  | .action (.fork _ _) | .action (.forkIn _ _ _) | .action (.forkScoped _ _) =>
    ((childTy sig ctx 0).map columnsJoin).getD true
  | .action (.runIn t _) | .action (.interrupt t) => properAt sig ctx.env false t
  | .action (.interruptAll ts _) | .action (.awaitAll ts) =>
    match termTy sig ctx.env ts with
    | some source => proper source || ((Checker.listOf? source).map proper).getD true
    | none => true
  | .action (.closeScope _ exit) => properAt sig ctx.env false exit
  | _ => false

/-- Term slots include the operation's own body and the five extended-slot environments. -/
def slotsJoin (sig : Signature Op) (ctx : Context Op) : Bool :=
  ((nodeArgs ctx.node).zipIdx).any fun (arg, index) =>
    match arg with
    | .term t | .optTerm (some t) =>
      ((slotEnv sig ctx index).map fun env => termJoin sig env false t).getD true
    | .cause c => cata_cause (causeJoinAlg sig) c ctx.env
    | .op op => match sig.termOf op with
      | none => false
      | some b => ((ctx.node.extSlotEnv sig ctx.env .opTerm).map fun env =>
          termJoin sig env false b.term).getD true
    | _ => false

/-- Pointwise insertion detection over the shared checked annotation table. -/
def joinsAtTable (sig : Signature Op) (entries : List Table.Entry) (p : Eff Op) (path : List Nat) : Bool :=
  ((contextAtTable entries p path).map fun ctx => nodeJoin sig ctx || slotsJoin sig ctx).getD false

/-- Invalid addresses insert nothing. Existing addresses include node and term sites. -/
def joinsAt (sig : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) : Bool :=
  joinsAtTable sig (annotate sig env0 p) p path

/-- Whether an enumerated program node requests an approved P2b annotation. -/
def needsSitesAt (sig : Signature Op) (entries : List Table.Entry) (p : Eff Op) : Bool :=
  (Node.addresses (.eff p)).any (joinsAtTable sig entries p)

/-- Site detection and printing share the same checked annotation table. -/
def needsSites (sig : Signature Op) (env0 : TyEnv) (p : Eff Op) : Bool :=
  needsSitesAt sig (annotate sig env0 p) p

/-- P2b's half of NoJoin. Combine with the parent's independent row-call annotation absence. -/
def NoSiteTypes (sig : Signature Op) (env0 : TyEnv) (p : Eff Op) : Prop :=
  ∀ path, joinsAt sig env0 p path = false

end Effect4.Codegen.PrintEliminators
