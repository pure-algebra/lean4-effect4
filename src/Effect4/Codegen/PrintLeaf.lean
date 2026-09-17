import Effect4.Program.Typing
import Effect4.Codegen.Names
import Effect4.Codegen.Types
import TypeScript

/-!
# Codegen.PrintLeaf — what the printer's table is made over: refusals, reserved heads, leaves, rows

The part of the printer that is not a clause of the table (`Codegen/Templates.lean`) and that the
table is built from: the refusal alphabet, the reserved heads, binder names, and the printers of
the leaf sorts (terms, causes, literals, fork options, service keys) and of a signature row
(`printRow`, whose inverse is the signature's `spell`). `Codegen/Print.lean` is the printer
proper: the generated fold over the table.

The `Nat` every printing function carries is the environment's length (decision D1: a
positional environment), so the next binder minted is `Var.name n = a{n}`. Nothing else decides
a name: the printer never reads a source identifier and never invents one twice.
-/

namespace Effect4.Program

open Effect4.Machine.Env (Requirement)

/-- Why the printer declined a program. `internalAction` names the `ActionTerm` constructor
whose rc.112 counterpart has no public export with the same frame shape. `layerRef` is the
declaration block's (the host rows slice): a layer reference whose target path names no layer,
so no `const` can be hoisted for it. -/
inductive PrintRefusal
  | internalAction (name : String)
  | layerRef (target : List Nat)
  /-- A row table carries an unsafe spelling (colliding with binders or reserved heads). -/
  | unsafeName (spelling : String)
  /-- A legacy target type has no structural reading in the supported profile. -/
  | typeSpelling (text : String)
deriving DecidableEq, Repr

/-- The first UTF-8 byte; no traversal of a `String` enters the proof graph. -/
def firstByte (s : String) : Option UInt8 := s.toByteArray.data.toList.head?

/-- Every expression head the printer can emit, and the reader recovers. -/
inductive Head
  | succeed | fail | failCause | sync | suspend | flatMap | gen | catchCause
  | matchCauseEffect | onExit | exit | uninterruptible | interruptible | whileLoop
  | yieldNowWith | join | await | forkChild | forkDetach | forkIn | forkScoped | runIn
  | interrupt | interruptAll | interruptAllAs | awaitAll | raceAll | context | fiberId
  | scopeClose | scoped | acquireRelease | causeFail | causeDie | causeInterrupt
  | causeCombine | undefined | withFiber
  | contextService | provide | service | provideService
  | layerSucceed | layerEffect | layerEffectDiscard | layerProvide | layerProvideMerge
  | layerMerge | layerFresh | layerOrDie
  | layerMergeAll
  | catchError | catchIf
  /-- The prelude's two `select` heads (the `select` packet §1.8): `optionCase(s, onNone,
  onSome)` and `caseTag(s, "tag", hit, miss)`, each suspending internally. -/
  | optionCase | caseTag
  /-- `Effect.map`, the head that maps an `iterate`'s printed `Effect.whileLoop` to its result
  (`reduce`'s shape, `internal/effect.ts:4450-4470`). -/
  | map
deriving DecidableEq, Repr

/-- The spelling of each head, exactly as `print` emits it. -/
def Head.spelling : Head → String
  | .succeed => "Effect.succeed"
  | .fail => "Effect.fail"
  | .failCause => "Effect.failCause"
  | .sync => "Effect.sync"
  | .suspend => "Effect.suspend"
  | .flatMap => "Effect.flatMap"
  | .gen => "Effect.gen"
  | .catchCause => "Effect.catchCause"
  | .catchError => "Effect.catch"
  | .catchIf => "Effect.catchIf"
  | .optionCase => "optionCase"
  | .caseTag => "caseTag"
  | .matchCauseEffect => "Effect.matchCauseEffect"
  | .onExit => "Effect.onExit"
  | .exit => "Effect.exit"
  | .uninterruptible => "Effect.uninterruptible"
  | .interruptible => "Effect.interruptible"
  | .whileLoop => "Effect.whileLoop"
  | .map => "Effect.map"
  | .yieldNowWith => "Effect.yieldNowWith"
  | .join => "Fiber.join"
  | .await => "Fiber.await"
  | .forkChild => "Effect.forkChild"
  | .forkDetach => "Effect.forkDetach"
  | .forkIn => "Effect.forkIn"
  | .forkScoped => "Effect.forkScoped"
  | .runIn => "Fiber.runIn"
  | .interrupt => "Fiber.interrupt"
  | .interruptAll => "Fiber.interruptAll"
  | .interruptAllAs => "Fiber.interruptAllAs"
  | .awaitAll => "Fiber.awaitAll"
  | .raceAll => "Effect.raceAll"
  | .context => "Effect.context"
  | .fiberId => "Effect.fiberId"
  | .scopeClose => "Scope.close"
  | .scoped => "Effect.scoped"
  | .acquireRelease => "Effect.acquireRelease"
  | .causeFail => "Cause.fail"
  | .causeDie => "Cause.die"
  | .causeInterrupt => "Cause.interrupt"
  | .causeCombine => "Cause.combine"
  | .undefined => "undefined"
  | .withFiber => "Effect.withFiber"
  | .contextService => "Context.Service"
  | .provide => "Effect.provide"
  | .service => "Effect.service"
  | .provideService => "Effect.provideService"
  | .layerSucceed => "Layer.succeed"
  | .layerEffect => "Layer.effect"
  | .layerEffectDiscard => "Layer.effectDiscard"
  | .layerProvide => "Layer.provide"
  | .layerProvideMerge => "Layer.provideMerge"
  | .layerMerge => "Layer.merge"
  | .layerFresh => "Layer.fresh"
  | .layerOrDie => "Layer.orDie"
  | .layerMergeAll => "Layer.mergeAll"

/-- Every head, once. -/
def heads : List Head :=
  [ .succeed, .fail, .failCause, .sync, .suspend, .flatMap, .gen, .catchCause
  , .matchCauseEffect, .onExit, .exit, .uninterruptible, .interruptible, .whileLoop
  , .yieldNowWith, .join, .await, .forkChild, .forkDetach, .forkIn, .forkScoped, .runIn
  , .interrupt, .interruptAll, .interruptAllAs, .awaitAll, .raceAll, .context, .fiberId
  , .scopeClose, .scoped, .acquireRelease, .causeFail, .causeDie, .causeInterrupt
  , .causeCombine, .undefined, .withFiber
  , .contextService, .provide, .service, .provideService
  , .layerSucceed, .layerEffect, .layerEffectDiscard, .layerProvide, .layerProvideMerge
  , .layerMerge, .layerFresh, .layerOrDie, .layerMergeAll, .catchError, .catchIf
  , .optionCase, .caseTag, .map ]

/-- Every spelling the printer reserves: a row's spelling and a term's atom must avoid
these. -/
def reserved : List String := heads.map Head.spelling

/-- The names in a row cannot capture a printed binder or a reserved program head. -/
def rowNamesSafe (row : Row) : Bool :=
  firstByte row.spelling != some 97 && !reserved.contains row.spelling &&
    row.trailing.all (fun name => firstByte name != some 97 && name != "undefined")

/-- A legal export name for the main declaration: a legal binder that is no printed binder
(`a…`), no reserved head, and no layer reference name (`L_…`), so a declaration block's own
names stay distinct from everything the reader decodes by name. -/
def exportNameSafe (name : String) : Bool :=
  Effect4.Codegen.Names.binderName name && firstByte name != some 97 &&
    !reserved.contains name && (LayerTerm.readRefName name).isNone


/-- The binder minted for environment position `index`: `a0`, `a1`, … The environment is
positional, so a position is a name and the printer needs no source identifiers. -/
def Var.name (index : Nat) : String := "a" ++ toString index

/-- A literal as target syntax: `undefined` for unit, the number, `true`/`false`, and the
quoted string (the renderer owns the quoting and the escapes). -/
def printLit : Lit → TypeScript.Expr
  | .unit => .ident "undefined"
  | .nat value => .int (Int.ofNat value)
  | .bool value => .bool value
  | .str value => .str value

mutual
  /-- A pure term: a variable as its binder name, a literal as itself, and an atom applied
  to its arguments as the call `atom(args)`. -/
  def printTerm : Term → TypeScript.Expr
    | .var index => .ident (Var.name index)
    | .lit value => printLit value
    | .app atom args => .call (.ident atom) (printTerms args)

  /-- The argument list of an atom application, in order. -/
  def printTerms : Terms → List TypeScript.Expr
    | .nil => []
    | .cons head tail => printTerm head :: printTerms tail
end

/-- A cause as the public `Cause` constructors of rc.112. `Cause.merge` is not an export at
the pin, so the merge of two causes is spelled `Cause.combine` (§5.1). -/
def printCause : CauseTerm → TypeScript.Expr
  | .fail error => .call (.ident "Cause.fail") [printTerm error]
  | .die defect => .call (.ident "Cause.die") [printTerm defect]
  | .interrupt none => .call (.ident "Cause.interrupt") []
  | .interrupt (some who) => .call (.ident "Cause.interrupt") [printTerm who]
  | .both left right => .call (.ident "Cause.combine") [printCause left, printCause right]

/-- The two components of a `pair` application, the request shape a tuple-call row
receives from an admitted program. -/
def pairArgs? : Term → Option (Term × Term)
  | .app atom (.cons x (.cons y .nil)) => if atom = "pair" then some (x, y) else none
  | _ => none

theorem pairArgs?_some {r x y : Term} (h : pairArgs? r = some (x, y)) :
    r = .app "pair" (.cons x (.cons y .nil)) := by
  unfold pairArgs? at h
  split at h
  · split at h
    · rename_i hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hp
      rfl
    · cases h
  · cases h

/-- The argument list of a tuple-call row (source-repairs §18): the components of a
`pair` application print as the two arguments the pinned two-argument export declares,
so the host infers the export's type parameters from them; any other request, a saved
variable in the admitted image, prints as `fst(request)` and `snd(request)`, one read
of the value per component. -/
def printTupleArgs (request : Term) : List TypeScript.Expr :=
  match pairArgs? request with
  | some (x, y) => [printTerm x, printTerm y]
  | none => [.call (.ident "fst") [printTerm request], .call (.ident "snd") [printTerm request]]

/-- A row's called head: its `spelling`, applied to the declared type arguments when it has
any. rc.112's `Deferred.make` has defaulted type parameters, so the arguments alone do not
determine the handle's types and the call must carry them (`E4-CHECK-CE-013`). -/
def rowTypeArgs (row : Row) : Option (List TypeScript.TypeRef) :=
  row.typeArgs.mapM Effect4.Codegen.Types.parseLegacy

def printRowHead (row : Row) : Except PrintRefusal TypeScript.Expr :=
  match rowTypeArgs row with
  | none => .error (.typeSpelling row.spelling)
  | some [] => .ok (.ident row.spelling)
  | some args => .ok (.generic (.ident row.spelling) args)

/-- The arguments of a method use the ordinary call or tuple-call convention.
The receiver is the first component of the original request. -/
def methodArgsRow (row : Row) : Row :=
  let args := match row.request with
    | .prod _ args => args
    | _ => .never
  { row with request := args, shape := match args with
      | .prod _ _ => .tupleCall
      | _ => .call }

@[simp] theorem methodArgsRow_spelling (row : Row) : (methodArgsRow row).spelling = row.spelling := rfl
@[simp] theorem methodArgsRow_trailing (row : Row) : (methodArgsRow row).trailing = row.trailing := rfl
@[simp] theorem methodArgsRow_typeArgs (row : Row) : (methodArgsRow row).typeArgs = row.typeArgs := rfl
@[simp] theorem methodArgsRow_kind (row : Row) : (methodArgsRow row).kind = row.kind := rfl

theorem methodArgsRow_shape (row : Row) :
    (methodArgsRow row).shape = .call ∨ (methodArgsRow row).shape = .tupleCall := by
  unfold methodArgsRow
  split <;> simp
  split <;> simp

def printMethodArgs (row : Row) (args : Term) : List TypeScript.Expr :=
  let trailing := row.trailing.map TypeScript.Expr.ident
  if (methodArgsRow row).shape = .tupleCall then printTupleArgs args ++ trailing
  else if (methodArgsRow row).request = Ty.unit then trailing
  else printTerm args :: trailing

def printMethod (row : Row) (receiver args : Term) : Except PrintRefusal TypeScript.Expr :=
  match rowTypeArgs row with
  | none => .error (.typeSpelling row.spelling)
  | some [] => .ok (.method (printTerm receiver) row.spelling (printMethodArgs row args))
  | some typeArgs => .ok (.call (.generic (.member (printTerm receiver) row.spelling) typeArgs)
      (printMethodArgs row args))

/-- A row's operation, by the row's declared shape and request type: a value row is the
bare `spelling` (the service route's nullary rows), a call row on a `unit` request is
`spelling()`, and every other call row is `spelling(request)`. A tuple-call row receives
`printTupleArgs` of its request as two ordinary arguments, then the declared trailing
names. A row that declares type arguments carries them on the head. -/
def printRow (row : Row) (request : Term) : Except PrintRefusal TypeScript.Expr := do
  let trailing := row.trailing.map TypeScript.Expr.ident
  match row.shape with
  | .value => .ok (.ident row.spelling)
  | .call =>
    let head ← printRowHead row
    if row.request = Ty.unit then .ok (.call head trailing)
    else .ok (.call head (printTerm request :: trailing))
  | .tupleCall =>
    let head ← printRowHead row
    .ok (.call head (printTupleArgs request ++ trailing))
  | .method =>
    match pairArgs? request with
    | some (receiver, args) => printMethod row receiver args
    | none => printMethod row (.app "fst" (.cons request .nil)) (.app "snd" (.cons request .nil))

/-- The fork options object rc.112's fork family takes:
`{ startImmediately: b, uninterruptible: true | false | "inherit" }`. `daemon` is not a
field — it selects `Effect.forkChild` against `Effect.forkDetach` instead. -/
def printForkOptions (options : Effect4.Supervision.ForkOptions) : TypeScript.Expr :=
  .object
    [ ("startImmediately", .bool options.startImmediately)
    , ("uninterruptible",
        match options.maskMode with
        | .uninterruptible => .bool true
        | .interruptible => .bool false
        | .inherit => .str "inherit") ]

variable {Op : Type}

/-- A service key as rc.112 spells one — `Context.Service<Shape>("key")`
(`Context.ts:201-215`): the key's two numbers as the string that is its runtime identity
(`:219`, so two spellings of one key are one service), with its carrier from the signature's
service table as the type argument when the table has one. Minted from the key's own data,
as `Var.name` mints a binder from its position: the printer invents no name. -/
def printKey (sig : Signature Op) (key : ServiceKey) : Except PrintRefusal TypeScript.Expr := do
  let head ← match sig.serviceTy key with
    | some ty => match Effect4.Codegen.Types.ofTy ty with
      | some target => .ok (.generic (.ident "Context.Service") [target])
      | none => .error (.typeSpelling ty.render)
    | none => .ok (.ident "Context.Service")
  .ok (.call head [.str ("k" ++ toString key.name.value ++ "_" ++ toString key.service.value)])

end Effect4.Program
