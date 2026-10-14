module

public import Effect4.Program.Authoring.Application
public import Effect4.Program.Authoring.Sugar
public import Effect4.Program.Typing
public import Effect4.Program.Native

/-!
# Program.Authoring.ApplicationService — an application as one Effect service

Slice E1 of the emitted-services note (`docs/research/2026-10-13-emitted-services/README.md`;
decisions row 378 (20)). An application becomes one definition block in the shape of a library
service (`Semaphore.serviceDefs`, `src/Effect4/Library/Semaphore/Defs.lean`). The module
printer prints the block's service as an Effect service key and its layer (`printServices`,
`src/Effect4/Codegen/Print.lean`). Nothing here adds a representation of a program.

* **The state is a context.** The initial program `<service>Context` reads the context of the
  keys that the application's rows require: `withFiber (.context R)`, printed as
  `Effect.context<R>()`. The layer runs it once, so the layer requires `R`.
* **A method is an entry under that context.** Entry `e` becomes method `e` of the service, the
  definition `<service>_<e>`. Its request is the state, then the entry's parameters. Its body
  runs the entry at its parameters inside `provideContext state`, which discharges the state's
  keys.
* **A method's columns are the checker's.** A method's answer and error are the checker's type
  of the entry's open program (`Application.openProgram`) at its parameters' types. Its
  requirement row is that type's row less the state's keys.
* **A refused entry refuses the block**, by the entry's name and the refusal: the scope
  reader's or the checker's.
* **An imposed banked block lives in the state** (decisions row 378 (8); `Application.Imposed`).
  The initial program makes each imposed block's state once, beside the context. A method binds
  each state under its name and runs its entry inside the block's wrapper, so `list` may read
  through a cache and `add` may invalidate it. The block's definitions stand first in the module,
  kept. With no imposed block the service is the one above, unchanged.

What it does not establish. The block check (`Checker.checkModule`,
`src/Effect4/Program/Definitions.lean`) types each method's body at its declared columns when
the module builds. A body reads its entry under one more binder than the open program does: the
request. So the columns come from the open program, and the build checks them. Nothing here
states what a method means.
-/

@[expose] public section

namespace Effect4.Program.Authoring

open Effect4.Program
open Effect4.Machine.Env (Requirement)

namespace Application

/-- Why an application has no service block: the scope reader refuses an entry's open program,
or the checker refuses it at the entry's parameters' types. Each names the entry. -/
inductive ServiceRefusal where
  | scope (entry : String) (refusal : Refusal)
  | typing (entry : String) (refusal : TypeRefusal)
  deriving DecidableEq

/-- The keys that the application's rows require, as one requirement row: the context that the
service's layer reads once. -/
def contextKeys (app : Application NativeOp) : Requirement :=
  Requirement.ofList (app.table.flatMap (·.requires))

/-- The service's state: the context of the rows' keys, and, when the application imposes banked
blocks, each block's state beside it, as one tuple (`requestTy`). -/
def stateTy (app : Application NativeOp) : Ty :=
  match app.imposed with
  | [] => .contextOf app.contextKeys
  | ms => .prod (.contextOf app.contextKeys) (requestTy (ms.map (·.stateTy)))

/-- An entry's type: the checker's type of its open program at its parameters' types, over the
application's table and definitions (`Application.signature`). A refusal names the entry. -/
def entryTy (app : Application NativeOp) (e : Application.Entry NativeOp) :
    Except ServiceRefusal EffTy :=
  match app.openProgram e with
  | .error refusal => .error (.scope e.name refusal)
  | .ok program =>
    match Checker.check app.signature (e.params.map (·.2)) [] program with
    | .error refusal => .error (.typing e.name refusal)
    | .ok t => .ok t

/-- Each imposed block's state, made in order by its `make` at the request `unit`, then `k` of
their terms. A step of `contextDef`. -/
def makeStates : List (Application.Imposed NativeOp) → List TermSrc →
    (List TermSrc → Src NativeOp) → Src NativeOp
  | [], made, k => k made
  | m :: ms, made, k => bindWith (Def.invoke m.make []) fun x => makeStates ms (made ++ [x]) k

/-- Each imposed block's state bound under its name, read from its part of the service's state,
around `body`. A step of `methodDef`. -/
def bindStates (ms : List (Application.Imposed NativeOp)) (parts : List TermSrc)
    (body : Src NativeOp) : Src NativeOp :=
  (ms.zip parts).foldr (fun mp rest => bind mp.1.state (succeed mp.2) rest) body

/-- The service's initial program `<service>Context`: it reads the context of the rows' keys
(`Effect.context<R>()`), so the layer requires them and each method runs under them. When the
application imposes banked blocks, it then makes each block's state once, and answers the context
beside them. -/
def contextDef (app : Application NativeOp) (service : String) : DefSrc NativeOp :=
  DefSrc.serviceInit service
    { name := service ++ "Context", params := [], answer := app.stateTy,
      requires := app.contextKeys.elems,
      body := fun _ => match app.imposed with
        | [] => withFiber (Action.context app.contextKeys)
        | ms => bindWith (withFiber (Action.context app.contextKeys)) fun context =>
          makeStates ms [] fun states => succeed (Authoring.app "pair" [context, requestOf states]) }

/-- Method `e` of the service, the definition `<service>_<e>`. Its request is the state, then the
entry's parameters. Its body runs the entry at its parameters under the context
(`provideContext`). When the application imposes banked blocks, the body first binds each block's
state under its name, and the entry runs inside each block's wrapper (`Imposed.wrap`), the first
block's outermost. Its columns are the entry's type `t`, the context's keys discharged. -/
def methodDef (app : Application NativeOp) (service : String) (e : Application.Entry NativeOp)
    (t : EffTy) : DefSrc NativeOp :=
  DefSrc.serviceMethod service e.name
    { name := service ++ "_" ++ e.name, params := ("context", app.stateTy) :: e.params,
      answer := t.answer, error := t.error,
      requires := (Effect4.Row.diff t.requires app.contextKeys).elems,
      body := fun
        | state :: args => match app.imposed with
          | [] => provideContext state (e.applied args)
          | ms => bindStates ms (requestParts ms.length (Authoring.app "snd" [state]))
            (ms.foldr (fun m inner => m.wrap e.name inner)
              (provideContext (Authoring.app "fst" [state]) (e.applied args)))
        | [] => e.body }

/-- **The application as one service** (decisions row 378 (20)): the initial program, then one
method for each entry, in entry order. A refused entry refuses the block. -/
def serviceDefs (app : Application NativeOp) (service : String) :
    Except ServiceRefusal (List (DefSrc NativeOp)) := do
  let methods ← app.entries.mapM fun e => do
    let t ← app.entryTy e
    pure (app.methodDef service e t)
  pure (app.contextDef service :: methods)

/-- The application's module with its service: its declarations, the definitions of each imposed
block, kept and first (`DefSrc.ofBlock`), its own definitions, then the service's block, and a main
program that answers the unit value (the emitted-services note's question 1). The kept blocks
stand first, so a body that invokes its own block keeps its positions. -/
def serviceModule (app : Application NativeOp) (service : String) :
    Except ServiceRefusal (Module NativeOp) := do
  let defs ← app.serviceDefs service
  pure { app.declarations with
    defs := app.imposed.flatMap (fun m => DefSrc.ofBlock m.block) ++ app.defs ++ defs }

end Application

end Effect4.Program.Authoring
