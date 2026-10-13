module

public import Effect4.Program.Authoring.Application
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

/-- The service's state: the context of the rows' keys. -/
def stateTy (app : Application NativeOp) : Ty := .contextOf app.contextKeys

/-- An entry's type: the checker's type of its open program at its parameters' types, over the
application's table. A refusal names the entry. -/
def entryTy (app : Application NativeOp) (e : Application.Entry NativeOp) :
    Except ServiceRefusal EffTy :=
  match app.openProgram e with
  | .error refusal => .error (.scope e.name refusal)
  | .ok program =>
    match Checker.check (nativeSignature app.table) (e.params.map (·.2)) [] program with
    | .error refusal => .error (.typing e.name refusal)
    | .ok t => .ok t

/-- The service's initial program `<service>Context`: it reads the context of the rows' keys
(`Effect.context<R>()`), so the layer requires them and each method runs under them. -/
def contextDef (app : Application NativeOp) (service : String) : DefSrc NativeOp :=
  DefSrc.serviceInit service
    { name := service ++ "Context", params := [], answer := app.stateTy,
      requires := app.contextKeys.elems,
      body := fun _ => withFiber (Action.context app.contextKeys) }

/-- Method `e` of the service, the definition `<service>_<e>`. Its request is the state, then the
entry's parameters. Its body runs the entry at its parameters under the state
(`provideContext`). Its columns are the entry's type `t`, the state's keys discharged. -/
def methodDef (app : Application NativeOp) (service : String) (e : Application.Entry NativeOp)
    (t : EffTy) : DefSrc NativeOp :=
  DefSrc.serviceMethod service e.name
    { name := service ++ "_" ++ e.name, params := ("context", app.stateTy) :: e.params,
      answer := t.answer, error := t.error,
      requires := (Effect4.Row.diff t.requires app.contextKeys).elems,
      body := fun
        | state :: args => provideContext state (e.applied args)
        | [] => e.body }

/-- **The application as one service** (decisions row 378 (20)): the initial program, then one
method for each entry, in entry order. A refused entry refuses the block. -/
def serviceDefs (app : Application NativeOp) (service : String) :
    Except ServiceRefusal (List (DefSrc NativeOp)) := do
  let methods ← app.entries.mapM fun e => do
    let t ← app.entryTy e
    pure (app.methodDef service e t)
  pure (app.contextDef service :: methods)

/-- The application's module with its service: its declarations and its own definitions, then
the service's block, and a main program that answers the unit value (the emitted-services note's
question 1). -/
def serviceModule (app : Application NativeOp) (service : String) :
    Except ServiceRefusal (Module NativeOp) := do
  let defs ← app.serviceDefs service
  pure { app.declarations with defs := app.defs ++ defs }

end Application

end Effect4.Program.Authoring
