import Effect4.Laws.Api.ModuleReadable
import Test.Program.DefinitionsControls
import Test.Program.InvokeControls

/-!
# A printed definition block (decisions row 328, slice PROC-3)

The module printer prints each definition of a block as a constant before the layers and the
main declaration, and an invocation as the definition's name applied to its request
(`Program.printModule`). The reader reads them back (`Program.readModule`). The round trip is
`Api.printModule_roundTrip` on a program in `blockReadable`, and the claim is
`module-defs-round-trip` (`readModule_printModule_defs`).

The lines below are finite evaluations of the printed text and of the readable domain at fixed
programs, the controls of each refusal, and one reader of the name bridge at a real block. The
printed text is target syntax only: tsgo's verdict and rc.112's run are the truth lane's.
-/

namespace Test.Codegen.DefinitionsPrint

open Effect4 Effect4.Program Test.Program.DefinitionsControls

/-! ## The printed text (finite evaluations) -/

-- a definition is an exported arrow from its request, with its declared result type, around a
-- suspension of its body; the main declaration invokes it by name
#guard (Api.printModule "main" twiceProg).map
    (fun m => String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))) =
  some ("export const twice = (a0: number): Effect.Effect<readonly [number, number], never, " ++
    "never> => Effect.suspend(() => Effect.succeed(pair(a0, a0)))\n" ++
    "export const main: Effect.Effect<readonly [number, number], never, never> = twice(21)\n")

-- two definitions that invoke each other print in the block's order, each invoking the other
#guard (Api.printModule "main" (evenOdd 7)).map
    (fun m => String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))) =
  some ("export const isEven = (a0: number): Effect.Effect<boolean, never, never> => " ++
    "Effect.suspend(() => ifCase(() => isZero(a0), () => Effect.succeed(true), () => " ++
    "isOdd(pred(a0))))\n" ++
    "export const isOdd = (a0: number): Effect.Effect<boolean, never, never> => " ++
    "Effect.suspend(() => ifCase(() => isZero(a0), () => Effect.succeed(false), () => " ++
    "isEven(pred(a0))))\n" ++
    "export const main: Effect.Effect<boolean, never, never> = isEven(7)\n")

/-! ## The readable domain (finite evaluations) -/

-- each block program is in the readable domain of a block, under the classes its module declares
-- (none), so the round trip holds by `Api.printModule_roundTrip`
#guard blockReadable [] (nativeSignature []) twiceProg
#guard blockReadable [] (nativeSignature []) (evenOdd 7)
#guard blockReadable [] (nativeSignature []) forkProg
#guard blockReadable [] (nativeSignature []) spinProg
-- control: a program with no block is outside it, and inside the plain domain
#guard !blockReadable [] (nativeSignature []) invokeId
#guard moduleReadable [] (nativeSignature []) (.succeed (.lit (.nat 1)) : NativeEff)
#guard !moduleReadable [] (nativeSignature []) twiceProg

/-! ## The module's layers (decisions row 341, step 2) -/

/-- The block with a module layer (`moduleLayerProg`, Test/Program/DefinitionsControls.lean). -/
def moduleLayered : NativeEff := moduleLayerProg

-- the module types, and runs to the layer's value
#guard Api.typeOf moduleLayered == some (EffTy.pure .nat)
#guard (match (Api.run moduleLayered 200).exit with
  | some (.success v) => v == .nat 7
  | _ => false)
-- the printer writes the module layer as a constant named by its path, after the definition
-- and before the main declaration, and both uses print as that name
#guard (Api.printModule "main" moduleLayered).map (fun m => m.decls.filterMap fun
    | .const c => some c.name
    | _ => none) = some ["readKey", "L_2_0", "main"]
-- the program is in the readable domain of a block, and its module reads back to it
#guard blockReadable [] (nativeSignature []) moduleLayered
#guard (Api.printModule "main" moduleLayered).map (fun m =>
  decide (Api.readModule m [] = .ok moduleLayered)) = some true

/-! ## The name bridge (a reader) -/

-- the printer's name check gives the names the block's spelling map reads back
example : DefsNamed (nativeSpell [])
    [{ name := "isEven", request := .nat, answer := .bool },
      { name := "isOdd", request := .nat, answer := .bool }] :=
  defsNamed_of_fault (name := "main") (by decide +kernel)

/-! ## Controls: what the printer refuses, by name -/

/-- `twice`'s block with its definition renamed. -/
def renamed (name : String) : NativeEff :=
  .defs [{ twiceDecl with name }] (.cons (.succeed (ap "pair" [.var 0, .var 0])) .nil)
    (.perform (.call 0) (.lit (.nat 21))) .nil

/-- The printer's refusal of a program, when its emission is refused there. -/
def printRefusal (p : NativeEff) : Option PrintRefusal :=
  match Api.emitModule "main" p with
  | .error (.print why) => some why
  | _ => none

-- the export name, a printed binder, a layer name and a dotted spelling are no definition names
#guard printRefusal (renamed "main") = some (.unsafeName "main")
#guard printRefusal (renamed "a0") = some (.unsafeName "a0")
#guard printRefusal (renamed "L_1") = some (.unsafeName "L_1")
#guard printRefusal (renamed "Ref.make") = some (.unsafeName "Ref.make")
-- two definitions with one name
#guard printRefusal (.defs [twiceDecl, twiceDecl]
    (.cons (.succeed (ap "pair" [.var 0, .var 0]))
      (.cons (.succeed (ap "pair" [.var 0, .var 0])) .nil))
    (.perform (.call 0) (.lit (.nat 21))) .nil) = some (.unsafeName "twice")

-- an empty block would print as its main program alone, and read back as it
#guard (Program.printModule (nativeSignature []) "main" (EffTy.pure .nat)
    (.defs [] .nil (.succeed (.lit (.nat 1))) .nil : NativeEff)).toOption.isNone

/-! ## A body's own layers (decisions row 341, step 3) -/

/-- A service key that a body's own layer provides. -/
def bodyKey : ServiceKey := ⟨⟨5⟩, ⟨4⟩⟩

/-- **A block whose definition body holds its own layer**: `readBoth : number → number` provides
its own layer, at `[0, 0, 0]`, around the module's layer `[2, 0]` and a second provision of its
own layer by reference, and adds the two services. -/
def bodyLayered : NativeEff :=
  .defs [{ name := "readBoth", request := .nat, answer := .nat }]
    (.cons (.provideLayer (.succeed bodyKey (.nat 3)) false
       (.provideLayer (.ref [2, 0]) false
         (.provideLayer (.ref [0, 0, 0]) false
           (.bind (.service bodyKey) (.bind (.service layerKey)
             (.succeed (ap "add" [.var 1, .var 2]))))))) .nil)
    (.perform (.call 0) (.lit (.nat 1)))
    (.cons (.succeed layerKey (.nat 7)) .nil)

-- the module types, and runs to the sum of the two services
#guard Api.typeOf bodyLayered == some (EffTy.pure .nat)
#guard (match (Api.run bodyLayered 300).exit with
  | some (.success v) => v == .nat 10
  | _ => false)
-- the body's own layer is a constant at the top of its suspension, named by its path, and both
-- of its uses print as that name; the module layer stays a module constant
#guard (Api.printModule "main" bodyLayered).map
    (fun m => String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))) =
  some ("export const readBoth = (a0: number): Effect.Effect<number, never, never> => " ++
    "Effect.suspend(() => {\n" ++
    "  let L_0_0_0 = Layer.succeed(Context.Service<\"k5_4\", number>(\"k5_4\"), 3)\n" ++
    "  return Effect.provide(Effect.provide(Effect.provide(Effect.flatMap(" ++
    "Effect.service(Context.Service<\"k5_4\", number>(\"k5_4\")), (a1) => Effect.flatMap(" ++
    "Effect.service(Context.Service<\"k4_4\", number>(\"k4_4\")), (a2) => " ++
    "Effect.succeed(add(a1, a2)))), L_0_0_0), L_2_0), L_0_0_0)\n" ++
    "})\n" ++
    "export const L_2_0 = Layer.succeed(Context.Service<\"k4_4\", number>(\"k4_4\"), 7)\n" ++
    "export const main: Effect.Effect<number, never, never> = readBoth(1)\n")
-- the program is in the readable domain of a block, and its module reads back to it
#guard blockReadable [] (nativeSignature []) bodyLayered
#guard (Api.printModule "main" bodyLayered).map (fun m =>
  decide (Api.readModule m [] = .ok bodyLayered)) = some true

/-- A block whose body holds its own layer and a reference to it, and names no module layer. -/
def ownLayerOnly : NativeEff :=
  .defs [{ name := "readOwn", request := .nat, answer := .nat }]
    (.cons (.provideLayer (.succeed bodyKey (.nat 3)) false
       (.provideLayer (.ref [0, 0, 0]) false (.service bodyKey))) .nil)
    (.perform (.call 0) (.lit (.nat 1))) .nil

/-- The verdict of the checked reading (`Api.admitModule`) on a program's emitted module, under
the effect namespaces: `some true` when it admits the program itself, `some false` when it
refuses the module as unbound. -/
def admitted (p : NativeEff) : Option Bool :=
  match Api.emitModule "main" p with
  | .error _ => none
  | .ok e =>
    match Api.admitModule "main" e.module [] Effect4.Codegen.effectOrigins
        [.named ["Effect", "Layer", "Context"] "effect"] with
    | .ok reading => if reading.program == p then some true else none
    | .error .unbound => some false
    | .error _ => none

/-- `ownLayerOnly` with the module's layer `[2, 0]` provided in the body by reference too. -/
def ownAndModuleLayer : NativeEff :=
  .defs [{ name := "readOwn", request := .nat, answer := .nat }]
    (.cons (.provideLayer (.succeed bodyKey (.nat 3)) false
       (.provideLayer (.ref [2, 0]) false
         (.provideLayer (.ref [0, 0, 0]) false (.service bodyKey)))) .nil)
    (.perform (.call 0) (.lit (.nat 1)))
    (.cons (.succeed layerKey (.nat 7)) .nil)

-- the checked reading admits a body's own layer: its constant is declared in the suspension,
-- before the uses that follow it
#guard admitted ownLayerOnly = some true
-- control: a module layer named from a body stays refused as unbound, as at step 2: the
-- definition is printed before the module constant it names (`SourceBindings`)
#guard admitted ownAndModuleLayer = some false

/-- `twice` with a layer inside its body that nothing names. -/
def layerInBody : NativeEff :=
  .defs [twiceDecl]
    (.cons (.provideLayer (.succeed ⟨⟨1⟩, ⟨1⟩⟩ .unit) false
      (.succeed (ap "pair" [.var 0, .var 0]))) .nil)
    (.perform (.call 0) (.lit (.nat 21))) .nil

-- a layer that nothing names prints in place, inside the body's suspension, so each run of the
-- body evaluates it again; the module reads back
#guard (Program.printModule (nativeSignature []) "main" (EffTy.pure (.prod .nat .nat))
    layerInBody).toOption.map
    (fun ds => String.join (ds.map fun c => TypeScript.Render.decl TypeScript.house0 (.const c))) =
  some ("export const twice = (a0: number): Effect.Effect<readonly [number, number], never, " ++
    "never> => Effect.suspend(() => Effect.provide(Effect.succeed(pair(a0, a0)), " ++
    "Layer.succeed(Context.Service(\"k1_1\"), undefined)))\n" ++
    "export const main: Effect.Effect<readonly [number, number], never, never> = twice(21)\n")
#guard (Program.printModule (nativeSignature []) "main" (EffTy.pure (.prod .nat .nat))
    layerInBody).toOption.map (fun ds =>
  decide (Program.readModule (nativeSignature []) (nativeSpell []) NativeOp.call NativeOp.param
    (ds.map TypeScript.Decl.const) = .ok layerInBody)) = some true

/-- Two definitions; the second names the first's own layer. -/
def otherBodyRef : NativeEff :=
  .defs [{ name := "first", request := .nat, answer := .nat },
      { name := "second", request := .nat, answer := .nat }]
    (.cons (.provideLayer (.succeed bodyKey (.nat 3)) false (.service bodyKey))
      (.cons (.provideLayer (.ref [0, 0, 0]) false (.service bodyKey)) .nil))
    (.perform (.call 1) (.lit (.nat 1))) .nil

/-- A definition, and a main program that names its body's own layer. -/
def mainBodyRef : NativeEff :=
  .defs [{ name := "first", request := .nat, answer := .nat }]
    (.cons (.provideLayer (.succeed bodyKey (.nat 3)) false (.service bodyKey)) .nil)
    (.provideLayer (.ref [0, 0, 0]) false (.service bodyKey)) .nil

/-- The raw module printer's refusal of a program, when it refuses. -/
def rawRefusal (p : NativeEff) : Option PrintRefusal :=
  match Program.printModule (nativeSignature []) "main" (EffTy.pure .nat) p with
  | .error why => some why
  | .ok _ => none

-- control: a body's layer is its constant, declared in its suspension, so a reference from another
-- body or from the main program would name what its site cannot see; the printer refuses it by its
-- target, as the checker refuses it at the site (`otherScope`)
#guard rawRefusal otherBodyRef = some (.layerRef [0, 0, 0])
#guard rawRefusal mainBodyRef = some (.layerRef [0, 0, 0])
#guard (Api.explain otherBodyRef).bind (fun r => match r.reason with
  | .referenceIllFormed t why => some (r.path, t, why)
  | _ => none) = some ([0, 1, 0, 0], [0, 0, 0], .otherScope)
#guard (Api.explain mainBodyRef).bind (fun r => match r.reason with
  | .referenceIllFormed t why => some (r.path, t, why)
  | _ => none) = some ([1, 0], [0, 0, 0], .otherScope)

/-! ## A definition's parameters (decisions row 340, slice HO-3) -/

/-- `apply : number → number`, with the parameter `f : number ⇒ number`. -/
def applyDecl : DefDecl :=
  { name := "apply", request := .nat, answer := .nat,
    params := [{ name := "f", request := .nat, answer := .nat }] }

/-- A block whose definition runs its parameter on its request. Nothing invokes it: an invocation
with programs prints from slice HO-3b. -/
def paramProg : NativeEff :=
  .defs [applyDecl] (.cons (.perform (.param 0) (.var 0)) .nil) (.succeed (.lit (.nat 1))) .nil

-- the module types
#guard Api.typeOf paramProg == some (EffTy.pure .nat)
-- the header prints the parameter after the request, as a function named by its declaration;
-- the body runs it as the row call of its name
#guard (Api.printModule "main" paramProg).map
    (fun m => String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))) =
  some ("export const apply = (a0: number, f: (a0: number) => Effect.Effect<number, never, " ++
    "never>): Effect.Effect<number, never, never> => Effect.suspend(() => f(a0))\n" ++
    "export const main: Effect.Effect<number, never, never> = Effect.succeed(1)\n")
-- the program is in the readable domain of a block, and its module reads back to it
#guard blockReadable [] (nativeSignature []) paramProg
#guard (Api.printModule "main" paramProg).map (fun m =>
  decide (Api.readModule m [] = .ok paramProg)) = some true

/-- `paramProg` with its parameter renamed. -/
def paramRenamed (name : String) : NativeEff :=
  .defs [{ applyDecl with params := [{ name, request := .nat, answer := .nat }] }]
    (.cons (.perform (.param 0) (.var 0)) .nil) (.succeed (.lit (.nat 1))) .nil

-- control: a parameter's name is no definition's, no printed binder, no imported name and not
-- the export name, each refused by name
#guard printRefusal (paramRenamed "apply") = some (.unsafeName "apply")
#guard printRefusal (paramRenamed "a0") = some (.unsafeName "a0")
#guard printRefusal (paramRenamed "succ") = some (.unsafeName "succ")
#guard printRefusal (paramRenamed "main") = some (.unsafeName "main")
-- control: two parameters with one name
#guard printRefusal (.defs [{ applyDecl with params :=
    [{ name := "f", request := .nat, answer := .nat }, { name := "f", request := .nat, answer := .nat }] }]
    (.cons (.perform (.param 0) (.var 0)) .nil) (.succeed (.lit (.nat 1))) .nil) =
  some (.unsafeName "f")

/-! ## An invocation with programs (decisions row 340, slice HO-3b) -/

-- the invocation prints as the definition's name on the request and on each program as a
-- function of the binder due at the call (`invokeProg`, Test/Program/InvokeControls.lean)
#guard (Api.printModule "main" Test.Program.InvokeControls.invokeProg).map
    (fun m => String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))) =
  some ("export const twice = (a0: number, f: (a0: number) => Effect.Effect<number, never, " ++
    "never>): Effect.Effect<number, never, never> => Effect.suspend(() => " ++
    "Effect.flatMap(f(a0), (a1) => f(a1)))\n" ++
    "export const main: Effect.Effect<number, never, never> = " ++
    "twice(5, (a0) => Effect.succeed(succ(a0)))\n")
-- each invocation program is in the readable domain of a block, and its module reads back to it:
-- one invocation, a program passed on through a second definition, and a run inside a fork
#guard [Test.Program.InvokeControls.invokeProg, Test.Program.InvokeControls.forwardProg,
    Test.Program.InvokeControls.forkProg].all fun p =>
  blockReadable [] (nativeSignature []) p &&
    (Api.printModule "main" p).any fun m => decide (Api.readModule m [] = .ok p)

/-! ## The printer's boundary for parameters (Codex's HO-3 review) -/

/-- A parameter from a number to a number. -/
def numParam (name : String) : ParamDecl := { name, request := .nat, answer := .nat }

/-- The printer's refusal of a program at a row table, when its emission is refused there. -/
def printRefusalAt (p : NativeEff) (table : RowTable) : Option PrintRefusal :=
  match Api.emitModule "main" p table with
  | .error (.print why) => some why
  | _ => none

/-- A host row, spelled qualified (`Widget.run`) or plain with a trailing name (`Token`). -/
def hostRow (qualified : Bool) : Row :=
  { name := "widgetRead", spelling := if qualified then "Widget.run" else "readWidget",
    trailing := if qualified then [] else [.name "Token"],
    kind := .async, registration := .external, request := .nat, answer := .nat, cite := "battery" }

/-- A definition whose parameter is named `param` and whose body calls the host row. -/
def hostCaller (param : String) : NativeEff :=
  .defs [{ name := "readExternal", request := .nat, answer := .nat, params := [numParam param] }]
    (.cons (.perform (.external 0) (.var 0)) .nil) (.succeed (.lit (.nat 1))) .nil

-- control (HO3-NAME-01): a parameter named as a row's qualified root, or as its trailing name,
-- would capture what the row's call names: refused by name; another name prints
#guard printRefusalAt (hostCaller "Widget") [hostRow true] = some (.unsafeName "Widget")
#guard printRefusalAt (hostCaller "Token") [hostRow false] = some (.unsafeName "Token")
#guard (Api.printModule "main" (hostCaller "use") [hostRow true]).isSome
#guard (Api.printModule "main" (hostCaller "use") [hostRow false]).isSome

/-- The fields of the payload `Payload`. -/
def payloadFields : List (String × Bool × Ty) := [("_tag", false, .lit "Payload"), ("id", false, .nat)]

/-- A definition that builds a `Payload`, with a parameter named `param`. -/
def payloadBuilder (param : String) : NativeEff :=
  .defs [{ name := "buildPayload", request := .nat, answer := .record payloadFields,
           params := [numParam param] }]
    (.cons (.succeed (.record payloadFields ["_tag", "id"]
      (.cons (.lit (.str "Payload")) (.cons (.lit (.nat 7)) .nil)))) .nil)
    (.succeed (.lit (.nat 1))) .nil

-- control (HO3-NAME-01): a parameter named as a payload class the module declares would capture
-- its constructor: refused by name
#guard printRefusalAt (payloadBuilder "Payload") [] = some (.unsafeName "Payload")
#guard (Api.printModule "main" (payloadBuilder "use")).isSome

/-- A service whose method, or whose initial program, takes a program. -/
def counterService (methodParam initParam : Bool) : NativeEff :=
  .defs [
    { name := "makeCounter", request := .unit, answer := .nat, role := .serviceInit "Counter",
      params := if initParam then [numParam "use"] else [] },
    { name := "readCounter", request := .nat, answer := .nat,
      role := .serviceMethod "Counter" "read" 0,
      params := if methodParam then [numParam "use"] else [] }]
    (.cons (if initParam then .perform (.param 0) (.lit (.nat 7)) else .succeed (.lit (.nat 7)))
      (.cons (if methodParam then .perform (.param 0) (.var 0) else .succeed (.var 0)) .nil))
    (.succeed (.lit (.nat 1))) .nil

-- control (HO3-SVC-01): a service's method or initial program with a parameter is refused by
-- name until slice HO-5 forwards its programs; the service without one prints
#guard printRefusalAt (counterService true false) [] = some (.internalAction "Counter.read")
#guard printRefusalAt (counterService false true) [] = some (.internalAction "Counter")
#guard (Api.printModule "main" (counterService false false)).isSome

/-- A payload named `OnlyParam`, which only a parameter's request names. -/
def onlyParamTy : Ty := .record [("_tag", false, .lit "OnlyParam"), ("id", false, .nat)]

/-- A definition whose parameter's request is `OnlyParam`. -/
def onlyParamHelper (request : Ty) : NativeEff :=
  .defs [{ name := "onlyHelper", request := .nat, answer := .nat,
           params := [{ name := "use", request, answer := .nat }] }]
    (.cons (.succeed (.lit (.nat 1))) .nil) (.succeed (.lit (.nat 1))) .nil

-- (HO3-ANN-01) a parameter's columns are types the program states: the module declares the
-- payload class that only a parameter names, and a repeated field there is unformed
#guard (Api.printModule "main" (onlyParamHelper onlyParamTy)).any fun m =>
  m.decls.any fun
    | .classDecl c => c.name == "OnlyParam"
    | _ => false
#guard (Formation.checkInput
  (onlyParamHelper (.record [("item", false, .nat), ("item", false, .nat)])) []).isSome
#guard (Formation.checkInput (onlyParamHelper (.record [("item", false, .nat)])) []).isNone

/-- `twice` invoked under the module's layer with a callback that reads the layer's service. -/
def serviceCallback : NativeEff :=
  .defs [Test.Program.InvokeControls.twiceDecl] (.cons Test.Program.InvokeControls.twiceBody .nil)
    (.provideLayer (.ref [2, 0]) false
      (.invoke 0 (.lit (.nat 5)) (.cons (.service layerKey) .nil)))
    (.cons (.succeed layerKey (.nat 7)) .nil)

-- control (HO3-REQ-01): the program types, but the printed header closes the callback's row as
-- `never`, so the invocation is refused at its path until the header can carry the row
#guard Api.wellTyped serviceCallback
#guard printRefusalAt serviceCallback [] = some (.callbackRequirement [1, 1])
-- a callback that needs nothing prints (`invokeProg`)
#guard (Api.printModule "main" Test.Program.InvokeControls.invokeProg).isSome

/-! ## Controls: what the reader refuses -/

/-- `twice` declaring a service it does not need. -/
def withService : NativeEff :=
  .defs [{ twiceDecl with requires := [⟨⟨1⟩, ⟨1⟩⟩] }]
    (.cons (.succeed (ap "pair" [.var 0, .var 0])) .nil) (.perform (.call 0) (.lit (.nat 21))) .nil

-- a requirement row other than `never` is printed and not read: the declaration is outside the
-- readable domain, and the reader refuses its header by name
#guard !(withService.defsOf.all DefDecl.readable)
#guard (Api.printModule "main" withService).isSome
#guard (Api.printModule "main" withService).map Api.readModule = some (.error (.shape "definition"))

end Test.Codegen.DefinitionsPrint
