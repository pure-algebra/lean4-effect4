import Effect4.Laws.Api.ModuleReadable
import Test.Program.DefinitionsControls

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
    "Effect.suspend(() => Effect.suspend(() => isZero(a0) ? Effect.succeed(true) : " ++
    "isOdd(pred(a0))))\n" ++
    "export const isOdd = (a0: number): Effect.Effect<boolean, never, never> => " ++
    "Effect.suspend(() => Effect.suspend(() => isZero(a0) ? Effect.succeed(false) : " ++
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
    (.perform (.call 0) (.lit (.nat 21)))

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
    (.perform (.call 0) (.lit (.nat 21)))) = some (.unsafeName "twice")

-- an empty block would print as its main program alone, and read back as it
#guard (Program.printModule (nativeSignature []) "main" (EffTy.pure .nat)
    (.defs [] .nil (.succeed (.lit (.nat 1))) : NativeEff)).toOption.isNone

/-- `twice` with a layer inside its body. -/
def layerInBody : NativeEff :=
  .defs [twiceDecl]
    (.cons (.provideLayer (.succeed ⟨⟨1⟩, ⟨1⟩⟩ .unit) false
      (.succeed (ap "pair" [.var 0, .var 0]))) .nil)
    (.perform (.call 0) (.lit (.nat 21)))

-- a layer inside a body is refused by name: rc.112 would build one layer object per invocation
#guard (Program.printModule (nativeSignature []) "main" (EffTy.pure (.prod .nat .nat))
    layerInBody).toOption.isNone

/-! ## Controls: what the reader refuses -/

/-- `twice` declaring a service it does not need. -/
def withService : NativeEff :=
  .defs [{ twiceDecl with requires := [⟨⟨1⟩, ⟨1⟩⟩] }]
    (.cons (.succeed (ap "pair" [.var 0, .var 0])) .nil) (.perform (.call 0) (.lit (.nat 21)))

-- a requirement row other than `never` is printed and not read: the declaration is outside the
-- readable domain, and the reader refuses its header by name
#guard !(withService.defsOf.all DefDecl.readable)
#guard (Api.printModule "main" withService).isSome
#guard (Api.printModule "main" withService).map Api.readModule = some (.error (.shape "definition"))

end Test.Codegen.DefinitionsPrint
