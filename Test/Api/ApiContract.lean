import Test.Api.ExternalContract
import Test.Api.PackagesContract
import Effect4.Api
import TypeScript.Render

/-!
# Api contract — the application face, crossed the way a caller crosses it

`src/Effect4/Api.lean` is the one module an application imports. This battery uses nothing but
its interface: a program is typed, printed, compiled and run through `Effect4.Api`, and the
Schema syntax is rendered through the pinned package. Rendered bytes appear only inside
`#guard`s (a battery definition over a rendered `String` reaches `Classical.choice`).
-/

namespace Test.Api.ApiContract

open Effect4 Effect4.Api
open Effect4.Api (Val)
open Effect4.Codegen (effectOrigins)
open TypeScript (house0)
open TypeScript.Render (expr)

/-- `Effect.succeed(42)`. -/
def p42 : Program := .succeed (.lit (.nat 42))

/-- `Effect.flatMap(Effect.succeed(1), (a0) => Effect.succeed(succ(a0)))`. -/
def pBind : Program :=
  .bind (.succeed (.lit (.nat 1))) (.succeed (.app "succ" (.cons (.var 0) .nil)))

/-- A program the printer refuses: an internal action of the machine. -/
def pInternal : Program := .withFiber (.setContext (.lit .unit))

/-- `Effect.succeed("x")`: a string literal is a machine value on the native route (DB-15, the
host rows slice, 2026-09-08). -/
def pStr : Program := .succeed (.lit (.str "x"))

/-- A string through a variable: `Effect.flatMap(Effect.succeed("a"), (a0) => Effect.succeed(a0))`. -/
def pStrBind : Program := .bind (.succeed (.lit (.str "a"))) (.succeed (.var 0))

/-! ## Typing and printing -/

#guard wellTyped p42
#guard wellTyped pBind
#guard (print p42).map (expr house0 0) = .ok "Effect.succeed(42)"
#guard (print pBind).map (expr house0 0)
  = .ok "Effect.flatMap(Effect.succeed(1), (a0) => Effect.succeed(succ(a0)))"
#guard (printDecl "main" p42).isSome
#guard (printDecl "main" pInternal).isNone
#guard (print pInternal).isOk = false
-- DB-15: string literals type, print, read back whole, and run to the carrier's `str` frame
#guard wellTyped pStr
#guard wellTyped pStrBind
#guard (print pStr).isOk
#guard roundTrip pStr = .ok pStr
#guard roundTrip pStrBind = .ok pStrBind
#guard (run pStr 100).exit = some (Exit.success (Val.str "x"))
#guard (run pStrBind 100).exit = some (Exit.success (Val.str "a"))
#guard (runSync pStr 100).2 = Exit.success (Val.str "x")

/-! Computed fragment admission uses the ordinary API without a Laws import. -/
#guard (admitStraightProgram p42).isOk
#guard match admitStraightProgram (.succeed (.var 0)) with
  | .error (.admission .illTyped) => true
  | _ => false
#guard match admitStraightProgram (.gen .nil) with
  | .error .outsideFragment => true
  | _ => false
#guard match admitStraightProgram (.bind p42 (.gen .nil)) with
  | .error .outsideFragment => true
  | _ => false

/-- Runtime-selected tuples expose joined fields without an unchecked projection. -/
def productUnion : Program := .bind
  (.branch (.lit (.bool true))
    (.succeed (.app "pair" (.cons (.lit (.str "Search")) (.cons (.lit (.nat 3)) .nil))))
    (.succeed (.app "pair" (.cons (.lit (.str "Done")) (.cons (.lit (.str "ok")) .nil)))))
  (.succeed (.app "snd" (.cons (.var 0) .nil)))
#guard typeOf productUnion = some ⟨.union .nat (.lit "ok"), .never, .empty⟩
#guard (run productUnion 100).exit = some (.success (.nat 3))
#guard roundTrip productUnion = .ok productUnion
#guard Effect4.Program.NativeAtom.projectProduct false
  (.union (.prod .nat .bool) (.prod .string .nat)) = some (.union .nat .string)
#guard Effect4.Program.NativeAtom.projectProduct true
  (.union (.prod .nat .bool) (.list .nat)) = none
#guard Effect4.Program.NativeAtom.projectProduct true (.list (.fiberOf .nat .never)) = none
#print axioms Effect4.Program.admitStraightProgram
#print axioms Effect4.Program.admitStraightProgram_admission_error
#print axioms Effect4.Program.admitStraightProgram_ok
#print axioms Effect4.Program.admitStraightProgram_outside

/-! Checked production keeps typing failures separate from printing failures and
uses the same type evidence as execution admission, without inheriting its limits. -/
#guard (checkTyping p42).map (·.ty) = typeOf p42
#guard match emitModule "main" pBind with
  | .ok emitted => emitted.typing.ty == (.pure .nat) &&
      (readModule emitted.module == .ok pBind)
  | .error _ => false
#guard (print (.succeed (.var 0))).isOk
#guard match emitModule "main" (.succeed (.var 0)) with
  | .error .illTyped => true
  | _ => false
#guard wellTyped (.withFiber .snapshotChildren)
#guard match emitModule "main" (.withFiber .snapshotChildren) with
  | .error (.print (.internalAction "snapshotChildren")) => true
  | _ => false

def syncSourceTable : Effect4.Program.RowTable :=
  [{ name := "query", spelling := "Host.query", kind := .sync,
     registration := .external, request := .unit, answer := .nat,
     error := .never, cite := "" }]
def syncSource : Program := .perform (.external 0) (.lit .unit)
#guard match admitProgram syncSource syncSourceTable with
  | .error (.table (.notAsync 0)) => true
  | _ => false
#guard match emitModule "main" syncSource syncSourceTable with
  | .ok emitted => emitted.typing.ty == (.pure .nat) &&
      (readModule emitted.module syncSourceTable == .ok syncSource)
  | _ => false
def malformedSourceTable : Effect4.Program.RowTable :=
  syncSourceTable.map fun row => { row with answer := .handle "not a type !" }
#guard match emitModule "main" syncSource malformedSourceTable with
  | .error (.print (.typeSpelling text)) => text == "not a type !"
  | _ => false

/-! ## Checked reading: one control per check of the module boundary

`admitModule` is the reading half of the module face: the lexical bindings of the original
module against permitted origins, the raw reconstruction, the one whole-program checker, and
the declaration envelope compared with what the printer emits for the checked type. The
emitted module of `pBind` admits once the host supplies the prelude its free names need
(`Effect`, and the `succ` atom); each control below changes exactly one fact and names the
refusal it causes. Nothing here claims the host's `effect` namespace is the pinned one. -/

/-- Permitted origins: the `effect` namespaces, the module the `succ` atom comes from, and
the host package of the external row. -/
def hostOrigins : List Effect4.Codegen.Bindings.Origin :=
  effectOrigins ++ [.imported "./atoms" (some "succ"), .imported "host" (some "Host")]

/-- The prelude an embedding host wraps a declaration block in. -/
def hostAmbient : List TypeScript.Import :=
  [.named ["Effect", "Layer", "Context", "Fiber"] "effect", .named ["succ"] "./atoms"]

/-- Replace the block's main declaration, keeping every layer declaration. -/
def patchMain (module : TypeScript.Module) (f : TypeScript.ConstDecl → TypeScript.ConstDecl) :
    TypeScript.Module :=
  { module with decls := module.decls.dropLast ++ (module.decls.getLast?.map fun d =>
      match d with | .const c => TypeScript.Decl.const (f c) | other => other).toList }

/-- Replace the block's first declaration, a layer constant when the block has one. -/
def patchFirst (module : TypeScript.Module) (f : TypeScript.ConstDecl → TypeScript.ConstDecl) :
    TypeScript.Module :=
  { module with decls := match module.decls with
      | .const c :: rest => .const (f c) :: rest
      | other => other }

/-- Two shared layer references, so the emitted block carries `L_…` declarations. -/
def sharedLayers : Program :=
  .bind
    (.provideLayer (.merge (.succeed ⟨⟨4⟩, ⟨4⟩⟩ (.nat 7)) (.ref [0, 0, 0])) false
      (.succeed (.lit .unit)))
    (.provideLayer (.ref [0, 0]) false (.succeed (.lit .unit)))

/-- `Effect.Effect<string, never>`: a declared type the checked program does not have. -/
def stringEffect : TypeScript.TypeRef :=
  .name ["Effect", "Effect"] [.name ["string"] [], .name ["never"] []]

-- 1. What the producer emitted is admitted, at the same program and the same recorded type.
#guard match emitModule "main" pBind with
  | .ok e => match admitModule "main" e.module [] hostOrigins hostAmbient with
    | .ok r => (r.program == pBind) && (r.typing.ty == (.pure .nat))
    | .error _ => false
  | .error _ => false

-- 2. A declared type the core does not give the program: no widening, so it refuses.
#guard match emitModule "main" pBind with
  | .ok e => match admitModule "main"
      (patchMain e.module (fun c => { c with type := some stringEffect })) []
      hostOrigins hostAmbient with
    | .error (.declaredType _ actual) => actual == some stringEffect
    | _ => false
  | .error _ => false

-- 3. The annotation removed while the requirement is empty: still a disagreement.
#guard match emitModule "main" pBind with
  | .ok e => match admitModule "main"
      (patchMain e.module (fun c => { c with type := none })) [] hostOrigins hostAmbient with
    | .error (.declaredType expected actual) => expected.isSome && actual == none
    | _ => false
  | .error _ => false

-- 4. The main declaration not exported.
#guard match emitModule "main" pBind with
  | .ok e => match admitModule "main"
      (patchMain e.module (fun c => { c with exported := false })) [] hostOrigins hostAmbient with
    | .error (.notExported name) => name == "main"
    | _ => false
  | .error _ => false

-- 5. Admitted under a name the block does not export.
#guard match emitModule "main" pBind with
  | .ok e => match admitModule "program" e.module [] hostOrigins hostAmbient with
    | .error (.exportName expected actual) => expected == "program" && actual == "main"
    | _ => false
  | .error _ => false

-- 6. The same block with no ambient prelude: `succ` and `Effect` are unbound.
#guard match emitModule "main" pBind with
  | .ok e => match admitModule "main" e.module [] hostOrigins [] with
    | .error .unbound => true
    | _ => false
  | .error _ => false

-- 7. A layer declaration carrying an annotation is not the plain constant the printer emits.
#guard match emitModule "main" sharedLayers with
  | .ok e => (admitModule "main" e.module [] hostOrigins hostAmbient).isOk
  | .error _ => false
#guard match emitModule "main" sharedLayers with
  | .ok e => match admitModule "main"
      (patchFirst e.module (fun c => { c with type := some (.name ["number"] []) })) []
      hostOrigins hostAmbient with
    | .error (.layerDeclaration name) => name == "L_0_0_0"
    | _ => false
  | .error _ => false

-- 8. A checked type with no target annotation: the envelope has nothing to compare.
def hostQueryModule : TypeScript.Module :=
  { header := [], imports := [],
    decls := [.const { doc := [], name := "main", value := .call (.ident "Host.query") [] }] }
#guard match admitModule "main" hostQueryModule malformedSourceTable hostOrigins
    [.named ["Host"] "host"] with
  | .error (.unrepresentable (.typeSpelling text)) => text == "not a type !"
  | _ => false

-- 9. Readable, lexically bound, and ill-typed: a fiber action on a number.
def joinNumberModule : TypeScript.Module :=
  { header := [], imports := [],
    decls := [.const { doc := [], name := "main", value := .call (.ident "Fiber.join") [.int 1] }] }
#guard (readModule joinNumberModule).isOk
#guard match admitModule "main" joinNumberModule [] hostOrigins [.named ["Fiber"] "effect"] with
  | .error .illTyped => true
  | _ => false

-- 10. The producer refuses an unsafe export name before anything can read it back.
#guard match emitModule "a0" pBind with
  | .error (.print (.unsafeName name)) => name == "a0"
  | _ => false

#print axioms Effect4.Codegen.admitModule
#print axioms Effect4.Codegen.envelopeCheck
#print axioms Effect4.Api.admitModule

/-! ## Running -/

#guard (run p42 100).outcome = Outcome.finished
#guard (run p42 100).exit = some (Exit.success (Val.nat 42))
#guard (run pBind 100).exit = some (Exit.success (Val.nat 2))
#guard (run p42 100).fiberCount = 1
#guard (runSync p42 100).2 = Exit.success (Val.nat 42)
-- No fuel: the run is a frontier, not a failure.
#guard (run p42 0).outcome = Outcome.frontier
-- An empty tape leaves the root unevaluated: a frontier with no exit.
#guard (replay p42 100 []).exit = none

/-! ## Schema, as syntax -/

#guard expr house0 0 (jsonExpr (.arr [])) = "[]"

/-! ## DI-73: a fiber id is a number the two faces assign differently

`Effect.flatMap(Effect.fiberId, (a0) => Effect.succeed(eq(a0, 0)))` answers `true` here (the
root is fiber `0`) and `false` on the pinned rc.112, whose ids are the runtime's own counter.
The witness of the 2026-09-13 audit, kept so that a change to what `getId` answers, or to
its type, is a deliberate ruling: renumbering the *output* cannot repair a Boolean decided
during the run, so DI-73's earlier "compare ids up to renumbering" is withdrawn. -/

def pIdIsZero : Program :=
  .bind (.withFiber .getId)
    (.succeed (.app "eq" (.cons (.var 0) (.cons (.lit (.nat 0)) .nil))))

#guard wellTyped pIdIsZero
#guard (run pIdIsZero 100).exit = some (Exit.success (Val.bool true))
#guard (runSync pIdIsZero 100).2 = Exit.success (Val.bool true)
#guard (print pIdIsZero).map (expr house0 0)
  = .ok "Effect.flatMap(Effect.fiberId, (a0) => Effect.succeed(eq(a0, 0)))"

/-! ## Codegen, through the face: an artefact and its bytes -/

-- the one crossing to bytes, kept inside the guard
#guard render (Effect4.Codegen.Artefact.json (.arr [])) = "[]\n"

/-! ## Type spellings and Result patterns, through the application import

Known target spellings from the DX specification; runtime handles still require
their exact allocation target. The Result patterns use Failure = 0, Success = 1,
the opposite success/failure order from Exit. -/

open Effect4.Program (Ty)

#guard ([Ty.result .string .nat, Ty.exit .string .nat, Ty.fiber .string .never,
  Ty.cause .string, Ty.array .nat, Ty.readonlyArray .string, Ty.null, Ty.undefined,
  Ty.undefinedOr .nat, Ty.nullOr .nat, Ty.nullable .nat, Ty.duration, Ty.dateTime,
  Ty.chunk (.result .string .nat), Ty.take .string, Ty.take .string .nat .bool].map Ty.render) =
  ["Result.Result<string, number>", "Exit.Exit<string, number>", "Fiber.Fiber<string, never>",
   "Cause.Cause<string>", "ReadonlyArray<number>", "ReadonlyArray<string>", "null", "undefined",
   "number | undefined", "number | null", "number | null | undefined", "Duration.Duration",
   "DateTime.DateTime", "Chunk.Chunk<Result.Result<string, number>>",
   "ReadonlyArray<string> | Exit.Exit<void, never>",
   "ReadonlyArray<string> | Exit.Exit<boolean, number>"]

/-- Application callers can use the exported helpers on both sides of a match. -/
def resultPayload? : Val → Option (Bool × Val)
  | .resultFailure err => some (false, err)
  | .resultSuccess val => some (true, val)
  | _ => none

-- Re-exported nullary and payload patterns also resolve with a local dotted spelling.
private def exitPayload? : Val → Option Val
  | .exitOk value => some value
  | .exitNil => some .unit
  | _ => none

#guard exitPayload? (.exitOk (Val.cell ⟨3⟩)) = some (.cell ⟨3⟩)
#guard exitPayload? .exitNil = some .unit

#guard resultPayload? (Val.resultFailure (.nat 7)) = some (false, .nat 7)
#guard resultPayload? (Val.resultSuccess (.str "ok")) = some (true, .str "ok")
#guard resultPayload? (.ctor 1 [.str "ok", .nat 0]) = none
#guard Effect4.Program.Val.hasTy (Val.resultSuccess (.str "ok")) (Ty.result .string .nat)
#guard !Effect4.Program.Val.hasTy (Val.resultFailure (.str "wrong")) (Ty.result .string .nat)
#guard Effect4.Program.Val.hasTy (.handle 7 0) (Ty.nullable .nat) ["null"]
#guard !Effect4.Program.Val.hasTy (.handle 7 0) Ty.duration ["DateTime.DateTime"]
#guard !Effect4.Program.Val.hasTy .unit Ty.null

#print axioms Effect4.Program.Ty.chunk
#print axioms Effect4.Program.Ty.take
#print axioms Effect4.Machine.Value.resultFailure
#print axioms Effect4.Machine.Value.resultSuccess

/-! ## Axiom receipts -/

#print axioms Effect4.Api.typeOf
#print axioms Effect4.Api.print
#print axioms Effect4.Api.printDecl
#print axioms Effect4.Api.compile
#print axioms Effect4.Api.replay
#print axioms Effect4.Api.run
#print axioms Effect4.Api.runSync
#print axioms Effect4.Api.schemaDocument
#print axioms Effect4.Api.jsonExpr

end Test.Api.ApiContract


namespace Test.Api.IntegerAdmission
open Effect4 Effect4.Program Effect4.Api

def row (answer : Ty) (request : Ty := .nat) (error : Ty := .never) : Effect4.Program.Row :=
  { name := "query", spelling := "Host.query", request, answer, error,
    kind := .async, registration := .external, cite := "" }
def program : Api.Program := .callback (.external 0) (.lit (.nat 1))
def refusal (p : Api.Program) (table : RowTable) : Option AdmitRefusal :=
  match admitProgram p table with
  | .error why => some why
  | .ok _ => none

#guard (typeOf program [row .int]).map (fun t => t.answer) = some .int
#guard refusal program [row .int] = some (.uninhabited ["table", "0", "answer"])
#guard refusal (.succeed (.lit (.nat 1))) [row .int] =
  some (.uninhabited ["table", "0", "answer"])
#guard refusal program [row .nat (.option (.list .int))] =
  some (.uninhabited ["table", "0", "request", "inner", "inner"])
#guard refusal program [row .nat .nat (.union .never .int)] =
  some (.uninhabited ["table", "0", "error", "right"])
#guard refusal program [row .nat] = none

-- The foreign Schema.Int representation still parses; its resulting program refuses.
def foreignInt : Representation := .number none [Schema.Check.int]
#guard Ty.ofSchema foreignInt = some .int
#guard (Ty.ofSchema foreignInt).bind (fun t => refusal program [row t]) =
  some (.uninhabited ["table", "0", "answer"])
#guard Ty.key .int = [3]
#guard findInt [] (.handle "int") = none
#guard findIntInTable [row .nat, { row .int with name := "other" }] =
  some ["table", "1", "answer"]
#guard ([ (.option .int, ["inner"]), (.list .int, ["inner"]),
    (.causeOf .int, ["error"]), (.prod .int .nat, ["left"]),
    (.prod .nat .int, ["right"]), (.except .int .nat, ["error"]),
    (.except .nat .int, ["value"]), (.exitOf .int .nat, ["value"]),
    (.exitOf .nat .int, ["error"]), (.fiberOf .int .nat, ["value"]),
    (.fiberOf .nat .int, ["error"]), (.union .int .nat, ["left"]),
    (.union .nat .int, ["right"]) ] : List (Ty × Path)).all
      (fun (t, path) => findInt [] t == some path)

#print axioms Api.findInt
#print axioms Api.findIntInTable
#print axioms Api.findIntInEffTy
#print axioms Api.admitProgram
#print axioms Api.admitProgram_table_int
#print axioms Api.admitProgram_type_int
end Test.Api.IntegerAdmission
