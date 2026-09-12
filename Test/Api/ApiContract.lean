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
