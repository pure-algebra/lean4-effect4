import Effect4.Api

/-!
# The error payload face: one `Data.TaggedError` class per tagged payload type

Finite controls for decisions row 120, part E2 (ruling (b)). A tagged payload record type is a
class, named by its tag: its type prints as the class name, a construction in the class form
prints as `new Tag({ … })` wherever it occurs, and the module declares the class before its
declaration block. The reader restores a construction's fields from the module's classes. The
laws are `readTerm_printTerm`, `readTerm_exact` (`Laws/Codegen/ReadLeaf.lean`), `read_print`,
`read_exact` and `readModule_printModule`; these controls pin the printed text, the five routes
of seat E1's printer probe, the refusals by name and the envelope. They are finite checks: tsgo's
verdict on the printed forms is `ts/eff/test/payload-classes.typecheck.ts`, and nothing here
claims target execution.
-/

namespace Effect4.Test.PayloadClasses

open Effect4 Effect4.Program Effect4.Codegen
open Effect4.Machine.Env (Requirement)

def notFoundFields : List (String × Bool × Ty) := [("_tag", false, .lit "NotFound"), ("id", false, .nat)]
def notFoundTy : Ty := .record notFoundFields
def notFound (id : Nat) : Term :=
  .record notFoundFields ["_tag", "id"] (.cons (.lit (.str "NotFound")) (.cons (.lit (.nat id)) .nil))

def unauthorizedFields : List (String × Bool × Ty) :=
  [("_tag", false, .lit "Unauthorized"), ("reason", false, .string)]
def unauthorizedTy : Ty := .record unauthorizedFields
def unauthorized (reason : String) : Term :=
  .record unauthorizedFields ["_tag", "reason"]
    (.cons (.lit (.str "Unauthorized")) (.cons (.lit (.str reason)) .nil))

-- Rendered bytes stay inside `#guard`s: a battery `def` over rendered text would reach
-- `Classical.choice` (AGENTS.md, Trust).

/-! ## The construction, at every route of E1's printer probe

`Api.print` is the expression face. A construction in the class form prints as `new Tag({ … })`
wherever it occurs: the class face is a property of the record's type, not of the position. -/

-- route 1: `fail` of a construction
def failDirect : NativeEff := .fail (notFound 9)
#guard (Api.print failDirect).map (TypeScript.Render.expr TypeScript.house0 0) = .ok "Effect.fail(new NotFound({ id: 9 }))"
-- route 2: a bound construction, failed later through its variable
def failBound : NativeEff := .bind (.succeed (notFound 9)) (.fail (.var 0))
#guard (Api.print failBound).map (TypeScript.Render.expr TypeScript.house0 0) =
  .ok "Effect.flatMap(Effect.succeed(new NotFound({ id: 9 })), (a0) => Effect.fail(a0))"
-- route 3: the same, handled inside
def handledInside : NativeEff := .catchCause failBound (.succeed (.lit (.nat 0)))
#guard (Api.print handledInside).map (TypeScript.Render.expr TypeScript.house0 0) =
  .ok "Effect.catchCause(Effect.flatMap(Effect.succeed(new NotFound({ id: 9 })), (a0) => Effect.fail(a0)), (a0) => Effect.succeed(0))"
-- route 4: reified by `exit`
def reified : NativeEff := .bind (.succeed (notFound 9)) (.exit (.fail (.var 0)))
#guard (Api.print reified).map (TypeScript.Render.expr TypeScript.house0 0) =
  .ok "Effect.flatMap(Effect.succeed(new NotFound({ id: 9 })), (a0) => Effect.exit(Effect.fail(a0)))"
-- route 5: a tagged record as data, never failed
def asData : NativeEff := .succeed (notFound 9)
#guard (Api.print asData).map (TypeScript.Render.expr TypeScript.house0 0) = .ok "Effect.succeed(new NotFound({ id: 9 }))"

/-! ## The types: the class name, a union by its members -/

#guard typeOfProgram (nativeSignature []) failBound = some ⟨.never, notFoundTy, Requirement.empty⟩
#guard (declarationType ⟨.never, .union notFoundTy unauthorizedTy, Requirement.empty⟩).map
    (·.map (TypeScript.Render.type TypeScript.house0)) =
  .ok (some "Effect.Effect<never, NotFound | Unauthorized, never>")
#guard (declarationType ⟨.exitOf .never notFoundTy, .never, Requirement.empty⟩).map
    (·.map (TypeScript.Render.type TypeScript.house0)) =
  .ok (some "Effect.Effect<Exit.Exit<never, NotFound>, never, never>")
-- a record that is no payload type keeps its object spelling
#guard (Types.ofTy (.record [("id", false, .nat)])).map (TypeScript.Render.type TypeScript.house0) =
  some "{ readonly id: number }"

/-! ## The module: the classes first, then the declaration block -/

#guard (Api.printModule "main" failDirect).map (fun m => String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))) = some
  ("export class NotFound extends Data.TaggedError(\"NotFound\")<{ readonly id: number }> {}\n" ++
   "export const main: Effect.Effect<never, NotFound, never> = Effect.fail(new NotFound({ id: 9 }))\n")
-- two classes: the error column is their union, and the module declares both, in order
def classUnion : NativeEff := .bind (.fail (notFound 9)) (.fail (unauthorized "bad token"))
#guard (Api.printModule "main" classUnion).map (fun m => String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))) = some
  ("export class NotFound extends Data.TaggedError(\"NotFound\")<{ readonly id: number }> {}\n" ++
   "export class Unauthorized extends Data.TaggedError(\"Unauthorized\")<{ readonly reason: string }> {}\n" ++
   "export const main: Effect.Effect<never, NotFound | Unauthorized, never> = Effect.flatMap(Effect.fail(new NotFound({ id: 9 })), (a0) => Effect.fail(new Unauthorized({ reason: \"bad token\" })))\n")
-- the same union through `select`: tsgo refuses the printed `Effect.suspend(() => c ? a : b)`
-- (TS2375, DI-55's finding F3, open before E2: TypeScript infers one arm's error, not their union);
-- the red twin `ts/eff/test/red/payload-classes.red.ts` pins it
def twoClasses : NativeEff :=
  .bind (.succeed (.lit (.bool true)))
    (.select (.var 0) .bool (.fail (notFound 9)) (.fail (unauthorized "bad token")))
#guard (Api.printModule "main" twoClasses).map (fun m => String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))) = some
  ("export class NotFound extends Data.TaggedError(\"NotFound\")<{ readonly id: number }> {}\n" ++
   "export class Unauthorized extends Data.TaggedError(\"Unauthorized\")<{ readonly reason: string }> {}\n" ++
   "export const main: Effect.Effect<never, NotFound | Unauthorized, never> = Effect.flatMap(Effect.succeed(true), (a0) => Effect.suspend(() => a0 ? Effect.fail(new NotFound({ id: 9 })) : Effect.fail(new Unauthorized({ reason: \"bad token\" }))))\n")
-- every route prints as a module, its class declared
#guard [failDirect, failBound, handledInside, reified, asData].all fun p =>
  match Api.printModule "main" p with
  | some m => (String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))).startsWith
      "export class NotFound extends Data.TaggedError(\"NotFound\")<{ readonly id: number }> {}\n"
  | none => false

/-! ## Reading back -/

-- the module reads back to its program, at every route
#guard [failDirect, failBound, handledInside, reified, asData, classUnion, twoClasses].all fun p =>
  match Api.printModule "main" p with
  | some m => decide (Api.readModule m = .ok p)
  | none => false
-- the expression round trip reads under the classes the program's constructions name
#guard [failDirect, failBound, handledInside, reified, asData, classUnion, twoClasses].all (Api.readable ·)
#guard Effect4.Program.classesOf twoClasses = [("NotFound", notFoundFields), ("Unauthorized", unauthorizedFields)]
-- red control: a bare expression declares no class, so the construction names nothing
#guard (Api.print failDirect).map (Api.read ·) = .ok (.error (.unknownIdent "NotFound"))
-- red control: a structural record in the class form is outside the printed image
#guard readTerm [("NotFound", notFoundFields)] 0
    (Record.writeRecord notFoundFields ["_tag", "id"] [.str "NotFound", .int 9]) =
  .error (.shape "record in class form")
-- red control: a class whose declaration is no payload type reads no construction
#guard readTerm [("NotFound", [("id", false, .nat)])] 0 (Classes.writeClass "NotFound" ["id"] [.int 9]) =
  .error (.shape "class")
-- the reader is untyped (decisions row 165): under a class with other fields it reads the term the
-- construction prints from, exactly, and the checker refuses that term
#guard match readTerm [("NotFound", [("_tag", false, .lit "NotFound"), ("code", false, .nat)])] 0
    (Classes.writeClass "NotFound" ["id"] [.int 9]) with
  | .ok t => printTerm 0 t == Classes.writeClass "NotFound" ["id"] [.int 9] &&
    (termTy nativeSignature [] t).isNone
  | .error _ => false
-- the class declaration reads back, exactly
#guard (Classes.classDecl "NotFound" notFoundFields).bind Classes.readClassDecl =
  some ("NotFound", notFoundFields)

/-! ## Naming and fields, each refused by name with the tag -/

def failRecord (fields : List (String × Bool × Ty)) (supplied : List (String × Term)) : NativeEff :=
  .fail (.record fields (supplied.map Prod.fst) (supplied.foldr (fun p ts => .cons p.2 ts) .nil))

def emitted (p : NativeEff) : Option PrintRefusal :=
  match Api.emitModule "main" p with
  | .error (.print why) => some why
  | _ => none

-- a tag that is no TypeScript identifier
#guard emitted (failRecord [("_tag", false, .lit "not-a-tag"), ("id", false, .nat)]
    [("_tag", .lit (.str "not-a-tag")), ("id", .lit (.nat 1))]) =
  some (.payloadClass "not-a-tag" .notIdentifier)
-- a tag that collides with an import, a builtin, a type name the printer spells, or a binder
#guard ["Effect", "Data", "Readonly", "Record", "Uint8Array", "main", "a7", "pair"].all fun tag =>
  emitted (failRecord [("_tag", false, .lit tag), ("id", false, .nat)]
    [("_tag", .lit (.str tag)), ("id", .lit (.nat 1))]) = some (.payloadClass tag .collides)
-- two payload types under one tag with different fields
#guard emitted (.bind (.succeed (notFound 1))
    (.fail (.record [("_tag", false, .lit "NotFound"), ("reason", false, .string)] ["_tag", "reason"]
      (.cons (.lit (.str "NotFound")) (.cons (.lit (.str "gone")) .nil))))) =
  some (.payloadClass "NotFound" .fieldsDiffer)
-- a construction outside the class form: `_tag` not its first name
#guard emitted (.fail (.record notFoundFields ["id", "_tag"]
    (.cons (.lit (.nat 1)) (.cons (.lit (.str "NotFound")) .nil)))) =
  some (.payloadClass "NotFound" .construction)
-- a field TypeScript spells like another: a binary64 `number` reads back as a natural
def rateFields : List (String × Bool × Ty) := [("_tag", false, .lit "Rate"), ("value", false, .number)]
#guard Classes.classTag? rateFields ["_tag"] (.cons (.lit (.str "Rate")) .nil) = some "Rate"
#guard (ClassTable.moduleClasses nativeSignature "main" ⟨.never, .record rateFields, Requirement.empty⟩
    (.succeed (.lit .unit))).isOk = false
#guard match ClassTable.moduleClasses nativeSignature "main"
    ⟨.never, .record rateFields, Requirement.empty⟩ (.succeed (.lit .unit)) with
  | .error why => why == .payloadClass "Rate" .unreadable
  | .ok _ => false
-- green control: the same type under a natural field declares its class
#guard (ClassTable.moduleClasses nativeSignature "main"
    ⟨.never, .record [("_tag", false, .lit "Rate"), ("value", false, .nat)], Requirement.empty⟩
    (.succeed (.lit .unit))).isOk

/-! ## Ruling (c): message-only and no-field classes keep their spellings

A record whose only fields are `_tag` and a string `message` is the pair, and `_tag` alone is the
literal: the checker refuses both as errors (`errorSpelling`), and as data they are no class. -/

def messageOnly : List (String × Bool × Ty) := [("_tag", false, .lit "E"), ("message", false, .string)]
#guard Types.payloadClass? messageOnly = none
#guard Types.payloadClass? [("_tag", false, .lit "E")] = none
#guard (Types.ofTy (.record messageOnly)).map (TypeScript.Render.type TypeScript.house0) =
  some "{ readonly _tag: \"E\"; readonly message: string }"

/-! ## A field named `cause`

rc.112's `Data.Error` passes a truthy `cause` to the native `ErrorOptions.cause`
(`vendor/effect-4.0.0-rc.112/src/internal/core.ts`, `Error`), so the instance's `cause` is that
value either way, and `toJSON` writes it from the constructor's arguments. A payload field typed
`unknown` is refused at the checker (ruling (a), `errorPayloadField`); a `cause` at an admitted type
is an ordinary field of the class. -/

def wrappedFields : List (String × Bool × Ty) := [("_tag", false, .lit "Wrapped"), ("cause", false, .string)]
def wrapped : NativeEff := failRecord wrappedFields [("_tag", .lit (.str "Wrapped")), ("cause", .lit (.str "disk"))]
#guard (Api.printModule "main" wrapped).map (fun m => String.join (m.decls.map (TypeScript.Render.decl TypeScript.house0))) = some
  ("export class Wrapped extends Data.TaggedError(\"Wrapped\")<{ readonly cause: string }> {}\n" ++
   "export const main: Effect.Effect<never, Wrapped, never> = Effect.fail(new Wrapped({ cause: \"disk\" }))\n")
#guard match Api.printModule "main" wrapped with
  | some m => decide (Api.readModule m = .ok wrapped)
  | none => false

/-! ## The envelope admits exactly the printed classes -/

def origins : List Bindings.Origin := effectOrigins
def ambient : List TypeScript.Import := [.named ["Effect", "Data"] "effect"]

#guard match Api.emitModule "main" failDirect with
  | .ok e => match Api.admitModule "main" e.module [] origins ambient with
    | .ok reading => reading.program == failDirect && reading.classes == [("NotFound", notFoundFields)]
    | .error _ => false
  | .error _ => false
-- red control: the class declaration removed
#guard match Api.emitModule "main" failDirect with
  | .ok e => match Api.admitModule "main" { e.module with decls := e.module.decls.drop 1 } [] origins
      ambient with
    | .error .unbound => true
    | _ => false
  | .error _ => false
-- red control: a class the program does not name, declared before the block
#guard match Api.emitModule "main" failDirect, Classes.classDecl "Unauthorized" unauthorizedFields with
  | .ok e, some extra =>
    match Api.admitModule "main" { e.module with decls := .classDecl extra :: e.module.decls } []
      origins ambient with
    | .error .classDeclarations => true
    | _ => false
  | _, _ => false
-- `Data` is a permitted import origin; without it the heritage is unbound
#guard match Api.emitModule "main" failDirect with
  | .ok e => match Api.admitModule "main" e.module [] origins [.named ["Effect"] "effect"] with
    | .error .unbound => true
    | _ => false
  | .error _ => false

end Effect4.Test.PayloadClasses
