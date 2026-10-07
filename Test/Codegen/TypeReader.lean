import Effect4.Laws.Codegen.Classes

/-!
# The checked type reader, and the types it reads back (the state plan's T5, part B)

The faces print a program type at three places: the type arguments an operation carries on its
call's head (`Deferred.make<A, E>()`), a loop's stated cursor type, and a list fold's stated
accumulator type. One reader reads such a type back, at the first two places:
`Classes.readTyChecked`, the class reader's field-type reader (`Classes.readTy`) kept only
where the type printer prints its answer as the spelling it read (`Types.ofTy`). The fold's
stated type is printed and not read yet.

The reader is exact on what it accepts (`readTyChecked_exact`). The type printer is not
injective, so the retraction holds on a domain, `Classes.ReadableTy`, and nowhere else
(`readTyChecked_of_readable`). This battery pins the domain at one type of each kind: the types
that read back, the collisions, the spellings with no reading, and the types with no printed
form. Each guard is a finite check on one type. None states target typing or a host run.
-/

set_option autoImplicit false

namespace Test.Codegen.TypeReader

open Effect4 Effect4.Program Effect4.Codegen Effect4.Codegen.Classes
open TypeScript (TypeRef)

/-- A tagged payload record type: it prints as the name of its class. -/
def tagged : Ty := .record [("_tag", false, .lit "Short"), ("needed", false, .nat)]

/-- A record type with no tag: it prints as an object type. -/
def plain : Ty := .record [("a", false, .nat), ("b", true, .string)]

/-! ## The types that read back -/

/-- One type of each kind that the checked reader answers from its own printed spelling. `never`
is among them since part B: the error column of `Deferred.make<A, never>()` is spelled so. -/
def readable : List Ty :=
  [ .unit, .bool, .nat, .string, .lit "x", .never, .null, .undefined, .bytes
  , .option .nat, .option .never, .list .string, .list (.option .unit)
  , .prod .nat .bool, .tuple [], .tuple [.nat], .tuple [.nat, .bool, .string]
  , .except .string .nat, .map .string .nat, plain, .union .nat .string ]

#guard readable.all ReadableTy
-- each prints, and its printed spelling reads back to it
#guard readable.all fun ty => (Types.ofTy ty).bind readTyChecked == some ty

-- the Queue's five spellings: `void`, `boolean`, `number`, `never` and `Option.Option<number>`
#guard readTyChecked (.name ["void"] []) = some .unit
#guard readTyChecked (.name ["boolean"] []) = some .bool
#guard readTyChecked (.name ["number"] []) = some .nat
#guard readTyChecked (.name ["never"] []) = some .never
#guard readTyChecked (.name ["Option", "Option"] [.name ["number"] []]) = some (.option .nat)
-- a list, item by item, and its printed forms back
#guard readTysChecked [.name ["void"] [], .name ["never"] []] = some [.unit, .never]
#guard writeTys [.unit, .never] = some [.name ["void"] [], .name ["never"] []]

/-! ## Outside the domain, by reason

Each list is a red control of the retraction: `readTyChecked_of_readable` has `ReadableTy` as
its premise, and the premise is false at every type below. -/

/-- **Collisions.** `int` and `number` print as `number`, which reads as `nat`. A union whose
members collapse in the target prints as one member. -/
def collisions : List Ty := [.int, .number, .option .int, .union .nat .int]

#guard collisions.all fun ty => !ReadableTy ty
-- each prints, and its spelling reads to another type
#guard collisions.all fun ty =>
  match (Types.ofTy ty).bind readTyChecked with
  | some other => other != ty
  | none => false
#guard (Types.ofTy .int).bind readTyChecked = some .nat
#guard (Types.ofTy .number).bind readTyChecked = some .nat
#guard (Types.ofTy (.union .nat .int)).bind readTyChecked = some .nat

/-- **Spellings with no reading.** `unknown`, the five handle heads, the scope handle and a
supplied handle, and a tagged payload record, which prints as the name of its class. -/
def unread : List Ty :=
  [ .unknown, .refOf .nat, .deferredOf .unit .never, .exitOf .nat .never, .causeOf .never
  , .fiberOf .nat .never, Ty.scope, .handle "SqlClient.SqlClient", tagged, .option tagged
  , .record [("hint", false, .deferredOf .unit .never)] ]

#guard unread.all fun ty => !ReadableTy ty
-- each prints, and no reading answers its spelling
#guard unread.all fun ty => (Types.ofTy ty).isSome && ((Types.ofTy ty).bind readTy).isNone
#guard Types.ofTy tagged = some (.name ["Short"] [])
#guard readTy (.name ["Short"] []) = none
#guard readTy (.name ["unknown"] []) = none
#guard readTy (.name ["Deferred", "Deferred"] [.name ["void"] [], .name ["never"] []]) = none

/-- **Not the reader's choice for its spelling.** `readonly [A, B]` reads as a product, never as
a tuple of two items. A union in another order of members prints as its normal form. -/
def otherChoice : List Ty := [.tuple [.nat, .bool], .union .string .nat]

#guard otherChoice.all fun ty => !ReadableTy ty
#guard (Types.ofTy (.tuple [.nat, .bool])).bind readTyChecked = some (.prod .nat .bool)
#guard (Types.ofTy (.union .string .nat)).bind readTyChecked = some (.union .nat .string)

/-- **No printed form.** A row template's parameter, a nominal application at arguments, a map
whose key is no string, and a handle whose legacy name does not parse. -/
def unprinted : List Ty :=
  [.var 0, .app "Foo" [.nat], .map .nat .nat, .handle "not a type !", .option (.var 0)]

#guard unprinted.all fun ty => !ReadableTy ty
#guard unprinted.all fun ty => (Types.ofTy ty).isNone
#guard writeTys [.unit, .var 0] = none

/-! ## The reader keeps only what prints back

The field-type reader is permissive: `number` reads as `nat` under any spelling of it. The
checked reader keeps an answer only when the printer prints it as the spelling read. A mutable
tuple is read by neither. -/

-- an empty union is no printed form: the printer writes `never` for the empty type
#guard readTy (.union []) = some .never
#guard readTyChecked (.union []) = none
-- a union of one member is no printed form: the printer writes the member alone
#guard readTy (.union [.name ["number"] []]) = some .nat
#guard readTyChecked (.union [.name ["number"] []]) = none
#guard readTyChecked (.tuple [.name ["number"] []] false) = none
#guard readTyChecked (.function [] (.name ["void"] [])) = none
#guard readTysChecked [.name ["void"] [], .name ["unknown"] []] = none

/-! ## The class reader shares the `never` arm

A payload class's field types go through the same field-type reader, so a declared field of
type `never` now reads, and its declaration prints back. No printed module declares such a
class: a tagged record with a `never` field is no payload class of the printer
(`Types.payloadClass?`). -/

def neverFields : Classes.Fields := [("_tag", false, .lit "X"), ("a", false, .never)]

#guard (classDecl "X" neverFields).bind readClassDecl = some ("X", neverFields)
#guard Types.payloadClass? neverFields = none

/-! ## The laws this battery reads -/

/-- Exactness, at any syntax: what the checked reader accepts prints back to it. -/
example {x : TypeRef} {ty : Ty} (h : readTyChecked x = some ty) : Types.ofTy ty = some x :=
  readTyChecked_exact h

/-- The retraction, on the readable types only. -/
example {ty : Ty} {x : TypeRef} (hr : ReadableTy ty = true) (hp : Types.ofTy ty = some x) :
    readTyChecked x = some ty :=
  readTyChecked_of_readable hr hp

/-- The two, item by item. -/
example {xs : List TypeRef} {tys : List Ty} (h : readTysChecked xs = some tys) :
    writeTys tys = some xs :=
  readTysChecked_exact h

example {tys : List Ty} {xs : List TypeRef} (hr : tys.all ReadableTy = true)
    (hp : writeTys tys = some xs) : readTysChecked xs = some tys :=
  readTysChecked_of_readable hr hp

end Test.Codegen.TypeReader
