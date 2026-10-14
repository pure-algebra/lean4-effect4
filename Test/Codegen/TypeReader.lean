import Effect4.Codegen.Classes
import Effect4.Codegen.ClassTable

/-!
# The checked type reader, and the types it reads back (the state plan's T5, part B)

The faces print a program type at three places in a program: the type arguments an operation
carries on its call's head (`Deferred.make<A, E>()`), a loop's stated cursor type, and a list
fold's stated accumulator type. A module prints one more: the columns of a definition's header.
One reader reads such a type back, at the first two places under no class and at a header under
the module's payload classes: `Classes.readTyChecked`, the class reader's field-type reader
(`Classes.readTy`) kept only where the type printer prints its answer as the spelling it read
(`Types.ofTy`). The fold's stated type is printed and not read yet.

The reader is exact on what it accepts (`readTyChecked_exact`). The type printer is not
injective, so the retraction holds on a domain, `Classes.ReadableTy`, and nowhere else
(`readTyChecked_of_readable`). This battery pins the domain at one type of each kind: the types
that read back, the collisions, the spellings with no reading, and the types with no printed
form. Each guard is a finite check on one type. None states target typing or a host run.
-/

set_option autoImplicit false

namespace Test.Codegen.TypeReader

open Effect4 Effect4.Program Effect4.Codegen Effect4.Codegen.Classes
open Effect4.Machine.Env (Requirement)
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
#guard readTyChecked {} (.name ["void"] []) = some .unit
#guard readTyChecked {} (.name ["boolean"] []) = some .bool
#guard readTyChecked {} (.name ["number"] []) = some .nat
#guard readTyChecked {} (.name ["never"] []) = some .never
#guard readTyChecked {} (.name ["Option", "Option"] [.name ["number"] []]) = some (.option .nat)
-- a list, item by item, and its printed forms back
#guard readTysChecked [] [.name ["void"] [], .name ["never"] []] = some [.unit, .never]
#guard writeTys [.unit, .never] = some [.name ["void"] [], .name ["never"] []]

/-! ## Outside the domain, by reason

Each list is a red control of the retraction: `readTyChecked_of_readable` has `ReadableTy` as
its premise, and the premise is false at every type below. -/

/-- **Collisions.** `int` and `number` print as `number`, which reads as `nat`. A union whose
members collapse in the target prints as one member. -/
def collisions : List Ty := [.int, .number, .option .int, .union .nat .int]

#guard collisions.all fun ty => !ReadableTy {} ty
-- each prints, and its spelling reads to another type
#guard collisions.all fun ty =>
  match (Types.ofTy ty).bind readTyChecked with
  | some other => other != ty
  | none => false
#guard (Types.ofTy .int).bind readTyChecked = some .nat
#guard (Types.ofTy .number).bind readTyChecked = some .nat
#guard (Types.ofTy (.union .nat .int)).bind readTyChecked = some .nat

/-- **Spellings with no reading** under no class. `unknown`, the five handle heads, the scope
handle and a supplied handle, and a tagged payload record, which prints as the name of its class
(under the classes that declare it, the name reads: the last section). -/
def unread : List Ty :=
  [ .unknown, .refOf .nat, .deferredOf .unit .never, .exitOf .nat .never, .causeOf .never
  , .fiberOf .nat .never, Ty.scope, .handle "SqlClient.SqlClient", tagged, .option tagged
  , .record [("hint", false, .refOf .nat)] ]

#guard unread.all fun ty => !ReadableTy {} ty
-- each prints, and no reading answers its spelling
#guard unread.all fun ty => (Types.ofTy ty).isSome && ((Types.ofTy ty).bind readTy).isNone
#guard Types.ofTy tagged = some (.name ["Short"] [])
#guard readTy {} (.name ["Short"] []) = none
#guard readTy {} (.name ["unknown"] []) = none
#guard readTy {} (.name ["Ref", "Ref"] [.name ["number"] []]) = none
#guard readTy {} (.name ["Deferred", "Deferred"] [.name ["void"] [], .name ["never"] []]) = none

/-- **Not the reader's choice for its spelling.** `readonly [A, B]` reads as a product, never as
a tuple of two items. A union in another order of members prints as its normal form. -/
def otherChoice : List Ty := [.tuple [.nat, .bool], .union .string .nat]

#guard otherChoice.all fun ty => !ReadableTy {} ty
#guard (Types.ofTy (.tuple [.nat, .bool])).bind readTyChecked = some (.prod .nat .bool)
#guard (Types.ofTy (.union .string .nat)).bind readTyChecked = some (.union .nat .string)

/-- **No printed form.** A row template's parameter, a nominal application at arguments, a map
whose key is no string, and a handle whose legacy name does not parse. -/
def unprinted : List Ty :=
  [.var 0, .app "Foo" [.nat], .map .nat .nat, .handle "not a type !", .option (.var 0)]

#guard unprinted.all fun ty => !ReadableTy {} ty
#guard unprinted.all fun ty => (Types.ofTy ty).isNone
#guard writeTys [.unit, .var 0] = none

/-! ## The reader keeps only what prints back

The field-type reader is permissive: `number` reads as `nat` under any spelling of it. The
checked reader keeps an answer only when the printer prints it as the spelling read. A mutable
tuple is read by neither. -/

-- an empty union is no printed form: the printer writes `never` for the empty type
#guard readTy {} (.union []) = some .never
#guard readTyChecked {} (.union []) = none
-- a union of one member is no printed form: the printer writes the member alone
#guard readTy {} (.union [.name ["number"] []]) = some .nat
#guard readTyChecked {} (.union [.name ["number"] []]) = none
#guard readTyChecked {} (.tuple [.name ["number"] []] false) = none
#guard readTyChecked {} (.function [] (.name ["void"] [])) = none
#guard readTysChecked [] [.name ["void"] [], .name ["unknown"] []] = none

/-! ## The class reader shares the `never` arm

A payload class's field types go through the same field-type reader, so a declared field of
type `never` now reads, and its declaration prints back. No printed module declares such a
class: a tagged record with a `never` field is no payload class of the printer
(`Types.payloadClass?`). -/

def neverFields : Classes.Fields := [("_tag", false, .lit "X"), ("a", false, .never)]

#guard (classDecl "X" neverFields).bind readClassDecl = some ("X", neverFields)
#guard Types.payloadClass? neverFields = none

/-! ## The context type (decisions row 349)

A context type prints as `Context.Context<R>`, its row in the one spelling of a requirement row
at the native scope key (`Types.ofTy_contextOf`). The checked reader reads it back to its keys.
An application's service holds a context as its state and passes it first in each method's
request (decisions row 378 (20)): the last type below is such a request. -/

/-- Two ordinary service keys. -/
def keyA : ServiceKey := ⟨⟨3⟩, ⟨7⟩⟩
def keyB : ServiceKey := ⟨⟨1⟩, ⟨12⟩⟩

/-- Context types that read back: no key, one key, the native scope, two keys, and a service
method's request of a context and a string. -/
def contexts : List Ty :=
  [ .contextOf (Requirement.ofList []), .contextOf (Requirement.ofList [keyA])
  , .contextOf (Requirement.ofList [nativeScopeKey]), .contextOf (Requirement.ofList [keyA, keyB])
  , .prod (.contextOf (Requirement.ofList [])) .string ]

#guard contexts.all ReadableTy
-- the printed text: the row in key order, the native scope as `Scope.Scope`
#guard Types.ofTy (.contextOf (Requirement.ofList [keyA, nativeScopeKey])) =
  some (.name ["Context", "Context"] [.union [.name ["Scope", "Scope"] [], .literal "k3_7"]])
-- control: the internal handle `Context.Context<unknown>` has no row, so no reading
#guard readTy {} (.name ["Context", "Context"] [.name ["unknown"] []]) = none
#guard !ReadableTy {} (.handle "Context.Context<unknown>")
-- control: a key written twice reads, and the checked reader refuses it, since the row prints the
-- key once; a literal that is no key's text decodes to a key that prints otherwise
#guard readTy {} (.name ["Context", "Context"] [.union [.literal "k3_7", .literal "k3_7"]]) =
  some (.contextOf (Requirement.ofList [keyA]))
#guard readTyChecked {} (.name ["Context", "Context"] [.union [.literal "k3_7", .literal "k3_7"]]) =
  none
#guard readTyChecked {} (.name ["Context", "Context"] [.literal "x"]) = none

/-! ## A payload class under the module's classes (decisions row 120)

A definition's header reads its columns under the module's payload classes (`readDefHead`,
`Codegen/Read.lean`): a class's name reads as the record that its declaration declares, so a
tagged record, which prints as the name of its class, reads back. Under no class the name has no
reading (`unread` above). -/

/-- The classes of a module that declares `Short` with `tagged`'s fields. -/
def shortClasses : Classes := [("Short", [("_tag", false, .lit "Short"), ("needed", false, .nat)])]

/-- The classes of a module that declares `Short` with another field type. -/
def otherShort : Classes := [("Short", [("_tag", false, .lit "Short"), ("needed", false, .string)])]

-- reader: the tagged record reads back under the classes that declare it: alone, under a type
-- constructor, and in a union, as an error column that names a class prints
#guard [tagged, .option tagged, .list tagged, .union (.prod (.lit "SqlError") .string) tagged].all
  (ReadableTy { classes := shortClasses })
#guard readTyChecked { classes := shortClasses } (.name ["Short"] []) = some tagged
-- control: under classes that declare `Short` with other fields the name reads as that record,
-- so `tagged` is outside the readable types there
#guard readTyChecked { classes := otherShort } (.name ["Short"] []) =
  some (.record [("_tag", false, .lit "Short"), ("needed", false, .string)])
#guard !ReadableTy { classes := otherShort } tagged
-- control: under classes that do not declare the name, it has no reading
#guard readTy { classes := [("Long", [("_tag", false, .lit "Long")])] } (.name ["Short"] []) = none
-- control: a union out of its normal form prints as the normal form, so it is outside the domain
#guard !ReadableTy { classes := shortClasses } (.union tagged (.prod (.lit "SqlError") .string))
-- control: the class reader reads a class's fields under no class, so a class whose field names
-- another class has no reading
#guard ((classDecl "Wrap" [("_tag", false, .lit "Wrap"), ("inner", false, tagged)]).bind
  readClassDecl).isNone

/-! ## `Ref.Ref<A>` in a definition's header (decisions row 378 (8))

A definition's header reads its columns under `sig.typeEnv classes` (`refs = true`), so
`Ref.Ref<A>` reads back as `.refOf A` — alone, in a product with a context, or over a cached option
of a list. Under `{}` (`refs = false`, an operation's type arguments or a loop's cursor),
`Ref.Ref<A>` still reads as nothing (`unread` above). -/

#guard [Ty.refOf .nat, .refOf (.option (.list plain)),
    .prod (.contextOf (Requirement.ofList [keyA])) (.refOf (.option (.list plain)))].all
  (ReadableTy { refs := true })
#guard readTyChecked { refs := true } (.name ["Ref", "Ref"] [.name ["number"] []]) =
  some (.refOf .nat)
-- control: `Deferred.Deferred<A, E>` still reads as nothing even when `refs = true`
#guard !ReadableTy { refs := true } (.deferredOf .unit .never)

end Test.Codegen.TypeReader
