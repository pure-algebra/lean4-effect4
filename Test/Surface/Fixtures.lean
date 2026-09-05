/-
The `shop` fixture domain, written as plain Lean terms.

Frozen by the wave-1b breaker from `docs/research/2026-09-04-surface-library-plan.md`
§6, §13.1 and §15 so that the batteries, the counterexample witnesses, the DSL
battery and `Test/Surface/Fixtures.lean` all read one set of rows. The
DSL wave checks its commands produce these very values by
`#guard <dsl> = <fixture>`; nothing here may depend on `Effect4.Meta.Surface`.

The reference application of plan §13.3 is `docs`, and it is deliberately not
this fixture: §13.6 rule 9 says coverage of carrier features lives in battery
fixtures, so `shop` is the fixture that exercises the carriers and `docs` stays
small.

Three entities: `Address` (a flat struct of strings), `User` (keyed by `id`,
optional `email`, a list, a literal union and a reference to `Address`) and
`NotFound` (the error body). Address precedes User because a reference table
lists referents before referrers.

The semantic layer of plan §15 is not optional, so every root bag carries
`identifier` and `description`, and every property of every entity carries a
`description` because `shop` is an `active` domain. The bags are written as
raw `AnnotationEntry` lists with the rc.112 key strings so this file does not
depend on the spelling wave 1a gives them in `src/Effect4/Surface/Annotate.lean`.
-/

import Effect4.Surface.Kind
import Effect4.Surface.Refusal
import Effect4.Surface.Entity
import Effect4.Surface.Api
import Effect4.Surface.Agent
import Effect4.Surface.Deploy
import Effect4.Surface.Site

set_option autoImplicit false

namespace Test.Surface.Fixtures

open Effect4 (Representation ReferenceEntry PropertySignature Annotations)
open Effect4.Surface

/-! ## The semantic layer, written as raw annotation entries -/

/-- A root bag: the two keys plan §15.2 makes mandatory. -/
def bag (identifier description : String) : Annotations :=
  some [⟨"identifier", .str identifier⟩, ⟨"description", .str description⟩]

/-- A property bag: `description` only. -/
def note (description : String) : Annotations :=
  some [⟨"description", .str description⟩]

/-- An entity's root representation: an `objects` node carrying its bag. -/
def entityRep (identifier description : String)
    (properties : List PropertySignature) : Representation :=
  .objects (bag identifier description) [] properties []

/-- A described property. -/
def field (name : String) (type : Representation) (description : String)
    (isOptional : Bool := false) : PropertySignature :=
  Effect4.Schema.property name type (isOptional := isOptional)
    (annotations := note description)

/-! ## Representations -/

/-- `Address`: three required string properties, so it is `Kind.text` as well
as `Kind.struct`. -/
def addressRep : Representation :=
  entityRep "Address" "A postal address of a user"
    [ field "street" Effect4.Schema.string "The street line"
    , field "city" Effect4.Schema.string "The city"
    , field "postcode" Effect4.Schema.string "The postal code" ]

/-- `User`: the plan's §6 entity, including the optional property, the array,
the literal union and the reference. -/
def userRep : Representation :=
  entityRep "User" "A registered shopper"
    [ field "id" Effect4.Schema.string "The user's stable identity"
    , field "name" Effect4.Schema.string "The display name"
    , field "email" Effect4.Schema.string "The contact address, when given"
        (isOptional := true)
    , field "tags" (Effect4.Schema.array Effect4.Schema.string) "Free-form labels"
    , field "role"
        (Effect4.Schema.anyOf (Effect4.Schema.literalString "admin")
          [Effect4.Schema.literalString "member"])
        "The user's role in the shop"
    , field "address" (Effect4.Schema.reference "Address") "Where the user ships to" ]

/-- `NotFound`: the error body. -/
def notFoundRep : Representation :=
  entityRep "NotFound" "The requested resource does not exist"
    [ field "_tag" (Effect4.Schema.literalString "NotFound") "The error discriminant"
    , field "message" Effect4.Schema.string "What was not found" ]

/-- The path-parameter struct of `/users/:id`. Not an entity, so plan §15.2's
property clause does not reach it. -/
def userIdRep : Representation :=
  Effect4.Schema.struct [Effect4.Schema.property "id" Effect4.Schema.string]

/-- The `POST /users` body. -/
def newUserRep : Representation :=
  Effect4.Schema.struct
    [ Effect4.Schema.property "name" Effect4.Schema.string
    , Effect4.Schema.property "email" Effect4.Schema.string (isOptional := true) ]

/-! ## Entities and the domain -/

def addressEntity : Entity :=
  { name := "Address", domain := "shop", rep := addressRep, key := ["street", "postcode"] }

def userEntity : Entity :=
  { name := "User", domain := "shop", rep := userRep, key := ["id"] }

def notFoundEntity : Entity :=
  { name := "NotFound", domain := "shop", rep := notFoundRep, key := ["_tag"]
  , stance := .view }

def shop : Domain :=
  { name := "shop", entities := [addressEntity, userEntity, notFoundEntity], active := true }

/-- The reference table, written out so a reordering of `Domain.refs` is a
visible failure rather than a silent one. -/
def shopRefs : List ReferenceEntry :=
  [ ⟨"Address", addressRep⟩, ⟨"User", userRep⟩, ⟨"NotFound", notFoundRep⟩ ]

/-! ## Schema slots

The only two admitted ways into `Sch` are `Sch.of?` and the anonymous
constructor with a kernel-checked equation; `sch` is the second one with the
equation discharged by `decide`. -/

def sch (k : Kind) (rep : Representation)
    (ok : kindCheck shopRefs 64 k rep = true := by decide) : Sch shopRefs k :=
  ⟨rep, ok⟩

def userIdParams : Sch shopRefs .text := sch .text userIdRep
def userBody : Sch shopRefs .json := sch .json (Effect4.Schema.reference "User")
def newUserBody : Sch shopRefs .json := sch .json newUserRep
def notFoundBody : Sch shopRefs .json := sch .json (Effect4.Schema.reference "NotFound")
def addressBody : Sch shopRefs .json := sch .json (Effect4.Schema.reference "Address")
def lookupParams : Sch shopRefs .struct := sch .struct userIdRep

/-- The three kinds plan §13.1 adds so the carrier can express what the v1
emitters refuse. They are the existing sets under new names, and the
distinction is carried by `Payload` and `ResponseBody`. -/
def userStream : Sch shopRefs .stream := sch .stream (Effect4.Schema.reference "User")
def newUserMultipart : Sch shopRefs .multipart := sch .multipart newUserRep
def newUserUrlEncoded : Sch shopRefs .urlEncoded := sch .urlEncoded userIdRep

/-! ## The API -/

def getUser : Endpoint shopRefs :=
  { id := "getUser", method := .get, path := ⟨[.param "id"]⟩
  , annotations := bag "getUser" "Read one user by id"
  , params := some userIdParams
  , success := [⟨200, .json userBody⟩]
  , errors := [⟨404, .json notFoundBody⟩]
  , requires := ["Db"] }

def createUser : Endpoint shopRefs :=
  { id := "createUser", method := .post, path := ⟨[]⟩
  , annotations := bag "createUser" "Register a new user"
  , payloads := [.json newUserBody]
  , success := [⟨201, .json userBody⟩]
  , errors := [⟨409, .json notFoundBody⟩]
  , requires := ["Db"] }

/-- A `204` success with no body: the `ResponseBody.void` arm. -/
def deleteUser : Endpoint shopRefs :=
  { id := "deleteUser", method := .delete, path := ⟨[.param "id"]⟩
  , annotations := bag "deleteUser" "Remove a user"
  , params := some userIdParams
  , success := [⟨204, .void⟩]
  , errors := [⟨404, .json notFoundBody⟩]
  , requires := ["Db"] }

def usersGroup : Group shopRefs :=
  { id := "users"
  , annotations := bag "users" "Everything about shoppers"
  , pathPrefix := some ⟨[.literal "users"]⟩
  , endpoints := [getUser, createUser, deleteUser] }

def shopApi : Api shopRefs :=
  { id := "Shop"
  , annotations := bag "Shop" "The shop's HTTP surface"
  , pathPrefix := some ⟨[.literal "api"]⟩
  , groups := [usersGroup] }

/-! ## The MCP server -/

def lookupUser : Tool shopRefs :=
  { name := "lookup_user"
  , annotations := bag "lookup_user" "Look a user up by id"
  , parameters := lookupParams
  , success := userBody
  , failure := some notFoundBody }

def usersResource : Resource :=
  { uri := "shop://users", name := "users"
  , annotations := bag "users" "Every user of the shop" }

def shopTools : McpServer shopRefs :=
  { name := "ShopTools", version := "1.0.0"
  , annotations := bag "ShopTools" "The shop's agent surface"
  , tools := [lookupUser]
  , resources := [usersResource]
  , prompts := [{ name := "greet", annotations := bag "greet" "Greet a user"
                , arguments := [("name", true)] }] }

/-! ## The deployment -/

def shopWorker : Deployment :=
  { name := "shop-worker", host := .cloudflareWorker
  , annotations := bag "shop-worker" "The shop's Cloudflare Worker"
  , main := some "src/worker.ts"
  , compatibilityDate := "2026-09-01"
  , bindings := [.d1 "DB" "shop-db" "0f0f", .kv "SESSIONS" "1a1a"]
  , routes := ["shop.example.com/*"]
  , serves := [{ api := "Shop", at_ := ⟨[.literal "api"]⟩ }]
  , provides := [("Db", "DB")] }

/-! ## The site -/

def homePage : Page :=
  { route := ⟨[]⟩, title := "Home", uses := [("Shop", "users", "getUser")] }

def newUserPage : Page :=
  { route := ⟨[.literal "users", .literal "new"]⟩, title := "New user"
  , form := some ("Shop", "users", "createUser") }

def shopSite : Site :=
  { name := "ShopSite"
  , annotations := bag "ShopSite" "The shop's browser surface"
  , pages := [homePage, newUserPage] }

end Test.Surface.Fixtures
