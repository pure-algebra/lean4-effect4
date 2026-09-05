/-
Executable witnesses for `E4-SURFACE-CE-038` through `E4-SURFACE-CE-042` and
`E4-SURFACE-CE-066`.

Contract: `Test/contracts/surface-agent.contract.md`. Frozen by the wave-1b
breaker before `src/Effect4/Surface/Agent.lean` exists; red until the builder
lands it.
-/

import Test.Surface.Fixtures

set_option autoImplicit false

namespace Test.Counterexamples.Surface.Agent

open Effect4.Surface
open Test.Surface.Fixtures

/--
`E4-SURFACE-CE-038`. Attacked statement: "a tool name is a legal identifier",
reusing `TypeScript.targetIdentifier` or a similar convention. MCP publishes a
different alphabet, `^[A-Za-z0-9_-]{1,64}$`: a hyphen is legal and a dot is
not, which is exactly backwards from a TypeScript identifier. A namespaced
name like `shop.lookupUser` passes a "looks like a name" check and is rejected
by the first MCP client that reads it.

Forced repair: `Tool.nameLegal` decides the MCP expression itself, character
by character, and `McpServer.wellFormed` uses it rather than the target
identifier predicate.
-/
def illegalToolNames : List String :=
  [ "shop.lookupUser", "lookup user", "lookup/user", "lookup:user", "lookup+user"
  , "lookupÜser", "", "look\tup" ]

#guard illegalToolNames.all (fun n => Tool.nameLegal n == false)
-- A hyphen is legal, which a TypeScript identifier check would refuse.
#guard Tool.nameLegal "lookup-user" = true
#guard Tool.check { lookupUser with name := "shop.lookupUser" }
  = .error (.toolNameIllegal "shop.lookupUser")
#guard McpServer.check { shopTools with tools := [{ lookupUser with name := "shop.lookupUser" }] }
  = .error (.toolNameIllegal "shop.lookupUser")

/--
`E4-SURFACE-CE-039`. Attacked statement: "the length bound is a formality".
It is not: the bound is 64 and the count is characters. A byte-length check
would admit a 64-character name containing a multi-byte character and refuse a
legal one; an off-by-one would admit 65.

Forced repair: the check counts characters and admits exactly `1..64`.
-/
def name64 : String := String.ofList (List.replicate 64 'a')
def name65 : String := String.ofList (List.replicate 65 'a')

#guard Tool.nameLegal name64 = true
#guard Tool.nameLegal name65 = false
#guard Tool.nameLegal "" = false

/--
`E4-SURFACE-CE-040`. Attacked statement: "a toolkit is a list of tools". A
client indexes `tools/call` by name, so two tools of one name make the call
ambiguous and the second is unreachable. A list carries no distinctness.

Forced repair: distinct tool names is a clause of `McpServer.wellFormed`.
-/
def twoToolsOneName : McpServer shopRefs := { shopTools with tools := [lookupUser, lookupUser] }

#guard McpServer.check twoToolsOneName = .error (.toolNameDuplicate "ShopTools" "lookup_user")
-- Each tool is well formed on its own, so the clause belongs to the server.
#guard twoToolsOneName.tools.all (fun t => Tool.check t == .ok ())
-- The control: a distinct name is admitted.
def lookupAddress : Tool shopRefs :=
  { lookupUser with
    name := "lookup_address"
    annotations := bag "lookup_address" "Look an address up by id" }

#guard McpServer.check { shopTools with tools := [lookupUser, lookupAddress] } = .ok ()

/--
`E4-SURFACE-CE-041`. Attacked statement: "resources are distinct because their
names are". The URI is the key a client reads; two resources on one URI make
`resources/read` ambiguous while their names differ, so a name-based check
passes.

Forced repair: distinct resource *URIs* is the clause, and the name is free.
-/
def twoResourcesOneUri : McpServer shopRefs :=
  { shopTools with
    resources := [{ usersResource with name := "a" }, { usersResource with name := "b" }] }

#guard McpServer.check twoResourcesOneUri
  = .error (.resourceUriDuplicate "ShopTools" "shop://users")
-- Two resources with one name and distinct URIs are admitted, which is the
-- observation that separates the two candidate keys.
#guard McpServer.check
  { shopTools with
    resources := [{ usersResource with uri := "shop://a" },
                  { usersResource with uri := "shop://b" }] } = .ok ()

/--
`E4-SURFACE-CE-042`. The same attack on prompts, which have no URI: the name
is the key there, so the two clauses read different fields and one clause
cannot stand for both.

Forced repair: distinct prompt names is its own clause.
-/
def twoPromptsOneName : McpServer shopRefs :=
  { shopTools with
    prompts := [{ name := "greet", annotations := bag "greet" "Greet a user" },
                { name := "greet", annotations := bag "greet" "Greet a user twice" }] }

#guard McpServer.check twoPromptsOneName = .error (.promptNameDuplicate "ShopTools" "greet")
#guard McpServer.check
  { shopTools with
    prompts := [{ name := "greet", annotations := bag "greet" "Greet a user" },
                { name := "farewell", annotations := bag "farewell" "Say goodbye" }] } = .ok ()

/--
`E4-SURFACE-CE-066`. Attacked statement: "a tool's description is
documentation". For MCP it is not: the description is what the model reads to
decide whether to call the tool, so an undescribed tool is not merely
undocumented, it is unusable by the only client that matters. Plan §15.3 also
forbids a fallback field on the carrier, so the omission is silent in
`toolsListJson` and in the emitted toolkit alike.

Forced repair: `descriptionMissing "tool" name` is a clause of `Tool.check`,
and `Resource.check` carries the same pair for a resource.
-/
def undescribedTool : Tool shopRefs :=
  { lookupUser with annotations := some [⟨"identifier", .str "lookup_user"⟩] }

#guard Tool.check undescribedTool = .error (.descriptionMissing "tool" "lookup_user")
#guard Tool.check { lookupUser with annotations := none }
  = .error (.identifierMissing "tool" "lookup_user")
#guard Resource.check { usersResource with annotations := none }
  = .error (.identifierMissing "resource" "users")
-- The emitters have nowhere else to read a description from, so an ill-formed
-- tool emits nothing rather than a module with a missing doc comment.
#guard (McpServer.toolkitModule { shopTools with tools := [undescribedTool] } shop).isNone

end Test.Counterexamples.Surface.Agent
