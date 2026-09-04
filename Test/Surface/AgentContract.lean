/-
Contract: `test/contracts/surface-agent.contract.md`.

Frozen by the wave-1b breaker before `Effect4/Surface/Agent.lean` exists, from
`docs/research/2026-09-04-surface-library-plan.md` §4.5 alone. Red until the
builder lands the module.

MCP names are a wire alphabet with a published regular expression, so the name
check is a modeled law and gets a census over a hostile alphabet rather than
one happy example. `toolsListJson` is pinned against a literal `Json` term:
the key order and the `inputSchema` spelling are the contract, and the
description is read from the annotation bag through the key of plan §15.1,
never from a field on the carrier.

Every negative receipt pins the exact refusal, not a Boolean.
-/

import Test.Surface.Fixtures
import Effect4.Data.Json

set_option autoImplicit false

namespace Test.Surface.AgentContract

open Effect4 (Json)
open Effect4.Surface
open Test.Surface.Fixtures

/-! ## The MCP name alphabet: `^[A-Za-z0-9_-]{1,64}$` -/

#guard Tool.nameLegal "lookup_user" = true
#guard Tool.nameLegal "a" = true
#guard Tool.nameLegal "A0-_" = true
#guard Tool.nameLegal "0" = true
-- Exactly 64 characters is the last admitted length.
#guard Tool.nameLegal (String.ofList (List.replicate 64 'a')) = true
-- `E4-SURFACE-CE-039`: 65 is one too many, and the count is characters.
#guard Tool.nameLegal (String.ofList (List.replicate 65 'a')) = false
#guard Tool.nameLegal "" = false
-- `E4-SURFACE-CE-038`: every character outside the class is refused.
#guard Tool.nameLegal "lookup.user" = false
#guard Tool.nameLegal "lookup/user" = false
#guard Tool.nameLegal "lookup user" = false
#guard Tool.nameLegal "lookup:user" = false
#guard Tool.nameLegal "lookupÜser" = false
#guard Tool.nameLegal "lookup\nuser" = false

/-! ## The fixture server is well formed -/

#guard Tool.check lookupUser = .ok ()
#guard Resource.check usersResource = .ok ()
#guard McpServer.check shopTools = .ok ()
#guard Tool.description lookupUser = some "Look a user up by id"
#guard Resource.description usersResource = some "Every user of the shop"

theorem lookupUser_clauses : Tool.Described lookupUser ∧ Tool.Named lookupUser :=
  (Tool.wellFormed_iff lookupUser).mp (by decide)

theorem lookupUser_wf : Tool.WellFormed lookupUser := by decide
theorem shopTools_wf : McpServer.WellFormed shopTools := by decide

/-! ## The mutants -/

-- `E4-SURFACE-CE-038`: an illegal tool name.
def dottedTool : Tool shopRefs := { lookupUser with name := "shop.lookupUser" }
#guard Tool.check dottedTool = .error (.toolNameIllegal "shop.lookupUser")
#guard McpServer.check { shopTools with tools := [dottedTool] }
  = .error (.toolNameIllegal "shop.lookupUser")

-- `E4-SURFACE-CE-066`: a tool an agent cannot read is ill-formed (plan §15.2).
def undescribedTool : Tool shopRefs :=
  { lookupUser with annotations := some [⟨"identifier", .str "lookup_user"⟩] }
#guard Tool.check undescribedTool = .error (.descriptionMissing "tool" "lookup_user")
#guard Tool.check { lookupUser with annotations := none }
  = .error (.identifierMissing "tool" "lookup_user")

-- The same clause on a resource.
#guard Resource.check { usersResource with annotations := none }
  = .error (.identifierMissing "resource" "users")

-- `E4-SURFACE-CE-040`: two tools of one name; a client indexes by name.
#guard McpServer.check { shopTools with tools := [lookupUser, lookupUser] }
  = .error (.toolNameDuplicate "ShopTools" "lookup_user")

-- The control: a differently named second tool is admitted.
def lookupAddress : Tool shopRefs :=
  { lookupUser with
    name := "lookup_address"
    annotations := bag "lookup_address" "Look an address up by id" }
#guard McpServer.check { shopTools with tools := [lookupUser, lookupAddress] } = .ok ()

-- `E4-SURFACE-CE-041`: two resources on one URI.
def resourceA : Resource := { usersResource with name := "a" }
def resourceB : Resource := { usersResource with name := "b" }
#guard McpServer.check { shopTools with resources := [resourceA, resourceB] }
  = .error (.resourceUriDuplicate "ShopTools" "shop://users")

-- Two resources with one name but distinct URIs are admitted: the URI is the key.
#guard McpServer.check
  { shopTools with
    resources := [{ usersResource with uri := "shop://a" },
                  { usersResource with uri := "shop://b" }] } = .ok ()

-- `E4-SURFACE-CE-042`: two prompts of one name.
#guard McpServer.check
  { shopTools with
    prompts := [{ name := "greet", annotations := bag "greet" "Greet a user" },
                { name := "greet", annotations := bag "greet" "Greet a user twice" }] }
  = .error (.promptNameDuplicate "ShopTools" "greet")

/-! ## `tools/list`, pinned to literal JSON -/

#guard McpServer.toolsListJson shopTools =
  some (.obj
    [ ("tools", .arr
        [ .obj
            [ ("name", .str "lookup_user")
            , ("description", .str "Look a user up by id")
            , ("inputSchema", .obj
                [ ("type", .str "object")
                , ("properties", .obj [("id", .obj [("type", .str "string")])])
                , ("required", .arr [.str "id"]) ]) ] ]) ])

-- A tool with no description omits the key rather than emitting `null`. Such
-- a tool is ill-formed, so this branch is reachable only from a refused value
-- and the battery pins it there rather than pretending it is a normal case.
#guard McpServer.toolsListJson { shopTools with tools := [undescribedTool] } =
  some (.obj
    [ ("tools", .arr
        [ .obj
            [ ("name", .str "lookup_user")
            , ("inputSchema", .obj
                [ ("type", .str "object")
                , ("properties", .obj [("id", .obj [("type", .str "string")])])
                , ("required", .arr [.str "id"]) ]) ] ]) ])

-- An empty toolkit still answers the envelope.
#guard McpServer.toolsListJson { shopTools with tools := [] } = some (.obj [("tools", .arr [])])

/-! ## The toolkit module, `isSome` only -/

#guard (McpServer.toolkitModule shopTools shop).isSome
-- The toolkit's description comes from the bag, so an ill-formed server emits
-- nothing rather than a module with a missing doc comment.
#guard (McpServer.toolkitModule { shopTools with tools := [undescribedTool] } shop).isNone

end Test.Surface.AgentContract
