/-
Executable witnesses for `E4-SURFACE-CE-058`, `E4-SURFACE-CE-059` and
`E4-SURFACE-CE-070`.

Contract: `test/contracts/surface-emit.contract.md`. Frozen by the wave-1b
breaker before `Effect4/Surface/Emit.lean` exists; red until the builder lands
it.
-/

import Test.Surface.Fixtures
import Effect4.Codegen.Rules

set_option autoImplicit false

namespace Test.Counterexamples.Surface.Emit

open Effect4.Surface
open Test.Surface.Fixtures

/--
`E4-SURFACE-CE-058`. Attacked statement: "a rule is `modeled` when its emitter
is right". Rightness is not an observation. The operator's sentence is "we can
emit anything but we cannot claim to model it", and the only thing that can
carry the stronger claim is a landed host receipt at the pin.

The failure this row guards is a review failure, not a code failure: a stance
field with no invariant is a comment, and the word `modeled` would be set by
whoever last edited the file. `Rule.modeled_has_receipt` makes the flip cost a
receipt name in the same change, and at landing the antecedent is empty, which
is the guard below.

Forced repair: the theorem, plus `Rule.receipt` naming the harness check.
-/
def landingStances : List Stance := Rule.all.map Rule.stance

#guard landingStances.all (· = .emitted)
#guard (Rule.all.map Rule.receipt).all (·.isNone)
#guard Rule.all.all (fun r => Rule.stance r != Stance.modeled)

theorem no_modeled_without_receipt :
    ∀ r : Rule, r.stance = .modeled → (Rule.receipt r).isSome :=
  Rule.modeled_has_receipt

/--
`E4-SURFACE-CE-059`. Attacked statement: "the census lists the emitters".
`Rule.all` is a hand-written list, and an emitter added to
`Effect4/Surface/` without a row is invisible to the stance table, to the gate
and to every report. The lowering lane already met this and answered it with a
tag census over the source (`scripts/check-lowering-coverage.sh`), checked in
both directions: every `-- surface: rule.<id>` tag is in `Rule.all.map
Rule.id`, and every id has a tag.

Forced repair: `Rule.mem_all` and `Rule.all_nodup` close the Lean half; the
shell half reuses the lowering tokenizer, and neither alone is enough. The
guard below is the Lean half only, and says so.
-/
def ids : List String := Rule.all.map Rule.id

#guard ids =
  [ "surface.entity.document", "surface.entity.constructor", "surface.entity.jsonSchema"
  , "surface.api.httpApi", "surface.api.client", "surface.api.openApi"
  , "surface.mcp.toolkit", "surface.mcp.toolsList"
  , "surface.deploy.wrangler", "surface.deploy.worker", "surface.site.routes" ]
#guard ids.eraseDups.length = 11
#guard Rule.all.all (fun r => Rule.ofId? (Rule.id r) == some r)
#guard (Rule.ofId? "surface.api.handlers").isNone

theorem every_rule_listed : ∀ r : Rule, r ∈ Rule.all := Rule.mem_all
theorem no_rule_listed_twice : Rule.all.Nodup := Rule.all_nodup

/--
`E4-SURFACE-CE-070`. Attacked statement: "an emitter given a shape it does not
support emits what it can". Plan §13.1 makes `multipart`, `urlEncoded` and
`stream` expressible precisely so a clause can name them, and plan §13.6 rule
8 forbids claiming anything about bytes without a receipt. An emitter that
skipped an unsupported response and emitted the rest would produce a module
that typechecks, passes the harness, and is missing an endpoint nobody
notices; an emitter that reached for `Decl.raw` would reopen
`E4-TARGET-CE-003`.

The endpoint itself stays well formed. That gap between what the model
expresses and what the v1 emitters lower is real and is stated in
`Rule.refuses`, not hidden by narrowing the carrier.

Forced repair: `Option`, answered `none`, and `Rule.refuses` naming the shape.
-/
def streamingEndpoint : Endpoint shopRefs :=
  { getUser with success := [⟨200, .stream userStream "text/event-stream" ["update"]⟩] }

def streamingGroup : Group shopRefs := { usersGroup with endpoints := [streamingEndpoint] }
def streamingApi : Api shopRefs := { shopApi with groups := [streamingGroup] }

-- Well formed, and not emitted.
#guard Endpoint.check streamingEndpoint = .ok ()
#guard Api.check streamingApi = .ok ()
#guard (httpApiModule streamingApi shop).isNone
#guard (clientModule streamingApi).isNone
#guard (openApi streamingApi shop).isNone

def multipartEndpoint : Endpoint shopRefs :=
  { createUser with payloads := [.multipart newUserMultipart] }

def multipartApi : Api shopRefs :=
  { shopApi with groups := [{ usersGroup with endpoints := [multipartEndpoint] }] }

#guard Endpoint.check multipartEndpoint = .ok ()
#guard (httpApiModule multipartApi shop).isNone

-- And the refusal is named, so the gap is readable rather than inferred from
-- a `none`.
#guard (Rule.refuses .apiHttpApi).contains "response.stream"
#guard (Rule.refuses .apiHttpApi).contains "payload.multipart"
#guard (Rule.refuses .apiHttpApi).contains "payload.urlEncoded"
#guard (Rule.refuses .apiOpenApi).contains "response.stream"
#guard (Rule.refuses .entityDocument).contains "schema.suspend"
#guard (Rule.refuses .siteRoutes) = []

end Test.Counterexamples.Surface.Emit
