/-
Contract: `test/contracts/surface-emit.contract.md`.

Frozen by the wave-1b breaker before `Effect4/Surface/Emit.lean` exists, from
`docs/research/2026-09-04-surface-library-plan.md` §5 alone. Red until the
builder lands the module.

"We can emit anything but we cannot claim to model it", as a type. The census
is checked in both directions: the id list is a literal in order, and
`Rule.mem_all` says every constructor is in it. At landing every rule is
`Stance.emitted` and every receipt is `none`; `Rule.modeled_has_receipt` makes
a flip without a receipt unrepresentable.

When a rule is later flipped, the two landing `#guard`s below fail and must be
replaced by the row that names the receipt. That is the intended maintenance
cost: the census cannot drift quietly.
-/

import Effect4.Codegen.Rules

set_option autoImplicit false

namespace Test.Surface.EmitContract

open Effect4.Surface

/-! ## The eleven ids, in order, in both directions -/

#guard Rule.all.map Rule.id =
  [ "surface.entity.document"
  , "surface.entity.constructor"
  , "surface.entity.jsonSchema"
  , "surface.api.httpApi"
  , "surface.api.client"
  , "surface.api.openApi"
  , "surface.mcp.toolkit"
  , "surface.mcp.toolsList"
  , "surface.deploy.wrangler"
  , "surface.deploy.worker"
  , "surface.site.routes" ]

#guard Rule.all.length = 11
#guard Rule.all = [.entityDocument, .entityConstructor, .entityJsonSchema,
  .apiHttpApi, .apiClient, .apiOpenApi, .mcpToolkit, .mcpToolsList,
  .deployWrangler, .deployWorker, .siteRoutes]
#guard (Rule.all.map Rule.id).eraseDups.length = 11

#guard Rule.all.all (fun r => Rule.ofId? (Rule.id r) == some r)
#guard (Rule.ofId? "surface.entity.document") = some .entityDocument
#guard (Rule.ofId? "surface.site.routes") = some .siteRoutes
#guard (Rule.ofId? "lowering.schema.struct").isNone
#guard (Rule.ofId? "surface.entity").isNone
#guard (Rule.ofId? "").isNone

theorem all_nodup : Rule.all.Nodup := Rule.all_nodup
theorem mem_all : ∀ r : Rule, r ∈ Rule.all := Rule.mem_all
theorem ofId_id : ∀ r : Rule, Rule.ofId? (Rule.id r) = some r := Rule.ofId?_id

/-! ## At landing every rule is `emitted` and owes its receipt

The plan §5 says so in one sentence and this is that sentence as two
receipts. -/

#guard (Rule.all.map Rule.stance).all (· = .emitted)
#guard (Rule.all.map Rule.receipt).all (·.isNone)
#guard Rule.all.all (fun r => !(Rule.pins r).isEmpty)

theorem modeled_has_receipt : ∀ r : Rule, r.stance = .modeled → (Rule.receipt r).isSome :=
  Rule.modeled_has_receipt

-- `E4-SURFACE-CE-058`: the theorem is what makes the flip cost a receipt. At
-- landing the antecedent is empty, and the guard below is the statement that
-- it is empty, so a flip is a visible change of this battery and not a silent
-- strengthening of a claim.
#guard Rule.all.all (fun r => Rule.stance r != Stance.modeled)

/-! ## Pins name a real file each -/

#guard (Rule.pins .apiHttpApi).all (fun p => !p.file.isEmpty && !p.lines.isEmpty)
#guard (Rule.pins .deployWrangler).all (fun p => !p.file.isEmpty)
#guard (Rule.pins .siteRoutes).all (fun p => !p.file.isEmpty)

end Test.Surface.EmitContract
