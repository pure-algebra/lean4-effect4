import Effect4.Codegen.Emit

/-!
# Codegen.SiteRoutes — the route table of a site

Rule `surface.site.routes` (`Rule.siteRoutes`), the `routes.generated.json` of the Surface
plan's §13.4. The table itself is `Surface.routesJson` (`Surface/Site.lean`): total on every
site, because every field of a page renders and a page with no semantics is refused by
`Site.check` before the table is asked for. This module is the checked entry: the carrier's
own refusal first, then the table, always `.ok`. It refuses nothing of its own, and
`Rule.refuses .siteRoutes` is empty.

| | |
| --- | --- |
| Carrier | none of its own: `Site` is `Surface/Site.lean`'s, `Json` the estate's |
| Operations | `routes`; the `Emit .siteRoutes` instance |
| Laws | none claimed |
| Structure | `Site.check`, then a total function |
| Payoff | the route table is reachable by its rule, and only for a site that checks |
| Anti-vacuity | the `DocsWeb` fixture emits the table `routesJson` renders; a site whose name is not a binding answers its own refusal |
-/

set_option autoImplicit false

namespace Effect4.Codegen.SiteRoutes

open Effect4 Effect4.Surface Effect4.Codegen

/-- The rule this module implements. -/
def rule : Rule := .siteRoutes

/-- The route table of a checked site. -/
def routes (site : Site) : Except Refusal Json := do
  let _ ← Site.check site
  pure (routesJson site)

instance : Emit .siteRoutes := ⟨routes⟩

/-! ## Anti-vacuity: the docs app site -/

#guard routes docsSite == .ok (routesJson docsSite)
#guard (emit .siteRoutes docsSite).toOption.isSome
-- the carrier's refusal, unwrapped
#guard (refusal? (routes { docsSite with name := "class" })).isSome
#guard refusal? (routes { docsSite with name := "class" }) ==
  refusal? (Site.check { docsSite with name := "class" })
#guard Rule.refuses .siteRoutes == []

end Effect4.Codegen.SiteRoutes
