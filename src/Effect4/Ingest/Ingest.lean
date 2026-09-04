import Effect4.Codegen.Emit

/-!
# Ingest.Ingest — the reader, keyed by the rule it inverts

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.4.

```lean
class Ingest (r : Rule) where
  ingest : Domain → r.target.Syntax → Except Refusal r.Input
```

A reader is an emitter read backwards: the rule's artefact comes in, the rule's input comes
out, under the domain whose references the input is checked against, and every refusal is a
constructor of the one alphabet (`Surface.Refusal`'s `jsonSchema*`, `mcp*`, `wrangler*`
groups). Wrapping an existing resource, the Surface plan's §4.8, is therefore one call per
rule: `ingest .deployWrangler dom json`.

The law a reader carries is stated once, `RoundTrip`, and is a round trip **up to a named
quotient**: what the artefact does not carry (a wrangler file has no place for a secret or
a description; a `tools/list` has no `success` schema) comes back as the quotient of what
went in, never silently as something else. Each instance names its quotient beside it; the
general theorems stay owed and the fixtures pin the round trips as `#guard`s, as before.
-/

set_option autoImplicit false

namespace Effect4.Ingest

open Effect4 Effect4.Surface Effect4.Codegen

/-- The reader of a rule's artefact. The method is `read`, not `ingest`, because inside
this namespace `Ingest.ingest` would name the function below. -/
class Ingest (r : Rule) where
  /-- The carrier the artefact describes, under a domain, or the first refusal by name. -/
  read : Domain → r.target.Syntax → Except Refusal r.Input

/-- The one call. -/
def ingest (r : Rule) [Ingest r] (dom : Domain) (artefact : r.target.Syntax) :
    Except Refusal r.Input :=
  Ingest.read dom artefact

/-- The round-trip law shape: reading back a checked carrier's artefact answers its quotient.
Stated per rule with the quotient named; proved by `#guard` on the fixtures until the
general theorem lands. -/
def RoundTrip (r : Rule) [Emit r] [Ingest r] (quotient : r.Input → r.Input) : Prop :=
  ∀ (dom : Domain) (x : r.Input) (out : r.target.Syntax),
    Emit.emit x = .ok out → Ingest.read dom out = .ok (quotient x)

end Effect4.Ingest
