# Surface emitter census and stance contract

Status: breaker packet, red, 2026-09-04 (wave 1b of
`docs/research/2026-09-04-surface-library-plan.md` §5)

Implementation (owed): `src/Effect4/Codegen/Emit.lean`

Battery: `Test/Surface/EmitContract.lean`

Counterexamples: `E4-SURFACE-CE-058`, `E4-SURFACE-CE-059`, `E4-SURFACE-CE-070`

Witnesses: `Test/Counterexamples/Surface/Emit.lean`

## Purpose

"We can emit anything but we cannot claim to model it", as a type. Every
emitter in `Effect4/Surface/` is one row of a closed census, carrying a
stance, its rc.112 or vendor pins, and the name of the harness check that
would justify the stronger stance. The theorem
`Rule.modeled_has_receipt` makes a stance flip without a receipt
unrepresentable, so no reviewer has to police the word "modeled" in prose.

## Frozen public declarations

All in namespace `Effect4.Surface`.

```lean
inductive Stance
  | modeled
  | emitted
deriving DecidableEq, Repr

structure Pin where
  file  : String
  lines : String
deriving DecidableEq, Repr

inductive Rule
  | entityDocument | entityConstructor | entityJsonSchema
  | apiHttpApi | apiClient | apiOpenApi
  | mcpToolkit | mcpToolsList
  | deployWrangler | deployWorker
  | siteRoutes
deriving DecidableEq, Repr

def Rule.id : Rule → String
def Rule.stance : Rule → Stance
def Rule.pins : Rule → List Pin
def Rule.receipt : Rule → Option String
def Rule.all : List Rule
def Rule.ofId? : String → Option Rule

theorem Rule.all_nodup : Rule.all.Nodup
theorem Rule.mem_all : ∀ r : Rule, r ∈ Rule.all
theorem Rule.ofId?_id : ∀ r : Rule, Rule.ofId? (Rule.id r) = some r
theorem Rule.modeled_has_receipt :
    ∀ r : Rule, r.stance = .modeled → r.receipt.isSome
```

`Stance` here is the emitter stance. The entity classification of plan §4.1 is
frozen as `EntityStance` in `surface-entity.contract.md`; the plan spells both
`Stance`, which is finding 1 of the wave-1b report.

## The eleven ids, frozen in `Rule.all` order

| # | constructor | `Rule.id` |
| --- | --- | --- |
| 1 | `entityDocument` | `surface.entity.document` |
| 2 | `entityConstructor` | `surface.entity.constructor` |
| 3 | `entityJsonSchema` | `surface.entity.jsonSchema` |
| 4 | `apiHttpApi` | `surface.api.httpApi` |
| 5 | `apiClient` | `surface.api.client` |
| 6 | `apiOpenApi` | `surface.api.openApi` |
| 7 | `mcpToolkit` | `surface.mcp.toolkit` |
| 8 | `mcpToolsList` | `surface.mcp.toolsList` |
| 9 | `deployWrangler` | `surface.deploy.wrangler` |
| 10 | `deployWorker` | `surface.deploy.worker` |
| 11 | `siteRoutes` | `surface.site.routes` |

The plan §5 gives the constructor list and one example id
(`"surface.entity.document"`). The other ten strings are frozen here; see
finding 4 of the wave-1b report.

## Observations

1. `Rule.all.map Rule.id`, compared against the literal eleven-element list
   above, in order. Both directions of the census are checked: the list is
   exactly `Rule.all`, and `Rule.mem_all` says every constructor is in it.
2. `(Rule.all.map Rule.stance).all (· = .emitted)`, which is `true` at
   landing.
3. `Rule.all.map (fun r => (Rule.receipt r).isSome)`, all `false` at landing.
4. The docstring tag census: the set of `-- surface: rule.<id>` tags in
   `Effect4/Surface/` equals `Rule.all.map Rule.id`, in both directions. This
   observation is a shell check, not a Lean one: it reuses the tokenizer of
   `git:c407ab7:scripts/check-lowering-coverage.sh` (`E4-SURFACE-CE-059`).

## Acceptance conditions

- `Rule.all` has all eleven constructors, exactly once each, in the table
  order. `Rule.all_nodup` and `Rule.mem_all` are `theorem`s.
- `Rule.ofId?` is a left inverse of `Rule.id` (`Rule.ofId?_id`), and answers
  `none` for an id that is not in the table.
- **At landing every rule is `Stance.emitted` and every `Rule.receipt` is
  `none`.** A rule becomes `modeled` only in the same change that lands its
  harness receipt and names it in `Rule.receipt`
  (`E4-SURFACE-CE-058`).
- `Rule.modeled_has_receipt` is a `theorem` proved by cases on `Rule`, not a
  `#guard`. It must remain provable after any future flip, which is what
  forces the receipt name to land in the same change.
- `Rule.refuses` is non-empty for every rule but `siteRoutes`, and every name
  in it is a shape the carrier can express. A refusal naming a shape the
  carrier cannot spell would be decoration.
- Every rule's `Rule.pins` is non-empty and names a real file: an rc.112
  `path:lines` for the six TypeScript emitters, the vendored wrangler schema
  digest for `deployWrangler`, and the wrangler schema plus
  `HttpApiBuilder.ts:63` for `deployWorker`. `siteRoutes` has no host pin and
  carries the plan section instead; it is the one rule that can never be
  flipped by a host receipt in this packet.

## What the v1 emitters refuse

Plan §13.1 makes `multipart`, `urlEncoded` and `stream` expressible so a
clause can talk about them, and plan §13.6 rule 8 forbids claiming anything
about bytes without a receipt. The two together mean the v1 emitters refuse
those shapes **by rule id**, and the refusal is a receipt, not an omission:

```lean
def Rule.refuses : Rule → List String   -- shapes this rule will not emit, by name
```

| rule | refuses |
| --- | --- |
| `apiHttpApi`, `apiClient`, `apiOpenApi` | `payload.multipart`, `payload.urlEncoded`, `response.stream`, `response.headers` |
| `entityDocument`, `entityConstructor`, `entityJsonSchema` | `schema.suspend`, `schema.declaration` |
| `mcpToolkit`, `mcpToolsList` | `schema.suspend` |
| `deployWorker` | `response.stream` |
| `siteRoutes` | none |

An emitter given a value that uses a refused shape answers `none`. It does
not emit a partial module, a `Decl.raw` escape hatch or a comment
(`E4-SURFACE-CE-070`). The endpoint itself stays well formed: the model
expresses more than the v1 emitters lower, and that gap is stated here rather
than hidden by narrowing the carrier.

## Assurance allocation

Graph edge `SURFACE-PG-EMIT`, the parent of every emitter leaf in this slice.

The census carrier itself closes with leaf receipts (census, nodup,
round trip through `ofId?`, axiom report). The edge that stays open is the
stance edge: eleven rules, zero receipts at landing, and the graph is not
closed until each rule either carries a receipt or is explicitly recorded as
permanently `emitted` with the reason.

This contract is the one place a coverage-shaped statement about this slice
may be written, and it is written as a table of eleven rows with their
stances, never as a count and never as a percentage.

## What this contract does not claim

It does not claim any rule's output is correct; a rule with `Stance.emitted`
carries no claim at all beyond "these bytes are a pure function of these
rows". It does not claim the census is complete with respect to some future
emitter set: completeness is enforced by the tag check of observation 4, which
is a gate, not a theorem. It does not claim a receipt, once landed, transfers
to a later rc.112 version: a pin change re-opens the row.
