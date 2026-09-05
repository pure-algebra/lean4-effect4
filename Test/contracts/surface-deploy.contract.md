# Surface deployment contract

Status: breaker packet, red, 2026-09-04 (wave 1b of
`docs/research/2026-09-04-surface-library-plan.md` §4.6)

Implementation (owed): `src/Effect4/Surface/Deploy.lean`

Battery: `Test/Surface/DeployContract.lean`

Counterexamples: `E4-SURFACE-CE-043` through `E4-SURFACE-CE-049`,
`E4-SURFACE-CE-067`

Shared: `Test/contracts/surface-facts.contract.md` owns the `Refusal`
alphabet.

Witnesses: `Test/Counterexamples/Surface/Deploy.lean`

Pins: `wrangler` 3.114.16 `config-schema.json` (vendored under
`vendor/wrangler-3.114.16/`, SHA-256 recorded there), rc.112
`unstable/httpapi/HttpApiBuilder.ts:63`

## Purpose

Deployment is the late binding of the plan's decision 1: one API lowers to
more than one host, and the host is chosen after the API is modeled. The
carrier holds a host, an entry point, a compatibility date, bindings, routes,
mounted APIs and the service names the bindings provide.

Two Boolean judgments, kept apart on purpose. `Deployment.wellFormed` reads
the deployment alone. `Deployment.satisfies` reads the deployment against the
APIs it mounts, and is the join between this surface and
`surface-api.contract.md`: every `requires` of every mounted endpoint is
covered by a `provides` entry. Merging the two would make a deployment's
well-formedness depend on an argument it does not carry.

## Frozen public declarations

All in namespace `Effect4.Surface`.

```lean
inductive Host
  | cloudflareWorker | cloudflarePages | node | static
deriving DecidableEq, Repr

inductive Binding
  | kv (name namespaceId : String)
  | d1 (name databaseName databaseId : String)
  | r2 (name bucket : String)
  | queue (name queue : String)
  | secret (name : String)
  | var (name value : String)
  | service (name worker : String)
  | durableObject (name className : String)
deriving DecidableEq, Repr

def Binding.name : Binding → String

structure Mount where
  api : String
  at_ : Path
deriving DecidableEq

structure Deployment where
  name              : String
  host              : Host
  annotations       : Effect4.Annotations := none
  main              : Option String := none
  compatibilityDate : String
  bindings          : List Binding := []
  routes            : List String := []
  serves            : List Mount := []
  provides          : List (String × String) := []
deriving DecidableEq

def Deployment.check (d : Deployment) : Except Refusal Unit
def Deployment.WellFormed (d : Deployment) : Prop := Deployment.check d = .ok ()

def Deployment.satisfies {refs} (d : Deployment) (apis : List (Api refs)) :
    Except Refusal Unit
def Deployment.Satisfies {refs} (d : Deployment) (apis : List (Api refs)) : Prop :=
  Deployment.satisfies d apis = .ok ()

def Deployment.Described (d : Deployment) : Prop
def Deployment.BindingNamesDistinct (d : Deployment) : Prop
def Deployment.EntryPointMatchesHost (d : Deployment) : Prop
def Deployment.ProvidesResolve (d : Deployment) : Prop

theorem Deployment.wellFormed_iff (d : Deployment) :
    Deployment.WellFormed d ↔
      (Deployment.Described d ∧ Deployment.BindingNamesDistinct d ∧
        Deployment.EntryPointMatchesHost d ∧ Deployment.ProvidesResolve d)

def Deployment.wranglerJson : Deployment → Option Effect4.Json
def Deployment.workerModule {refs} (d : Deployment) (apis : List (Api refs)) :
    Option TypeScript.Module

def workerNameLegal (name : String) : Bool
def bindingNameLegal (name : String) : Bool
def compatibilityDateLegal (date : String) : Bool
```

## Observations

1. `Deployment.check d : Except Refusal Unit`.
2. `Deployment.satisfies d apis : Except Refusal Unit` against the fixture
   `shopApi`; a failure names the service or the API it could not join.
3. `Deployment.wranglerJson d : Option Json`, compared against a literal
   `Json` term, so the wrangler key spellings (`kv_namespaces`,
   `d1_databases`, `r2_buckets`, `queues.producers`, `vars`, `services`,
   `durable_objects.bindings`, `compatibility_date`, `main`) are pinned in
   the battery and not only in the harness.
4. The three name predicates, over a hostile alphabet.

## Acceptance conditions

- `workerNameLegal` decides `^[a-z0-9-]{1,63}$` exactly. An uppercase letter,
  an underscore, an empty name and a 64-character name are all refused
  (`E4-SURFACE-CE-049`).
- `bindingNameLegal` decides `^[A-Za-z_][A-Za-z0-9_]*$` exactly. A leading
  digit, a hyphen and an empty name are refused (`E4-SURFACE-CE-044`).
- `compatibilityDateLegal` decides `YYYY-MM-DD` on digits and separators, and
  additionally refuses a month outside `01..12` and a day outside `01..31`.
  `"2026-9-01"`, `"2026-13-01"` and `"tomorrow"` are refused
  (`E4-SURFACE-CE-048`).
- `Deployment.check` clause order, first refusal wins:

  | # | clause | refusal | id |
  | --- | --- | --- | --- |
  | 1 | bag carries `identifier` | `identifierMissing "deployment" d.name` | `E4-SURFACE-CE-067` |
  | 2 | bag carries `description` | `descriptionMissing "deployment" d.name` | `E4-SURFACE-CE-067` |
  | 3 | `workerNameLegal d.name` | `workerNameIllegal d.name` | `E4-SURFACE-CE-049` |
  | 4 | every binding name legal | `bindingNameIllegal d.name b` | `E4-SURFACE-CE-044` |
  | 5 | binding names distinct | `bindingNameDuplicate d.name b` | `E4-SURFACE-CE-043` |
  | 6 | `compatibilityDateLegal` | `compatibilityDateIllegal d.name date` | `E4-SURFACE-CE-048` |
  | 7 | `cloudflareWorker`/`node` has `main` | `mainMissing d.name` | `E4-SURFACE-CE-045` |
  | 8 | `static` has no `main` | `mainForbidden d.name` | `E4-SURFACE-CE-045` |
  | 9 | every `provides` binding exists | `providedBindingAbsent d.name b` | `E4-SURFACE-CE-047` |

- `Deployment.satisfies d apis` is `.ok ()` exactly when every `Mount` in
  `d.serves` names an element of `apis` (`mountedApiAbsent d.name api`
  otherwise) and every name in that API's `Api.requirements` appears as a
  first component of `d.provides` (`requirementUnprovided d.name service`,
  `E4-SURFACE-CE-046`). A mount naming an API that is not in the list is a
  refusal, not a vacuous success.
- `wranglerJson` answers `none` for a deployment that is not well formed, and
  emits only keys the vendored 3.114.16 config schema declares.

## Assurance allocation

Graph edge `SURFACE-PG-DEPLOY` for `satisfies`; leaf receipts for the rest.

`Deployment.satisfies` is a cross-surface admission judgment and takes the
graph route, with obligations `admission-positive` (the fixture worker
satisfies `shopApi`), `admission-negative` (`E4-SURFACE-CE-046` and
`E4-SURFACE-CE-047`) and `bridges` (the `requires`/`provides` join to
`surface-api.contract.md`, which is the only place a service name crosses
surfaces).

`Host`, `Binding`, `Mount`, `Deployment` and the three name predicates are
passive alphabets and records on leaf receipts.

`surface.deploy.wrangler` and `surface.deploy.worker` land `Stance.emitted`.
The receipt that flips `deployWrangler` is validation of the emitted JSON
against the vendored config schema at the pin; the harness names which of the
two validators (a node validator over the vendored schema, or a `wrangler`
dry-run) actually ran.

## What this contract does not claim

It does not claim a deployment deploys, that a binding resolves at run time,
or that the emitted worker serves anything. It does not model Cloudflare
account ids, environments, `[env.*]` sections, migrations, observability,
placement, or limits. `provides` is a name-level join only: nothing here
checks that the binding's *type* can implement the service the endpoint
requires, and that gap is deliberate until the runtime lane's service rows
join this surface.
