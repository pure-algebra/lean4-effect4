# Checked service-session landing

Land the checked positional session constructor only, from base `33e55d96e`.
The engine, loader, driver, and journal-format changes remain outside this slice.
The owner authorizes this slice through the reviewed host/runtime discussion.

## Contract

`Api.Built.session : Built → String → Except SessionRefusal Built` selects one formed service.
It derives its request and reply rows, constructs an ordinary `Eff` main program, and applies existing program admission.
The result has no remaining service requirements.
It retains the source declarations, bodies, module layers, named types, and service declarations.
It appends rows, so existing external positions keep their meanings.
It invokes definitions by position, including when their names repeat.

The main program provides the initializer's required keys with unit values and initializes once.
It then receives optional tagged requests, invokes the selected method, sends its exit, and repeats.
An absent request ends the program.
The existing checker refuses non-unit provisions, unsupplied program parameters, row collisions, and unsupported incoming handle columns.
Outgoing handle columns and arbitrary method strings receive no additional restriction.
Any remaining requirements produce a separate refusal at the generated main program.

Reuse the existing service-formation, authoring, and program-admission refusals without erasing their locations.
Unknown service selection names the missing service.
Do not add a profile record, method representation, second checker, or host guard.

## Mathematical basis and limits

`SigApp` supplies operation request and answer types.
The constructor composes existing program syntax constructors and the checker.
It is a checked protocol adaptation, not a categorical duality theorem.
The selected sequential protocol and its tags are explicit design choices.

Plotkin and Pretnar's [Handling Algebraic Effects](https://homepages.inf.ed.ac.uk/gdp/publications/handling-algebraic-effects.pdf)
connect handlers with models and their induced homomorphisms.
Plotkin and Power's [Tensors of Comodels and Models for Operational Semantics](https://homepages.inf.ed.ac.uk/gdp/publications/Tensors_Comodels_Models.pdf)
separates computations from the stateful interpretations of operations.
These sources support the separation. They do not establish this constructor's program admission or runtime behaviour.
`Eff` remains this project's scoped syntax. No new claim equates all its constructors with an ordinary unquotiented free monad.

## Proof placement before proof work

| Claim | Concept and role | Exact reach | Exclusions | Consumer and requirement |
| --- | --- | --- | --- | --- |
| `service-session-checked`, `Built.session_ok_iff` | `host-session-protocol`, compatibility | Success exactly when candidate construction and program admission succeed and result requirements are empty | No progress or general behaviour theorem | Public constructor and callers, R6/R13 |
| `service-session-retains`, `Built.session_retains` | `host-session-protocol`, compatibility | Successful construction keeps original declarations, bodies, module layers, signature declarations, and row prefix | Does not preserve the replaced main program's behaviour | Positional invocation and existing typing checks, R6/R13 |

Helpers name one of these claims and its consuming theorem.
The laws live under `Effect4.Laws.Api.Session` and the registry points to them before proof work.
No claim of arbitrary-service acceptance is made.

## Finishing criteria

1. Compile the core API and its direct importers.
2. Prove the two placed obligations and audit the landed modules.
3. Generate the new refusal codec and test its actual carriers.
4. Exercise ordinary and cached to-do sessions, duplicate names, collisions, missing services, and rejected profiles.
5. Compare a printed session's actual Effect execution with the Lean run through the existing TypeScript tooling.
6. Run the behaviour gates the change reaches and the touched batteries.
7. Update the authority records, retain exact evidence, and commit explicit paths.

The controls distinguish finite evaluation, Lean proof, and outside execution evidence.
