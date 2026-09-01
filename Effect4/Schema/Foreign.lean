/-!
# Schema.Foreign.lean

Owner: Fail-closed host reviver boundary.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

The boundary where a stable registered identity crosses to host code. The
disposition is `foreignBoundary`: a registered identity crosses, an arbitrary
closure never does. A missing reviver is a refusal, not a default — hence
*fail-closed*.

## Assigned future obligations

This empty stub discharges none of the obligations below. Because it exports
no declaration, it has no assurance route yet. The assigned main role crosses
the proof-graph threshold, so its graph must be allocated and frozen before
the first public owner declaration. A separately contracted passive helper
may still qualify for a leaf receipt.

- `SC-HOST-02` reviver bijection and negative tests

and feeds `SC-HOST-01` generated TypeScript registry, `SC-HOST-03` direct
rc.112 typecheck plus diagnostic gate, `SC-HOST-04` runtime differential
vectors, and `SC-HOST-05` source/profile drift gate.

## Retains

- `E4-SCHEMA-CE-008` missing declaration reviver
- `E4-SCHEMA-CE-010` local symbol cannot enter portable wire data
- `E4-SCHEMA-CE-011` non-JSON annotation pruning

`E4-SCHEMA-CE-010` has a necessary condition enforced by the current alphabet:
`PropertyKeyKind` has no `localSymbol` constructor (`E4-SCHEMA-CE-022`). Its
leaf receipt and parent edge remain cutover-open, and the local exclusion would
not discharge `-010` anyway because that attack reaches the payload and
lowering layers.

## Gated by

The registry and the payload carrier. The exact rc.112 bytes are host-local at
`library/effects/node_modules/effect/src/SchemaRepresentation.ts` in the
Foldlab checkout and already support the lexical census gate; they are not
vendored into Effect4. The host reviver, runtime, and language-service gates
remain open, and lexical tag agreement does not close them. See
`SC-REP-CENSUS-PIN` in `docs/SCHEMA-CUTOVER.md`.

## Host evidence at the pin

Read off rc.112 source; not executed here, and host-local for the reason given
just above. Reading source establishes what the host *code says*; it is a
finite reading, not a runtime observation, and it closes no `SC-HOST-*` row.

On the missing-reviver case the fail-closed disposition recorded above
**agrees with the host**: `internal/schema/fromRepresentation.ts:95` throws
`Missing reviver for <id>` instead of substituting a default, and
`SchemaRepresentation.ts:1250` states that none are installed implicitly. So
`E4-SCHEMA-CE-008` names a refusal rc.112 also performs. The row stays open. A
host throw is evidence about rc.112, not an Effect4 refusal classification,
and this repository must still decide whether that refusal is a typed failure,
a defect, or a domain refusal — a decision `PLAN.md` requires be made
explicitly rather than inherited.

Two places where the host boundary is **wider** than this module's
disposition. The boundary design has to survive both rather than assume them
away, and neither may be cited as support for fail-closed:

- **A reviver returns a host object and may raise.** `revive` produces a
  `Schema.Top` (`SchemaRepresentation.ts:509`), and the host contract is that
  reviver "results are used directly, and exceptions raised by a reviver pass
  through unchanged" (`:1212`). rc.112 therefore does not confine reviver
  failure to a value; an arbitrary host exception escapes `fromRepresentation`.
  This is the concrete shape of the `foreignBoundary` disposition: what crosses
  is a registered identity, but what the *host* runs behind that identity is
  unconstrained code with an unconstrained failure mode.
- **For declarations and leaf filters, `representation` is optional only in
  the live interface.** The persisted `DeclarationSchema` and `FilterSchema` require it
  (`SchemaRepresentation.ts:956-960,977-983`), so `fromJson` rejects an
  omission before revival. A hand-constructed live declaration or filter can
  still omit it, and revival then throws `Missing representation annotation`
  (`internal/schema/fromRepresentation.ts:126,142`). That is a layer split
  between live construction, persisted admission, and revival; this module
  must not flatten the three.

## A second door for `E4-SCHEMA-CE-010`

`E4-SCHEMA-CE-022` closes one route by absence: `PropertyKeyKind` has no
`localSymbol` constructor, so a local symbol has no spelling as a *persisted
property key*. That exclusion is real and it is not sufficient, because the
persisted representation is not the only place a key-like value travels.

The rc.112 issue alphabet carries a `Pointer.path` (class `SchemaIssue.ts:316`,
field `:321`,
recursion at `:325`) which admits local symbols, and `Base.input` (`:157`) is
retained **by reference** rather than copied (`SchemaAST.ts:529`) and is
reachable on nine of the eleven issue variants. rc.112 itself writes a live
host `symbol` into `input` (`SchemaAST.ts:4098-4102`). So a local symbol that
the representation alphabet can never spell can still be reached through a
diagnostic produced while decoding that representation.

This does not reopen `E4-SCHEMA-CE-022`, which is about the key alphabet and
remains discharged by absence. It does mean `E4-SCHEMA-CE-010` may not be
treated as approaching closure once the key alphabet and the payload carrier
are settled: whichever module ends up owning `SC-ISSUE-01` inherits a second
door, and that ownership is currently unassigned. See
`docs/SCHEMA-ISSUE-SURVEY.md` for the per-field host-boundary account.

Attribution: read off rc.112 source and finite host probes recorded in that
survey; one build on one host, and not reproducible from this checkout alone.
-/
