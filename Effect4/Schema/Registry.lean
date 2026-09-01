/-!
# Schema.Registry.lean

Owner: Stable schema declarations and registered foreign meanings.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

The open first-order declaration and check registry. Declarations and checks
carry open stable identifiers; closedness is *evidence* from a checked
registry or target profile, not a new constructor family.

This is why `Declaration` and the check nodes need no closed-world assumption
in `Effect4/Schema/Representation.lean`: the alphabet is closed, the registry
is open.

## Assigned future obligations

This empty stub discharges none of the obligations below. Because it exports
no declaration, it has no assurance route yet. The assigned main role crosses
the proof-graph threshold, so its graph must be allocated and frozen before
the first public owner declaration. A separately contracted passive helper
may still qualify for a leaf receipt.

- `SC-REG-01` first-order declaration/check registry
- `SC-REG-02` uniqueness, arity, payload admission
- `SC-REG-03` denotation lookup agreement

`SC-REG-01` and `SC-REG-02` are also preconditions of the whole `SC-DEN-*`
family, so this module gates the denotation.

## Retains

- `E4-SCHEMA-CE-009` duplicate reviver identity

## Gated by

The payload carrier, since a registry row admits a payload.

## Host evidence at the pin

The reviver-resolution file cited throughout this section is
`internal/schema/fromRepresentation.ts`, SHA-256
`0b95c360800d3c1dfe3e6c5683f79265fa7217494c8ce9cedb5c6dcbf936d82e`. It is
cited here and in `Effect4/Schema/Foreign.lean` but carried no digest in the
repository's pin block, so it is recorded at first use per the convention that
every cited host file gets one.

Read off rc.112 source; not executed here. The pinned bytes are host-local at
`library/effects/node_modules/effect/src/` in the Foldlab checkout and are not
vendored into this repository, so these citations are reproducible only on a
host carrying that package. Reading source establishes what the host *code
says*. It is not a runtime observation and it closes no `SC-REG-*` obligation.

The reviver record is three fields (`SchemaRepresentation.ts:502-510`): a
`string` `id`, a `payloadSchema` of type `Schema.Decoder<P>`, and a `revive`
function returning a host `Schema.Top` (`:509`). `FilterReviver` (`:518`) and
`FilterGroupReviver` (`:534`) repeat that three-field shape and differ only in
what `revive` receives and returns. `Reviver` is their union (`:558`) and
`AnyReviver` erases the payload parameter (`:566`).

The registry is **open in the host's own shape**, which is why the ownership
note above needs no closed-world assumption: revivers are supplied per call as
`fromRepresentation(document, { revivers })` (`:1236`, `:1260`), never as a
global table, and the host installs none implicitly (`:1212`, `:1250`).

Three facts bear directly on `SC-REG-02`:

- **Identifier uniqueness is enforced, eagerly and by position.**
  `internal/schema/fromRepresentation.ts:42` throws `Duplicate reviver for
  <id>` while building the reviver map, at path `["revivers", index, "id"]`.
  The check sits in map construction (`:34-50`), so it fires on a duplicate
  that no document ever mentions. This is a host witness for
  `E4-SCHEMA-CE-009`, not a proof about any Effect4 declaration.
- **Payload admission is decided by the payload schema, not by the row.**
  Each reviver's `payloadSchema` is rewrapped as `Schema.toCodecJson(...)` on
  entry to the map (`:46`), and a payload is admitted by
  `Schema.decodeUnknownResult` (`:105`), failing with `Invalid representation
  payload for <id>` (`:107`). The payload discipline is therefore carried by a
  schema, and a payload's wire form is JSON. The host reviver has no arity
  field; if Effect4 checks type-parameter arity, that is additional registry
  data and remains an open part of `SC-REG-02`.
- **Lookup is by `id` against that local map only.** `resolveReviver`
  (`:89-97`) reads `reviverMap.get(representation.id)` and throws `Missing
  reviver for <id>` (`:95`) on absence.

`SC-REG-03` denotation lookup agreement is untouched by all of the above.
These citations fix what the host does when a lookup fails; they say nothing
about agreement between a lookup and a denotation.
-/
