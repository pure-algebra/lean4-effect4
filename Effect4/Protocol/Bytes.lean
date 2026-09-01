/-!
# Protocol.Bytes.lean

Owner: Canonical portable protocol bytes.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

The byte face of a portable document: the layer beneath any tag vocabulary,
where a document is still text and has not yet been read as a representation.

## Assigned future obligations

The proof graph in `docs/SCHEMA-CUTOVER.md`, under `SCHEMA-PG-WIRE`,
names five wire obligations —

- `SC-WIRE-01` duplicate-preserving raw JSON
- `SC-WIRE-02` decoder soundness
- `SC-WIRE-03` encoder/decoder round trip
- `SC-WIRE-04` canonicalization idempotence
- `SC-WIRE-05` canonical encoding injectivity

— are assigned here by the graph in `docs/SCHEMA-CUTOVER.md`. This empty stub
discharges none of them and receives no graph merely for containing the
assignment. `SCHEMA-PG-WIRE` must be opened before the first semantic byte or
codec declaration enters this module.

`SC-WIRE-01` is necessarily below Schema vocabulary: duplicate keys have to
be rejected or preserved before any `_tag` is read. The dependency direction
is an architecture ruling in `docs/ARCHITECTURE.md`, not something inferred
from the order in which the root aggregator happens to import modules.

## Host evidence at the pin

Executed probes, not source reading. Captures and a runner are in
`test/fixtures/schema-representation/`; the runner is digest-gated and refuses
off-pin bytes. Finite probes on one host, reported as finite probes; they
discharge nothing and are not reproducible from this checkout alone.

Two observations give these obligations their shape, and both are facts about
the JSON layer rather than about Effect:

- **A duplicate references-table key collapses silently, last-wins, inside
  `JSON.parse`.** Effect never sees the first binding. This is the executed
  reason `SC-WIRE-01` needs a duplicate-preserving door below the parser, and
  it is the same door `E4-SCHEMA-CE-012` attacks.
- **`encode (decode bytes) = bytes` is false on authored wire text.** A
  references table whose names are integer-like comes back reordered, because
  JavaScript objects order integer-like keys numerically ahead of insertion
  order — and again the reorder happens inside `JSON.parse`, before Effect is
  called. So `SC-WIRE-03` may not be stated as byte identity over arbitrary
  accepted bytes. It must either restrict to canonical bytes or quotient by
  the reordering, and `SC-WIRE-04` is what would justify the quotient.

Neither observation is an Effect4 refusal. Per `E4-SCHEMA-CE-025` the
directional rule binds here too: these are host acceptances, and an Effect4
byte layer that refuses them is stricter than rc.112, not in agreement with it.

## Gated by

The payload carrier, for `SC-WIRE-02` onward, since a decoder is sound only
with respect to a carrier that exists. `SC-WIRE-01` is not gated on it: the
duplicate-key door is statable over raw JSON alone and is the one edge here
that could be opened first.
-/
