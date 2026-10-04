# Exact tuple target syntax

Base: `064236a4` on the integration branch.
The record seat continues on its own branch, `codex/tuple-codegen`, from this base.
The owner authorizes robust, expressive implementation through the data-language plan.

## Contract

Use `tupleAt<"2">("2")(target)` for static projection.
The two literal strings must match the canonical decimal spelling of the stored natural index.
The structural printer and reader retain every natural index, including values above JavaScript's exact numeric range.
The helper requires a readonly tuple containing the requested key.
It retains `never` for an impossible receiver.
It refuses arrays, absent positions and non-tuples at target typing.
The TypeScript reifier refuses indices it cannot store exactly in its existing numeric representation.
Construction uses the existing variadic `tuple` native atom with its const-generic result.
Do not add a target-number restriction to the Lean structural round-trip theorem.

The pinned tsgo probe at `/private/tmp/effect4-tuple-index-probe.ts` checks the proposed helper shape.
It checks ordinary positions, impossible receivers and oversized literal indices.
This finite probe does not prove target execution or the Lean reconstruction laws.

## Placement and consumers

Concept: Exact Codecs & Data Plane Embeddings in `docs/core/semantics.md`.
Claims: `printed-modules` and `collection-term-print-read`; requirements R2 and R3.
Retraction retains the existing scope premise on raw terms.
Exactness assumes only successful structural reading.
Decimal helpers serve the tuple reader and existing service-key or variable readers.
Reuse existing byte-based natural parsing and proofs, extracting a shared helper when necessary.
Do not give tuple indices the nominal identity of logical milliseconds.
No theorem claims host execution, general target-language admission or liveness.

```mermaid
flowchart LR
  D[Canonical natural text] --> T[Tuple expression reader]
  T --> R[Term reconstruction laws]
  R --> M[Checked module reconstruction]
  H[Target tuple helper] --> F[Finite tsgo and execution controls]
```

## Ownership

The seat owns new `Codegen/Tuple.lean` and `Laws/Codegen/Tuple.lean` modules.
It owns tuple cases in `Codegen/PrintLeaf.lean`, `Codegen/Read.lean`, `Laws/Codegen/ReadLeaf.lean` and `Laws/Codegen/PrintReadable.lean`.
It may extract decimal helpers into `Data/NatDecimal.lean` with their directly required laws and consumers.
It owns tuple cases in `Codegen/Blame.lean` only if needed.
It owns target helper source, reader cases and focused fixtures under `harness/truth` and `ts/eff`.
Existing map and record behavior must remain intact.
The coordinator owns generators, generated outputs, root imports, manifests, decisions and policy census.
Request generated PreludeAtoms and TsGen companions after a checked source checkpoint.
Do not edit Schema or tuple typing and handle proof files.

## Finishing criteria

Build changed source modules and direct consumers using the shared Lean lane.
Keep theorem statements and the axiom ceiling unchanged.
Check empty, singleton, two-item and larger tuples, literals, unions and impossible branches.
Refuse malformed markers, noncanonical decimals, missing positions and number-rounding cases.
Use only pinned tsgo 7 and existing Bun dependencies for target checks.
Record exact commands, results, trust queries and remaining host assumptions in a receipt.
Commit explicit paths after focused checks; do not push or run a full sweep.
