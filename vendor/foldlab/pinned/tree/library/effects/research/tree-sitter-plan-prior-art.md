# The lean4-tree-sitter plan as prior art for schema bundles

Status: project research input, 2026-08-26

Claim posture: bounded design comparison only. This note adopts no code,
amends no ratified rule on its own authority, and admits no tool. The
`predictable-machines/lean4-tree-sitter` repository is separately listed as
pending admission in [TOOLS.md](../../../docs/lab-core/TOOLS.md) as a Stage 1
extractor instrument; that instrument role and this design-inspiration role
are distinct and neither implies the other.

## Source identity

| Field | Value |
| --- | --- |
| Document | `docs/tree-sitter-implementation-plan.md` |
| Repository | [`predictable-machines/lean4-tree-sitter`](https://github.com/predictable-machines/lean4-tree-sitter) |
| Revision at fetch | `main` HEAD `3a57f55e1401484251cfe80e26583d9ed94c82c8` (ls-remote, 2026-08-26) |
| Fetched bytes | `53213` |
| SHA-256 | `f108a91d0ed8c5ff9ea0cbe0689a27ce5485303faa2118db769bddc866979e6b` |

The fetch was of the mutable `main` raw URL with the HEAD commit recorded at
the same moment; no clone was made and no Source Lock entry is created.
Pattern-level design input only. If a claim surface ever cites this document,
it enters the lock through the ordinary resolution procedure first.

## The load-bearing pattern

The document's `GrammarSpec` typeclass carries a proof obligation as a
*field*: every instance must discharge `decl_nodes_total` at instantiation,
so an unmapped declaration node is a compile error rather than a review
finding. Transferred to the ratified conformance workflow, this realizes the
schema bundle as a Lean structure whose fields are the template's holes,
whose laws are proof fields, and whose anti-vacuity kit is also fields — an
obligation instance is a term, and a term without its kit does not elaborate.

Two ratified rules are strengthened by this realization, recorded in the
workflow document's ratification record:

1. **Kit enforcement upgrades from convention to types** (refines WGR-7):
   proved-without-kit becomes unrepresentable for Lean-side artifacts; the
   gate grep survives only for artifacts outside the structures.
2. **The plain-meaning source upgrades from docstring to field** (refines the
   plain-meaning rule): `sentence` and `represents` are `String` fields,
   mechanically extractable — the ledger emitter is an `#eval` projection
   over typed instances, not a comment parser. Docstrings carry the ratified
   *templates*; fields carry the *instances*.

## Secondary patterns

- **Subset inductives with totality over the declared list**: reify only the
  node kinds the contract observes (their ~10 of 200+), prove totality of the
  mappings over the declared subset, and let exhaustive `match` make
  omissions compile errors. Template for the `Decision` carrier and the
  operation-signature family.
- **Cross-instance consistency as `rfl`-cheap theorems**: their
  cross-language agreement lemmas map to cross-family coherence lemmas here.
- **Ledger rows can carry declaration locations**: their source-map concern,
  reduced to what this workflow needs — the emitter already knows names, so
  file:line beside them turns the one-grep audit path into zero-grep.

## Does not transfer

- The thin-proof-layer split — their totality proofs sit on a pure mapping
  while the tree walker is `partial def` in `IO`. Legitimate for their goals;
  the exact temptation this workflow's model core must refuse (I-002:
  total, structural).
- The C FFI, vendoring, and grammar machinery — irrelevant to this library.
- Their registry-JSON-plus-vendor-script is a weaker cousin of the Source
  Lock discipline already in force; nothing to adopt.
- Hand-maintained session checklists — superseded by the generated briefing.
