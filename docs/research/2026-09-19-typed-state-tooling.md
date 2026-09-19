# Typed-state tooling: checked declarations, one proof graph

Base: `23e668b0cb6839d73c5679d4676d65fbb0b00b4f`.
Branch: `codex/typed-state-tooling`. The owner authorized the tooling phases on
2026-09-19. Runtime and language changes remain separate consumers.

## Acceptance

1. A scanner cannot return a successful partial inventory. Type instances are
   visited separately. Whole-value use is a dependency. A copied field is only
   unchanged relative to an explicitly identified source record.
2. Skeleton declarations elaborate in Lean from structured input. No generated
   source text or TSV is an authority. Unsupported shapes fail with a location.
3. Clause/transition obligations have stable identities, propositions and checked
   theorem evidence. Search success is not evidence until Lean checks the proof.
   Missing evidence, deliberate open work and unsupported analysis are distinct.
4. Frame proofs are checked by the kernel. Remaining obligations have explicit
   placeholders and a decreasing ceiling. Missing/stale entries fail, even when
   the count happens to be unchanged.
5. Aesop uses the existing named TypedState bank, with positive and negative
   controls. Laws and tooling stay outside the runtime/LCNF dependency graph.

## Sequence and cuts

Land scanner repairs and their adversarial controls first. Then replace the
source writer with direct declaration generation. Add the reusable proof graph
and ledger as its first consumer, retaining exact proposition and axiom checks.
Delete retired writer/driver wiring once callers have moved. Do not create a
second theorem-reference validator: share the existing Conform validation seam
without making Effect4 depend on Conform. No new persistent TSV.

The first consumer after tooling is per-cell typing and generic Ref/Deferred
operations, including term-based atomic update. Language work must retain the
existing L2/L4/L6/L7 dependency order; this tooling does not settle HandlesFit or
promise-world ownership. LCNF and future vendored modules consume the runtime
root, never the proof-search graph.

## Independent controls and probes

The pre-change audit reproduced five false-success cases: zero scan fuel,
pattern-match reads, cross-record field copies, two instances of the same
container, and an unsupported recursive carrier. It also found that an opaque
whole-store predicate yields an empty projection census. Each becomes a focused
regression control. A two-field clause must retain both dependencies. Proof-graph
controls include wrong proposition, non-theorem, extra axioms, stale placeholder,
missing placeholder and a ceiling violation. A search result must retain its
checked term, not merely a count or name.

Design sources: the main checkout's `2026-09-18-position-census-design.md` §3b,
`2026-09-18-metaprogramming-review.md`, `2026-09-18-research-proof-engineering.md`
§§3.2–3.3, and `2026-09-18-synthesis-tooling-first.md`. Their earlier text/TSV
proposals are superseded by in-environment generation.

Focused module builds and executable controls are required per commit. This is
not a request for a whole-repository or host sweep. Record actual commands,
results, axiom output and remaining boundaries in the final receipt.
