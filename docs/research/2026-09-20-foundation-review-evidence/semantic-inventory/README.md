# Pinned Effect semantic inventory evidence

This is a read-only source inventory for a design review. It is not a production
generator, a CI check, an implementation backlog approval, or semantic coverage.

`original-counts.json` preserves the exact first interactive AST-probe result.
That probe retained counts, not individual names or paths. `inventory.cjs` uses
the same exported-name walk and the exact proposed 13-family root partition to
materialize the missing per-file evidence once. Its output is compared with the
preserved counts; it does not replace the earlier measurement with a new claim.

Reproduce from a checkout with the pinned vendor sources and the existing local
TypeScript dependency:

```sh
node docs/research/2026-09-20-foundation-review-evidence/semantic-inventory/inventory.cjs "$PWD" /tmp/effect4-semantic-inventory
```

Outputs:

- `files.json`: every one of the 452 source paths, grouping, SHA-256, direct export
  names, unresolved export-star locations, and syntax diagnostics.
- `root-family-partition.json`: the proposed 13 semantic ownership families and
  the complete 137-module root partition.
- `summary.json`: counts, pin, parser, completeness checks, 18 unstable groups,
  root barrel namespaces, four testing modules plus barrel, and census inputs.
- `source-sha256.tsv`: the exact source bytes read.
- `verification.json`: comparison with the preserved interactive counts and
  consistency checks over the saved artifacts.

The inventory counts types and aliases alongside values, without resolving
symbol identity. Export-star targets, nested namespace members, type members,
overload branches, module initialization and dynamic semantics remain to be
reviewed. Parser success proves syntax parsing only. See `summary.json` for all
limitations. No Lean, runtime-census report, host behavior test, or production generator ran
to produce this inventory.
