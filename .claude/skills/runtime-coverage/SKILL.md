---
name: runtime-coverage
description: Report, extend, or re-pin the Effect v4 runtime coverage metric of this repo in its one sanctioned format. Use when asked how much of the Effect runtime is covered, when adding a Lean theorem as a witness for a census row, when adding or re-pinning a behaviour row after an Effect upstream change, or when a coverage number is about to appear in a handoff, plan, or pull request.
---

# Runtime coverage

Authority: `docs/RUNTIME-COVERAGE.md`. This skill is the procedure; that file
is the definition. Numbers come from the gate, never from memory.

## Quick start

```bash
scripts/report-effect-runtime-coverage.sh      # the only report format
scripts/check-effect-runtime-census.sh         # the gate; must PASS before any claim
```

Paste the report block verbatim with its commit line. Do not compute
percentages, do not round, do not call a row covered unless it is `green`.

## Workflow: answer "how much is covered"

1. Run the report script; if it fails, say the module does not build and stop.
2. Quote the block. Headline pair is owned-with-green over the denominator.
3. For "what would it take", read the row families in
   `docs/RUNTIME-COVERAGE.md` under "Path to full coverage" and take exact
   counts from `generated/effect-runtime-census.tsv`, never from prose.

## Workflow: add a witness

Only `Test/Audit/RuntimeCoverage.lean` changes.

- [ ] The theorem exists in `src/Effect4/`, is a `theorem`, and `#print axioms`
      shows only `propext` and/or `Quot.sound`.
- [ ] Add `w \`Name "receipt"` to the row's `witnesses`.
- [ ] Add `#check (@Name : …)` in `StatementSnapshot`, transcribed from
      `#check @Name` output, and append `Name` to `snapshotWitnesses` in the
      same order.
- [ ] Set the row's coverage: `green` only if every clause of the census
      summary line has a theorem; otherwise `partial` and note what is missing.
- [ ] `expectedRowTotal` and `expectedDenominator` still true.
- [ ] `lake build Test.Audit.RuntimeCoverage` then the gate.

## Workflow: add or re-pin a census row

Only `scripts/generate-effect-runtime-census.sh` and the Lean row list change.

- [ ] Row line `kind|id|file|anchor|offset-start|offset-end|sha|summary`;
      the anchor occurs exactly once in the vendored file.
- [ ] Compute the span digest with `sed -n 'a,bp' file | shasum -a 256`.
- [ ] Add the Lean row: same id and kind, a manifest disposition, `absent`,
      no witness. Update per-kind counts and totals in both places.
- [ ] `scripts/generate-effect-runtime-census.sh > generated/effect-runtime-census.tsv`
- [ ] Gate passes. An upstream re-pin moves the whole vendored pin, its
      README digests, and every span digest together, in one commit.

## Do not

- Add a witness that is a `def`, a finite probe, or a model-integrity lemma.
- Edit `generated/effect-runtime-census.tsv` by hand.
- Cite the frozen surface census in the retired FiberAssurance battery:
  it, its two scripts and its projection were retired on
  2026-09-04 with the machines they counted, so a declaration under
  `src/Effect4/Machine/` now moves only the coverage join. Freeze a surface by
  its `#check` ascription snapshot in the join instead.
- Describe coverage as compatibility or equivalence with Effect.
