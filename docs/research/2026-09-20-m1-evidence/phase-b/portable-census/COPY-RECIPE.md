Reviewed promotion recipe (not executed)

```sh
cd /Users/pooks/Dev/lean4-effect4
mkdir -p docs/research/2026-09-20-m1-evidence/portable-census
cp -p /tmp/m1-tools/portable-census-evidence/* docs/research/2026-09-20-m1-evidence/portable-census/
cd docs/research/2026-09-20-m1-evidence/portable-census
shasum -a 256 -c SHA256SUMS
```

Review receipt.md, summary.json and module-baseline.tsv before copying. The archive preserves every raw evidence file losslessly; archive-manifest.json maps each original path to the retained member and hash. Stage explicit promoted paths only. package.py writes to its named scratch output directory; it is retained for review, not intended to rerun in the promoted directory.
