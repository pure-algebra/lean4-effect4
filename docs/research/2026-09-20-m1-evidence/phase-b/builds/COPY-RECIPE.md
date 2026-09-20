Reviewed promotion recipe (not executed)

The coordinator may copy this directory after reviewing commands-and-results.json and receipt.md. It contains only retained build evidence and packaging metadata; no source patch or generated artifact.

```sh
cd /Users/pooks/Dev/lean4-effect4
mkdir -p docs/research/2026-09-20-m1-evidence/phase-b-builds
cp -p /tmp/m1-tools/phase-b-build-evidence/* docs/research/2026-09-20-m1-evidence/phase-b-builds/
cd docs/research/2026-09-20-m1-evidence/phase-b-builds
shasum -a 256 -c SHA256SUMS
```

This command copies only top-level packaged files. The archive keeps the raw logs losslessly. Do not rerun package.py from the repository destination: it intentionally writes only the original scratch directory. Stage explicit promoted paths only after reviewing the copy.
