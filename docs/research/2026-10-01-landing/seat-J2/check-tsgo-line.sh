#!/usr/bin/env bash
# Receipt J, step 7 (iii): the proposed check-tsgo recipe line, verbatim, run from the worktree root.
cd "$(dirname "$0")/../../../.." || exit 99
python3 -c 'import json,pathlib,sys; v=lambda p: json.loads(p.read_text())["version"]; bad=[p.as_posix()+": "+v(p) for r in ("ts","harness","tools") for p in sorted(pathlib.Path(r).rglob("node_modules/typescript/package.json")) if int(v(p).split(".")[0]) < 7]; print("\n".join(["FAIL check-tsgo: typescript below 7 (tsgo 7 is the one compiler):"]+bad) if bad else "PASS check-tsgo: no typescript below 7 under ts/, harness/ or tools/"); sys.exit(1 if bad else 0)'
