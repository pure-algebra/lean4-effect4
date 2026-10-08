#!/usr/bin/env python3
"""Run the four generated authoring examples against the pinned Effect install.

The Lean probe writes the declarations first. This script supplies the existing
truth prelude, checks them with the pinned tsgo, and runs their finite assertions.
It downloads nothing and changes no generated group in the repository.
"""
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--modules", type=Path, required=True)
parser.add_argument("--work", type=Path, default=Path("/private/tmp/effect4-module-authoring-host"))
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root / "scripts/lib"))
import truth_host

modules = args.modules.resolve()
expected_compiler = truth_host.pinned_compiler(root)
refusal = truth_host.compiler_refusal(modules, expected_compiler)
if refusal:
    raise SystemExit(refusal)
version = json.loads((modules / "effect/package.json").read_text())["version"]
if version != truth_host.PINNED:
    raise SystemExit(f"expected Effect {truth_host.PINNED}, found {version}")
bun = shutil.which("bun")
if not bun:
    raise SystemExit("bun is required")
work = args.work.resolve()
truth = root / "harness/truth"
truth_host.copy_prelude(truth, work)
shutil.copytree(truth / "session", work / "session", dirs_exist_ok=True)
link = work / "node_modules"
if link.exists():
    if link.resolve() != modules:
        raise SystemExit("temporary node_modules selects another installation")
else:
    truth_host.link_install(link, modules)
imports = [line for line in (truth / "generated/pQueueDefs.ts").read_text().splitlines()
           if line.startswith("import ")]
if len(imports) != 2:
    raise SystemExit("unexpected truth example import envelope")
for name in ["queue", "semaphore", "waiting", "combined"]:
    path = work / "generated" / (name + ".ts")
    source = path.read_text()
    if not source.startswith("// authoring host probe"):
        path.write_text("// authoring host probe\n" + "\n".join(imports) + "\n" + source)
runner = r'''import assert from "node:assert/strict"
import { Effect, Option } from "effect"
import { main as queue } from "./generated/queue.ts"
import { main as semaphore } from "./generated/semaphore.ts"
import { main as waiting } from "./generated/waiting.ts"
import { main as combined } from "./generated/combined.ts"

const q = await Effect.runPromise(queue)
assert.deepEqual([q[0], q[1], Option.isNone(q[2])], [3, "three", true])
const s = await Effect.runPromise(semaphore)
assert.deepEqual(s, [1, 2, true, false])
const w = await Effect.runPromise(waiting)
assert.deepEqual(w, [1, 1])
const c = await Effect.runPromise(combined)
assert.deepEqual(c, [23, 1])
console.log(JSON.stringify({ queue: [q[0], q[1], "None"], semaphore: s, waiting: w, combined: c }))
'''
(work / "run.ts").write_text(runner)
config = json.loads((truth / "tsconfig.json").read_text())
config.pop("//", None)
config["include"] = ["generated/*.ts", "run.ts", "prelude.ts"]
(work / "tsconfig.json").write_text(json.dumps(config, indent=2) + "\n")
print(f"Effect {version}; tsgo {expected_compiler}; bun " +
      subprocess.check_output([bun, "--version"], text=True).strip(), flush=True)
subprocess.run(truth_host.compiler(modules) + ["--noEmit", "-p", str(work / "tsconfig.json")],
               cwd=work, check=True)
subprocess.run([bun, "--no-install", "run", str(work / "run.ts")], cwd=work, check=True, timeout=30)
print("PASS: four generated authoring examples typecheck and return their expected answers")
