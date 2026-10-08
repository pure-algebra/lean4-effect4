#!/usr/bin/env python3
"""Compare three emitted programs with the actual pinned Effect modules.

Run the companion Lean probe's emit command first. This driver writes raw
observations for Conform; known differences remain counterexamples in its report.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--modules", type=Path, required=True)
parser.add_argument("--work", type=Path, default=Path("/private/tmp/effect4-module-compatibility"))
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root / "scripts/lib"))
import truth_host

modules = args.modules.resolve()
expected_compiler = truth_host.pinned_compiler(root)
refusal = truth_host.compiler_refusal(modules, expected_compiler)
if refusal:
    raise SystemExit(refusal)
effect_version = json.loads((modules / "effect/package.json").read_text())["version"]
if effect_version != truth_host.PINNED:
    raise SystemExit(f"expected Effect {truth_host.PINNED}, found {effect_version}")
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
names = ["semaphore-immediate", "semaphore-over-release", "pool-acquisition-failure"]
for name in names:
    path = work / "generated" / (name + ".ts")
    source = path.read_text()
    if not source.startswith("// native module compatibility probe"):
        path.write_text("// native module compatibility probe\n" + "\n".join(imports) + "\n" + source)
runner = r'''import { Effect, Pool, Semaphore } from "effect"
import { main as emittedImmediate } from "./generated/semaphore-immediate.ts"
import { main as emittedOverRelease } from "./generated/semaphore-over-release.ts"
import { main as emittedFailedPool } from "./generated/pool-acquisition-failure.ts"

const nativeImmediate = Effect.gen(function* () {
  const q = yield* Semaphore.make(2)
  const taken = yield* Semaphore.take(q, 1)
  const free = yield* Semaphore.release(q, 1)
  const first = yield* Semaphore.takeIfAvailable(q, 2)
  const second = yield* Semaphore.takeIfAvailable(q, 1)
  return [taken, free, first, second]
})
const nativeOverRelease = Effect.gen(function* () {
  const q = yield* Semaphore.make(2)
  const taken = yield* Semaphore.take(q, 1)
  const free = yield* Semaphore.release(q, 3)
  return [taken, free]
})
const nativeFailedPool = Effect.scoped(
  Effect.as(Pool.make({ size: 1, acquire: Effect.fail(77) }), "made")
)
const observe = (p: Effect.Effect<unknown, unknown, never>) => Effect.runPromise(
  Effect.match(p, {
    onFailure: (value) => ({ tag: "failure", value }),
    onSuccess: (value) => ({ tag: "success", value })
  })
)
const samples = []
for (const [id, emitted, native] of [
  ["semaphore-immediate", emittedImmediate, nativeImmediate],
  ["semaphore-over-release", emittedOverRelease, nativeOverRelease],
  ["pool-acquisition-failure", emittedFailedPool, nativeFailedPool]
] as const) {
  samples.push({ id, emitted: await observe(emitted), native: await observe(native) })
}
console.log(JSON.stringify(samples))
'''
(work / "run.ts").write_text(runner)
config = json.loads((truth / "tsconfig.json").read_text())
config.pop("//", None)
config["include"] = ["generated/*.ts", "run.ts", "prelude.ts"]
(work / "tsconfig.json").write_text(json.dumps(config, indent=2) + "\n")
subprocess.run(truth_host.compiler(modules) + ["--noEmit", "-p", str(work / "tsconfig.json")],
               cwd=work, check=True)
raw = subprocess.check_output([bun, "--no-install", "run", str(work / "run.ts")],
                              cwd=work, text=True, timeout=30)
samples = json.loads(raw)
if [s["id"] for s in samples] != names:
    raise SystemExit("host results differ from the declared scenarios")
# Independent controls: these are the exits checked by the companion Lean probe.
expected = [
    {"tag": "success", "value": [1, 2, True, False]},
    {"tag": "success", "value": [1, 2]},
    {"tag": "failure", "value": 77},
]
if [s["emitted"] for s in samples] != expected:
    raise SystemExit("the emitted executions disagree with the checked Lean cases")
program_paths = ["src", "Test", "tools", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]
source_commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
source_state = subprocess.check_output(
    ["git", "status", "--porcelain", "--untracked-files=no", "--", *program_paths],
    cwd=root, text=True).strip() or "clean"
pins = [
    {"name": "program-source-commit", "value": source_commit},
    {"name": "program-source-tracked-state", "value": source_state},
    {"name": "Effect", "value": effect_version},
    {"name": "tsgo", "value": expected_compiler},
    {"name": "bun", "value": subprocess.check_output([bun, "--version"], text=True).strip()},
    {"name": "Lean", "value": (root / "lean-toolchain").read_text().strip()},
]
paths = [("scenario-driver", work / "run.ts"),
         ("Lean-probe", root / "docs/research/2026-10-08-module-compatibility-probe.lean"),
         ("host-driver", Path(__file__).resolve()),
         ("compiler-options", work / "tsconfig.json"),
         ("effect-package", modules / "effect/package.json"),
         ("effect-Semaphore", modules / "effect/dist/Semaphore.js"),
         ("effect-Pool", modules / "effect/dist/Pool.js")]
paths += [("generated/" + name, work / "generated" / (name + ".ts")) for name in names]
paths += [("host/" + str(p.relative_to(work)), p) for p in sorted(work.glob("*.ts"))
          if p.name != "run.ts"]
paths += [("host/" + str(p.relative_to(work)), p) for p in sorted((work / "session").glob("**/*.ts"))]
inputs = [{"name": name, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
          for name, path in paths]
output = work / "observations.json"
output.write_text(json.dumps({"pins": pins, "inputs": inputs, "samples": samples}, indent=2) + "\n")
print("Typechecked with tsgo " + expected_compiler + "; Effect " + effect_version)
print(json.dumps(samples, indent=2))
print("Raw finite observations: " + str(output))
