#!/usr/bin/env python3
"""Regenerate or check the semantics report without installing host dependencies.

Default: two fresh reports must equal the maintained generated files, then Lean
refusal controls, pinned tsgo 7 and strict Bun decoding controls must pass.
`--generate DIRECTORY` writes the report and a separate .lake/gen run receipt.
Both modes require prepared Lake artifacts: freshness checks never build or install.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import struct
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
FILES = ("semantics.json", "semantics.md")
TARGETS = ("Effect4.Laws", "Test.Program.TypedProgBindRed", "Test.Program.ProtocolPosts", "Test.Audit.SemanticsCensus",
           "Drivers.Semantics", "Drivers.SemanticsControls")
POLICY_FILES = ("Test/Audit/AxiomGate.lean", "tools/ProofGraph/Proof.lean")
INPUTS = ("tools/Tools/SemanticsRegistry.lean", "tools/Tools/Semantics.lean",
          "tools/Drivers/Semantics.lean", "tools/Drivers/SemanticsControls.lean",
          "src/Effect4/Laws/Auto/Semantics.lean", "Test/Audit/SemanticsCensus.lean",
          "Test/Counterexamples/REGISTER.md", "docs/core/decisions.md", "lean-toolchain",
          "scripts/check-semantics.py", "ts/eff/semantics.ts", "ts/eff/check-semantics.ts",
          "ts/eff/test/semantics.test.ts", "ts/eff/test/semantics.fixture.json",
          "ts/eff/package.json", "ts/eff/bun.lock", "ts/eff/tsconfig.json")
TRACE_DIR = ".lake/build/lib/lean/"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def lake_binary_hash(data):
    """Pinned v4.33.1 Lake Hash.ofByteArray, not a .hash-cache lookup.

    Lake/Build/Trace.lean:108,169–182 wraps ByteArray.hash with mixHash(1723,...).
    runtime/object.cpp:2460–2462 uses runtime/hash.cpp's MurmurHash64A, seed 11.
    The final mixing operation is include/lean/lean.h:2152–2160.
    """
    mask, multiplier = (1 << 64) - 1, 0xc6a4a7935bd1e995
    size = len(data)
    value = 11 ^ ((size * multiplier) & mask)
    end = size - size % 8
    for (word,) in struct.iter_unpack("=Q", memoryview(data)[:end]):
        word = (word * multiplier) & mask
        word ^= word >> 47
        word = (word * multiplier) & mask
        value = ((value ^ word) * multiplier) & mask
    if end != size:
        value ^= int.from_bytes(data[end:], "little")
        value = (value * multiplier) & mask
    value ^= value >> 47
    value = (value * multiplier) & mask
    value ^= value >> 47
    mixed = (value * multiplier) & mask
    mixed ^= mixed >> 47
    mixed ^= multiplier
    return f"{((1723 ^ mixed) * multiplier) & mask:016x}"


def verify_saved_outputs(receipt):
    """Check the prepared targets and their resolved import artifacts against traces.

    Lake setup importArts is the resolved transitive map (Lean/Setup.lean:66–107;
    Lake/Build/Module.lean:636–643); bundled toolchain imports have no Lake trace here.
    ModuleOutputDescrs outputs.o/rs/r is the saved artifact list (ModuleArtifacts.lean:37–51).
    No rebuilt module is exempt, and the mutable sibling .hash files are never evidence.
    """
    bases = set()
    for target in TARGETS:
        relative = Path(*target.split("."))
        bases.add(ROOT / TRACE_DIR / relative)
        setup_path = ROOT / ".lake/build/ir" / relative.with_suffix(".setup.json")
        setup = json.loads(setup_path.read_text())
        if setup.get("name") != target or not isinstance(setup.get("importArts"), dict):
            raise RuntimeError(f"{setup_path}: missing or wrong resolved import map")
        for module, arrays in setup["importArts"].items():
            if not isinstance(arrays, list) or not arrays or not arrays[0]:
                raise RuntimeError(f"{setup_path}: malformed import artifact for {module}")
            artifact = Path(arrays[0][0])
            if not artifact.is_absolute():
                raise RuntimeError(f"{module}: import artifact is not a resolved absolute path")
            expected_tail = Path(*module.split(".")).with_suffix(".olean").as_posix()
            if not artifact.as_posix().endswith("/lib/lean/" + expected_tail):
                raise RuntimeError(f"{module}: unexpected import artifact path {artifact}")
            if not artifact.resolve().is_relative_to(ROOT.resolve()):
                raise RuntimeError(f"{module}: import artifact is outside this prepared checkout: {artifact}")
            bases.add(artifact.with_suffix(""))
    observed = {}
    deadline = time.monotonic() + 180
    for base in sorted(bases):
        trace_path = base.with_suffix(".trace")
        trace = json.loads(trace_path.read_text())
        outputs = trace.get("outputs", {})
        descriptions = outputs.get("o", [])
        if not isinstance(descriptions, list) or not descriptions:
            raise RuntimeError(f"{trace_path}: no saved import output hashes")
        descriptions = [*descriptions, *(outputs[key] for key in ("rs", "r") if key in outputs)]
        seen = set()
        for description in descriptions:
            match = re.fullmatch(r"([0-9a-f]{16})\.(olean(?:\.server|\.private)?|ir(?:\.sig)?)", description) if isinstance(description, str) else None
            if not match or match[2] in seen:
                raise RuntimeError(f"{trace_path}: malformed or duplicate saved output {description}")
            expected, suffix = match.groups()
            seen.add(suffix)
            artifact = Path(str(base) + "." + suffix)
            if artifact.stat().st_size > 128 * 1024 * 1024:
                raise RuntimeError(f"{artifact}: saved-output check exceeds the 128 MiB per-file limit")
            if time.monotonic() > deadline:
                raise RuntimeError("saved-output hash checks exceeded 180 seconds")
            actual = lake_binary_hash(artifact.read_bytes())
            if actual != expected:
                raise RuntimeError(f"saved-output hash mismatch: {artifact}: expected {expected}, received {actual}")
            observed[str(artifact.relative_to(ROOT))] = actual
        if "olean" not in seen:
            raise RuntimeError(f"{trace_path}: missing saved primary olean hash")
    receipt["savedOutputs"] = observed
    receipt["savedOutputBoundary"] = "prepared project/package roots and resolved transitive import artifacts; bundled toolchain is pinned"


def publish_reports(stage, out):
    """Validate first, then replace both reports; restore old bytes on partial failure."""
    out.mkdir(parents=True, exist_ok=True)
    previous = {name: (out / name).read_bytes() if (out / name).exists() else None for name in FILES}
    pending, published = [], []
    try:
        for name in FILES:
            with tempfile.NamedTemporaryFile(dir=out, prefix=".semantics-", delete=False) as stream:
                pending.append((name, Path(stream.name)))
                stream.write((stage / name).read_bytes())
        for name, path in pending:
            os.replace(path, out / name)
            published.append(name)
    except OSError:
        for name in published:
            if previous[name] is None:
                (out / name).unlink(missing_ok=True)
            else:
                (out / name).write_bytes(previous[name])
        raise
    finally:
        for _, path in pending:
            path.unlink(missing_ok=True)


def require_report_roots(path):
    """The registry owns roots; this gate requires their prepared verification coverage."""
    roots = json.loads(path.read_text())["provenance"]["roots"]
    if not isinstance(roots, list) or not roots or any(not isinstance(root, str) for root in roots):
        raise RuntimeError(f"{path}: invalid report extraction roots")
    unverified = sorted(set(roots) - set(TARGETS))
    if unverified:
        raise RuntimeError(f"report roots outside the verified preparation targets: {', '.join(unverified)}; "
                           "update and prepare the semantics targets before admitting these roots")


def snapshot():
    paths = (*INPUTS, *POLICY_FILES,
             *(TRACE_DIR + target.replace(".", "/") + ".trace" for target in TARGETS))
    return {name: digest(ROOT / name) for name in paths}


def command(name, default):
    return shlex.split(os.environ.get(name, default))


def run(args, receipt, *, cwd=ROOT, timeout=180, echo=True):
    """Bound the whole subprocess group, including children of Lake or Bun."""
    entry = {"command": list(map(str, args)), "cwd": os.path.relpath(cwd, ROOT)}
    receipt["commands"].append(entry)
    env = {**os.environ, "LEAN_NUM_THREADS": "1", "GOMAXPROCS": "1", "GOMEMLIMIT": "512MiB"}
    with subprocess.Popen(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True, start_new_session=True) as process:
        try:
            output, _ = process.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                output, _ = process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                output, _ = process.communicate()
            entry.update(exit=process.returncode, timeout=True, output=output[-6000:])
            raise RuntimeError(f"command exceeded {timeout}s: {shlex.join(entry['command'])}")
    entry.update(exit=process.returncode, output=output[-6000:])
    if output and echo:
        print(output, end="" if output.endswith("\n") else "\n", flush=True)
    if process.returncode:
        raise RuntimeError(f"command exited {process.returncode}: {shlex.join(entry['command'])}")
    return output.strip()


def lean(file, receipt, *args):
    return run([*command("LAKE", "lake"), "env", "lean", "-j1", "-M4096",
                "-DwarningAsError=true", "--run", file, *map(str, args)], receipt, timeout=600)


def require_artifacts(receipt):
    # Lake may compile several modules concurrently. This gate refuses stale roots
    # rather than starting a build; the owner prepares them in the bounded Lean lane.
    try:
        run([*command("LAKE", "lake"), "--no-build", "--no-cache", "--rehash", "build", *TARGETS],
            receipt, timeout=900)
    except RuntimeError as error:
        prepare = shlex.join([*command("LAKE", "lake"), "build", *TARGETS])
        raise RuntimeError(f"required Lake artifacts are not ready: {error}; "
                           f"prepare in the bounded Lean lane with: {prepare}") from error
    verify_saved_outputs(receipt)


def require_host():
    modules = ROOT / "ts/eff/node_modules"
    package = json.loads((ROOT / "ts/eff/package.json").read_text())
    versions = {}
    for name, pin in (("effect", package["dependencies"]["effect"]),
                      ("@typescript/native-preview", package["devDependencies"]["@typescript/native-preview"])):
        installed = modules / name / "package.json"
        if not installed.is_file():
            raise RuntimeError(f"missing pinned installation: ts/eff/node_modules/{name}; install separately")
        version = json.loads(installed.read_text())["version"]
        if version != pin:
            raise RuntimeError(f"{name}: installed {version}, required {pin}; install separately")
        versions[name] = version
    if not versions["@typescript/native-preview"].startswith("7."):
        raise RuntimeError("semantics requires the pinned tsgo 7 compiler")
    for name, default in (("BUN", "bun"), ("NODE", "node")):
        if not shutil.which(command(name, default)[0]):
            raise RuntimeError(f"{name.lower()} is required; install separately")
    tsgo = modules / "@typescript/native-preview/bin/tsgo"
    if not tsgo.is_file():
        raise RuntimeError("missing pinned tsgo launcher; install separately")
    return tsgo, versions


def check_real_producer_refusal(receipt):
    """A missing real register row must refuse before replacing existing outputs."""
    register = (ROOT / "Test/Counterexamples/REGISTER.md").read_text()
    row = re.compile(r"^\|\s*`?E4-TYPED-CE-030`?\s*\|")
    lines = register.splitlines(keepends=True)
    if sum(bool(row.match(line)) for line in lines) != 1:
        raise RuntimeError("real producer refusal control requires exactly one CE-030 register data row")
    with tempfile.TemporaryDirectory(prefix="effect4-semantics-refusal-") as temporary:
        mirror = Path(temporary)
        register_path = mirror / "Test/Counterexamples/REGISTER.md"
        register_path.parent.mkdir(parents=True)
        register_path.write_text("".join(line for line in lines if not row.match(line)))
        for name in ("docs/core/decisions.md", "lean-toolchain"):
            target = mirror / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / name).read_bytes())
        out = mirror / "outputs"
        out.mkdir()
        sentinel = b"existing report: refusal must leave these bytes intact\n"
        for name in FILES:
            (out / name).write_bytes(sentinel)
        # Lake resolves its environment in the real project. The child changes cwd
        # only for the producer's authored register reads, retaining those import paths.
        child = """import subprocess, sys
result = subprocess.run(['lean', '-j1', '-M4096', '-DwarningAsError=true', '--run',
                         sys.argv[1], sys.argv[3]], cwd=sys.argv[2],
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
print(result.stdout, end='')
if result.returncode != 1:
    print('expected producer exit 1, received', result.returncode, file=sys.stderr)
    sys.exit(1)
"""
        output = run([*command("LAKE", "lake"), "env", sys.executable, "-c", child,
                      str(ROOT / "tools/Drivers/Semantics.lean"), str(mirror), str(out)],
                     receipt, timeout=600)
        if "bind-closed" not in output or "E4-TYPED-CE-030" not in output:
            raise RuntimeError("real producer refusal did not locate bind-closed and E4-TYPED-CE-030")
        if any((out / name).read_bytes() != sentinel for name in FILES):
            raise RuntimeError("real producer refusal replaced an existing report")
    print("PASS real semantics producer refusal: bind-closed / E4-TYPED-CE-030; existing outputs intact")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generate", metavar="DIRECTORY", type=Path,
                        help="write the projection instead of checking it")
    args = parser.parse_args()
    mode = "generate" if args.generate is not None else "check"
    receipt_path = ROOT / f".lake/{'gen' if args.generate is not None else 'check'}/semantics.receipt.json"
    receipt = {"format": "effect4-semantics-run-v1", "mode": mode,
               "result": "failed", "gate": "notAudited", "commands": []}
    staging = None
    try:
        receipt["head"] = run(["git", "rev-parse", "HEAD"], receipt, echo=False)
        receipt["dirty"] = bool(run(["git", "status", "--porcelain", "--untracked-files=normal"], receipt, echo=False))
        policy = {"ceiling": ["propext", "Quot.sound"],
                  "files": {name: digest(ROOT / name) for name in POLICY_FILES}}
        receipt["policy"] = policy
        receipt["policyHash"] = hashlib.sha256(json.dumps(policy, sort_keys=True).encode()).hexdigest()
        host = require_host() if mode == "check" else None
        # Required runtime import roots are separate from the thin driver's imports.
        require_artifacts(receipt)
        before = snapshot()
        receipt["inputs"] = before
        if args.generate is not None:
            out = args.generate if args.generate.is_absolute() else ROOT / args.generate
            staging = tempfile.TemporaryDirectory(prefix="effect4-semantics-stage-")
            stage = Path(staging.name)
            lean("tools/Drivers/Semantics.lean", receipt, stage)
            require_report_roots(stage / "semantics.json")
            if {file.name for file in stage.iterdir()} != set(FILES):
                raise RuntimeError("producer wrote an unexpected set of report files")
            receipt["outputs"] = {name: digest(stage / name) for name in FILES}
        else:
            with tempfile.TemporaryDirectory(prefix="effect4-semantics-") as temporary:
                first, second = (Path(temporary) / name for name in ("first", "second"))
                for out in (first, second):
                    lean("tools/Drivers/Semantics.lean", receipt, out)
                    require_report_roots(out / "semantics.json")
                    if {file.name for file in out.iterdir()} != set(FILES):
                        raise RuntimeError("producer wrote an unexpected set of report files")
                for name in FILES:
                    expected = ROOT / "generated" / name
                    if not expected.is_file():
                        raise RuntimeError(f"missing generated/{name}; run make gen-semantics")
                    if (first / name).read_bytes() != (second / name).read_bytes():
                        raise RuntimeError(f"{name}: two fresh producer runs differ")
                    if (first / name).read_bytes() != expected.read_bytes():
                        raise RuntimeError(f"generated/{name}: drift; run make gen-semantics")
                receipt["outputs"] = {name: digest(first / name) for name in FILES}
            lean("tools/Drivers/SemanticsControls.lean", receipt)
            check_real_producer_refusal(receipt)
            tsgo, versions = host
            receipt["versions"] = versions
            receipt["versions"]["bun"] = run([*command("BUN", "bun"), "--version"], receipt)
            run([*command("NODE", "node"), str(tsgo), "--version"], receipt)
            run([*command("NODE", "node"), str(tsgo), "--noEmit", "-p", "ts/eff/tsconfig.json"], receipt)
            run([*command("BUN", "bun"), "run", "check-semantics.ts", "../../generated/semantics.json"],
                receipt, cwd=ROOT / "ts/eff")
            run([*command("BUN", "bun"), "test", "test/semantics.test.ts"], receipt, cwd=ROOT / "ts/eff")
        if before != snapshot():
            raise RuntimeError("a semantics input changed during this run; rerun after the edit finishes")
        # Detect imported source edits too, even if no producer refreshed their traces.
        require_artifacts(receipt)
        if args.generate is not None:
            publish_reports(stage, out)
        receipt["result"] = "passed"
        print("PASS gen-semantics: report written" if mode == "generate" else
              f"PASS check-semantics: two byte-identical reports; Lean refusal controls; "
              f"tsgo {versions['@typescript/native-preview']}; strict decoding controls")
        return 0
    except (OSError, RuntimeError, ValueError, KeyError) as error:
        receipt["error"] = str(error)
        print(f"FAIL {mode}-semantics: {error}", file=sys.stderr)
        return 1
    finally:
        if staging is not None:
            staging.cleanup()
        receipt_path.parent.mkdir(parents=True, exist_ok=True)
        receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")


if __name__ == "__main__":
    sys.exit(main())
