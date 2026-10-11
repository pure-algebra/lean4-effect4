"""Probe the latest device algebra and a producer repair in a temporary overlay."""
from pathlib import Path
import difflib
import hashlib
import json
import os
import re
import subprocess
import tempfile

packet = Path(__file__).resolve().parent
repo = packet.parents[3]
source_pin = "21d8e031f31318db62afea392b3d043beef2e0be"
generator_pin = "bfe97080657ecb87d4551fc8a4511580369f698d"
env = dict(os.environ, LEAN_NUM_THREADS="3")
record = {"sourcePin": source_pin, "generatorSourcePin": generator_pin, "commands": []}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def run(argv, expected=0):
    result = subprocess.run(argv, cwd=repo, env=env, capture_output=True, text=True)
    record["commands"].append({"argv": argv, "exitCode": result.returncode,
                               "stdout": result.stdout, "stderr": result.stderr})
    (packet / "evidence.json").write_text(json.dumps(record, indent=2) + "\n")
    if result.returncode != expected:
        raise SystemExit(result.stdout + result.stderr)
    return result.stdout + result.stderr

producer = (repo / "tools/Effect4Gen/Fold.lean").read_text()
assert producer.encode() == subprocess.check_output(
    ["git", "show", generator_pin+":tools/Effect4Gen/Fold.lean"], cwd=repo)
start = producer.index("def emitBlock (root : Name)")
end = producer.index("/-! ## A block whose children sit under containers", start)
body = producer[start:end]
old = '    s := s ++ "termination_by structural node\\n"'
new = '    if recursiveLabels.contains label then\n      s := s ++ "termination_by structural node\\n"'
assert body.count(old) == 8, "Refuse a changed producer shape"
body = body.replace(old, new)
opening = '  let labels := block.map (·.1)\n'
replacement = opening + '''  -- Match Lean's split of a mutual block: only a cycle needs termination evidence.
  let successors := fun label => block.flatMap fun (fam, _, rows) =>
    if fam == label then rows.flatMap (fun r => r.args.filterMap Arg.recFam) else []
  let recursiveLabels := (Lean.SCC.scc labels successors).flatMap fun component =>
    match component with
    | [label] => if (successors label).contains label then [label] else []
    | labels => labels
'''
assert body.count(opening) == 1
body = body.replace(opening, replacement)

# A leaf foldMap uses its callback, but has no child results to combine.
for declaration in ["foldMapAt", "foldMap"]:
    opening = '  for (label, fam, rows) in block do\n    s := s ++ s!"def ' + declaration + '_{label}'
    replacement = '  for (label, fam, rows) in block do\n    let opName := if rows.any (fun r => r.args.any (fun a => a.recFam.isSome)) then "op" else "_op"\n    s := s ++ s!"def ' + declaration + '_{label}'
    assert body.count(opening) == 1
    body = body.replace(opening, replacement)
assert body.count('(op : M → M → M)') == 2
body = body.replace('(op : M → M → M)', '({opName} : M → M → M)')
# A member without children never forwards the other family callbacks.
body = body.replace('  let fAtParams := String.intercalate', '  let fAtParams := fun label hasChildren => String.intercalate')
body = body.replace('  let fParams := String.intercalate', '  let fParams := fun label hasChildren => String.intercalate')
assert body.count('s!"(f_{l} :') == 2
body = body.replace('s!"(f_{l} :', 's!"({if hasChildren || l == label then "" else "_"}f_{l} :')
old_op = '    let opName := if rows.any (fun r => r.args.any (fun a => a.recFam.isSome)) then "op" else "_op"'
new_op = '    let hasChildren := rows.any (fun r => r.args.any (fun a => a.recFam.isSome))\n    let opName := if hasChildren then "op" else "_op"'
assert body.count(old_op) == 2
body = body.replace(old_op, new_op)
body = body.replace('{fAtParams}', '{fAtParams label hasChildren}').replace('{fParams}', '{fParams label hasChildren}')
candidate = producer[:start] + body + producer[end:]
(packet / "producer.patch").write_text("".join(difflib.unified_diff(
    producer.splitlines(keepends=True), candidate.splitlines(keepends=True),
    fromfile="a/tools/Effect4Gen/Fold.lean", tofile="b/tools/Effect4Gen/Fold.lean")))
record["producerSha256"] = sha(producer.encode())
record["candidateProducerSha256"] = sha(candidate.encode())
run(["lake", "build", "effect4gen"])
source = subprocess.check_output(["git", "show", source_pin+":tools/Tools/View/Picture.lean"], cwd=repo)
record["pictureSha256"] = sha(source)
with tempfile.TemporaryDirectory(prefix="effect4-device-fold-") as tmp:
    root = Path(tmp)
    src = root / "source"
    artifacts = root / "lib"
    for module in ["Tools", "Effect4Gen"]:
        base = repo / ".lake/build/lib/lean" / module
        for item in base.rglob("*"):
            if item.is_file():
                link = artifacts / item.relative_to(base.parent)
                link.parent.mkdir(parents=True, exist_ok=True)
                link.symlink_to(item)
    def compile_at(relative, contents):
        path = src / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents)
        out = artifacts / Path(relative).with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        for sibling in out.parent.glob(out.stem + ".*"):
            if sibling.is_symlink():
                sibling.unlink()
        run(prefix + ["lean", "-DwarningAsError=true", "--root="+str(src), "-o", str(out), str(path)])
    shell = 'export LEAN_PATH="$1:$LEAN_PATH"; shift; exec "$@"'
    prefix = ["lake", "env", "sh", "-c", shell, "device-fold-overlay", str(artifacts)]
    compile_at("Tools/View/Picture.lean", source.decode())
    original_cli = [str(repo / ".lake/build/bin/effect4gen"), "Fold"]
    def emit(cli, path, imports, types, extra=None, header=None):
        run(prefix + cli + ["--group", "TerminalDevProbe", "--imports", imports,
            "--out", str(path.relative_to(repo)), "--header-out", header or "tools/Tools/View/DevFold.lean"]
            + (extra or []) + types)
    original = packet / "OriginalDev.lean"
    emit(original_cli, original, "Tools.View.Picture", ["Tools.View.Dev"])
    first = original.read_bytes()
    emit(original_cli, original, "Tools.View.Picture", ["Tools.View.Dev"])
    assert first == original.read_bytes()
    failure = run(prefix + ["lean", "-DwarningAsError=true", str(original)], expected=1)
    errors = re.findall(r"error: (.*)", failure)
    assert errors == ["unused `termination_by`, function is not recursive"] * 8, failure
    record["originalErrors"] = errors
    compile_at("Effect4Gen/Fold.lean", candidate)
    wrapper = src / "Candidate.lean"
    wrapper.write_text("import Effect4Gen.Fold\ndef main := Effect4Gen.Fold.cli\n")
    candidate_cli = ["lean", "--run", str(wrapper)]
    generated = packet / "DevFold.lean"
    emit(candidate_cli, generated, "Tools.View.Picture", ["Tools.View.Dev"])
    first = generated.read_bytes()
    emit(candidate_cli, generated, "Tools.View.Picture", ["Tools.View.Dev"])
    assert first == generated.read_bytes()
    assert b"dev_shape" in first
    assert b"termination_by" not in first
    assert original.read_text().replace("termination_by structural node\n", "").replace("(op : M → M → M)", "(_op : M → M → M)") == generated.read_text()
    run(prefix + ["lean", "-DwarningAsError=true", "--root="+str(packet),
                  "-o", str(artifacts/"DevFold.olean"), str(generated)])
    record["candidateDevCompiled"] = True
    record["byteIdenticalRegeneration"] = True
    record["includesLatestShape"] = True
    record["generatedSha256"] = sha(first)
    record["checkOutput"] = run(prefix + ["lean", "-DwarningAsError=true", str(packet/"Checks.lean")])
    # Existing plain and nested recursive consumers share this one manifest group.
    group = next(g for g in json.loads((repo/"tools/Effect4Gen/manifest.json").read_text())["groups"] if g["Name"] == "Fold")
    fixed = ["--group", group["Name"], *group.get("Flags", []), "--imports", group["Imports"],
             "--header-out", group["Out"], "--append", group["Guards"].replace("\\", "/"), *group["Types"]]
    before, after = root/"Fold.before.lean", root/"Fold.after.lean"
    run(prefix + original_cli + fixed + ["--out", str(before)])
    run(prefix + candidate_cli + fixed + ["--out", str(after)])
    assert before.read_bytes() == after.read_bytes(), "Existing Fold output changed"
    record["existingFoldUnchangedSha256"] = sha(before.read_bytes())
    compile_at("Fixtures.lean", (packet/"Fixtures.lean").read_text())
    for name in ["Stem", "Branch"]:
        target = packet / ("Fixture"+name+".lean")
        emit(candidate_cli, target, "Fixtures", ["DeviceFoldFixture."+name], header="Fixture"+name+".lean")
        run(prefix + ["lean", "-DwarningAsError=true", str(target)])
    record["mutualFixturesCompiled"] = ["acyclic Stem to Leaf", "Branch and Twig cycle with leaf Tag"]
record["limits"] = ["The candidate changes only a temporary producer; production is unchanged.",
                    "No terminal renderer, native host execution, or full sweep.",
                    "Latest pinned Picture compiles against the generator-base toolchain in a temporary overlay."]
(packet / "evidence.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({k: v for k,v in record.items() if k not in ["commands", "checkOutput"]}))
