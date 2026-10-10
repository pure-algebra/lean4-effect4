#!/usr/bin/env python3
"""Read-only comparison of the pinned promoted tables and graph merge."""
import csv
import hashlib
import io
import json
import subprocess
from pathlib import Path

OUT = Path(__file__).resolve().parent
GATE = "87a17323d14d15ae6aebd6456c65b268ac3d7cf0"
MERGE = "8a876482d0cb8600a4b186f1fdeee47f29607a24"
GRAPH = "86d72c1062d0b63f51f4d8b55b194c48fafd8863"

def show(rev, path):
    return subprocess.check_output(["git", "show", f"{rev}:{path}"])

def table(rev, path):
    lines = show(rev, path).decode().splitlines()
    if lines[0].startswith("#"):
        header = next(line[2:] for line in lines if line.startswith("# ") and "\t" in line)
        body = [line for line in lines if line and not line.startswith("#")]
        text = "\n".join([header, *body])
    else:
        text = "\n".join(lines)
    rows = list(csv.DictReader(io.StringIO(text), delimiter="\t"))
    key = list(rows[0])[0]
    result = {r[key]: r for r in rows}
    assert len(result) == len(rows), (path, "duplicate key")
    return result

results = {}
for path, allowed in [
    ("harness/truth/corpus-results.tsv", {"note"}),
    ("generated/tsdiag-agreement.tsv", {"observed", "side", "verdict"}),
    ("generated/row-citations.tsv", {"actualRequest", "actualAnswer", "note"}),
]:
    old, new = table(GATE + "^", path), table(GATE, path)
    assert old.keys() == new.keys(), (path, "row inventory changed")
    changes = []
    for key in old:
        delta = {c: [old[key][c], new[key][c]] for c in old[key] if old[key][c] != new[key][c]}
        if delta:
            assert delta.keys() <= allowed, (path, key, delta)
            if path.endswith("corpus-results.tsv"):
                assert old[key]["wellTyped"] == new[key]["wellTyped"] == "no"
                assert old[key]["tsc"] == new[key]["tsc"] == "errors"
            elif path.endswith("tsdiag-agreement.tsv"):
                assert old[key]["wellTyped"] == new[key]["wellTyped"] == "false"
                if "verdict" in delta:
                    assert delta["verdict"] == ["refused-silent", "refused-unmapped"]
            else:
                assert key == "Atom/tuple"
                assert old[key]["status"] == new[key]["status"]
            changes.append({"key": key, "columns": delta})
    results[path] = {"rows": len(old), "changed_rows": len(changes), "changes": changes}

path = "Test/fixtures/target/selection.json"
old, new = [json.loads(show(r, path)) for r in [GATE + "^", GATE]]
selection_changes = {}
for key in old.keys() | new.keys():
    if old.get(key) != new.get(key):
        assert isinstance(old[key], list) and isinstance(new[key], list)
        assert new[key][:len(old[key])] == old[key]
        added = new[key][len(old[key]):]
        assert added == ["pQueueService", "pSemaphoreService"]
        selection_changes[key] = {"added": added, "removed": [], "before": len(old[key]), "after": len(new[key])}
assert selection_changes
results[path] = selection_changes

paths = ["tools/Tools/Graph/Index.lean", "tools/Tools/Session/Snapshot.lean",
    "tools/Tools/View/Flow.lean", "tools/Tools/View/FlowLaws.lean",
    "tools/Tools/View/Graph.lean", "tools/Tools/View/Run.lean"]
results["graph_merge"] = {"reviewed_graph": GRAPH, "merge": MERGE, "files": {}}
for path in paths:
    a, b = show(GRAPH, path), show(MERGE, path)
    assert a == b, (path, "merged implementation differs")
    results["graph_merge"]["files"][path] = hashlib.sha256(b).hexdigest()

results["limits"] = "Committed table/source comparison only; no compiler, external runtime, or rendered-output rerun."
(OUT / "table-and-merge-review.json").write_text(json.dumps(results, indent=2) + "\n")
print(json.dumps({"gate_commit": GATE,
    "changed_rows": {k: v["changed_rows"] for k, v in results.items() if isinstance(v, dict) and "changed_rows" in v},
    "selection": selection_changes, "identical_graph_files": len(paths)}, indent=2))
