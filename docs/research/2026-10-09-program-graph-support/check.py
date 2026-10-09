#!/usr/bin/env python3
"""Check retained finite observations; this does not execute Lean or prove a law."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent

def read(name):
    return json.loads((root / name).read_text())

manifest = read("draft-manifest.json")
assert hashlib.sha256((root / "draft.patch").read_bytes()).hexdigest() == manifest["patchSha256"]
runtime = read("runtime-output.json")
draft = read("draft-output.json")
partial = read("level-only-output.json")
repaired = read("repaired-output.json")
landed = read("landed-output.json")
assert runtime["caseCount"] == len(runtime["cases"])
assert all(row["admitted"] for row in runtime["cases"])
runs = {row["name"]: row for row in runtime["cases"]}
assert len(runs) == runtime["caseCount"]
assert runs["release-runs-at-scope-close"]["refs"] == [10, 20, 30]
assert runs["empty-race-is-live"]["exit"] == "live"
assert runs["race-success-does-not-launch-later-entrant"]["refs"] == [10]
assert runs["fork-has-no-implicit-join"]["exit"] == "success 2"
repeated = runs["one-fork-site-two-runtime-fibers"]
assert len({tuple(site) for site in repeated["forkSites"]}) == 1
assert len(set(repeated["childIds"])) == 2
assert len(set(repeated["fiberGraphKeys"])) == 3

def failed(report):
    assert report["bindingCount"] == len(report["bindings"])
    assert all(row["admitted"] for row in report["bindings"])
    assert report["allBindingsMatch"] == all(row["matches"] for row in report["bindings"])
    return {row["name"] for row in report["bindings"] if not row["matches"]}

expected_failures = {
    "first-of-two-fibers", "second-of-two-fibers", "unrelated-newer-value",
    "generator-bindings", "release-has-two-binders", "alias-is-outside-direct-spawn-reading",
}
assert failed(draft) == expected_failures
assert failed(partial) == {"closed-layer-resets-bindings"}
assert failed(repaired) == set()
assert [row["name"] for row in draft["bindings"]] == [row["name"] for row in repaired["bindings"]]
assert [row["expected"] for row in draft["bindings"]] == [row["expected"] for row in repaired["bindings"]]
release = {node["key"]: node for node in draft["scopedRelease"]["nodes"]}
marker_paths = {10: "[0 0 0 0]", 20: "[0 1 0]", 30: "[0 0 1 0]"}
drawn_order = sorted(marker_paths, key=lambda n: release[marker_paths[n]]["y"])
assert drawn_order == [10, 30, 20]
assert draft["emptyRace"]["width"] < 0
assert draft["choiceAndParallelHaveIdenticalGeometry"]
# The binding repair does not silently claim to fix other layout observations.
assert draft["scopedRelease"] == repaired["scopedRelease"]
assert draft["emptyRace"] == repaired["emptyRace"]
assert failed(landed) == set()
assert landed["projection"]["admitted"]
assert not landed["projection"]["matches"]
assert landed["projection"]["actual"] == [["[1 1]", "[0 0]"], ["[1 1]", "[1 0 0]"]]
assert landed["projection"]["expected"] == [["[1 1]", "[0 0]"]]
assert landed["projectionSelectedFiber"] == 1
assert not landed["choiceAndParallelHaveIdenticalGeometry"]
assert landed["emptyRace"]["width"] < 0
assert landed["emptyRace"]["boxesApart"] and landed["emptyRace"]["edgesDescend"]
assert not any('child→spawn-control/end' in route for route in landed["spawn"]["routes"])
assert any('parent→spawn-control/end' in route for route in landed["spawn"]["routes"])
landed_nodes = {node["key"]: node for node in landed["scopedRelease"]["nodes"]}
assert sorted(marker_paths, key=lambda n: landed_nodes[marker_paths[n]]["y"]) == [10, 30, 20]
summary = {
    "draftBase": manifest["base"], "capturedAt": manifest["capturedAt"],
    "reviewedCommit": "78f7bcbef09fc286242eedc549462e647c7c0b33",
    "runtimeBase": runtime["base"],
    "resolved": ["PGS-1 binding levels and closed scope", "PGS-4 visible implicit spawn join", "PGS-5 branch marks"],
    "open": ["PGS-2 cleanup sequencing", "PGS-3 empty composition geometry", "PGS-6 projected wait targets"],
    "evidence": "finite Lean evaluations and source inspection; no new theorem or host check",
    "runtimeControls": runtime["caseCount"], "bindingControls": repaired["bindingCount"],
    "draftBindingFailures": sorted(failed(draft)),
    "partialRepairFailures": sorted(failed(partial)),
    "repairedBindingFailures": sorted(failed(repaired)),
    "landedBindingFailures": sorted(failed(landed)),
    "projectionWaits": landed["projection"],
    "candidateRepairStatus": "superseded by Claude's landed fix; do not apply to the landed tree",
    "cleanupRuntimeOrder": runs["release-runs-at-scope-close"]["refs"],
    "cleanupDrawnOrder": drawn_order, "emptyRaceWidth": draft["emptyRace"]["width"],
    "bindingRepairSha256": hashlib.sha256((root / "binding-repair.patch").read_bytes()).hexdigest(),
}
print(json.dumps(summary, indent=2))
