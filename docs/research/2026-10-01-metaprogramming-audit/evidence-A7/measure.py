#!/usr/bin/env python3
"""Source-only A7 census at an immutable revision; never invokes Lean/Lake.

Reads tracked src/tools Lean blobs, strips comments/strings for source inventories,
and joins their explicit import names. External-package imports remain frontier
nodes: this is NOT a full Lean import-closure or compiled-environment measurement.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = "198dd5331eb6607e1e94f3abad39ebbda90c86dc"


def strip_comments_strings(text: str) -> str:
    """Blank comments/strings without changing line or byte-character positions."""
    chars = list(text)
    i = 0
    depth = 0
    string = False

    def blank(start: int, end: int) -> None:
        for j in range(start, end):
            if chars[j] != "\n":
                chars[j] = " "

    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                blank(i, i + 2)
                i += 2
            elif pair == "-/":
                depth -= 1
                blank(i, i + 2)
                i += 2
            else:
                blank(i, i + 1)
                i += 1
        elif string:
            if text[i] == "\\":
                end = min(i + 2, len(text))
                blank(i, end)
                i = end
            else:
                if text[i] == '"':
                    string = False
                blank(i, i + 1)
                i += 1
        elif pair == "/-":
            depth = 1
            blank(i, i + 2)
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            blank(i, end)
            i = end
        elif text[i] == '"':
            string = True
            blank(i, i + 1)
            i += 1
        else:
            i += 1
    assert text.count("\n") == "".join(chars).count("\n")
    return "".join(chars)


def module_name(path: str) -> str:
    return path.removeprefix("src/").removeprefix("tools/").removesuffix(".lean").replace("/", ".")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)

    def git(*argv: str) -> str:
        return subprocess.check_output(["git", *argv], cwd=args.repo, text=True)

    resolved = git("rev-parse", BASE + "^{commit}").strip()
    assert resolved == BASE
    paths = {}
    for entry in git("ls-tree", "-r", BASE, "--", "src", "tools").splitlines():
        meta, path = entry.split("\t", 1)
        if path.endswith(".lean"):
            paths[path] = meta.split()[2]

    process = subprocess.Popen(["git", "cat-file", "--batch"], cwd=args.repo,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    assert process.stdin is not None and process.stdout is not None

    def blob(ref: str) -> str:
        process.stdin.write((ref + "\n").encode())
        process.stdin.flush()
        header = process.stdout.readline().decode().split()
        assert len(header) == 3 and header[1] == "blob", header
        size = int(header[2])
        data = process.stdout.read(size)
        assert len(data) == size
        assert process.stdout.read(1) == b"\n"
        return data.decode()

    graph = {}
    source = {}
    clean = {}
    locations = {}
    imports = []
    provenance = []
    for path, sha in paths.items():
        name = module_name(path)
        assert name not in graph, name
        text = blob(sha)
        source[name] = text
        clean[name] = strip_comments_strings(text)
        locations[name] = path
        graph[name] = set()
        provenance.append({"module": name, "path": path, "git_blob": sha,
                           "sha256": hashlib.sha256(text.encode()).hexdigest()})
        for line_no, line in enumerate(clean[name].splitlines(), 1):
            match = re.match(r"^(?:(?:public|private|meta) )?import +(.*)$", line)
            if match:
                for imported in match[1].split():
                    graph[name].add(imported)
                    imports.append({"module": name, "path": path, "line": line_no,
                                    "imported": imported})

    def closure(root: str, edges=None) -> set[str]:
        if edges is None:
            edges = graph
        seen = set()
        todo = list(edges.get(root, set()))
        while todo:
            node = todo.pop()
            if node in seen:
                continue
            seen.add(node)
            todo.extend(edges.get(node, set()) - seen)
        return seen

    runtime = closure("Effect4") | {"Effect4"}
    laws = closure("Effect4.Laws") | {"Effect4.Laws"}
    closures = {name: closure(name) for name in graph}

    def dependents(name: str) -> dict:
        rev = sorted(m for m, c in closures.items() if name in c)
        direct = sorted(m for m, c in graph.items() if name in c)
        return {"module": name, "direct": direct, "direct_count": len(direct),
                "transitive": rev, "transitive_count": len(rev),
                "runtime_transitive": [m for m in rev if m in runtime],
                "laws_transitive": [m for m in rev if m in laws]}

    def is_lean(name: str) -> bool:
        return name == "Lean" or name.startswith("Lean.")

    direct_lean = []
    for name in sorted(graph):
        if locations[name].startswith("src/Effect4/") and any(map(is_lean, graph[name])):
            row = dependents(name)
            row.update({"path": locations[name], "runtime_reachable": name in runtime,
                        "laws_reachable": name in laws,
                        "lean_imports": [r for r in imports if r["module"] == name and is_lean(r["imported"])]})
            direct_lean.append(row)

    fold_sites = []
    runtime_meta_sites = []
    macro_pattern = re.compile(r"^\s*(?:scoped )?(?:macro(?: |$)|macro_rules(?: |$)|elab(?: |$)|syntax(?: |$))")
    eff_pattern = re.compile(r"(?<![\w])eff\s+(?:do\b|\{)")
    program_eff_sites = []
    for name, text in clean.items():
        raw_lines = source[name].splitlines()
        for line_no, line in enumerate(text.splitlines(), 1):
            if re.match(r"^\s*fold_of\s+", line):
                fold_sites.append({"module": name, "path": locations[name], "line": line_no,
                                   "text": raw_lines[line_no - 1].strip()})
            if name in runtime and macro_pattern.match(line):
                runtime_meta_sites.append({"module": name, "path": locations[name], "line": line_no,
                                           "text": raw_lines[line_no - 1].strip()})
            if eff_pattern.search(line):
                program_eff_sites.append({"module": name, "path": locations[name], "line": line_no,
                                          "text": raw_lines[line_no - 1].strip()})

    test_files = ["Test/Program/AuthorContract.lean", "Test/Program/AuthoringContract.lean",
                  "Test/Program/AuthoringScope.lean"]
    test_eff_sites = []
    for path in test_files:
        text = blob(BASE + ":" + path)
        raw_lines = text.splitlines()
        for line_no, line in enumerate(strip_comments_strings(text).splitlines(), 1):
            if eff_pattern.search(line):
                test_eff_sites.append({"path": path, "line": line_no,
                                       "text": raw_lines[line_no - 1].strip(),
                                       "intentional_rejection": path.endswith("AuthoringScope.lean") and line_no == 30})

    directives = {}
    for command in ["#proof_wanted", "#obligation_proved", "#typed_state_obligations"]:
        sites = []
        pattern = re.compile(r"^\s*" + re.escape(command) + r"\s+")
        for name, text in clean.items():
            if not locations[name].startswith("src/Effect4/") and name != "Effect4.Laws":
                continue
            for line_no, line in enumerate(text.splitlines(), 1):
                if pattern.match(line):
                    sites.append({"path": locations[name], "line": line_no})
        directives[command] = {"count": len(sites), "files": len(set(s["path"] for s in sites)), "sites": sites}

    process.stdin.close()
    assert process.wait() == 0
    pruned = {m: set(xs) for m, xs in graph.items()}
    pruned["Effect4"].discard("Effect4.Program.FoldOf")
    pruned_runtime = closure("Effect4", pruned) | {"Effect4"}

    summary = {
        "base": BASE,
        "scope": "tracked src/tools .lean modules at the base; explicit source imports only",
        "method": "git cat-file blobs; comment/string stripping; graph reachability; no Lean compiler",
        "project_modules": len(graph),
        "runtime_project_modules_including_root": len(runtime & graph.keys()),
        "laws_project_modules_including_root": len(laws & graph.keys()),
        "runtime_external_frontier": sorted(runtime - graph.keys()),
        "laws_external_frontier": sorted(laws - graph.keys()),
        "src_effect4_direct_lean_importers": len(direct_lean),
        "runtime_direct_lean_importers": [r["module"] for r in direct_lean if r["runtime_reachable"]],
        "fold_command_sites": len(fold_sites),
        "fold_command_files": dict(sorted(Counter(s["path"] for s in fold_sites).items())),
        "src_tools_eff_block_sites": len(program_eff_sites),
        "test_eff_block_sites": len(test_eff_sites),
        "test_eff_accepting_sites": sum(not s["intentional_rejection"] for s in test_eff_sites),
        "test_eff_intentional_rejecting_sites": sum(s["intentional_rejection"] for s in test_eff_sites),
        "remove_foldof_root_edge_project_runtime_count": len(pruned_runtime & graph.keys()),
        "remove_foldof_root_edge_direct_project_lean_importers": sorted(m for m in pruned_runtime & graph.keys() if any(map(is_lean, pruned[m]))),
        "limits": ["External package import graphs are not traversed.",
                   "Source parsing is a bounded lexical census, not Lean.Elab.parseImports or a compiled environment.",
                   "No .olean provenance, axiom audit, compilation, build time, or memory cost is measured.",
                   "Reverse counts exclude the subject and exclude Test and downstream external applications.",
                   "Three named Test files are scanned separately for authoring blocks; these do not enter the import graph."]
    }
    assert summary["project_modules"] == 475
    assert summary["runtime_project_modules_including_root"] == 135
    assert summary["laws_project_modules_including_root"] == 351
    assert summary["fold_command_sites"] == 62
    assert summary["src_tools_eff_block_sites"] == 0
    assert summary["test_eff_block_sites"] == 21
    outputs = {
        "summary.json": summary,
        "project-modules.json": provenance,
        "imports.json": imports,
        "root-closures.json": {"runtime_project": sorted(runtime & graph.keys()),
                               "laws_project": sorted(laws & graph.keys()),
                               "runtime_external_frontier": sorted(runtime - graph.keys()),
                               "laws_external_frontier": sorted(laws - graph.keys())},
        "direct-lean-importers.json": direct_lean,
        "fold-sites.json": fold_sites,
        "sugar-dependents.json": dependents("Effect4.Program.Authoring.Sugar"),
        "authoring-block-sites.json": {"src_tools": program_eff_sites, "selected_tests": test_eff_sites},
        "runtime-meta-sites.json": runtime_meta_sites,
        "obligation-command-sites.json": directives,
    }
    for name, data in outputs.items():
        (args.out / name).write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
