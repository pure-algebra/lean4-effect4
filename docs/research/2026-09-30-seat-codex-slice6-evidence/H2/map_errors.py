#!/usr/bin/env python3
"""Attribute Lean diagnostics to copied declarations; this does not measure repair necessity."""
import argparse
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("probe", choices=("Baseline", "PartOne"))
parser.add_argument("log", type=Path)
args = parser.parse_args()
base = Path(__file__).resolve().parent
mapping = json.loads((base / f"{args.probe}.map.json").read_text())
pattern = re.compile(r"^(.+\.lean):(\d+):(\d+): (error|warning|info): (.*)$")
items = []
for line in args.log.read_text().splitlines():
    match = pattern.match(line)
    if match:
        path, number, column, severity, message = match.groups()
        if Path(path).name != f"{args.probe}.lean":
            continue
        number = int(number)
        declaration = next((d for d in mapping["declarations"]
                            if d["harness_start"] <= number <= d["harness_end"]), None)
        source = next((s for s in mapping["line_map"] if s["harness_line"] == number), None)
        items.append({"line": number, "column": int(column), "severity": severity,
                      "message": message, "source": source, "declaration": declaration})
    elif items:
        items[-1]["message"] += "\n" + line
primary = [item for item in items if item["severity"] == "error" and
           "declaration uses 'sorry'" not in item["message"]]
theorems = sorted({item["declaration"]["original_declaration"] for item in primary
                   if item["declaration"] and item["declaration"]["kind"] == "theorem"})
other = [item for item in primary if not item["declaration"] or
         item["declaration"]["kind"] != "theorem"]
print(json.dumps({"probe": args.probe,
                  "note": "Compiler-error regions only. Root must distinguish harness, cascade, and required body repairs.",
                  "distinct_primary_error_theorem_regions": theorems,
                  "distinct_primary_error_theorem_region_count": len(theorems),
                  "non_theorem_primary_errors": other, "diagnostics": items}, indent=2))
