#!/usr/bin/env python3
"""Extract every executable doc fence from the pinned stream dependency surface."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MODULES = ("Stream", "Channel", "Pull", "Queue", "Scope", "Sink", "PubSub", "Fiber")
PIN = "vendor/effect-4.0.0-rc.112/src"
FENCE = re.compile(r"```ts import\.meta\.vitest\n(.*?)\n\s*\*\s*```", re.S)


def census():
    rows = []
    paths = [f"{PIN}/{module}.ts" for module in MODULES]
    owners = json.loads(subprocess.check_output(
        ["bun", "harness/streams/census-owners.ts", *paths], cwd=ROOT, text=True))
    for module in MODULES:
        path = f"{PIN}/{module}.ts"
        source = (ROOT / path).read_text()
        for ordinal, match in enumerate(FENCE.finditer(source), 1):
            program = "\n".join(re.sub(r"^\s*\* ?", "", line)
                                for line in match[1].splitlines())
            # TypeScript offsets count UTF-16 code units, Python offsets code points.
            start = len(source[:match.start()].encode("utf-16-le")) // 2
            candidates = [node for node in owners[path] if node["start"] <= start < node["end"]]
            if not candidates:
                candidates = [node for node in owners[path] if node["start"] > start]
            concurrent = bool(re.search(r"\b(?:forkChild|forkScoped|merge|broadcast|subscribe|buffer|zip)\b|concurrency", program))
            mechanics = [module.lower()]
            for word, tag in (("toPull", "channel.toPull"), ("done", "pull.done"),
                              ("scoped", "scope.close"), ("acquireRelease", "scope.finalizerOrder"),
                              ("shutdown", "queue.shutdown"), ("end", "queue.end"),
                              ("dropping", "queue.dropping"), ("sliding", "queue.sliding")):
                if re.search(r"\b" + word + r"\b", program):
                    mechanics.append(tag)
            rows.append({
                "id": f"{module}-{ordinal:03d}", "module": module,
                "export": candidates[0]["name"] if candidates else module,
                "source": path,
                "sourceLines": [source.count("\n", 0, match.start()) + 1,
                                source.count("\n", 0, match.end()) + 1],
                "spanDigest": hashlib.sha256(match[0].encode()).hexdigest(),
                "program": program,
                "expected": re.findall(r"// =>(.*)", program),
                "mechanics": mechanics,
                "distinction": ["explicit-concurrency" if concurrent else "sequential-observation"],
                "layer": 2 if concurrent else 0,
                "leanStatus": "unrepresented",
            })
    return {"format": "effect4-stream-census-v1", "pin": "4.0.0-rc.112", "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--out", type=Path, default=ROOT / "harness/streams/census.json")
    args = parser.parse_args()
    data = census()
    rendered = json.dumps(data, ensure_ascii=False, indent=2) + "\n"
    if args.check:
        if not args.out.exists() or args.out.read_text() != rendered:
            raise SystemExit("stream census differs; run scripts/generate-effect-stream-census.sh")
    else:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered)
    print(json.dumps({module: sum(row["module"] == module for row in data["rows"])
                      for module in MODULES}))


if __name__ == "__main__":
    main()
