#!/usr/bin/env python3
"""The proof graph's structure as tables, read from the semantics report's JSON.

    python3 semantics_tables.py SEMANTICS_JSON

The JSON is what `lake exe semantics-report OUT` writes (`OUT/semantics.json`); its Markdown is
`generated/semantics.md`. The script prints counts only: claims by concept and status, by role,
the requirements' statuses with their node counts, the plan's nodes by standing, the planned goals
with the nodes that rest on them, the placements, and the codegen's claims. It asserts nothing.
"""
import collections
import json
import sys


def main() -> int:
    data = json.load(open(sys.argv[1]))
    claims = data["claims"]
    print(f"claims {len(claims)}")
    status = collections.Counter(c["status"]["_tag"] for c in claims)
    print("by status", dict(status))
    concepts = [c["id"] for c in data["concepts"]]
    print("\nconcept\tclaims\t" + "\t".join(sorted(status)))
    for k in concepts:
        row = collections.Counter(c["status"]["_tag"] for c in claims if c["concept"] == k)
        print(f"{k}\t{sum(row.values())}\t" + "\t".join(str(row.get(s, 0)) for s in sorted(status)))
    print("\nrole\tclaims")
    for role, n in collections.Counter(c["role"] for c in claims).most_common():
        print(f"{role}\t{n}")

    plan = data["plan"]
    print("\nrequirement\tstatus\ttop\tplaced\topenParts\ttop-proved\tplaced-proved\tplaced-modulo\tplaced-goal")
    for r in plan["requirements"]:
        top, placed = r.get("top", []), r.get("placed", [])
        tops = collections.Counter(n["status"] for n in top)
        places = collections.Counter(n["status"] for n in placed)
        rid = r.get("id") or r["title"][:24]
        print(f"{rid}\t{r['status']}\t{len(top)}\t{len(placed)}\t{len(r.get('openParts', []))}\t"
              f"{tops.get('proved', 0)}\t{places.get('proved', 0)}\t{places.get('modulo', 0)}\t{places.get('goal', 0)}")
    states = collections.Counter(p["state"] for r in plan["requirements"] for p in r.get("openParts", []))
    print("open parts by state", dict(states))

    nodes = plan["nodes"]
    print(f"\nplan nodes {len(nodes)}", dict(collections.Counter(n["status"] for n in nodes)))
    by_module = collections.Counter(n["module"].split(".")[0] + "." + ".".join(n["module"].split(".")[1:3])
                                    for n in nodes)
    print("plan nodes by area (top 12)", by_module.most_common(12))
    goals = [n for n in nodes if n["status"] == "goal"]
    resting = collections.defaultdict(list)
    for n in nodes:
        for g in n.get("restsOn", []):
            resting[g].append(n["name"])
    print("\nplanned goal\tmodule\tnodes resting on it")
    for g in goals:
        print(f"{g['name']}\t{g['module']}\t{len(resting.get(g['name'], []))}\t{sorted(resting.get(g['name'], []))}")
    print("next goals", plan["next"])
    print("unplaced goals", plan["unplacedGoals"])

    placement = data["placement"]
    decls = placement["declarations"]
    print(f"\nplacement universe: {placement['universe']}")
    print(f"placed declarations {len(decls)}", dict(collections.Counter(d["placement"] for d in decls)),
          "unplaced", placement["unplacedCount"])
    print("placed by concept", dict(collections.Counter(d["concept"] for d in decls)))

    print("\ncodegen claims (a witness in a Codegen module)")
    for c in claims:
        w = c["status"].get("witness") or {}
        module = w.get("module", "")
        if "Codegen" in module or c["concept"] == "exact-codecs":
            print(f"{c['id']}\t{c['concept']}\t{c['role']}\t{c['status']['_tag']}\t{module}\t{w.get('name', '')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
