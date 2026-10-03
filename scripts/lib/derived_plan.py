"""Plan derived generation from manifest inputs and Lean-parsed source headers."""

EXECUTABLE_ROOTS = {
    "effect4gen": "Effect4Gen.Exe",
    "effect4gen-catalogue": "Effect4Gen.CatalogueExe",
}


def imports_of(row):
    args = row["args"]
    return args[args.index("--imports") + 1].split(",")


def stages(plan):
    """Stable topological stages; reject incomplete or cyclic dependency evidence."""
    rows = plan["commands"]
    graph = {}
    for entry in plan["imports"]:
        name = entry["module"]
        if name in graph:
            raise ValueError(f"duplicate module in import graph: {name}")
        graph[name] = entry["imports"]
    owners, outputs, names = {}, set(), set()
    for index, row in enumerate(rows):
        name, output, args = row["name"], row["out"].replace("\\", "/"), row["args"]
        if name in names or output in outputs:
            raise ValueError(f"duplicate generated name or output: {name}: {output}")
        names.add(name)
        outputs.add(output)
        if args[:1] != ["exe"] or args[1] not in EXECUTABLE_ROOTS:
            raise ValueError(f"unknown generator executable: {name}: {args[:2]}")
        if output.startswith("src/") and output.endswith(".lean"):
            owners[output[4:-5].replace("/", ".")] = index

    def closure(roots):
        seen, pending = set(), list(roots)
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            if module not in graph:
                raise ValueError(f"missing import evidence for {module}")
            pending.extend(graph[module])
        return seen

    early = closure([EXECUTABLE_ROOTS["effect4gen"]])
    if any(m == "Effect4" or m.startswith("Effect4.") for m in early):
        raise ValueError("early generator imports the Effect4 library")
    dependencies = []
    for index, row in enumerate(rows):
        modules = closure(imports_of(row) + [EXECUTABLE_ROOTS[row["args"][1]]])
        deps = {owners[module] for module in modules if module in owners}
        if index in deps:
            raise ValueError(f"generator depends on its own output: {row['name']}")
        dependencies.append(deps)
    pending, finished, result = set(range(len(rows))), set(), []
    while pending:
        ready = sorted(i for i in pending if dependencies[i] <= finished)
        if not ready:
            raise ValueError("generation dependency cycle: " + ", ".join(rows[i]["name"] for i in sorted(pending)))
        result.append([rows[i] for i in ready])
        pending.difference_update(ready)
        finished.update(ready)
    return result
