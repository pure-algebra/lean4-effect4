#!/usr/bin/env python3
"""status: one screen of what is true at HEAD, measured, never hand-written.

    HEAD and the uncommitted paths; the last battery build against the Lean sources changed
    since; which check and generation markers are fresh against the inputs the Makefile names
    for them; the committed generated files that differ from HEAD; the semantics claims by
    status (generated/semantics.md); the open ledger goals (#proof_wanted); the decision
    registers and the counterexample register by status; the stale references in the
    authority documents (scripts/lib/doc_refs.py).

No Lean runs. Freshness is read from GNU make's own database (`make -pn`): a marker is fresh
when it exists and none of its prerequisites is newer; the two inventories (`.lake/check/inventory`,
`.lake/check/paths`) are recomputed and compared. `make status` runs it.
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts" / "lib"))

from doc_refs import stale_references  # noqa: E402
from build_profile import profile  # noqa: E402


class StatusError(Exception):
    """A measurement could not be taken; the report refuses rather than guess."""


def run(*args: str) -> str:
    """The command's standard output; a nonzero exit is a StatusError carrying its diagnostic."""
    done = subprocess.run(args, cwd=ROOT, capture_output=True, text=True)
    if done.returncode != 0:
        detail = (done.stderr or done.stdout).strip().splitlines()
        raise StatusError(f"`{' '.join(args)}` exited {done.returncode}: " + (detail[-1] if detail else "no output"))
    return done.stdout


def mtime(path: str) -> float:
    try:
        return os.stat(ROOT / path).st_mtime
    except FileNotFoundError:
        return -1.0


def lean_sources() -> list[str]:
    out = []
    for top in ("src", "Test"):
        for dirpath, _, files in os.walk(ROOT / top):
            for name in files:
                if name.endswith(".lean"):
                    out.append(os.path.relpath(os.path.join(dirpath, name), ROOT))
    return out


def head_line() -> tuple[str, list[str]]:
    branch = run("git", "rev-parse", "--abbrev-ref", "HEAD").strip()
    commit = run("git", "log", "-1", "--format=%h %cs").strip()
    dirty = [line[3:] for line in run("git", "status", "--porcelain").split("\n") if line]
    return f"{branch} @ {commit}", dirty


def make_database() -> tuple[dict[str, list[str]], dict[str, str]]:
    """Every rule `target: prerequisites` make knows (order-only prerequisites dropped, files make
    lists as "Not a target" skipped) and every `NAME := value`."""
    text = run("make", "-pn", "help")
    rules: dict[str, list[str]] = {}
    variables: dict[str, str] = {}
    lines = text.split("\n")
    for i, line in enumerate(lines):
        assignment = re.match(r"^([A-Z_][A-Z0-9_]*) :?= (.*)$", line)
        if assignment:
            variables[assignment.group(1)] = assignment.group(2)
            continue
        if not line or line[0] in "#\t " or (i > 0 and lines[i - 1].startswith("# Not a target")):
            continue
        rule = re.match(r"^([^:=\s][^:=]*?):(?![:=])\s*(.*)$", line)
        if rule and " " not in rule.group(1) and not re.fullmatch(r"\.[A-Z_]+", rule.group(1)):
            rules.setdefault(rule.group(1), rule.group(2).split("|", 1)[0].split())
    missing = [name for name in ("CHECKS", "HERMETIC_GROUPS", "GENERATED_PATHS") if not variables.get(name, "").split()]
    if missing or ".lake/check/roots" not in rules:
        raise StatusError("make's database lacks " + ", ".join(missing or [".lake/check/roots"]) +
                          "; the Makefile changed shape or did not parse")
    return rules, variables


def inventory_fresh(marker: str, current: list[str]) -> bool:
    path = ROOT / marker
    if not path.exists():
        return False
    return path.read_text().split("\n")[:-1] == current or path.read_text().split() == current


def stale_reason(target: str, rules: dict[str, list[str]], inventories: dict[str, list[str]],
                 memo: dict[str, str | None]) -> str | None:
    """Why make would rebuild `target`, or None when it would not: the target is missing, an
    inventory it reads changed, a prerequisite is missing, newer, or itself stale (followed through
    every prerequisite that has a rule, so a stale upstream marker makes its consumers stale)."""
    if target in memo:
        return memo[target]
    memo[target] = None  # a cycle is make's error, not this report's
    if target in inventories:
        memo[target] = None if inventory_fresh(target, inventories[target]) else "the inventory changed"
        return memo[target]
    stamp = mtime(target)
    if stamp < 0:
        memo[target] = "missing"
        return memo[target]
    for prerequisite in rules.get(target, []):
        if prerequisite == "FORCE":
            continue
        if prerequisite in rules or prerequisite in inventories:
            upstream = stale_reason(prerequisite, rules, inventories, memo)
            if upstream is not None:
                memo[target] = f"{prerequisite}: {upstream}"
                return memo[target]
        when = mtime(prerequisite)
        if when < 0:
            memo[target] = f"{prerequisite}: missing"
            return memo[target]
        if when > stamp:
            memo[target] = f"{prerequisite} is newer"
            return memo[target]
    return None


def marker_state(marker: str, rules: dict[str, list[str]], inventories: dict[str, list[str]],
                 memo: dict[str, str | None]) -> str:
    if mtime(marker) < 0:
        return "never"
    return "fresh" if stale_reason(marker, rules, inventories, memo) is None else "stale"


def table_rows(path: str) -> list[list[str]]:
    rows = []
    for line in (ROOT / path).read_text().split("\n"):
        if line.startswith("| ") and not line.startswith("| ---"):
            cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
            rows.append(cells)
    return rows


def claims() -> Counter:
    counts: Counter = Counter()
    for cells in table_rows("generated/semantics.md"):
        if len(cells) == 6 and re.fullmatch(r"[a-z0-9-]+", cells[0]) and cells[2] in (
                "proved", "absent", "refuted", "assumed", "wanted", "open"):
            counts[cells[2]] += 1
    return counts


STATUS_WORDS = ("open", "ruled", "landed", "basis", "seeded", "repaired", "pinned", "retired", "closed")


def status_word(cell: str) -> str:
    """The status a register cell opens with: one of the known words, else `other`."""
    head = cell.replace("*", "").strip().lower()[:24]
    first = re.split(r"[\s,;:(]+", head)[0] if head else ""
    if first == "re-ruled":
        return "ruled"
    return first if first in STATUS_WORDS else "other"


def decisions() -> Counter:
    counts: Counter = Counter()
    for cells in table_rows("docs/core/decisions.md"):
        if cells and re.fullmatch(r"\d+", cells[0]):
            status = next((c for c in reversed(cells) if c), "")
            counts[status_word(status)] += 1
    return counts


def design_issues() -> Counter:
    counts: Counter = Counter()
    for cells in table_rows("docs/DESIGN-ISSUES.md"):
        if cells and cells[0].startswith("DI-") and len(cells) > 3:
            counts[status_word(cells[3])] += 1
    return counts


def counterexamples() -> Counter:
    counts: Counter = Counter()
    for cells in table_rows("Test/Counterexamples/REGISTER.md"):
        if cells and cells[0].strip("`").startswith("E4-") and len(cells) > 1:
            counts[status_word(cells[1])] += 1
    return counts


def ledger_goals() -> int:
    """The library's open goals: `#proof_wanted` under src/. The ledger's own controls in Test/
    (Test/Audit/Obligations.lean, IndexedColumns.lean) test the instrument and are not goals."""
    count = 0
    for path in lean_sources():
        if not path.startswith("src/") or path.endswith("Laws/Auto/Obligations.lean"):
            continue
        for line in (ROOT / path).read_text().split("\n"):
            if re.match(r"^\s*#proof_wanted\s+\S", line):
                count += 1
    return count


def summarise(counts: Counter, order: tuple[str, ...] = ()) -> str:
    keys = [k for k in order if k in counts] + sorted(k for k in counts if k not in order)
    return " · ".join(f"{counts[k]} {k}" for k in keys) if keys else "none"


def main() -> int:
    rules, variables = make_database()  # first: a failed measurement prints nothing else
    head, dirty = head_line()
    print(f"effect4   {head}")
    if dirty:
        shown = ", ".join(dirty[:6]) + (f", +{len(dirty) - 6} more" if len(dirty) > 6 else "")
        print(f"dirty     {len(dirty)}: {shown}")
    else:
        print("dirty     clean")

    sources = sorted(lean_sources())
    battery = ".lake/build/lib/lean/Test/All.trace"
    built = mtime(battery)
    if built < 0:
        print("build     never (lake build)")
    else:
        changed = sum(1 for s in sources if mtime(s) > built)
        when = subprocess.run(["date", "-r", str(int(built)), "+%Y-%m-%d %H:%M"], capture_output=True,
                              text=True).stdout.strip()
        state = "up to date" if changed == 0 else f"{changed} Lean source(s) changed since (lake build)"
        print(f"build     battery built {when}; {state}")
    log = ROOT / ".lake/gen/build.log"
    last = profile(log) if log.is_file() else None
    if last is not None:
        print(f"profile   last make build: {len(last['times'])} modules rebuilt, {last['summed']:.0f} s summed, "
              f"critical path {last['critical']:.0f} s; slowest {last['ranked'][0][0]} (make build-profile)")

    inventories = {".lake/check/inventory": sources,
                   ".lake/check/paths": run("git", "ls-files").split("\n")[:-1]}
    checks = variables.get("CHECKS", "").split()
    memo: dict[str, str | None] = {}
    states = {name: marker_state(f".lake/check/{name}", rules, inventories, memo) for name in checks}
    by_state: dict[str, list[str]] = {}
    for name, state in states.items():
        by_state.setdefault(state, []).append(name)
    print("checks    " + "; ".join(f"{state}: {' '.join(names)}" for state, names in
                                  sorted(by_state.items(), key=lambda kv: ("fresh", "stale", "never").index(kv[0]))))
    groups = variables.get("HERMETIC_GROUPS", "").split()
    gen_states = {g: marker_state(f".lake/gen/{g}", rules, inventories, memo) for g in groups}
    stale_groups = [g for g, s in gen_states.items() if s != "fresh"]
    generated = variables.get("GENERATED_PATHS", "").split()
    drift = [line[3:] for line in run("git", "status", "--porcelain", "--", *generated).split("\n") if line]
    gen_line = "all groups fresh" if not stale_groups else f"stale: {' '.join(stale_groups)} (make check-gen)"
    drift_line = "no committed generated file differs" if not drift else f"{len(drift)} generated file(s) differ: {' '.join(drift[:4])}"
    print(f"generated {gen_line}; {drift_line}")

    print(f"claims    {summarise(claims(), ('proved', 'absent', 'refuted', 'assumed', 'wanted'))}  (generated/semantics.md)")
    print(f"ledger    {ledger_goals()} open goal(s) (#proof_wanted)")
    print(f"decisions {summarise(decisions(), ('open', 'ruled', 'landed'))}  (docs/core/decisions.md)")
    print(f"issues    {summarise(design_issues(), ('open', 'ruled', 'basis'))}  (docs/DESIGN-ISSUES.md)")
    print(f"counterex {summarise(counterexamples(), ('seeded', 'repaired', 'pinned', 'retired'))}  (Test/Counterexamples/REGISTER.md)")
    if "--why" in sys.argv:
        for name in checks:
            if states[name] == "stale":
                print(f"  check-{name}: {stale_reason(f'.lake/check/{name}', rules, inventories, memo)}")
        for g in groups:
            if gen_states[g] == "stale":
                print(f"  gen-{g}: {stale_reason(f'.lake/gen/{g}', rules, inventories, memo)}")
    stale = stale_references(ROOT)
    if stale:
        files = len({s.file for s in stale})
        print(f"docs      {len(stale)} stale reference(s) in {files} document(s) (make check-docs)")
    else:
        print("docs      every path, link, citation and make target resolves")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except StatusError as error:
        print(f"FAIL status: {error}", file=sys.stderr)
        sys.exit(2)
