#!/usr/bin/env python3
"""Check every citation in docs/DESIGN-BASIS.md against a stated commit.

Seat H of the 2026-10-01 landing (the DESIGN-BASIS refresh). No build, no generator: files
are read with `git show` and from disk. Run from anywhere:

  python3 check_citations.py [basis.md]   # exit 0 when every check outside the history passes
  python3 check_citations.py --self-test  # the red control: seeded defects must be reported
  python3 check_citations.py --base <rev> [basis.md]  # the same checks at another commit
  python3 check_citations.py --drift <rev> [basis.md] # where each line citation's text sits at <rev>

Every backticked span of the basis is one of:
  * a file citation `path`, `path:n` or `path:n-m`. The file must exist and the lines lie
    inside it. Tree paths are read at BASE; `Effects/...` in the pinned `effects` package at
    PKG_REV; `git:<rev>:<path>` at <rev>; `docs/research/...` at BASE when tracked there, else
    at HEAD of this branch (notes this refresh force-adds), else at TRACK (notes tracked on
    refactor/phase1-phase3 since), else on the main checkout's disk (untracked); `Lean/...` in
    the pinned Lean toolchain's sources; a bare rc.112 file
    (`Layer.ts:54`, `internal/effect.ts:726`) under `vendor/effect-4.0.0-rc.112/src/` at BASE;
    a short `.lean` path by its unique suffix under src/, Test/ or harness/.
  * a commit (7-40 hex digits): a commit of this repository or the package, or an external pin
    named below. A 64-hex SHA-256 next to a `Lean/...` path is recomputed from the toolchain.
  * a version tag: the toolchain's version or a tag of the package.
  * a single identifier: declared in the tree at BASE (src/, Test/, tools/, harness/), in the
    package, or in a research probe the basis cites; or on the allowlist with its reason. The
    index holds every declared name and each of its dotted components, so this says a name
    exists somewhere, not where; the witness pairs below are the check that says where.
Witness checks:
  * `` `name` (`path:n`) ``: the name is on line n of path (or inside n-m).
  * `` `name` (witness missing at `BASE`; ... `docs/research/....lean:n` ...) ``: the name is
    NOT declared in the tree at BASE, and it IS on line n of the named probe.
  * every witness pair whose declaration is a `ProofGraph.Obligation` is listed: a declared
    statement, not a proof; the text must call it "declared".
Register ids and DI numbers: every `E4-...-CE-nnn` is a row of the register or its archive
(`Test/Counterexamples/REGISTER.md`, `Test/Counterexamples/Archive/REGISTER.md`) at BASE, or else
at TRACK (reported as registered after BASE); every `...-FB-...` fallback id is named in one of
them; every DI-nn is a row of `docs/DESIGN-ISSUES.md` at BASE.
Source marks: every `docs/research/...` path in a Sources field agrees with its "(tracked" or
"(untracked" mark, tracked meaning present at BASE, at HEAD or at TRACK.
Structure: every DB row ends in the six fields, each once and in order (Decision, Witnesses,
Refusals, Sources, Literature, Status), with nothing after them but their own continuation
lines; and no line outside a table or a code block repeats the line before it.
A failure inside the history appendix (after the heading `## History`) is reported as STALE:
that text is kept as written on its date and is not corrected; it does not fail the run.
The drift report (`--drift <rev>`) is not a check: for every `path:n[-m]` citation into a file
that changed between BASE and <rev>, it prints where the cited text sits at <rev>, so the
citations can be re-pinned at a merge.
"""
import fnmatch
import hashlib
import os
import re
import subprocess
import sys

BASE = "dceae006"
REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
MAIN = "/Users/pooks/Dev/lean4-effect4"           # the main checkout: untracked research
PKG_DIR = os.path.join(MAIN, ".lake", "packages", "effects")
PKG_REV = "a4ee7a14"
# refactor/phase1-phase3 when this refresh closed: a note is tracked when it is present at BASE,
# at HEAD of this branch, or here (seat F tracked eighteen notes at 27495d51). A fixed commit, not
# the moving branch name, so a rerun gives the same answer.
TRACK = "efcf1ae2"
VENDOR = "vendor/effect-4.0.0-rc.112/src/"
HISTORY_MARK = "\n## History"

_cache = {}


def run(args, cwd=REPO):
    return subprocess.run(args, cwd=cwd, capture_output=True, text=True)


def show(rev, path, cwd=REPO):
    key = (cwd, rev, path)
    if key not in _cache:
        r = run(["git", "show", f"{rev}:{path}"], cwd=cwd)
        _cache[key] = r.stdout.split("\n") if r.returncode == 0 else None
    return _cache[key]


def exists_at(rev, path, cwd=REPO):
    return run(["git", "cat-file", "-e", f"{rev}:{path}"], cwd=cwd).returncode == 0


def toolchain_dir():
    pin = (show(BASE, "lean-toolchain") or [""])[0].strip()           # leanprover/lean4:v4.33.1
    version = pin.split(":")[-1]
    return version, os.path.expanduser(f"~/.elan/toolchains/leanprover--lean4---{version}/src/lean")


TOOL_VERSION, TOOL_SRC = toolchain_dir()
_tree_files = None


def tree_files():
    global _tree_files
    if _tree_files is None:
        r = run(["git", "ls-tree", "-r", "--name-only", BASE, "src", "Test", "harness"])
        _tree_files = [p for p in r.stdout.split() if p.endswith(".lean")]
    return _tree_files


def read_file(path):
    """(lines, where) or (None, reason). A directory reads as []."""
    if path.startswith("git:"):
        m = re.match(r"git:([0-9a-f]+\^?):(.+)$", path)
        if not m:
            return None, "bad git: form"
        lines = show(m.group(1), m.group(2))
        return (lines, f"git {m.group(1)}") if lines is not None else (None, f"absent at {m.group(1)}")
    if path.startswith("Effects/"):
        lines = show(PKG_REV, path, cwd=PKG_DIR)
        return (lines, f"package {PKG_REV}") if lines is not None else (None, "absent in the package")
    if path.startswith("Lean/"):
        disk = os.path.join(TOOL_SRC, path)
        if os.path.isfile(disk):
            with open(disk, encoding="utf-8", errors="replace") as f:
                return f.read().split("\n"), f"toolchain {TOOL_VERSION}"
        return None, f"absent in toolchain {TOOL_VERSION}"
    if path.startswith("docs/research/"):
        for rev, where in ((BASE, f"tracked at {BASE}"), ("HEAD", "tracked on this branch")):
            if exists_at(rev, path.rstrip("/")):
                return (show(rev, path) or []), where
        if exists_at(TRACK, path.rstrip("/")):
            return (show(TRACK, path) or []), f"tracked at {TRACK}"
        for root, where in ((MAIN, "untracked (main checkout)"), (REPO, "this worktree, not yet committed")):
            disk = os.path.join(root, path)
            if os.path.isfile(disk):
                with open(disk, encoding="utf-8", errors="replace") as f:
                    return f.read().split("\n"), where
            if os.path.isdir(disk):
                return [], where + " (directory)"
        return None, "absent"
    if re.match(r"^[A-Za-z]+\.ts$|^(internal|unstable|testing)/", path):
        lines = show(BASE, VENDOR + path)
        return (lines, "rc.112 vendor") if lines is not None else (None, "absent in vendor")
    lines = show(BASE, path)
    if lines is not None:
        return lines, f"tree {BASE}"
    if exists_at(BASE, path.rstrip("/")):
        return [], f"tree {BASE} (directory)"
    if path.endswith(".lean"):
        hits = [p for p in tree_files() if p.endswith("/" + path)]
        if len(hits) == 1:
            return show(BASE, hits[0]), f"tree {BASE} via {hits[0]}"
        if len(hits) > 1:
            return None, "ambiguous short path: " + ", ".join(hits)
    return None, f"absent at {BASE}"


DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom|macro|syntax|elab|fold_of)\s+"
    r"(?:\{[^}]*\}\s*)?([^\s(:{\[]+)")
CTOR = re.compile(r"^\s*\|\s*\.?([A-Za-z_][A-Za-z0-9_'!?]*)")
FIELD = re.compile(r"^\s{2,}([A-Za-z_][A-Za-z0-9_'!?]*)\s*:\s")
INSTFIELD = re.compile(r"^\s{2,}([A-Z][A-Za-z0-9_'!?]*)(?:\s+[A-Za-z_][A-Za-z0-9_']*)*\s*:=")
NAMESPACE = re.compile(r"^\s*namespace\s+([^\s]+)")


def index_lines(lines, into):
    for ln in lines:
        for rx in (DECL, CTOR, FIELD, INSTFIELD, NAMESPACE):
            m = rx.match(ln)
            if m:
                full = m.group(1)
                into.add(full)
                for part in full.split("."):
                    into.add(part)


def build_index():
    names = set()
    r = run(["git", "ls-tree", "-r", "--name-only", BASE, "src", "Test", "tools", "harness"])
    for path in r.stdout.split():
        if path.endswith(".lean"):
            index_lines(show(BASE, path) or [], names)
    r = run(["git", "ls-tree", "-r", "--name-only", PKG_REV, "Effects"], cwd=PKG_DIR)
    for path in r.stdout.split():
        if path.endswith(".lean"):
            index_lines(show(PKG_REV, path, cwd=PKG_DIR) or [], names)
    return names


def tree_declared(name):
    """Is `name` (its last component) declared under src/ or Test/ at BASE?"""
    short = name.split(".")[-1]
    sp = "[[:space:]]"
    pat = (r"^" + sp + r"*(@\[[^]]*\]" + sp + r"*)?((private|protected|noncomputable)" + sp + r"+)*"
           r"(theorem|lemma|def|abbrev|structure|inductive|class|instance)" + sp + r"+([A-Za-z0-9_.']*\.)?"
           + re.escape(short) + r"([^A-Za-z0-9_']|$)")
    # git grep's ERE here has neither \b nor \s: POSIX classes, checked by the red control
    return run(["git", "grep", "-n", "-E", pat, BASE, "--", "src", "Test"]).stdout.strip() != ""


# External pins: commits of other repositories, named by the rows with their URLs.
EXTERNAL_COMMITS = {
    "2600f62f4532026928454dcea8d1c48557b3f942": "Effect-TS/effect (DB-09; also in four contract packets)",
    "5e4d380b6fcd20f048dd8d41515bcd9ea47ffda4": "Effect-TS/language-service (DB-09)",
    "3937f7ff0830cca33d6b35a24aef55bcbe3b6bc9": "Verified-zkEVM/PolyFun (DB-10)",
    "5611c3a": "pure-algebra/lean4-effects v0.1.0 (the archived register's MOVED rows)",
}
EXTERNAL_PATHS = {
    "src/Schema.ts": "the installed effect@4.0.0-rc.112 package's file (DB-09), not this tree",
    "PORT-MANIFEST.md": "named by the text as never having existed here",
}

# Names that are not declarations of this tree at BASE, each group with its reason. Only names
# the index does not already match are listed (the index is coarse: every component of every
# declared name), so every entry here is needed by the rows, the history or the red control.
ALLOW = {
    "Lean core, a keyword or attribute, or the toolchain (v4.33.1), not a tree declaration": [
        "StateT", "EStateM", "ExceptT", "Nat", "Type", "DecidableEq", "EStateM.run_throw",
        "Lean.collectAxioms", "collectAxioms", "Lean.Util.CollectAxioms", "Std.Do", "unsafe", "abbrev",
        "implemented_by"],
    "rc.112 / TypeScript name (vendored source, not Lean)": [
        "updateContext", "scheduleTask", "ClockImpl", "clearTimeout", "setTimeout", "setTime",
        "Effect.catchReason", "SqlError", "SqlClient.withTransaction", "Option.fromNullable",
        "JSON.stringify", "Equal", "Statement.PrimitiveKind", "Headers", "File.Info", "UniqueViolation",
        "AuthenticationError", "UnknownError", "InternalError", "PersistenceError", "constraint",
        "mergeAllEffect", "Latch.scheduleUnsafe", "TxRef", "Date", "Uint8Array", "_tag", "catchTag",
        "ApplyServices"],
    "a name of an earlier commit or an earlier document (the archived Flow route, the pre-src/ "
    "layout; history)": [
        "Behavior", "HHandler", "interpretRef", "loop_obs_mono", "run_obs_mono", "region_obs_mono",
        "runRegions_obs_mono", "Chain.stable", "loop_fuel_stable", "Chain.colimit", "Chain.colimit_below",
        "Chain.colimit_bound_mono", "Chain.colimit_eq_of_settled", "runColimitDefault",
        "run_fuelFor_finishes", "runRegionsColimit", "Effect4.Logic.wp_iff_wlp_and_total",
        "Effect4.Flow.wp_iff", "box_sound", "Flow.wlp_runDefault", "wp_runDefault", "build_total",
        "buildAll_total", "Construction", "noStr", "Logic", "ProfileRefusal"],
    "PolyFun's name (DB-10; an external repository at its pinned commit)": ["FreeM"],
    "named by a ruling, or proved only on a seat branch or in a probe; not in the tree at BASE": [
        "abandon", "emptyColumn", "lower_refines_build", "denoteR_typed", "evalTerm_fits",
        "fits_normalize", "fits_subN"],
    "prose or notation in code font, not a declaration": ["Psq", "or", "not", "wp", "wlp", "Σ",
                                                           "π"],
    "another runtime's name, cited for its role (Eio, Riot)": ["In_transition", "Delay"],
}
ALLOW_SET = {n: why for why, names in ALLOW.items() for n in names}

# Unicode names (`Ψ_S`, `Ψ_F`) are names too: a letter or underscore, then word characters
IDENT = re.compile(r"^[^\W\d][\w'.!?]*$")
PATHLINE = re.compile(r"^((?:git:[0-9a-f]+\^?:)?[A-Za-z0-9_./@+-]+?\.(?:lean|md|ts|toml|json|py|sh|tsv|ml|mjs|txt))"
                      r"(?::(\d+)(?:-(\d+))?)?$")
DIRPATH = re.compile(r"^(?:src|Test|docs|harness|tools|scripts|vendor|ocaml|generated)/[A-Za-z0-9_./-]*/?$")
NAME = r"[^\W\d][\w'.!?]*"
PAIR = re.compile(r"`(" + NAME + r")`\s*\(`([^`]+?):(\d+)(?:-(\d+))?`")
MISSING = re.compile(r"`(" + NAME + r")`[^`\n]{0,40}\(witness missing at `" + BASE + r"`([^)]*)\)")
PROBE_AT = re.compile(r"`(docs/research/[^`]+?\.lean):(\d+)`")
DIGEST_PAIR = re.compile(r"`(Lean/[^`]+)`\s*\|\s*`([0-9a-f]{64})`")


REGISTERS = ("Test/Counterexamples/REGISTER.md", "Test/Counterexamples/Archive/REGISTER.md")
CE_ID = re.compile(r"`(E4-[A-Z0-9]+(?:-[A-Z0-9]+)*-CE-\d{3})`")
FB_ID = re.compile(r"`([A-Z0-9]+(?:-[A-Z0-9]+)*-FB(?:-[A-Z0-9]+)+)`")
DI_NUM = re.compile(r"\bDI-\d+\b")


def check_ids(text):
    """(fails, registered after BASE, counts) for the register ids and the DI numbers."""
    fails, late = [], []
    regs = {rev: "\n".join("\n".join(show(rev, f) or []) for f in REGISTERS) for rev in (BASE, TRACK)}
    ces, fbs = sorted(set(CE_ID.findall(text))), sorted(set(FB_ID.findall(text)))
    for i in ces:
        row = re.compile(r"^\|\s*`" + re.escape(i) + r"`\s*\|", re.M)
        if row.search(regs[BASE]):
            continue
        if row.search(regs[TRACK]):
            late.append(i)
            continue
        fails.append(f"register id {i}: a row of neither register at {BASE} nor at {TRACK}")
    for i in fbs:
        if not re.search(r"(?<![A-Z0-9-])" + re.escape(i) + r"(?![A-Z0-9-])", regs[BASE]):
            fails.append(f"fallback id {i}: named in neither register at {BASE}")
    issues = "\n".join(show(BASE, "docs/DESIGN-ISSUES.md") or [])
    dis = sorted(set(DI_NUM.findall(text)), key=lambda d: int(d[3:]))
    for d in dis:
        if not re.search(r"^\|\s*" + re.escape(d) + r"\s*\|", issues, re.M):
            fails.append(f"{d}: no row in docs/DESIGN-ISSUES.md at {BASE}")
    return fails, late, (len(ces), len(fbs), len(dis))


def on_line(lines, lo, hi, name):
    short = name.split(".")[-1]
    rx = r"(?<![\w'])" + re.escape(short) + r"(?![\w'])"
    return any(re.search(rx, ln) for ln in lines[lo - 1:hi])


def check(text, label):
    fails, obligations, external = [], [], []
    names = build_index()
    probe_names = set()
    spans = re.findall(r"`([^`\n]+)`", text)
    for span in spans:
        m = PATHLINE.match(span)
        if m and m.group(1).startswith("docs/research/") and m.group(1).endswith(".lean"):
            lines, _ = read_file(m.group(1))
            index_lines(lines or [], probe_names)
    counts = dict(paths=0, commits=0, digests=0, tags=0, idents=0, pairs=0, missing=0)
    for span in spans:
        if span in EXTERNAL_PATHS or span in EXTERNAL_COMMITS:
            external.append(span)
            continue
        if "*" in span and "/" in span and " " not in span:
            counts["paths"] += 1
            listing = run(["git", "ls-tree", "-r", "--name-only", BASE]).stdout.split()
            if not any(fnmatch.fnmatch(f, span) for f in listing):
                fails.append(f"glob {span}: matches no file at {BASE}")
            continue
        m = PATHLINE.match(span)
        if m or DIRPATH.match(span):
            counts["paths"] += 1
            path = m.group(1) if m else span
            lines, where = read_file(path)
            if lines is None:
                fails.append(f"path {span}: {where}")
            elif m and m.group(2):
                lo, hi = int(m.group(2)), int(m.group(3) or m.group(2))
                if not lines or hi > len(lines) or lo < 1 or lo > hi:
                    fails.append(f"line {span}: outside the file ({len(lines)} lines, {where})")
            continue
        if re.match(r"^[0-9a-f]{64}$", span):
            counts["digests"] += 1          # checked below when paired with a toolchain path
            continue
        if re.match(r"^[0-9a-f]{7,40}$", span):
            counts["commits"] += 1
            if run(["git", "cat-file", "-e", span + "^{commit}"]).returncode != 0 and \
               run(["git", "cat-file", "-e", span + "^{commit}"], cwd=PKG_DIR).returncode != 0:
                fails.append(f"commit {span}: not a commit of this repository or the package")
            continue
        if re.match(r"^v\d+\.\d+\.\d+$", span):
            counts["tags"] += 1
            pkg_tags = run(["git", "tag", "-l"], cwd=PKG_DIR).stdout.split()
            if span != TOOL_VERSION and span not in pkg_tags:
                fails.append(f"tag {span}: neither the toolchain ({TOOL_VERSION}) nor a package tag")
            continue
        if IDENT.match(span):
            counts["idents"] += 1
            short = span.split(".")[-1]
            if span in ALLOW_SET or span in names or short in names or span in probe_names \
                    or short in probe_names:
                continue
            fails.append(f"name {span}: not declared in the tree, the package or a cited probe")
    paired = set()
    for m in PAIR.finditer(text):
        lines, _ = read_file(m.group(2))
        lo, hi = int(m.group(3)), int(m.group(4) or m.group(3))
        if lines and hi <= len(lines) and on_line(lines, lo, hi, m.group(1)):
            paired.add(m.group(1))
    fails = [f for f in fails if not (f.startswith("name ") and f.split(" ")[1].rstrip(":") in paired)]
    for m in DIGEST_PAIR.finditer(text):
        lines, where = read_file(m.group(1))
        disk = os.path.join(TOOL_SRC, m.group(1))
        if lines is None or not os.path.isfile(disk):
            fails.append(f"digest {m.group(1)}: {where}")
            continue
        with open(disk, "rb") as f:
            got = hashlib.sha256(f.read()).hexdigest()
        if got != m.group(2):
            fails.append(f"digest {m.group(1)}: recorded {m.group(2)[:12]}…, toolchain has {got[:12]}…")
    for m in PAIR.finditer(text):
        counts["pairs"] += 1
        name, path = m.group(1), m.group(2)
        lo, hi = int(m.group(3)), int(m.group(4) or m.group(3))
        lines, where = read_file(path)
        if not lines:
            fails.append(f"pair {name} @ {path}:{lo}: file {where}")
            continue
        if not on_line(lines, lo, hi, name):
            fails.append(f"pair {name} @ {path}:{lo}{'-' + str(hi) if hi > lo else ''}: "
                         f"name not on the cited line ({where})")
            continue
        tail = "\n".join(lines[lo - 1:lo + 30])
        stop = tail.find(":=")
        if "ProofGraph.Obligation" in (tail[:stop] if stop >= 0 else tail):
            obligations.append(f"{name} @ {path}:{lo}")
    for m in MISSING.finditer(text):
        counts["missing"] += 1
        name = m.group(1)
        if tree_declared(name):
            fails.append(f"missing-claim {name}: declared in the tree at {BASE}, so not missing")
        at = PROBE_AT.search(m.group(2))
        if not at:
            fails.append(f"missing-claim {name}: names no probe `docs/research/...lean:n` that proves it")
            continue
        lines, where = read_file(at.group(1))
        n = int(at.group(2))
        if not lines or n > len(lines) or not on_line(lines, n, n, name):
            fails.append(f"missing-claim {name}: not at {at.group(1)}:{n} ({where})")
    # the Sources fields: every research path agrees with its tracked/untracked mark
    marks = 0
    for field in re.findall(r"- \*\*Sources\.\*\*(.*?)(?=\n- \*\*|\n\n|\Z)", text, re.S):
        for item in re.split(r";\s*", field):
            mark = re.search(r"\((un)?tracked", item)
            paths = re.findall(r"`(docs/research/[^`]+?)`", item)
            if not paths:
                continue
            if not mark:
                fails.append(f"source mark: no tracked/untracked mark for {paths[0]}")
                continue
            want_tracked = mark.group(1) is None
            for path in paths:
                marks += 1
                is_tracked = any(exists_at(rev, path) for rev in (BASE, "HEAD", TRACK))
                if is_tracked != want_tracked:
                    fails.append(f"source mark {path}: marked {'tracked' if want_tracked else 'untracked'}, "
                                 f"is {'tracked' if is_tracked else 'untracked'}")
    counts["marks"] = marks
    id_fails, late, (n_ce, n_fb, n_di) = check_ids(text)
    fails += id_fails
    summary = (f"{label}: {counts['paths']} file citations, {counts['commits']} commits, "
               f"{counts['digests']} digests, {counts['tags']} tags, {counts['idents']} identifiers, "
               f"{counts['pairs']} witness pairs, {counts['missing']} 'witness missing' claims, "
               f"{counts.get('marks', 0)} source marks, {n_ce} register ids ({len(late)} registered "
               f"after {BASE}, at {TRACK}), {n_fb} fallback ids, {n_di} DI numbers, "
               f"{len(external)} external pins; {len(fails)} failures; "
               f"{len(obligations)} witnesses are declared obligations")
    return fails, obligations, summary


RED = """
`src/Effect4/Laws/Program/NoSuchFile.lean:3`
`run_eq_ref` (`src/Effect4/Laws/Program/RuntimeR.lean:212`)
`definitely_not_a_declaration_xyz`
`src/Effect4/Laws/Program/RuntimeR.lean:999999`
`run_eq_ref` (witness missing at `dceae006`; a false claim of absence)
`M6Ledger.step_loop` (`src/Effect4/Laws/Program/Typed/Assembly.lean:278`)
`0123abcd` is not a commit
`not_a_probe_theorem` (witness missing at `dceae006`; proved in `docs/research/2026-10-01-formal-pass/algebra/probes/P1Coproduct.lean:85`)
| `Lean/Expr.lean` | `0000000000000000000000000000000000000000000000000000000000000000` |
`v9.9.9`
`E4-NOPE-CE-999` `NOPE-FB-NOTHING` and DI-999
`Ψ_S` (`src/Effect4/Laws/Program/Typed/Residual.lean:84`)
- **Sources.** `docs/research/2026-09-07-grill-agenda.md` §3 (untracked); `docs/research/2026-09-05-a4-reader-landing.md` §2 (tracked).

green controls, which must not fail:
`run_eq_ref` (`src/Effect4/Laws/Program/RuntimeR.lean:211`)
`sum_is_coproduct` (witness missing at `dceae006`; proved in `docs/research/2026-10-01-formal-pass/algebra/probes/P1Coproduct.lean:85`)
| `Lean/Environment.lean` | `ee364e4788ce0560c87f621eeb3c4c3dfec62e8db4e15e099fd80e6adc533b86` |
`v4.33.1` `v0.8.0` `Sched.lean:32-39` `docs/research/2026-09-07-lit-papers.md`
`E4-TYPED-CE-009` (registered after the base) `E4-SCHED-CE-004` `PROV-FB-KEY-FORGERY` DI-62
`Ψ_S` (`src/Effect4/Laws/Program/Typed/Residual.lean:83`)
- **Sources.** `docs/research/2026-09-30-model-probe/synthesis.md` §3 (tracked); `docs/research/2026-09-05-reification-effhol.md` (untracked).
"""
# Expected failures (17): a missing path; a wrong pair line; an unknown name; a line past the
# end; the false absence of `run_eq_ref` twice (declared in the tree; names no proving probe);
# a non-commit; `not_a_probe_theorem` twice (unknown name; not at the cited probe line); a
# wrong toolchain digest; an unknown tag; two wrong source marks (the grill agenda marked
# untracked, an untracked note marked tracked); an unknown register id, fallback id and DI
# number; a Unicode name on the wrong line (17). One obligation (`M6Ledger.step_loop`). The green
# lines must not fail.
RED_EXPECTED = 17


FIELDS = ("Decision", "Witnesses", "Refusals", "Sources", "Literature", "Status")
FIELD_RX = re.compile(r"^- \*\*(" + "|".join(FIELDS) + r")(?:\.\*\*|\*\*)")


def structure(text):
    """Every DB row ends in the six fields, in order; no line repeats the line before it."""
    fails = []
    lines = text.split("\n")
    heads = [i for i, ln in enumerate(lines) if ln.startswith("### DB-")]
    for k, h in enumerate(heads):
        name = lines[h].split(" ")[1]
        stop = heads[k + 1] if k + 1 < len(heads) else len(lines)
        stop = next((i for i in range(h + 1, stop) if lines[i].startswith("## ")), stop)
        row = lines[h + 1:stop]
        found = [(i, m.group(1)) for i, ln in enumerate(row) for m in [FIELD_RX.match(ln)] if m]
        got = [f for _, f in found]
        if got != list(FIELDS):
            fails.append(f"row {name}: fields {got}, want the six in order")
            continue
        for ln in row[found[0][0]:]:
            if ln.strip() and not FIELD_RX.match(ln) and not ln.startswith("  "):
                fails.append(f"row {name}: text after its fields begin: {ln[:60]!r}")
                break
    fence = False
    for i, ln in enumerate(lines):
        if ln.startswith("```"):
            fence = not fence
        if i and not fence and ln.strip() and not ln.lstrip().startswith("|") and ln == lines[i - 1]:
            fails.append(f"line {i + 1} repeats the line before it: {ln[:60]!r}")
    return fails


RED_STRUCTURE = """
### DB-97 — fields out of order and one missing

- **Decision.** a
- **Witnesses** (re-read at `dceae006`). b
- **Sources.** c
- **Refusals.** d
- **Status.** e

### DB-98 — prose after the fields

- **Decision.** a
- **Witnesses.** b
- **Refusals.** c
- **Sources.** d
- **Literature.** e
- **Status.** f

A paragraph that belongs above the fields.

### DB-99 — a green row, with a line repeated

- **Decision.** a
  the same continuation
  the same continuation
- **Witnesses.** b
- **Refusals.** c
- **Sources.** d
- **Literature.** e
- **Status.** f
"""
RED_STRUCTURE_EXPECTED = 3      # DB-97's fields; DB-98's paragraph; DB-99's repeated line


def drift(text, rev):
    """(moved, unchanged): where each tree `path:n[-m]` citation's text sits at rev, the path as
    the text writes it (a short path is followed by the file it resolves to)."""
    changed = set(run(["git", "diff", "--name-only", BASE, rev]).stdout.split())
    moved, same, seen = [], 0, set()
    for m in re.finditer(r"`([^`\s]+?):(\d+)(?:-(\d+))?`", text):
        path, lo = m.group(1), int(m.group(2))
        hi = int(m.group(3) or lo)
        if path.startswith(("git:", "Effects/", "Lean/")):
            continue                                   # pinned elsewhere: no drift
        lines, where = read_file(path)
        if lines is None or not where.startswith((f"tree {BASE}", f"tracked at {BASE}")):
            continue
        full = where.split(" via ")[-1] if " via " in where else path
        if full not in changed or (full, lo, hi) in seen:
            continue
        seen.add((full, lo, hi))
        new = show(rev, full)
        old = lines[lo - 1:hi]
        if new is not None and new[lo - 1:hi] == old:
            same += 1
            continue
        at = [] if new is None else \
            [i + 1 for i in range(len(new) - len(old) + 1) if new[i:i + len(old)] == old]
        span = f"{lo}" if hi == lo else f"{lo}-{hi}"
        to = "gone" if new is None else (
            ", ".join(f"{a}" if hi == lo else f"{a}-{a + hi - lo}" for a in at) or "text changed")
        moved.append(f"{path}:{span} -> {to}" + (f" ({full})" if full != path else ""))
    return moved, same


# one citation that moves at efcf1ae2 and one, in another file that changed, that does not
DRIFT_FIXTURE = "`src/Effect4/Program/Provision.lean:69` `src/Effect4/Laws/Program/DenoteR.lean:69`"
DRIFT_REV, DRIFT_EXPECTED = "efcf1ae2", ["src/Effect4/Program/Provision.lean:69 -> 71"]


def report(fails, obligations, summary, history_fails=()):
    print(summary)
    for f in fails:
        print("  FAIL", f)
    for f in history_fails:
        print("  STALE (history, text kept)", f)
    for o in obligations:
        print("  DECLARED (an obligation, not a proof)", o)


def main():
    global BASE
    if len(sys.argv) > 2 and sys.argv[1] == "--base":
        # rerun every check at another commit (for a drift report; the stated commit stays BASE)
        BASE = sys.argv[2]
        del sys.argv[1:3]
    if len(sys.argv) > 2 and sys.argv[1] == "--drift":
        rev = sys.argv[2]
        target = sys.argv[3] if len(sys.argv) > 3 else os.path.join(REPO, "docs", "DESIGN-BASIS.md")
        with open(target, encoding="utf-8") as f:
            text = f.read()
        cut = text.find(HISTORY_MARK)
        moved, same = drift(text if cut < 0 else text[:cut], rev)
        for line in moved:
            print("  MOVED", line)
        print(f"drift {BASE} -> {rev}: {len(moved)} line citations moved or changed, {same} unchanged "
              f"(citations into files that changed; the history appendix is not re-pinned)")
        sys.exit(0)
    if len(sys.argv) > 1 and sys.argv[1] == "--self-test":
        s_fails = structure(RED_STRUCTURE)
        for f in s_fails:
            print("  FAIL (structure)", f)
        s_ok = len(s_fails) == RED_STRUCTURE_EXPECTED and not any("DB-99: fields" in f for f in s_fails)
        print(f"structure control: {'as expected' if s_ok else 'NOT as expected'} ({len(s_fails)} "
              f"failures, expected {RED_STRUCTURE_EXPECTED})")
        d_moved, d_same = drift(DRIFT_FIXTURE, DRIFT_REV)
        d_ok = d_moved == DRIFT_EXPECTED and d_same == 1
        print(f"drift control: {'as expected' if d_ok else 'NOT as expected'} ({d_moved}, {d_same} unchanged; "
              f"expected {DRIFT_EXPECTED}, 1 unchanged)")
        fails, obligations, summary = check(RED, "red control")
        report(fails, obligations, summary)
        green = [f for f in fails if f.startswith((
            "pair run_eq_ref @ src/Effect4/Laws/Program/RuntimeR.lean:211", "name sum_is_coproduct",
            "missing-claim sum_is_coproduct", "digest Lean/Environment.lean", "tag v4.33.1",
            "tag v0.8.0", "path Sched.lean", "line Sched.lean", "path docs/research/2026-09-07-lit-papers.md",
            "source mark docs/research/2026-09-30-model-probe/synthesis.md",
            "source mark docs/research/2026-09-05-reification-effhol.md", "register id E4-TYPED-CE-009",
            "register id E4-SCHED-CE-004", "fallback id PROV-FB-KEY-FORGERY", "DI-62:",
            "pair Ψ_S @ src/Effect4/Laws/Program/Typed/Residual.lean:83:"))]
        ok = len(fails) == RED_EXPECTED and len(obligations) == 1 and not green and s_ok and d_ok
        print(f"red control: {'as expected' if ok else 'NOT as expected'} ({len(fails)} failures, "
              f"expected {RED_EXPECTED}; {len(obligations)} obligation, expected 1; "
              f"{len(green)} green failures, expected 0)")
        sys.exit(0 if ok else 1)
    target = sys.argv[1] if len(sys.argv) > 1 else os.path.join(REPO, "docs", "DESIGN-BASIS.md")
    with open(target, encoding="utf-8") as f:
        text = f.read()
    cut = text.find(HISTORY_MARK)
    body, history = (text, "") if cut < 0 else (text[:cut], text[cut:])
    fails, obligations, summary = check(body, os.path.relpath(target, REPO) + " (rows)")
    h_fails, h_obl, h_summary = check(history, "history appendix") if history else ([], [], "no history")
    report(fails, obligations, summary)
    print(h_summary)
    for f in h_fails:
        print("  STALE (history, text kept)", f)
    s_fails = structure(body)                # the history is kept as written: not checked
    print(f"structure: {sum(1 for ln in body.split(chr(10)) if ln.startswith('### DB-'))} rows; "
          f"{len(s_fails)} failures")
    for f in s_fails:
        print("  FAIL (structure)", f)
    sys.exit(1 if fails or s_fails else 0)


if __name__ == "__main__":
    main()
