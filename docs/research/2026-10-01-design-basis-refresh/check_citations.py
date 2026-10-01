#!/usr/bin/env python3
"""Check every citation in docs/DESIGN-BASIS.md against a stated commit.

Seat H of the 2026-10-01 landing (the DESIGN-BASIS refresh). No build, no generator: files
are read with `git show` and from disk. Run from anywhere:

  python3 check_citations.py [basis.md]   # exit 0 when every check outside the history passes
  python3 check_citations.py --self-test  # the red control: seeded defects must be reported
  python3 check_citations.py --base <rev> [basis.md]  # the same checks at another commit (drift)

Every backticked span of the basis is one of:
  * a file citation `path`, `path:n` or `path:n-m`. The file must exist and the lines lie
    inside it. Tree paths are read at BASE; `Effects/...` in the pinned `effects` package at
    PKG_REV; `git:<rev>:<path>` at <rev>; `docs/research/...` at BASE when tracked there, else
    at HEAD of this branch (notes this refresh force-adds), else on the main checkout's disk
    (untracked); `Lean/...` in the pinned Lean toolchain's sources; a bare rc.112 file
    (`Layer.ts:54`, `internal/effect.ts:726`) under `vendor/effect-4.0.0-rc.112/src/` at BASE;
    a short `.lean` path by its unique suffix under src/, Test/ or harness/.
  * a commit (7-40 hex digits): a commit of this repository or the package, or an external pin
    named below. A 64-hex SHA-256 next to a `Lean/...` path is recomputed from the toolchain.
  * a version tag: the toolchain's version or a tag of the package.
  * a single identifier: declared in the tree at BASE (src/, Test/, tools/, harness/), in the
    package, or in a research probe the basis cites; or on the allowlist with its reason.
Witness checks:
  * `` `name` (`path:n`) ``: the name is on line n of path (or inside n-m).
  * `` `name` (witness missing at `BASE`; ... `docs/research/....lean:n` ...) ``: the name is
    NOT declared in the tree at BASE, and it IS on line n of the named probe.
  * every witness pair whose declaration is a `ProofGraph.Obligation` is listed: a declared
    statement, not a proof; the text must call it "declared".
A failure inside the history appendix (after the heading `## History`) is reported as STALE:
that text is kept as written on its date and is not corrected; it does not fail the run.
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
        if exists_at("refactor/phase1-phase3", path.rstrip("/")):
            return (show("refactor/phase1-phase3", path) or []), "tracked on refactor/phase1-phase3"
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

# Names that are not declarations of this tree, each group with its reason.
ALLOW = {
    "Lean core or toolchain (v4.33.1), not a tree declaration": [
        "StateT", "EStateM", "ExceptT", "Except", "Expr", "Option", "Nat", "Bool", "String", "Prop",
        "Type", "Id", "Unit", "List", "Array", "Float", "Int", "Json", "Repr", "DecidableEq",
        "LawfulMonad", "Monad", "Function.Injective", "EStateM.run_throw", "Lean.collectAxioms",
        "collectAxioms", "WellFounded.fix", "WellFounded.Nat.fix", "decide", "aesop", "native_decide",
        "sorry", "propext", "Quot.sound", "Classical.choice", "partial", "unsafe", "abbrev", "Std.Do",
        "toOption", "theorem_wanted", "#proof_wanted", "Lean.Util.CollectAxioms", "implemented_by",
        "extern"],
    "rc.112 / TypeScript name (vendored source, not Lean)": [
        "Effect.provide", "Layer.provide", "Layer.merge", "Layer.mergeAll", "Layer.effect", "Layer.succeed",
        "Effect.service", "provideService", "setContext", "updateContext", "scheduleTask", "TestClock",
        "ClockImpl", "clearTimeout", "setTimeout", "setTime", "Effect.mapError", "Effect.catchReason",
        "SqlError", "SqlError.message", "SqlClient.withTransaction", "SqliteMigrator.layer",
        "KeyValueStore.get", "Option.fromNullable", "JSON.parse", "JSON.stringify", "Equal.equals",
        "Equal", "Statement.PrimitiveKind", "Headers", "File.Info", "SocketCloseError.code", "Schema.Int",
        "UniqueViolation", "AuthenticationError", "UnknownError", "InternalError", "PersistenceError",
        "constraint", "mergeAllEffect", "Latch.scheduleUnsafe", "TxRef", "Exit", "Cause", "Ref",
        "Deferred", "Queue", "Semaphore", "Pool", "PubSub", "Latch", "Mailbox", "Scope", "Layer",
        "Context", "Effect", "Fiber", "Stream", "Channel", "Schema", "Config", "Cache", "Effect.scoped",
        "HttpApiMiddleware.ApplyServices", "Layer.Layer", "Effect.Effect", "Exclude", "Duration",
        "Schedule", "Random", "number", "bigint", "Date", "Uint8Array", "string", "undefined", "null",
        "void", "_tag", "Schema.Struct", "Schema.Number", "catchTag", "retry", "timeout", "forEach",
        "all", "ApplyServices"],
    "the archived Flow route or an earlier commit (history)": [
        "Flow", "RawFlow", "CheckedFlow", "BlockId", "Behavior", "HHandler", "Refusal.failed",
        "interpretRef", "Observation.le", "loop_obs_mono", "run_obs_mono", "region_obs_mono",
        "runRegions_obs_mono", "Chain.stable", "loop_fuel_stable", "Chain.colimit",
        "Chain.colimit_below", "Chain.colimit_bound_mono", "Chain.colimit_eq_of_settled",
        "runColimitDefault", "run_fuelFor_finishes", "runRegionsColimit", "Frontier.fuel",
        "Effect4.Logic.wp_iff_wlp_and_total", "Effect4.Flow.wp_iff", "box_sound", "Flow.wlp_runDefault",
        "wp_runDefault", "build_total", "buildAll_total", "Construction", "ProgName", "LayerDesc",
        "LayerTable", "lower", "runOver", "noStr", "PolyFun", "FreeM", "Foldlab",
        "EffHOL", "runLoop_mono", "LoopMeans_unique", "denoteK", "Verified"],
    "prose or notation in code font, not a declaration": [
        "Σ_core", "Σ_app", "Σ", "Rep", "Work", "RowStep", "observe", "HostState", "HostVal",
        "ProfileRefusal", "boom", "B-print", "B-accept", "B-row", "B-tape", "Psq", "Logic", "or", "not",
        "and", "INV-TAPE-1", "INV-TAPE-2", "N_J", "N_S", "now", "scheduled", "broadcast", "signal",
        "sweep", "Task.wake", "J", "I", "subN", "Ψ_S", "Ψ_F", "Γ", "Π", "Ρ", "Θ", "inl", "inr",
        "ProfileData", "Binding", "LawfulSig", "AdmittedSig", "admitSig_ok_iff", "SigExtends",
        "SigProgram", "LocalLawful", "Fresh", "inhabited", "decode", "natToString", "Ty.record",
        "Ty.foreign", "Ty.app", "Ty.lit", "Err.value", "Val.eqAt", "fits_normalize", "fits_subN",
        "fits_join_left", "fits_join_right", "evalTerm_fits", "denoteR_typed", "savedOk_mono",
        "stackAccepts_mono", "IteratorProtocol", "LoopProtocol", "HookLaws", "Conv", "ExitHasTy",
        "Denote.ExitHasTy", "EnvFits", "HandleWorld", "Ty.Normal", "uninhabited", "emptyColumn",
        "Deadlocked", "ReplayRel", "lower_refines_build", "FitsN", "running", "stuck", "CTy",
        "effect4-host-session-v3", "keyed-v3", "wp", "wlp", "total"],
    "another runtime's name, cited for its role (Eio, Riot)": ["In_transition", "Delay"],
    "a planned operation named by a ruling, not in the tree": ["abandon"],
}
ALLOW_SET = {n: why for why, names in ALLOW.items() for n in names}

IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.!?₀-₉]*$")
PATHLINE = re.compile(r"^((?:git:[0-9a-f]+\^?:)?[A-Za-z0-9_./@+-]+?\.(?:lean|md|ts|toml|json|py|sh|tsv|ml|mjs|txt))"
                      r"(?::(\d+)(?:-(\d+))?)?$")
DIRPATH = re.compile(r"^(?:src|Test|docs|harness|tools|scripts|vendor|ocaml|generated)/[A-Za-z0-9_./-]*/?$")
NAME = r"[A-Za-z_][A-Za-z0-9_'.!?₀-₉]*"
PAIR = re.compile(r"`(" + NAME + r")`\s*\(`([^`]+?):(\d+)(?:-(\d+))?`")
MISSING = re.compile(r"`(" + NAME + r")`[^`\n]{0,40}\(witness missing at `" + BASE + r"`([^)]*)\)")
PROBE_AT = re.compile(r"`(docs/research/[^`]+?\.lean):(\d+)`")
DIGEST_PAIR = re.compile(r"`(Lean/[^`]+)`\s*\|\s*`([0-9a-f]{64})`")


def on_line(lines, lo, hi, name):
    short = name.split(".")[-1]
    rx = r"(?<![A-Za-z0-9_'])" + re.escape(short) + r"(?![A-Za-z0-9_'])"
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
                is_tracked = any(exists_at(rev, path) for rev in (BASE, "HEAD", "refactor/phase1-phase3"))
                if is_tracked != want_tracked:
                    fails.append(f"source mark {path}: marked {'tracked' if want_tracked else 'untracked'}, "
                                 f"is {'tracked' if is_tracked else 'untracked'}")
    counts["marks"] = marks
    summary = (f"{label}: {counts['paths']} file citations, {counts['commits']} commits, "
               f"{counts['digests']} digests, {counts['tags']} tags, {counts['idents']} identifiers, "
               f"{counts['pairs']} witness pairs, {counts['missing']} 'witness missing' claims, "
               f"{counts.get('marks', 0)} source marks, "
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
- **Sources.** `docs/research/2026-09-07-grill-agenda.md` §3 (untracked); `docs/research/2026-09-08-build-path.md` §2 (tracked).

green controls, which must not fail:
`run_eq_ref` (`src/Effect4/Laws/Program/RuntimeR.lean:211`)
`sum_is_coproduct` (witness missing at `dceae006`; proved in `docs/research/2026-10-01-formal-pass/algebra/probes/P1Coproduct.lean:85`)
| `Lean/Environment.lean` | `ee364e4788ce0560c87f621eeb3c4c3dfec62e8db4e15e099fd80e6adc533b86` |
`v4.33.1` `v0.8.0` `Sched.lean:32-39` `docs/research/2026-09-07-lit-papers.md`
- **Sources.** `docs/research/2026-09-30-model-probe/synthesis.md` §3 (tracked); `docs/research/2026-09-05-reification-effhol.md` (untracked).
"""
# Expected failures (11): a missing path; a wrong pair line; an unknown name; a line past the
# end; the false absence of `run_eq_ref` twice (declared in the tree; names no proving probe);
# a non-commit; `not_a_probe_theorem` twice (unknown name; not at the cited probe line); a
# wrong toolchain digest; an unknown tag; two wrong source marks (the grill agenda marked
# untracked, the build path marked tracked). One obligation (`M6Ledger.step_loop`). The green
# lines must not fail.
RED_EXPECTED = 13


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
    if len(sys.argv) > 1 and sys.argv[1] == "--self-test":
        fails, obligations, summary = check(RED, "red control")
        report(fails, obligations, summary)
        green = [f for f in fails if f.startswith((
            "pair run_eq_ref @ src/Effect4/Laws/Program/RuntimeR.lean:211", "name sum_is_coproduct",
            "missing-claim sum_is_coproduct", "digest Lean/Environment.lean", "tag v4.33.1",
            "tag v0.8.0", "path Sched.lean", "line Sched.lean", "path docs/research/2026-09-07-lit-papers.md",
            "source mark docs/research/2026-09-30-model-probe/synthesis.md",
            "source mark docs/research/2026-09-05-reification-effhol.md"))]
        ok = len(fails) == RED_EXPECTED and len(obligations) == 1 and not green
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
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
