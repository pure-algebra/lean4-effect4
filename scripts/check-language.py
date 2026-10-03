#!/usr/bin/env python3
"""check-language: the controlled-English findings of the documents (docs/core/controlled-english.md).

The rules and the dictionary are read from the specification itself (scripts/lib/language.py);
there is no second list. Five modes:

    check-language.py                  the report: findings per document, by rule; exit 0
    check-language.py --show FILE...   every finding in the named files; exit 0
    check-language.py --strict FILE... every finding in the named files; exit 1 if there is one
    check-language.py --fix FILE...    rewrite the files' line citations by declaration name
                                       (scripts/lib/line_cites.py) and list each one left; exit 0
    check-language.py --self-test      the red and green controls below; exit 1 if one fails

The documents are the ones `make check-docs` reads (scripts/lib/doc_refs.py: every tracked
Markdown file that is not history); `--show` and `--strict` also take any other Markdown file.
`make check-language` runs `--strict` on the specification and AGENTS.md.
"""
from __future__ import annotations

import argparse
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts" / "lib"))

import language  # noqa: E402
from doc_refs import doc_files  # noqa: E402
from language import RULES, SPEC, Checker, Finding, load_spec  # noqa: E402
from line_cites import ZERO, Fixer, git_blame, git_file_at, git_first_seen  # noqa: E402


# The controls: each Markdown fixture, checked against the real dictionary, must give exactly the
# findings listed (rule names, in order). A red control proves its rule can fail; a green one
# proves an exemption holds. `anchor` fixtures are checked as if they were the specification.
SENTENCE_25 = " ".join(["word"] * 24) + " end."
CONTROLS: list[tuple[str, str, str, list[str]]] = [
    ("red: a descriptive sentence over 25 words", "doc", SENTENCE_25.replace("end.", "word end."), ["length"]),
    ("green: a descriptive sentence of 25 words", "doc", SENTENCE_25, []),
    ("red: a procedural sentence over 20 words", "doc", "Run " + " ".join(["word"] * 19) + " now.", ["length"]),
    ("green: a procedural sentence of 20 words", "doc", "Run " + " ".join(["word"] * 18) + " now.", []),
    ("green: a table cell is exempt from length", "doc", "| a | b |\n| --- | --- |\n| " + SENTENCE_25 * 2 + " | x |", []),
    ("green: a code span counts as one word", "doc", "Read " + " ".join(["`a b c d`"] * 19) + ".", []),
    ("red: a trust word with no qualifier", "doc", "The checker is sound.", ["qualifier"]),
    ("green: a trust word with its judgment in code", "doc", "The checker is sound against `HasTy`.", []),
    ("green: a trust word named by an identifier", "doc", "check_sound makes the checker sound.", []),
    ("green: a trust word in double quotes is a mention", "doc", "Never write \"sound\" alone.", []),
    ("green: a trust word in a fenced block", "doc", "```text\nThe checker is sound.\n```", []),
    ("green: a trust word in a blockquote", "doc", "> The checker is sound.", []),
    ("green: a trust word in an italic title", "doc", "Wright and Felleisen, *A Syntactic Approach to Type Soundness*.", []),
    ("red: a trust word in italic emphasis", "doc", "The checker is *sound*.", ["qualifier"]),
    ("red: complete in its everyday sense", "doc", "The slice is complete.", ["qualifier"]),
    ("red: a first use of syntax with no qualifier", "doc", "The syntax is first-order. The syntax is data.", ["qualifier"]),
    ("green: a first use of syntax qualified", "doc", "The program syntax is first-order. The syntax is data.", []),
    ("red: admission with no qualifier", "doc", "Canonicality does not certify admission.", ["qualifier"]),
    ("green: reply admission", "doc", "Reply admission refuses the stale reply.", []),
    ("green: a qualifier inside a hyphenated compound", "doc", "It leaves the typed-module admission open.", []),
    ("green: a qualifier elsewhere in a table row", "doc", "| claim | role |\n| --- | --- |\n| `fits_subN` | preservation |", []),
    ("red: a word not to use", "doc", "The host table is empty.", ["avoid"]),
    ("green: a word not to use, quoted", "doc", "The dictionary replaces \"host table\".", []),
    ("green: a word not to use, in code", "doc", "The field `host table` is empty.", []),
    ("red: a filler word", "doc", "We do it in order to win.", ["filler"]),
    ("red: a line in a citation of a repository file", "doc", "See `src/Effect4/Program/Eff.lean:12`.", ["line-cite"]),
    ("red: a bare line after a repository path", "doc", "See `src/Effect4/Program/Eff.lean:12` and `:14`.", ["line-cite", "line-cite"]),
    ("green: a line of the pinned vendored source", "doc", "See `vendor/effect-4.0.0-rc.112/src/Effect.ts:10`.", []),
    ("green: a line of the Lean toolchain", "doc", "See `Lean/Parser/Do.lean:52`.", []),
    ("red: an anchor whose file lacks the name", "spec",
     "| " + " | ".join(language.DICT_HEADER) + " |\n| --- | --- | --- | --- | --- | --- |\n"
     "| **x** | y | `no_such_name_xyz` (`src/Effect4/Program/Eff.lean`) | — | — | — |", ["anchor"]),
    ("green: an anchor whose file holds the name", "spec",
     "| " + " | ".join(language.DICT_HEADER) + " |\n| --- | --- | --- | --- | --- | --- |\n"
     "| **x** | y | `Eff` (`src/Effect4/Program/Eff.lean`) | — | — | — |", []),
]


# The fix controls run the fixer over a fake tree and history. `src/A.lean` was cited at `r1`;
# at `r2` (the citing line's last edit, unless a control says otherwise) the file is unchanged, and
# at `r3` it has moved, so line 3 lies in `bar`. At `r1` line 3 lay in `foo`'s body, line 6 in
# `bar`'s docstring, line 9 in `gone` (declared nowhere at HEAD) and line 11 in `moved_one`
# (declared at HEAD in `src/C.lean` only). `src/Other/A.lean` shares the file name.
FIX_OLD = ("theorem foo : True := by\n  trivial\n  -- line 3\n\n/-- `bar`'s docstring,\n"
           "  line 6 -/\ntheorem bar : True := trivial\n\ntheorem gone : True := trivial\n\n"
           "theorem moved_one : True := trivial\n")
FIX_MOVED = "theorem bar : True := by\n  trivial\n  -- line 3\n\ntheorem foo : True := trivial\n"
FIX_FILES = {
    (ZERO, "src/A.lean"): "theorem bar : True := trivial\n\ntheorem foo : True := by\n  trivial\n",
    ("r1", "src/A.lean"): FIX_OLD, ("r2", "src/A.lean"): FIX_OLD, ("r3", "src/A.lean"): FIX_MOVED,
    (ZERO, "src/C.lean"): "theorem moved_one : True := trivial\n",
    (ZERO, "src/Other/A.lean"): "theorem foo2 : True := trivial\n",
}
FIX_SEEN = {("A.lean", 3): "r1", ("A.lean", 4): "r1", ("A.lean", 6): "r1", ("A.lean", 9): "r1",
            ("A.lean", 11): "r1"}
FIX_CONTROLS: list[tuple[str, str, str, int, str]] = [
    ("green: a named citation drops its line", "`foo` (`src/A.lean:3`)", "`foo` (`src/A.lean`)", 0, "r2"),
    ("green: a paragraph that names the declaration keeps only the path",
     "`foo` holds (`src/A.lean:3`).", "`foo` holds (`src/A.lean`).", 0, "r2"),
    ("green: a docstring line belongs to the declaration below it",
     "`bar` is cited at `src/A.lean:6`.", "`bar` is cited at `src/A.lean`.", 0, "r2"),
    ("green: a range names the declaration that holds most of its lines",
     "`bar` spans `src/A.lean:4-7`.", "`bar` spans `src/A.lean`.", 0, "r2"),
    ("green: a shared file name resolves to the file that declares the name",
     "`foo2` (`A.lean:1`)", "`foo2` (`src/Other/A.lean`)", 0, "r2"),
    ("green: a shared file name resolves to the file whose history holds the line",
     "`foo` is at `A.lean:3-4`.", "`foo` is at `src/A.lean`.", 0, "r2"),
    ("green: a continuation named in place takes the file",
     "`foo` (`src/A.lean:3`) and `bar` (`:6`)", "`foo` (`src/A.lean`) and `bar` (`src/A.lean`)", 0, "r2"),
    ("green: a continuation the paragraph names is dropped with its separator",
     "`foo` and `bar` hold (`src/A.lean:3`, `:6`).", "`foo` and `bar` hold (`src/A.lean`).", 0, "r2"),
    ("green: a moved declaration is cited at its new file",
     "`moved_one` holds (`src/A.lean:11`).", "`moved_one` holds (`src/C.lean`).", 0, "r2"),
    ("green: the paragraph confirms what the line's last edit contradicts",
     "`foo` again (`src/A.lean:3`).", "`foo` again (`src/A.lean`).", 0, "r3"),
    ("red: history alone is listed, not written", "See `src/A.lean:3`.", "See `src/A.lean:3`.", 1, "r2"),
    ("red: a line edited after the cited file moved is left", "See `src/A.lean:3`.", "See `src/A.lean:3`.", 1, "r3"),
    ("red: a declaration gone from the tree is left",
     "`gone` holds (`src/A.lean:9`).", "`gone` holds (`src/A.lean:9`).", 1, "r2"),
    ("red: a named citation whose name is gone is left",
     "`zap` (`src/A.lean:3`)", "`zap` (`src/A.lean:3`)", 1, "r2"),
    ("red: a span with more than the citation is left",
     "See `src/A.lean:3: foo`.", "See `src/A.lean:3: foo`.", 1, "r2"),
]


def fix_self_test() -> int:
    tracked = ["src/A.lean", "src/C.lean", "src/Other/A.lean", "control.md"]
    failed = 0
    for title, text, expected, left, blamed in FIX_CONTROLS:
        fixer = Fixer(tracked, lambda path: not path.startswith("vendor/"),
                      lambda revision, path: FIX_FILES.get((revision, path)),
                      lambda doc, blamed=blamed: {1: blamed},
                      lambda name, line: FIX_SEEN.get((name, line)))
        got, result = fixer.fix("control.md", text)
        ok = got == expected and len(result.left) == left
        failed += not ok
        if not ok:
            print(f"FAIL {title}: expected {expected!r} with {left} left, got {got!r} with "
                  f"{len(result.left)} left {[entry.reason for entry in result.left]}")
    return failed


def self_test(checker: Checker) -> int:
    failed = 0
    for title, kind, text, expected in CONTROLS:
        path = SPEC if kind == "spec" else "control.md"
        got = [f.rule for f in checker.check(path, text)]
        ok = got == expected
        failed += not ok
        if not ok:
            print(f"FAIL {title}: expected {expected}, got {got}")
    failed += fix_self_test()
    total = len(CONTROLS) + len(FIX_CONTROLS)
    print(f"{'PASS' if not failed else 'FAIL'} check-language self-test: "
          f"{total - failed} of {total} controls")
    return 1 if failed else 0


def fix(checker: Checker, names: list[str]) -> int:
    """Rewrite the named documents' line citations in place; list what is left, and why."""
    fixer = Fixer(checker.tracked, checker.ours, git_file_at(ROOT), git_blame(ROOT), git_first_seen(ROOT))
    rewritten = 0
    left = []
    for name in names:
        path = relative(name)
        text = (ROOT / path).read_text(errors="replace")
        fixed, result = fixer.fix(path, text)
        if fixed != text:
            (ROOT / path).write_text(fixed)
        rewritten += result.rewritten
        left += result.left
    for entry in left:
        print(f"{entry.doc}:{entry.line}: left `{entry.cite}`: {entry.reason}")
    print(f"check-language --fix: {rewritten} citation(s) rewritten, {len(left)} left, in {len(names)} file(s)")
    return 0


def relative(name: str) -> str:
    path = Path(name).resolve()
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return name


def findings_of(checker: Checker, names: list[str]) -> dict[str, list[Finding]]:
    out: dict[str, list[Finding]] = {}
    for name in names:
        path = relative(name)
        out[path] = checker.check(path, (ROOT / path).read_text(errors="replace"))
    return out


def report(results: dict[str, list[Finding]], top: int) -> None:
    total = Counter(f.rule for found in results.values() for f in found)
    flagged = sum(1 for found in results.values() if found)
    print(f"check-language: {sum(total.values())} finding(s) in {flagged} of {len(results)} documents"
          f" ({', '.join(f'{rule} {total[rule]}' for rule in RULES)})")
    rows = sorted(((len(found), path, Counter(f.rule for f in found)) for path, found in results.items() if found),
                  key=lambda row: (-row[0], row[1]))
    if top:
        rows = rows[:top]
    print(f"  {'total':>5} " + " ".join(f"{rule:>9}" for rule in RULES) + "  document")
    for count, path, by_rule in rows:
        print(f"  {count:>5} " + " ".join(f"{by_rule[rule]:>9}" for rule in RULES) + f"  {path}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--strict", nargs="+", metavar="FILE", help="fail on any finding in these files")
    mode.add_argument("--show", nargs="+", metavar="FILE", help="print every finding in these files")
    mode.add_argument("--fix", nargs="+", metavar="FILE", help="rewrite these files' line citations")
    mode.add_argument("--self-test", action="store_true", help="run the red and green controls")
    parser.add_argument("--rule", choices=RULES, help="with --show: only this rule")
    parser.add_argument("--top", type=int, default=0, help="the report: only the N documents with most findings")
    args = parser.parse_args()
    if args.rule and not args.show:
        parser.error("--rule filters what --show prints; strict mode and the report judge every rule")

    spec = load_spec(ROOT)
    if not spec.entries:
        print(f"FAIL check-language: no dictionary entries read from {SPEC}")
        return 1
    checker = Checker(ROOT, spec)

    if args.self_test:
        return self_test(checker)
    if args.fix:
        return fix(checker, args.fix)

    if args.show or args.strict:
        results = findings_of(checker, args.show or args.strict)
        shown = [f for found in results.values() for f in found if not args.rule or f.rule == args.rule]
        for finding in shown:
            print(finding.render())
        if args.strict:
            if shown:
                print(f"FAIL check-language: {len(shown)} finding(s) in {len(results)} strict document(s)")
                return 1
            everything = findings_of(checker, doc_files(ROOT))
            others = sum(len(v) for k, v in everything.items() if k not in results)
            print(f"PASS check-language: no finding in {', '.join(results)}; the other documents carry "
                  f"{others} finding(s) (report: python3 scripts/check-language.py)")
        return 0

    report(findings_of(checker, doc_files(ROOT)), args.top)
    return 0


if __name__ == "__main__":
    sys.exit(main())
