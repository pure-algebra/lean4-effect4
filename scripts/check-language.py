#!/usr/bin/env python3
"""check-language: the controlled-English findings of the documents (docs/core/controlled-english.md).

The rules and the dictionary are read from the specification itself (scripts/lib/language.py);
there is no second list. Four modes:

    check-language.py                  the report: findings per document, by rule; exit 0
    check-language.py --show FILE...   every finding in the named files; exit 0
    check-language.py --strict FILE... every finding in the named files; exit 1 if there is one
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


def self_test(checker: Checker) -> int:
    failed = 0
    for title, kind, text, expected in CONTROLS:
        path = SPEC if kind == "spec" else "control.md"
        got = [f.rule for f in checker.check(path, text)]
        ok = got == expected
        failed += not ok
        if not ok:
            print(f"FAIL {title}: expected {expected}, got {got}")
    print(f"{'PASS' if not failed else 'FAIL'} check-language self-test: "
          f"{len(CONTROLS) - failed} of {len(CONTROLS)} controls")
    return 1 if failed else 0


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
