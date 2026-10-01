#!/usr/bin/env python3
"""Count Schema usage by kind in three file sets (seat EFFECT, data probe, 2026-10-01).

Each category is one regular expression; a count is the number of non-overlapping matches
(the same number `grep -oP '<pattern>' FILE | wc -l` prints). Counts are raw source text:
comments and strings are not stripped, so a JSDoc example counts. `.d.ts` files are excluded
from the usage counts and reported separately.

Sets:
  probe    the five model-probe programs p1..p5 (docs/research/2026-09-30-model-probe/programs/ts)
  dogfood  the dogfood idiomatic and library sources under docs/research (listed in DOGFOOD below)
  corpus   Foldlab's 34-project corpus (/Users/pooks/Dev/foldlab/corpus), file list and Effect
           generation taken from the ingest census (docs/research/ingest-delivery/commit-4/census/
           files.jsonl); split by generation v4 / v3 / pre-v3 / none.

Usage: python3 count_schema.py > counts.log
"""
import json
import os
import re
import sys
from collections import Counter, defaultdict

ROOT = "/Users/pooks/Dev/lean4-effect4"
CORPUS = "/Users/pooks/Dev/foldlab/corpus"
CENSUS = ROOT + "/docs/research/ingest-delivery/commit-4/census/files.jsonl"

# (name, pattern). Spellings are rc.112's (v4) unless the name says v3.
CATEGORIES = [
    ("any Schema.<member>", r"\bSchema\.[A-Za-z_]\w*"),
    # records and nominal records
    ("Schema.Struct(", r"\bSchema\.Struct\("),
    ("Schema.TaggedStruct(", r"\bSchema\.TaggedStruct\("),
    ("Schema.Class / TaggedClass", r"\bSchema\.(?:Class|TaggedClass)\b"),
    ("Schema.Record(", r"\bSchema\.Record\("),
    ("Schema.Array / NonEmptyArray(", r"\bSchema\.(?:Array|NonEmptyArray)\("),
    ("Schema.Tuple(", r"\bSchema\.Tuple\("),
    # sums and literals
    ("Schema.Union(", r"\bSchema\.Union\("),
    ("Schema.TaggedUnion / toTaggedUnion", r"\bSchema\.(?:TaggedUnion|toTaggedUnion)\b"),
    ("Schema.Literal / Literals(", r"\bSchema\.(?:Literal|Literals)\("),
    ("Schema.Enum / Enums(", r"\bSchema\.(?:Enum|Enums)\("),
    # errors
    ("Schema.TaggedError (and beta spelling TaggedErrorClass)", r"\bSchema\.TaggedError(?:Class)?\b"),
    ("Schema.Error (and beta spelling ErrorClass)", r"\bSchema\.(?:Error|ErrorClass)\b"),
    ("Data.TaggedError(", r"\bData\.TaggedError\("),
    ("SchemaError (v4 error payload)", r"\bSchemaError\b"),
    ("ParseError / ParseResult. (v3 payload)", r"\bParseError\b|\bParseResult\."),
    # optional fields and defaults
    ("optional field: optional / optionalKey / optionalWith", r"\bSchema\.(?:optional|optionalKey|optionalWith)\("),
    ("nullable: NullOr / UndefinedOr / NullishOr", r"\bSchema\.(?:NullOr|UndefinedOr|NullishOr)\("),
    ("defaults: with*Default*", r"\bSchema\.with(?:Constructor|Decoding)Default\w*\(|\bdefault\s*:\s*\(\)\s*=>"),
    # running a schema
    ("decodeUnknown*(", r"\bSchema\.decodeUnknown\w*\("),
    ("decode<Suffix>( (run, v4 and v3)", r"\bSchema\.decode(?:Effect|Sync|Exit|Option|Result|Promise|Either)\("),
    ("bare Schema.decode( (v4: transformation; v3: run)", r"\bSchema\.decode\("),
    ("encodeUnknown* / encode<Suffix>( (run)", r"\bSchema\.encode(?:Unknown\w*|Effect|Sync|Exit|Option|Result|Promise|Either)\("),
    ("bare Schema.encode( (v4: transformation; v3: run)", r"\bSchema\.encode\("),
    ("is / asserts / validate*(", r"\bSchema\.(?:is|asserts|validate\w*)\("),
    # JSON
    ("JSON.parse(", r"\bJSON\.parse\("),
    ("Schema JSON: fromJsonString / parseJson / UnknownFromJsonString / toCodecJson",
     r"\bSchema\.(?:fromJsonString|parseJson|UnknownFromJsonString|toCodecJson)\b"),
    ("response .json()", r"\.json\(\)"),
    # filters (refinements)
    ("v4 filter: Schema.is<X> (not the guards isSchema/isSchemaError) / makeFilter / check / refine",
     r"\bSchema\.(?:is(?!Schema\b|SchemaError\b)[A-Z]\w*|makeFilter\w*|check|refine)\b"),
    ("brand: Schema.brand / fromBrand", r"\bSchema\.(?:brand|fromBrand)\b"),
    ("v4 .check( call", r"\.check\("),
    ("refined leaf: Int / Finite / NonEmptyString / Trimmed / Positive / NonNegative / UUID / ULID",
     r"\bSchema\.(?:Int|Finite|NonEmptyString|NonEmptyTrimmedString|Trimmed|Positive|PositiveInt|NonNegative|NonNegativeInt|Natural|UUID|ULID|Char)\b"),
    ("v3 filter: filter / pattern / minLength / maxLength / int / positive / nonNegative / greaterThan* / lessThan* / between / nonEmptyString",
     r"\bSchema\.(?:filter|pattern|minLength|maxLength|length|int|positive|nonNegative|negative|greaterThan\w*|lessThan\w*|between|nonEmptyString|startsWith|endsWith|includes|multipleOf|finite)\("),
    # transformations
    ("transformation combinator: decodeTo / encodeTo / transform / transformOrFail / compose / link / middleware* / catch*",
     r"\bSchema\.(?:decodeTo|encodeTo|transform|transformOrFail|transformLiteral|transformLiterals|compose|link|middlewareDecoding|middlewareEncoding|catchDecoding\w*|catchEncoding\w*)\b"),
    ("SchemaTransformation. / SchemaGetter.", r"\bSchema(?:Transformation|Getter)\."),
    ("named codec schema: Schema.<X>From<Y>", r"\bSchema\.[A-Z]\w*From[A-Z]\w*\b"),
    # recursion
    ("Schema.suspend(", r"\bSchema\.suspend\("),
    # leaves
    ("primitive leaf: String / Number / Boolean / BigInt", r"\bSchema\.(?:String|Number|Boolean|BigInt)\b"),
    ("declaration leaf: Date / DateTimeUtc / Duration / Option / Either / Result / Exit / Cause / Redacted / URL / Uint8Array",
     r"\bSchema\.(?:Date|DateTimeUtc|Duration|Option|Either|Result|Exit|Cause|Redacted|URL|Uint8Array|BigDecimal)\b"),
    ("Unknown / Any / Json", r"\bSchema\.(?:Unknown|Any|Json|MutableJson)\b"),
    ("schema as a type-level parameter: Schema.Schema / Codec / Top / Decoder / Encoder / Constraint",
     r"\bSchema\.(?:Schema|Codec|Top|Decoder|Encoder|Constraint)\b"),
]
COMPILED = [(name, re.compile(pat)) for name, pat in CATEGORIES]

PROBE = [
    "docs/research/2026-09-30-model-probe/programs/ts/p1-http-cache.ts",
    "docs/research/2026-09-30-model-probe/programs/ts/p2-handler-layers.ts",
    "docs/research/2026-09-30-model-probe/programs/ts/p3-worker-queue.ts",
    "docs/research/2026-09-30-model-probe/programs/ts/p4-rate-limiter.ts",
    "docs/research/2026-09-30-model-probe/programs/ts/p5-ledger-service.ts",
]

# The dogfood sources an Effect user wrote (not the printer's image, not run harnesses):
# dogfoods 1-3's idiomatic files and dogfood 6's foreign library sources and controls.
DOGFOOD = [
    "docs/research/2026-09-15-dogfood-1-evidence/idiomatic_rate_limiter.ts",
    "docs/research/2026-09-15-dogfood-2-evidence/idiomatic_job_queue.ts",
    "docs/research/2026-09-15-dogfood-3-evidence/idiomatic_session_cache.ts",
    "docs/research/2026-09-16-dogfood-6-evidence/library-counter.ts",
    "docs/research/2026-09-16-dogfood-6-evidence/library-quicklook.ts",
    "docs/research/2026-09-16-dogfood-6-evidence/library-run.ts",
]


def count_file(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as f:
            text = f.read()
    except OSError:
        return None
    return {name: len(rx.findall(text)) for name, rx in COMPILED}


def project_dir(project_id):
    """Census ids are folder names with `_` as `-` and repeated `-` collapsed."""
    for name in os.listdir(CORPUS):
        norm = re.sub(r"-+", "-", name.replace("_", "-").lower())
        if norm == project_id:
            return os.path.join(CORPUS, name)
    return None


LIBRARY_RX = re.compile(r"(^|/)repos/effect/")
TEST_RX = re.compile(r"(^|/)(test|tests|typetest|__tests__)/|\.(test|spec|tst)\.tsx?$")
GEN_NAME_RX = re.compile(r"(^|/)Generated\.ts$|\.gen\.ts$|\.generated\.ts$")
GEN_HEAD_RX = re.compile(r"generated|do not edit|@generated", re.I)


def subset_of(relpath, abspath):
    """library (a vendored copy of the Effect repository) / generated / test / app."""
    if LIBRARY_RX.search(relpath):
        return "library"
    if GEN_NAME_RX.search(relpath):
        return "generated"
    try:
        with open(abspath, encoding="utf-8", errors="replace") as f:
            head = f.read(400)
    except OSError:
        head = ""
    if GEN_HEAD_RX.search(head):
        return "generated"
    if TEST_RX.search(relpath):
        return "test"
    return "app"


def report(title, rows):
    """rows: list of (label, project, counts)."""
    occ = Counter()
    files = Counter()
    projects = defaultdict(set)
    for label, project, counts in rows:
        for name, n in counts.items():
            if n:
                occ[name] += n
                files[name] += 1
                projects[name].add(project)
    print(f"## {title}: {len(rows)} files, {len({p for _, p, _ in rows})} projects")
    print(f"{'category':<100} {'occurrences':>11} {'files':>7} {'projects':>8}")
    for name, _ in CATEGORIES:
        print(f"{name:<100} {occ[name]:>11} {files[name]:>7} {len(projects[name]):>8}")
    print()
    return occ, files, projects


def per_file(title, rows):
    print(f"## {title}: per file, nonzero categories")
    for label, project, counts in rows:
        nz = {k: v for k, v in counts.items() if v}
        print(f"- {label}: {json.dumps(nz)}")
    print()


def main():
    os.chdir(ROOT)
    probe = [(p, "probe", count_file(p)) for p in PROBE]
    per_file("probe (a)", probe)
    report("probe (a)", probe)

    dog = [(p, p.split("/")[2], count_file(p)) for p in DOGFOOD]
    per_file("dogfood (b)", dog)
    report("dogfood (b)", dog)

    by_gen = defaultdict(list)
    dts = Counter()
    missing = 0
    dirs = {}
    with open(CENSUS) as f:
        for line in f:
            r = json.loads(line)
            proj = r["project"]
            if proj not in dirs:
                dirs[proj] = project_dir(proj)
            gen = r.get("generation") or "none"
            if r["file"].endswith(".d.ts"):
                dts[gen] += 1
                continue
            if dirs[proj] is None:
                missing += 1
                continue
            abspath = os.path.join(dirs[proj], r["file"])
            counts = count_file(abspath)
            if counts is None:
                missing += 1
                continue
            sub = subset_of(r["file"], abspath)
            by_gen[(gen, sub)].append((r["file"], proj, counts))
    print(f"corpus: .d.ts excluded by generation {dict(dts)}; unreadable or unmapped {missing}")
    print(f"corpus: unmapped projects {[p for p, d in dirs.items() if d is None]}")
    print()
    print("corpus subsets (files):", {f"{g}/{u}": len(v) for (g, u), v in sorted(by_gen.items())})
    print()
    for key in [("v4", "app"), ("v4", "test"), ("v4", "generated"), ("v4", "library"), ("v3", "app"), ("v3", "test"),
                ("v3", "generated"), ("pre-v3", "app"), ("none", "app")]:
        gen = "/".join(key)
        occ, files, projects = report(f"corpus (c) generation {gen}", by_gen[key])
        if key not in [("v4", "app"), ("v3", "app")]:
            continue
        # per-project breakdown for the categories the brief names
        named = ["Schema.Struct(", "Schema.Class / TaggedClass", "Schema.TaggedError (and beta spelling TaggedErrorClass)", "Data.TaggedError(",
                 "decodeUnknown*(", "decode<Suffix>( (run, v4 and v3)", "bare Schema.decode( (v4: transformation; v3: run)",
                 "JSON.parse(", "Schema JSON: fromJsonString / parseJson / UnknownFromJsonString / toCodecJson",
                 "v4 filter: Schema.is<X> (not the guards isSchema/isSchemaError) / makeFilter / check / refine",
                 "transformation combinator: decodeTo / encodeTo / transform / transformOrFail / compose / link / middleware* / catch*",
                 "Schema.suspend(", "Schema.Union(", "Schema.Literal / Literals(",
                 "optional field: optional / optionalKey / optionalWith", "SchemaError (v4 error payload)"]
        perproj = defaultdict(Counter)
        for _, proj, counts in by_gen[key]:
            for name in named:
                perproj[proj][name] += counts[name]
        print(f"### corpus {gen}: per project (named categories; occurrences)")
        short = ["Struct", "Class", "S.TaggedErr", "D.TaggedErr", "decUnknown", "decSuffix", "decode(", "JSON.parse",
                 "S.JSON", "filter", "transform", "suspend", "Union", "Literal", "optional", "SchemaError"]
        print(f"{'project':<40} " + " ".join(f"{s:>11}" for s in short))
        for proj in sorted(perproj, key=lambda p: -sum(perproj[p].values())):
            if sum(perproj[proj].values()) == 0:
                continue
            print(f"{proj:<40} " + " ".join(f"{perproj[proj][n]:>11}" for n in named))
        print()


if __name__ == "__main__":
    main()
