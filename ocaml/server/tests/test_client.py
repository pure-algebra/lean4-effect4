#!/usr/bin/env python3
"""The `effect4d` test client.

Drives the daemon through every request type on every committed golden of the four families
this checkout carries, on the committed avatar-face outputs of the `fiber`, `extra` and
`corpus` sets, and on a slice of the adversarial corpus -- on all three hosts (bytecode,
native, js_of_ocaml under node) -- and asserts:

  rows-vs-golden      the daemon's `run` rows are the committed golden's rows, under every
                      mask of `generated/traces/masks.tsv`, by the daemon's own `diff` and by
                      this client's independent comparison;
  rows-vs-avatar      the daemon's `run` rows are byte-identical to the avatar's own
                      committed face (`ocaml/avatar/out/*.ocaml.tsv`), which is
                      what says the daemon has not changed the avatar's behaviour;
  hosts-agree         the three hosts produce identical rows for every program;
  determinism         the same program run twice in one daemon session gives identical rows,
                      which is what the global-state reset of `E4d_reset` is for;
  every-request       `version`, `pins`, `families`, `masks`, `programs`, `load`, `inspect`,
                      `run`, `step`, `diff`, `explain`, `why`, `reachable`, `budget`, `reset`
                      and `ping` all answer `ok` with the fields the README's schema names.

Transports: the daemon is driven as a live newline-delimited JSON session on all three hosts
-- a request written, its answer read back, one process for the whole run. The native host is
additionally driven over TCP, and the node host additionally in one batch (every request
written, stdin closed, answers read in order), which is the sharpest check that the avatar's
module-level state is reset between requests.

Usage: test_client.py [--build DIR] [--corpus N] [--hosts native,bytecode,jsoo] [-v]
"""
import argparse
import json
import os
import shutil
import socket
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SERVER = os.path.dirname(HERE)
# <repo>/ocaml/server/tests -> <repo>/ocaml -> <repo>. The estate lived under
# `workshop/OCaml5/` until 2026-09-04; these three are the paths that moved with it.
OCAML = os.path.dirname(SERVER)
REPO = os.path.abspath(os.path.join(OCAML, ".."))
AVATAR = os.path.join(OCAML, "avatar")
AVATAR_OUT = os.path.join(AVATAR, "out")
# The goldens and the mask table left main with the Flow route (75002d7); the copies under
# server/generated/traces/ are the archived ones (tools/vendor-archived-inputs.sh).
TRACES = os.environ.get("W2_TRACES") or next(
    (d for d in (os.path.join(REPO, "generated", "traces"),
                 os.path.join(SERVER, "generated", "traces")) if os.path.isdir(d)),
    os.path.join(SERVER, "generated", "traces"))
# Where the three hosts are, when `--build` is not given: dune's own output (`dune build`
# from `ocaml/`). `W2_BUILD` overrides and names that directory itself -- the shell build's
# `W2_BUILD` named a scratch root and the hosts sat in its `build/` subdirectory; the shell
# build is reference-only (BUILD-DUNE.md §1) and `dune-test.sh` passes `--build` anyway.
DEFAULT_BUILD = os.environ.get(
    "W2_BUILD", os.path.join(OCAML, "_build", "default", "server"))
# The node host: `W2_NODE` is the node command (default `node`; under WSL the Windows
# `node.exe` works through interop), `W2_JSOO` the path of effect4d.js as that command
# sees it (a Windows path for node.exe).
NODE = os.environ.get("W2_NODE", "node").split()

GOLDEN_FAMILIES = ["ref", "deferred", "scope", "layer"]
# The classified divergences the daemon compiles in (avatar/corpus/known-divergences.tsv):
# program -> class. The table is the avatar's and may be empty (it is, since seat F3 closed
# `hYieldStorm`), so the `diff` check below reads its expectation off the table.
KNOWN_DIVERGENCES = os.path.join(AVATAR, "corpus", "known-divergences.tsv")


def known_divergences():
    table = {}
    if os.path.exists(KNOWN_DIVERGENCES):
        for line in open(KNOWN_DIVERGENCES):
            cells = line.rstrip("\n").split("\t")
            if len(cells) >= 2 and cells[0] and not cells[0].startswith("#"):
                table[cells[0]] = cells[1]
    return table
EVENT_KINDS = {"op", "answer", "failed", "decide", "enter", "leave", "finalizer", "done",
               "frontier"}


# --- the estate's comparison, independently of the daemon's --------------------------

def parse_trace(text):
    header, rows = {}, []
    for line in text.split("\n"):
        if line == "":
            continue
        cells = line.split("\t")
        if cells[0] in EVENT_KINDS:
            rows.append(line)
        elif cells[0].startswith("#"):
            continue
        else:
            header[cells[0]] = "\t".join(cells[1:])
    return header, rows


def parse_masks(text):
    masks = []
    for line in text.split("\n"):
        cells = line.split("\t")
        if cells[0] != "mask":
            continue
        flags = [c == "1" for c in cells[2:]]
        ops, answers, decisions, regions, finalizers, outcome, frontier = flags
        masks.append((cells[1], {"op": ops, "answer": answers, "failed": answers,
                                 "decide": decisions, "enter": regions, "leave": regions,
                                 "finalizer": finalizers, "done": outcome,
                                 "frontier": frontier}))
    return masks


def project(mask, rows):
    return [r for r in rows if mask[r.split("\t")[0]]]


MASKS = parse_masks(open(os.path.join(TRACES, "masks.tsv")).read())


# --- transports -----------------------------------------------------------------------

class Interactive:
    """A live NDJSON session on a POSIX host."""

    def __init__(self, argv):
        self.proc = subprocess.Popen(argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.PIPE, text=True, bufsize=1)

    def ask(self, request):
        self.proc.stdin.write(json.dumps(request) + "\n")
        self.proc.stdin.flush()
        line = self.proc.stdout.readline()
        if not line:
            raise RuntimeError("daemon closed the pipe: " + self.proc.stderr.read())
        return json.loads(line)

    def close(self):
        try:
            self.proc.stdin.close()
        except Exception:
            pass
        self.proc.wait(timeout=30)


def batch_session(argv, requests):
    """One process, many requests: the check that the daemon resets its state between them."""
    payload = "".join(json.dumps(r) + "\n" for r in requests)
    result = subprocess.run(argv, input=payload, capture_output=True, text=True, timeout=600)
    if result.returncode != 0:
        raise RuntimeError("batch failed: %s" % result.stderr[:400])
    return [json.loads(line) for line in result.stdout.strip().split("\n") if line.strip()]


class Tcp:
    def __init__(self, argv, port):
        self.proc = subprocess.Popen(argv + ["--tcp", str(port)], stderr=subprocess.PIPE,
                                     text=True)
        deadline = time.time() + 10
        while time.time() < deadline:
            try:
                self.sock = socket.create_connection(("127.0.0.1", port), timeout=5)
                break
            except OSError:
                time.sleep(0.05)
        else:
            raise RuntimeError("effect4d --tcp never accepted a connection")
        self.file = self.sock.makefile("rw")

    def ask(self, request):
        self.file.write(json.dumps(request) + "\n")
        self.file.flush()
        return json.loads(self.file.readline())

    def close(self):
        try:
            self.sock.close()
        finally:
            self.proc.terminate()
            self.proc.wait(timeout=10)


# --- the checks -------------------------------------------------------------------------

class Counts:
    def __init__(self):
        self.checks = 0
        self.failures = []
        self.by_name = {}

    def check(self, ok, name, detail=""):
        self.checks += 1
        self.by_name[name] = self.by_name.get(name, 0) + 1
        if not ok:
            self.failures.append("%s: %s" % (name, detail))
        return ok


def golden_files():
    out = []
    for family in GOLDEN_FAMILIES:
        directory = os.path.join(TRACES, family)
        if not os.path.isdir(directory):
            continue
        for name in sorted(os.listdir(directory)):
            if name.endswith(".tsv"):
                out.append((family, name[:-4], os.path.join(directory, name)))
    return out


def avatar_faces(prefix):
    out = []
    if not os.path.isdir(AVATAR_OUT):
        return out
    for name in sorted(os.listdir(AVATAR_OUT)):
        if name.startswith(prefix + ".") and name.endswith(".ocaml.tsv"):
            program = name[len(prefix) + 1:-len(".ocaml.tsv")]
            out.append((prefix, program, os.path.join(AVATAR_OUT, name)))
    return out


def corpus_faces(limit):
    directory = os.path.join(AVATAR_OUT, "corpus")
    if not os.path.isdir(directory):
        return []
    names = sorted(n for n in os.listdir(directory) if n.endswith(".ocaml.tsv"))
    return [("corpus", n[:-len(".ocaml.tsv")], os.path.join(directory, n))
            for n in names[:limit]]


def compare_masked(counts, label, expected_rows, actual_rows):
    for name, mask in MASKS:
        want = project(mask, expected_rows)
        got = project(mask, actual_rows)
        counts.check(want == got, "rows-under-mask",
                     "%s mask %s: %d expected, %d actual, first difference at %s"
                     % (label, name, len(want), len(got),
                        next((i for i in range(max(len(want), len(got)))
                              if i >= len(want) or i >= len(got) or want[i] != got[i]), "-")))


def exercise_program(session, counts, label, request, expected_rows, verbose):
    """`run`, `diff`, `why`, `explain`, `step`, `reachable`, `budget` on one program."""
    answer = session.ask(dict(request, request="run", expect=expected_rows))
    if not counts.check(answer.get("ok"), "run-ok", "%s %s" % (label, answer.get("error"))):
        return None
    rows = answer["rows"]
    counts.check(answer.get("agree") is True, "run-agrees-with-reference",
                 "%s %s" % (label, json.dumps(answer.get("verdicts"))[:400]))
    compare_masked(counts, label, expected_rows, rows)
    counts.check(rows == expected_rows, "rows-identical",
                 "%s: %d vs %d rows" % (label, len(expected_rows), len(rows)))

    # every response carries the golden's header fields
    header = answer.get("headerFields", {})
    for field in ("format", "face", "program", "tape", "rules", "pin", "generator", "inputs"):
        counts.check(field in header, "header-field", "%s missing %s" % (label, field))
    counts.check(header.get("face") == "ocaml", "header-face", label)
    counts.check(any(line.startswith("pin\teffects\t") for line in answer.get("header", [])),
                 "header-pin", label)

    # diff: the daemon's own port of compare.py
    diff = session.ask({"request": "diff", "left": expected_rows, "right": rows,
                        "program": request.get("program", "")})
    counts.check(diff.get("ok") and diff.get("agree") is True, "diff-agrees",
                 "%s %s" % (label, json.dumps(diff.get("verdicts"))[:300]))

    # why: no divergence against its own reference
    why = session.ask(dict(request, request="why", reference=expected_rows))
    counts.check(why.get("ok") and why["why"].get("diverges") is False, "why-no-divergence",
                 "%s %s" % (label, json.dumps(why.get("why", {}))[:300]))

    # explain: every service row names at least one avatar arm, and the arm cites Lean
    explain = session.ask(dict(request, request="explain"))
    if counts.check(explain.get("ok"), "explain-ok", "%s %s" % (label, explain.get("error"))):
        counts.check(len(explain["rows"]) == len(rows), "explain-row-count", label)
        service_rows = [r for r in explain["rows"] if r["kind"] in ("op", "answer", "failed")]
        unarmed = [r["row"] for r in service_rows if not r["arms"]]
        counts.check(not unarmed, "explain-every-row-has-an-arm",
                     "%s: %s" % (label, unarmed[:3]))
        # How far the citation chain reaches is reported as a number, not asserted: seat
        # W1's checkpoint-1 store cases carry no Lean citation, so a `ref` or `scope` run
        # resolves to an avatar arm and no further. What is asserted is that the daemon's own
        # count agrees with the rows it sent.
        # "cited" means the arm resolves to a Lean *site*: a declaration, or a citation
        # token that resolved. An `unresolved` token (an rc.112 or harness line the Lean file
        # does not carry) is not a site.
        cited = [r for r in service_rows
                 if any(a["leanDeclarations"] or any(c["sites"] for c in a["citations"])
                        for a in r["arms"])]
        summary = explain["citations"]
        counts.check(summary["serviceRows"] == len(service_rows)
                     and summary["withArm"] == len([r for r in service_rows if r["arms"]])
                     and summary["withLeanSite"] == len(cited),
                     "explain-citation-count-is-honest",
                     "%s %s vs %d/%d/%d" % (label, summary, len(service_rows),
                                            len([r for r in service_rows if r["arms"]]),
                                            len(cited)))
        if label.startswith("avatar fiber."):
            counts.check(not service_rows or cited, "explain-fiber-arms-cite-lean", label)

    # step: a snapshot at rounds 0 and at rounds 1, and the full run
    for rounds in (0, 1, 1000):
        step = session.ask(dict(request, request="step", rounds=rounds))
        if counts.check(step.get("ok"), "step-ok", "%s %s" % (label, step.get("error"))):
            machine = step["machine"]
            counts.check(isinstance(machine.get("fibers"), list) and machine["fibers"],
                         "step-has-fibers", label)
            fiber = machine["fibers"][0]
            for field in ("id", "status", "frame", "observers", "children", "dispatcher",
                          "pending", "currentOpCount", "exit"):
                counts.check(field in fiber, "step-fiber-field", "%s %s" % (label, field))
            counts.check("control" in fiber["frame"], "step-continuation-status", label)
            counts.check("buckets" in fiber["dispatcher"], "step-dispatcher-buckets", label)
    counts.check(step.get("complete") in (True, False), "step-complete-flag", label)

    reach = session.ask(dict(request, request="reachable", rounds=1000))
    if counts.check(reach.get("ok"), "reachable-ok", "%s %s" % (label, reach.get("error"))):
        r = reach["reachable"]
        for field in ("fibers", "resumable", "armed", "observersPending", "finished"):
            counts.check(field in r, "reachable-field", "%s %s" % (label, field))
        for f in r["fibers"]:
            counts.check("resumable" in f and "parkedOn" in f, "reachable-per-fiber", label)

    budget = session.ask(dict(request, request="budget"))
    if counts.check(budget.get("ok"), "budget-ok", "%s %s" % (label, budget.get("error"))):
        b = budget["budget"]
        for field in ("maxOpsBeforeYield", "yields", "injections", "perFiber"):
            counts.check(field in b, "budget-field", "%s %s" % (label, field))

    if verbose:
        print("  %-44s %3d rows  ok" % (label, len(rows)))
    return rows


def properties(session, counts):
    """README §0: the wire, run/step and streaming properties, one check each."""
    # W1: a reply carries the request's id back
    answer = session.ask({"id": "w1", "request": "ping"})
    counts.check(answer.get("id") == "w1", "W1-id-echoed", str(answer.get("id")))
    answer = session.ask({"request": "ping"})
    counts.check(answer.get("id") is None, "W1-no-id-is-null", str(answer.get("id")))

    # W2: a replayed request returns the recorded reply and changes nothing. `load` is the
    # sharpest case: answered twice it would otherwise mint two program ids.
    first = session.ask({"id": "w2-load", "request": "load", "source": "fixture",
                         "family": "ref", "program": "makeGet"})
    second = session.ask({"id": "w2-load", "request": "load", "source": "fixture",
                          "family": "ref", "program": "makeGet"})
    counts.check(first == second, "W2-replay-is-identical", "%s vs %s" % (first, second))
    third = session.ask({"id": "w2-load-b", "request": "load", "source": "fixture",
                         "family": "ref", "program": "makeGet"})
    counts.check(third["programId"] != first["programId"], "W2-a-new-id-is-a-new-request",
                 "%s vs %s" % (third["programId"], first["programId"]))

    # W3: replies in request order. The pipeline below is answered in the order sent.
    order = [session.ask({"id": "w3-%d" % i, "request": "ping"})["id"] for i in range(5)]
    counts.check(order == ["w3-%d" % i for i in range(5)], "W3-replies-in-order", str(order))

    # W5: the journal is bounded at 64; the 66th distinct id evicts the first, so a replay of
    # the first is answered afresh -- which for `load` means a new program id.
    for i in range(66):
        session.ask({"id": "w5-%d" % i, "request": "ping"})
    replayed = session.ask({"id": "w2-load", "request": "load", "source": "fixture",
                            "family": "ref", "program": "makeGet"})
    counts.check(replayed["programId"] != first["programId"], "W5-journal-is-bounded",
                 "%s vs %s" % (replayed["programId"], first["programId"]))

    # R2: `step` is prefix-closed in `rounds` and NOT in `fuel`.
    program = {"source": "fixture", "family": "fiber",
               "program": "raceImmediateSuccessStopsLaunch", "tape": "0:1,1:0"}
    by_rounds = [session.ask(dict(program, id="r2-%d" % r, request="step", rounds=r))["rowsSoFar"]
                 for r in range(6)]
    prefix_closed = all(by_rounds[i] == by_rounds[i + 1][:len(by_rounds[i])]
                        for i in range(len(by_rounds) - 1))
    counts.check(prefix_closed, "R2-step-prefix-closed-in-rounds",
                 str([len(x) for x in by_rounds]))
    fuel_program = {"source": "fixture", "family": "fiber",
                    "program": "parentInterruptDuringChildWait", "tape": "0:0,1:0"}
    by_fuel = [len(session.ask(dict(fuel_program, id="r2f-%d" % f, request="step", fuel=f,
                                    rounds=1000))["rowsSoFar"])
               for f in range(1, 6)]
    counts.check(any(by_fuel[i] > by_fuel[i + 1] for i in range(len(by_fuel) - 1)),
                 "R2-fuel-is-not-monotone-as-documented", str(by_fuel))

    # S1, S2, S5: FIFO, at most once, explicit terminator.
    opened = session.ask({"id": "s-open", "request": "run", "source": "fixture",
                          "family": "scope", "program": "lifo", "chunk": 2})
    counts.check("stream" in opened and "first" in opened, "S-run-opens-a-stream",
                 str(opened.get("error")))
    counts.check("rows" not in opened, "S-streamed-run-omits-inline-rows",
                 str(list(opened.keys())))
    stream = opened["stream"]["stream"]
    chunks = opened["first"]["items"][:]
    counts.check(opened["first"]["cursor"] == 0, "S1-first-chunk-is-zero", str(opened["first"]))
    replay = session.ask({"id": "s-replay", "request": "pull", "stream": stream, "cursor": 0})
    counts.check(replay["pull"]["error"]["kind"] == "chunk-already-delivered",
                 "S2-at-most-once-per-chunk", str(replay["pull"]))
    ahead = session.ask({"id": "s-ahead", "request": "pull", "stream": stream, "cursor": 5})
    counts.check(ahead["pull"]["error"]["kind"] == "out-of-order-pull", "S1-fifo",
                 str(ahead["pull"]))
    cursor = 1
    terminal = None
    for _ in range(20):
        item = session.ask({"id": "s-pull-%d" % cursor, "request": "pull", "stream": stream,
                            "cursor": cursor})["pull"]
        if "error" in item:
            break
        if not item["more"]:
            terminal = item.get("terminal")
            break
        chunks.extend(item["items"])
        cursor = item["next"]
    counts.check(terminal is not None, "S5-explicit-terminator", str(terminal))
    whole = session.ask({"id": "s-whole", "request": "run", "source": "fixture",
                         "family": "scope", "program": "lifo"})
    counts.check(chunks == whole["rows"][:len(chunks)], "S-stream-rows-are-the-run-rows",
                 "%d streamed, %d inline" % (len(chunks), len(whole["rows"])))

    # S3: the bound on open streams is enforced, not exceeded.
    session.ask({"id": "s-reset", "request": "reset"})
    errors = []
    for i in range(10):
        answer = session.ask({"id": "s3-%d" % i, "request": "run", "source": "fixture",
                              "family": "scope", "program": "lifo", "chunk": 2})
        if not answer.get("ok"):
            errors.append(answer["error"]["kind"])
    counts.check("too-many-streams" in errors, "S3-open-stream-bound-enforced", str(errors))
    listed = session.ask({"id": "s3-list", "request": "streams"})
    counts.check(listed["open"] <= listed["max"], "S3-open-never-exceeds-max",
                 "%d/%d" % (listed["open"], listed["max"]))
    session.ask({"id": "s3-reset", "request": "reset"})

    # the schema answers the alphabet and the properties
    schema = session.ask({"id": "schema", "request": "schema"})
    counts.check(len(schema["requests"]) >= 15, "schema-lists-the-requests",
                 str(len(schema["requests"])))
    counts.check(all(set(r) >= {"name", "kind", "requestTy", "answerTy", "errorTy", "params"}
                     for r in schema["requests"]), "schema-rows-are-OpSpec-shaped", "")
    counts.check(len(schema["properties"]) >= 10, "schema-lists-the-properties",
                 str(len(schema["properties"])))
    counts.check(all(set(p) == {"code", "statement", "how", "theoremShape"}
                     for p in schema["properties"]), "schema-properties-carry-a-theorem-shape",
                 "")


def run_host(host, argv, counts, corpus_limit, verbose, interactive):
    session = Interactive(argv)
    assert interactive
    rows_by_program = {}
    try:
        # --- the request types that name no program
        for what in ("ping", "version", "pins", "families", "masks", "programs"):
            answer = session.ask({"request": what, "id": what})
            counts.check(answer.get("ok"), "%s-ok" % what, str(answer.get("error")))
            counts.check(answer.get("protocol") == "effect4d/1", "protocol", what)
            counts.check(answer.get("id") == what, "id-echo", what)
        version = session.ask({"request": "version"})
        # `Sys.backend_type` names the js_of_ocaml host `js_of_ocaml`, not `jsoo`.
        expected_host = {"jsoo": "js_of_ocaml"}.get(host, host)
        counts.check(version["host"] == expected_host, "host-name",
                     "%s vs %s" % (version["host"], expected_host))
        counts.check(len(version["pin"]["effects"]) == 40, "pin-is-a-commit", version["pin"])
        counts.check(len(version["inputs"]) >= 10, "pins-lists-inputs", len(version["inputs"]))
        families = session.ask({"request": "families"})
        counts.check(len(families["families"]) == 5, "five-families",
                     [f["family"] for f in families["families"]])
        for family in families["families"]:
            counts.check(family["operations"], "family-has-operations", family["family"])
            counts.check(family["source"], "family-cites-its-source", family["family"])

        # an unknown request and an unknown program are errors, not crashes
        bad = session.ask({"request": "nonesuch"})
        counts.check(bad.get("ok") is False and bad["error"]["kind"] == "unknown-request",
                     "unknown-request-is-an-error", str(bad))
        bad = session.ask({"request": "run", "source": "fixture", "family": "ref",
                           "program": "nonesuch"})
        counts.check(bad.get("ok") is False, "unknown-program-is-an-error", str(bad))

        # --- the committed goldens
        for family, program, path in golden_files():
            text = open(path).read()
            header, expected = parse_trace(text)
            loaded = session.ask({"request": "load", "source": "golden", "text": text,
                                  "family": family})
            if not counts.check(loaded.get("ok"), "load-ok",
                                "%s.%s %s" % (family, program, loaded.get("error"))):
                continue
            counts.check(loaded["program"] == "%s.%s" % (family, program), "load-names-program",
                         loaded.get("program"))
            inspect = session.ask({"request": "inspect", "programId": loaded["programId"]})
            if counts.check(inspect.get("ok"), "inspect-ok", program):
                spec = inspect["inspect"]
                for field in ("operations", "alphabet", "roots", "family", "program"):
                    counts.check(field in spec, "inspect-field", "%s %s" % (program, field))
                counts.check(spec["alphabet"]["rowKinds"], "inspect-alphabet", program)
            rows = exercise_program(session, counts, "golden %s.%s" % (family, program),
                                    {"programId": loaded["programId"], "program": program},
                                    expected, verbose)
            if rows is not None:
                rows_by_program["%s.%s" % (family, program)] = rows

        # --- the committed avatar faces: fiber, extra, and a slice of the corpus
        for prefix in ("fiber", "extra"):
            for family, program, path in avatar_faces(prefix):
                header, expected = parse_trace(open(path).read())
                request = {"source": "fixture", "family": family, "program": program,
                           "tape": header.get("tape", ""), "program_name": program}
                request = {"source": "fixture", "family": family, "program": program,
                           "tape": header.get("tape", "")}
                rows = exercise_program(session, counts, "avatar %s.%s" % (family, program),
                                        request, expected, verbose)
                if rows is not None:
                    rows_by_program["%s.%s" % (family, program)] = rows

        for _family, program, path in corpus_faces(corpus_limit):
            header, expected = parse_trace(open(path).read())
            request = {"source": "corpus", "program": program}
            rows = exercise_program(session, counts, "corpus %s" % program, request, expected,
                                    verbose)
            if rows is not None:
                rows_by_program["corpus.%s" % program] = rows
            inspect = session.ask({"request": "inspect", "source": "corpus", "program": program})
            if counts.check(inspect.get("ok"), "inspect-corpus-ok", program):
                spec = inspect["inspect"]
                counts.check(spec["form"] == "corpus", "inspect-corpus-form", program)
                counts.check(spec["main"], "inspect-corpus-has-main", program)
                counts.check("usedOperations" in spec, "inspect-corpus-operations", program)

        # --- the stated properties (README §0), one check each
        properties(session, counts)

        # --- a real divergence: `why` finds the first differing row and the events
        # around it. The reference is the golden with one answer altered, so the divergence
        # is one this client planted and can name.
        planted = ["op\tmake\t7", "answer\tmake\t0", "op\tget\t0", "answer\tget\t99",
                   'done\t{"success":99}']
        answer = session.ask({"request": "why", "source": "fixture", "family": "ref",
                              "program": "makeGet", "reference": planted})
        if counts.check(answer.get("ok"), "why-planted-ok", str(answer.get("error"))):
            w = answer["why"]
            counts.check(w["diverges"] is True, "why-finds-the-divergence", str(w)[:200])
            counts.check(w["expected"] == "answer\tget\t99" or
                         w["expected"] == 'done\t{"success":99}',
                         "why-names-the-expected-row", str(w.get("expected")))
            counts.check(w["actual"] in ("answer\tget\t7", 'done\t{"success":7}'),
                         "why-names-the-actual-row", str(w.get("actual")))
            counts.check(w["eventsUpToDifference"], "why-carries-the-event-trace",
                         str(len(w.get("eventsUpToDifference", []))))
            counts.check(w["buckets"] >= 1 and w["granularity"] in
                         ("flush-round", "drive-command", "coarse"),
                         "why-states-its-granularity", w.get("granularity"))
        # `diff` reports the same divergence, and the classified table is consulted: for a
        # program the table classifies, the class comes back; for one it does not (every
        # program, when the table is empty), `classified` is null.
        known = known_divergences()
        classified_program = next(iter(known), "cAwaitAllTwoGenerations")
        d = session.ask({"request": "diff", "left": planted,
                         "right": ["op\tmake\t7", "answer\tmake\t0", "op\tget\t0",
                                   "answer\tget\t7", 'done\t{"success":7}'],
                         "program": classified_program})
        counts.check(d["agree"] is False, "diff-reports-a-divergence", str(d)[:200])
        if classified_program in known:
            counts.check(d["classified"] is not None and
                         d["classified"]["class"] == known[classified_program],
                         "diff-reads-the-classified-table", str(d.get("classified")))
        else:
            counts.check(d["classified"] is None, "diff-reads-the-classified-table",
                         "table has no rows; classified=%s" % d.get("classified"))

        # --- determinism: the same program twice in one session
        first = session.ask({"request": "run", "source": "fixture", "family": "layer",
                             "program": "releaseOrder"})
        second = session.ask({"request": "run", "source": "fixture", "family": "layer",
                              "program": "releaseOrder"})
        counts.check(first.get("rows") == second.get("rows"), "determinism-in-one-session",
                     "%s vs %s" % (first.get("rows"), second.get("rows")))

        # --- reset clears the loaded table
        counts.check(session.ask({"request": "reset"}).get("ok"), "reset-ok", "")
    finally:
        session.close()
    return rows_by_program


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--build", default=DEFAULT_BUILD)
    parser.add_argument("--corpus", type=int, default=20)
    parser.add_argument("--hosts", default="bytecode,native,jsoo")
    parser.add_argument("-v", "--verbose", action="store_true")
    args = parser.parse_args()

    found = shutil.which("ocamlrun")
    ocaml_bin = os.environ.get("OCAML5_BIN") or (os.path.dirname(found) if found else "")
    if not ocaml_bin:
        sys.exit("no ocamlrun on the PATH: enter the switch "
                 "(eval $(opam env --switch=effect4)) or set OCAML5_BIN")
    jsoo = os.environ.get("W2_JSOO", os.path.join(args.build, "effect4d.js"))
    hosts = {
        "bytecode": ([os.path.join(ocaml_bin, "ocamlrun"),
                      os.path.join(args.build, "effect4d.byte")], True),
        "native": ([os.path.join(args.build, "effect4d.native")], True),
        "jsoo": (NODE + [jsoo], True),
    }

    counts = Counts()
    per_host = {}
    for host in args.hosts.split(","):
        argv, interactive = hosts[host]
        print("=== host %s (%s)" % (host, "interactive" if interactive else "batch"))
        started = time.time()
        per_host[host] = run_host(host, argv, counts, args.corpus, args.verbose, interactive)
        print("    %d programs, %.1fs" % (len(per_host[host]), time.time() - started))

    # --- the three hosts agree
    names = sorted(set().union(*[set(rows) for rows in per_host.values()])) if per_host else []
    for name in names:
        values = [per_host[h].get(name) for h in per_host]
        counts.check(all(v == values[0] for v in values), "hosts-agree", name)

    # --- one process, many requests: the reset check on the transport that batches
    node_argv = NODE + [jsoo]
    if "jsoo" in args.hosts.split(","):
        requests = [{"request": "run", "source": "fixture", "family": "layer",
                     "program": "releaseOrder"} for _ in range(3)]
        requests += [{"request": "run", "source": "fixture", "family": "scope",
                      "program": "lifo"}]
        requests += [{"request": "run", "source": "fixture", "family": "layer",
                      "program": "releaseOrder"}]
        answers = batch_session(node_argv, requests)
        counts.check(len(answers) == 5, "batch-answers-every-request", len(answers))
        counts.check(answers[0]["rows"] == answers[1]["rows"] == answers[2]["rows"]
                     == answers[4]["rows"], "batch-state-is-reset",
                     [a["rows"] for a in answers])

    # --- TCP on the native host
    native = os.path.join(args.build, "effect4d.native")
    if os.path.exists(native) and "native" in args.hosts.split(","):
        tcp = Tcp([native], 47311)
        try:
            answer = tcp.ask({"request": "run", "source": "fixture", "family": "ref",
                              "program": "makeGet"})
            counts.check(answer.get("ok"), "tcp-ok", str(answer.get("error")))
            counts.check(answer["rows"][-1] == 'done\t{"success":7}', "tcp-rows",
                         str(answer.get("rows")))
        finally:
            tcp.close()

    print()
    print("checks: %d" % counts.checks)
    for name in sorted(counts.by_name):
        print("  %-38s %d" % (name, counts.by_name[name]))
    if counts.failures:
        print()
        print("FAILURES: %d" % len(counts.failures))
        for failure in counts.failures[:40]:
            print("  " + failure)
        sys.exit(1)
    print("PASS")


if __name__ == "__main__":
    main()
