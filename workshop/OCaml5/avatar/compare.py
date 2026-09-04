#!/usr/bin/env python3
"""Compare a face's TSV with the Lean golden under every mask.

A transcription of `effect4-tools/packages/harness/trace.mjs`'s `parseGolden`, `parseMasks`,
`keeps`, `project` and the comparison loop, so the avatar's third face is judged by exactly
the rule the estate's own gate applies -- without editing `harness/trace` or `scripts`.
"""
import argparse
import os
import sys

EVENT_KINDS = {"op", "answer", "failed", "decide", "enter", "leave", "finalizer", "done",
               "frontier"}


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
        masks.append({"name": cells[1], "op": ops, "answer": answers, "failed": answers,
                      "decide": decisions, "enter": regions, "leave": regions,
                      "finalizer": finalizers, "done": outcome, "frontier": frontier})
    return masks


def project(mask, rows):
    return [r for r in rows if mask[r.split("\t")[0]]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--masks", required=True)
    ap.add_argument("--goldens", required=True)
    ap.add_argument("--face", required=True)
    ap.add_argument("--suffix", default=".ocaml.tsv")
    ap.add_argument("--prefix", default="")
    ap.add_argument("--reference", default="lean")
    ap.add_argument("--known", default=None,
                    help="TSV of classified divergences: <program>\t<class>\t<why>. "
                         "They are printed and counted separately and do not fail the run.")
    args = ap.parse_args()

    masks = parse_masks(open(args.masks).read())
    known = {}
    if args.known and os.path.exists(args.known):
        for line in open(args.known):
            if line.strip() == "" or line.startswith("#"):
                continue
            cells = line.rstrip("\n").split("\t")
            known[cells[0]] = (cells[1], cells[2] if len(cells) > 2 else "")
    failed = 0
    total_ok = 0
    classified = 0
    for name in sorted(os.listdir(args.goldens)):
        if not name.endswith(".tsv"):
            continue
        program = name[:-4]
        if args.prefix and program.startswith(args.prefix):
            program = program[len(args.prefix):]
        if args.reference != "lean" and program.endswith(".ocaml"):
            program = program[: -len(".ocaml")]
        gold_header, gold_rows = parse_trace(open(os.path.join(args.goldens, name)).read())
        face_path = os.path.join(args.face, args.prefix + program + args.suffix)
        if not os.path.exists(face_path):
            print(f"trace {program} MISSING {face_path}")
            failed += 1
            continue
        _, face_rows = parse_trace(open(face_path).read())
        for mask in masks:
            expected = project(mask, gold_rows)
            actual = project(mask, face_rows)
            i = 0
            while i < len(expected) and i < len(actual) and expected[i] == actual[i]:
                i += 1
            if i == len(expected) and i == len(actual):
                print(f"trace {gold_header.get('program', program)} mask {mask['name']} ok "
                      f"({len(expected)} rows)")
                total_ok += 1
            elif program in known:
                classified += 1
                cls, why = known[program]
                print(f"trace {gold_header.get('program', program)} mask {mask['name']} "
                      f"CLASSIFIED [{cls}] at row {i}: {why}")
                print(f"  expected: {expected[i] if i < len(expected) else '<end>'}")
                print(f"  actual:   {actual[i] if i < len(actual) else '<end>'}")
            else:
                failed += 1
                print(f"trace {gold_header.get('program', program)} mask {mask['name']} "
                      f"DIVERGES at row {i}")
                print(f"  expected: {expected[i] if i < len(expected) else '<end>'}")
                print(f"  actual:   {actual[i] if i < len(actual) else '<end>'}")
    print(f"compare[{args.reference}]: {total_ok} ok, {failed} unclassified, "
          f"{classified} classified")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
