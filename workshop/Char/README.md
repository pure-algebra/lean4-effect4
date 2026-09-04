# Char: the room for the characterized-components vertical slice

This directory is a bootstrap room. Each numbered folder is one section of one vertical slice:
a piece of the Effect runtime (first: the bounded `Queue`) taken from a Lean model to generated
TypeScript, replayed against the pinned `effect@4.0.0-rc.112`, recorded in a content-addressed
registry, and gated. The room is filled first with *items* (notes, source spans, references,
recipes, candidate signatures, fixture samples, skill sequences), then connected into code.
The library that the room feeds is `Effect4/Char/`.

Read [00-pedigree/BRIEF.md](00-pedigree/BRIEF.md) before anything else. It says what this
estate is, what it has already built, which rulings bind, and what "verified" means here.

## The operating definition of verified

Verified means pinned, replayed and proved against basic system semantics, so that software
written by coding LLMs lands close to correct. It is not a safety-critical claim. It is far
above ordinary testing: a kernel-checked model, its literal source spans by digest, and a finite
replay against the real implementation. Every claim records which of the three rungs it sits
on, and a claim never outranks its evidence.

## Rules of the room

1. **Everything is content.** Every item cites its sources as `path:lines` plus the SHA-256 of
   the file at the time of reading. Every folder keeps an `INDEX.md` listing its items with each
   item's own SHA-256. Assume the whole estate lives in a content-addressed store and write as
   if the digest is the name.
2. **Everything downstream of the model is generated.** The five hand-authored parts of a
   component are carriers, step, invariants with proofs, tests, mutants. Manifests, snapshot
   blocks, pin tables, TypeScript wrappers, replay drivers, fixtures, census rows, sweep rows,
   docs tables: all emitted by `lake exe`, deterministic bytes, checked by a gate. An item that
   proposes a hand-maintained artefact must say why it cannot be generated.
3. **Lean is the source of truth.** The certificate a component carries is a JSON Effect Schema
   document emitted by Lean, decoded by rc.112's own codec, annotated with this estate's
   branded annotation. Proofs are referenced by hash.
4. **Reuse before invention.** effect-nats-verified holds a kernel-checked `Queue` model; port
   it, stub what does not fit, do not rewrite it. The Pass A skeleton matters more than a
   perfect proof; the pipeline matters more than either.
5. **Fast.** The gate for a component is a set of decidable receipts under Lake plus one stamped
   script for bytes and replay. Nothing re-runs when inputs are unchanged.
6. **Built for coding LLMs.** Every section ends in a skill sequence: which skill, in which
   order, with which packet, produces the next component. Prefer the skills this estate has
   already used many times (named in the brief).
7. **Bootstrap phase is items, not code.** Until the connect phase begins, nothing under
   `Effect4/Char/` beyond the stub changes. Items may carry candidate Lean signatures, JSON
   samples, TSV rows, and shell recipes, as text.

## Item format

One file per item, `NN-slug.md`, with this header:

```
---
title: <one line>
kind: source-span | reference | ruling | candidate-signature | recipe | fixture-sample | skill-sequence | open-question | pedigree
sources:
  - path: <absolute or repo-relative path>
    sha256: <64 hex>
    lines: <start-end>   # optional
section: <folder name>
---
```

Body: plain prose, no em-dashes, tables where the content is tabular, code blocks for
anything that will be typed verbatim. Every claim about existing code cites `path:line`.

## Sections

| Folder | Section of the slice | Owns the question |
| --- | --- | --- |
| [00-pedigree](00-pedigree/) | the estate | what has been built, which rulings bind, which skills exist |
| [01-model](01-model/) | Lean model | machine, reading, grade, kit, tests, mutants; the Queue port |
| [02-pins](02-pins/) | source spans | pins as store content, the generator and checker, drift |
| [03-certificate](03-certificate/) | the certificate | the canonical Effect Schema document per component, the branded annotation, proof hashes |
| [04-harness](04-harness/) | conformance harness | the JS replay driver generated from Lean, the Dafny bootstrap, runSync determinism |
| [05-registry](05-registry/) | registry | store items, claims, evidence, rungs, usage edges, composite grades |
| [06-gates](06-gates/) | gates | fast Lean IO tests over the Char API, stamped sweep rows, what fails on what |
| [07-skills](07-skills/) | LLM workflow | the skill sequence, the packet, auto-characterization |
| [08-codegen](08-codegen/) | codegen | the one `lake exe` that emits everything, determinism, the TypeScript target |

## Phases

1. **Bootstrap.** Agents fill the folders with items. Each folder's `INDEX.md` is the receipt.
2. **Connect.** One plan, written from the indexes, names the files under `Effect4/Char/`,
   `harness/`, `scripts/` and `generated/` that the items become, in dependency order.
3. **Slice.** The Queue lands end to end. The room is then archived under `docs/research/`
   and the second component is produced by the skill sequence alone.
