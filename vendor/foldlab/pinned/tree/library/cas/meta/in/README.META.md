# `meta/in` — the meta plane's declared inputs

One input, and it is the first: `model-gated.META.json`, the trust
census's curated list of shipped TypeScript files a conformance
artifact holds to the Lean model. It carries a row in
`MANIFEST.META.json`'s `inputs` and `lake exe trust` reads it from
here, refusing rather than defaulting when it is missing, malformed,
carries a key the census does not read, or is addressed to another
reader.

Every other emitter in `tools/` still reads only the compiled Lean
environment, the committed store content, or a config file it names as
a Lean constant.

## The input-admission law (M4)

**An emitter may read only files with a `MANIFEST.META.json` row.**
Inputs are declared or they are refused. There is no ambient read.

The law is what makes hydration provenance ENUMERABLE: generated data
is the Lean environment, plus store content, plus the declared inputs,
and nothing else. A consumer that trusts an emitted artifact can list
everything that decided its bytes without reading the emitter.

The manifest's `inputs` section carries this sentence as its own
`convention` field, so the law travels with the registry rather than
only with this page.

## Enforcement

Activated end to end for the first time by the strata/meta lane, at the
one input this directory holds. The reader's half is real and running:
`tools/TrustCensus.lean` names the file, the document name it must
declare, and the reader it must address, and every departure from that
is a refusal naming what is wrong — a declared input that vanishes is a
red build, never a silent default.

The other half — REFUSING an emitter that opens an undeclared path —
is still held by reading. Nothing today mechanically stops a tool from
opening a file with no row; catching that needs a syscall-level or
source-level census of the emitters, which is its own slice. What has
changed is that the discipline now has a worked instance to copy
rather than only a rule to remember.

## What lands here next

The file-shaped inputs M4 names and this directory does not yet hold:
the laws/rulings source (today a Lean value in `tools/Law.lean`), the
compositionality measurement fragments, and `ViewSpec` instances. Each
arrives with its `MANIFEST.META.json` row — path, role, authority, and
the emitter that reads it — written in the same commit as the file,
because a file here without a row is exactly what the law refuses.
