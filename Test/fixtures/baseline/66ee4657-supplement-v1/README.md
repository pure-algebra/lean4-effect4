# Frozen constructor and layout supplement

This is a new, explicitly promoted supplement to `../66ee4657/`. Every file in
that original directory remains unchanged. Ordinary generation and comparison
commands never overwrite either directory.

The authority is Git commit `66ee465730126048ad90d99d24ce4f12f5bb2982`, built with
`leanprover/lean4:v4.33.1`. `snapshot.json` contains 49 retained root families and
7 additional applied payload carriers reached from them. It records constructor
arguments, proof flags, structure field order, applied type syntax, constructor
ordinals, 15 `Kind` bytes, 6 `HandleKind` bytes, 12 `Tag` bytes, framing definitions,
and the six existing consumer selections. The 39-source import closure and its
SHA-256 hashes are included in the snapshot. `extraction.json` pins the actual
extractor and retained inventory; `Extract.lean.txt` retains its recipe as text.

The parameterized program families are instantiated at `NativeOp`, matching the
retained manifest and OCaml World. Core containers are identified by nominal type
and pinned Lean toolchain. Reducible aliases normalize when closed. Dependent
field references retain bound indices; those open expressions are not reduced
outside their telescope. Proof fields are recorded; proof bodies are not. Project
payload dependencies are followed to closure, including Schema's applied helpers.
Unsupported open carriers or expression forms refuse. Depth 512 and closure 256
are refusal limits, not evidence of a universal bound; all selected data fit them.

## Reproduce and compare

From the repository root, choose a nonexistent temporary directory. `reflect`
runs Lake and must hold the repository's serialized Lean lane.

```sh
python3 scripts/check-compatibility.py prepare --revision 66ee465730126048ad90d99d24ce4f12f5bb2982 --work /private/tmp/effect4-g2-reproduce
python3 scripts/check-compatibility.py reflect --work /private/tmp/effect4-g2-reproduce
python3 scripts/check-compatibility.py compare --baseline Test/fixtures/baseline/66ee4657-supplement-v1/snapshot.json --candidate /private/tmp/effect4-g2-reproduce/snapshot.json
python3 scripts/test-compatibility.py
python3 scripts/test-compatibility-history.py
```

Preparation copies immutable Git sources and build metadata. It reuses the local
`.lake/packages` cache under the pinned manifest; it does not download a new
compiler or prove integrity of that installed compiler/cache. The four built
imports are `Effect4.Program.Native`, `Effect4.Schema.Document`,
`Effect4.Store.Pin`, and `Effect4.Store.Node`. The extractor may run from a
separate checkout without adding a library or Test import. If its producer changes,
use this retained recipe with its pinned hash for a historical reproduction.

To capture the current uncommitted sources for a candidate, use `prepare
--working-tree --work <new-temporary-directory>`, then `reflect` and `compare`.
Preparation retains exact source/build/layout inputs; reflection checks their
hashes before building. A working-source candidate cannot be promoted as this
historical supplement. Changes made after capture require a fresh capture.

A named structural append policy has the form:

```json
{"constructor_appends":["Effect4.Program.Ty.futureCtor"],"consumer_appends":["deriving:Program:Effect4.Program.NewFamily"]}
```

Only trailing constructors of an existing sum and named trailing consumer
selections are eligible. Existing payloads, field order, byte maps and framing
must stay identical. New applied family selections refuse pending a reviewed
policy extension. Unused or unknown permissions refuse. This conservatism is
intentional: the tool cannot infer that an arbitrary new encoding is compatible.

## Evidence and boundaries

The extractor was run against the frozen source closure, then repeated with
byte-identical output. A deliberately exhausted traversal refused before writing
an output file. Independent tests accept unchanged shapes and named appends;
they reject payload substitution, constructor reorder/removal, field reorder,
byte remapping/tag reuse, changed framing, missing consumers and malformed shapes.

The history observer separately compiles the current production OCaml decoder,
encoder and checker in a temporary directory. It reads immutable old bytes via
Git and checks them against the retained digests: 50 old byte vectors re-encode
exactly and refuse a trailing byte; 42 additionally match their old JSON values.
It reports checker outputs separately against the retained `.ty` outputs. A
Boolean-error control is independently assembled and remains decodable.

A shape comparison establishes only its stated structural/layout judgment.
Decoder observations are finite, and typing changes use explicit expected deltas.
`compare-observations` compares supplied admission or execution-permission rows;
it does not execute a checker or host. A named Boolean-error narrowing is tested
as a policy example, not claimed to be implemented by this supplement. No runtime
is invoked, no host permission is inferred, and no codec theorem is supplied.
