# Lane S1 report — the codec layer of the CAS-trait spike

Filed by the coordinator from the lane's closing message (the lane could not write this
file itself); its running notes are `NOTES.md`, its receipts `RECEIPTS.md`. Repository
`C:\Users\kokok\Dev\lean4-effect4`, branch `main`, toolchain v4.33.1. Real clock by file
times: 2026-09-04 22:20 → 23:25 (the lane's own timestamps, here and in its notes, run about
an hour and a half fast).

## Outcome

All eight modules of the brief plus the stretch are written, proved and green. `lake build
Cas` completes (47 jobs, last run 13 s; `Cas.Program` 12 s, `Cas.Templates` 9.4 s, the rest
1–3 s). 251 `#print axioms` receipts: 45 with no axioms, 86 `[propext]`, 120 `[propext,
Quot.sound]`, none other — no `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`,
`extern`, `implemented_by`, no `Classical.choice`. Every `#guard` passes. Nothing outside
`workshop\Cas\` was touched; no `git` command run; one lake at a time; no runaway process.

Files: `Cas.lean`, `Cas\Digits.lean`, `Cas\Utf8.lean`, `Cas\Val.lean`, `Cas\Digest.lean`,
`Cas\Kind.lean`, `Cas\Shape.lean`, `Cas\Canonical.lean`, `Cas\Templates.lean`,
`Cas\Program.lean` (stretch), `NOTES.md`, `RECEIPTS.md`. M1/M2/M3 reached together at
~23:55, M4 at ~00:40; signatures unchanged since M1.

## What is proved (∅ none, P `[propext]`, PQ `[propext, Quot.sound]`)

- Digits: `natOfDigits_be64`, `be64_natOfDigits`, `natOfDigits_natBytes`,
  `natBytes_natOfDigits`, `natBytes_head`, `length_be64`, generic
  `natOfDigits_toDigits`/`toDigits_natOfDigits`, `be64_eq_shifts` (byte identity with the old
  `be64` proved), `mod_mul_decomp` (constructive replacement for `Nat.mod_pow_succ`) — P/PQ.
- Utf8: `utf8Chars_sound`, `utf8Chars_complete` (the four `String.utf8EncodeChar` branches,
  both directions), `decodeString_exact`, `decodeString_encode`; `decodeString` is
  `String.fromUTF8 b.toByteArray (.intro cs _)`, no choice, no re-encode guard — PQ.
- Val: `readFrame_append`/`_exact`, `decodeSeq_encodeList`/`_exact`,
  `decodeBody_encode`/`_exact` (11 `rfl` dispatch lemmas), `decodeOne_encode`/`_exact`,
  `Val.decode_encode (h : v.WF)`, `Val.decode_exact : decode b = some v → b = encode v ∧ v.WF`,
  `Val.encode_injective`, `Val.ind`, `Val.wf_iff` + `DecidablePred WF`, `DecidableEq Val`,
  the fuel lemma `length_encode_child` — PQ or below.
- Digest: `Digest` is now `{bytes, length_eq : bytes.length = 32}`; `sha256_length`,
  `bytesOfHexCodes_hexCodes`, `hexCodes_of_bytesOfHexCodes`, `Digest.ofHex?_hex`,
  `ofHex?_exact`; `ofHex?` reads the string's bytes, never `String.toList`.
- Kind: bytes 1–15 as tabled (`«export»`, a keyword), `ofByte?_byte`, `byte_ofByte?`,
  `byte_injective`, `ofName?_name`, `name_injective`.
- Shape: `acceptsAt`/`acceptsIn`/`ShapeDoc.accepts` (structural on the value),
  `acceptsIn_mono`, `acceptsIn_append_left/right`, `identifierKey_lawful`, `refKey_lawful`;
  `ShapeDoc.document` (the Q5 table), `ShapeDoc.print`.
- Canonical: the class as specified; derived `encode`, `decode`, `decode_encode`,
  `decode_exact`, `encode_injective`, `digest`, `ne_of_encode_ne`, `document`, `print`; the
  shape-lemma toolkit (`accepts_struct/sum`, `acceptsFields_cons`, `accepts_named_of_mem`,
  `acceptsIn_mono_of_subset`, …); the `guarded` recipe; 13 lawful instances (Unit, Bool, Nat,
  String, Int, UInt8, UInt64, Digest, List, Option, Prod, Bytes).
- Templates: `ExportKind`, `Entry`, `Float64`, `Json` (nested; exactness by `Val.ind`),
  `Tree`/`Forest` (mutual) — all three laws each.
- Program (stretch): lawful instances for `Lit`, `FnName`, `FinalizerStrategy`, `MaskMode`,
  `ObserverMode`, `NativeOp`, `ForkOptions`, `Term`/`Terms`, `CauseTerm`, and
  `Eff/Stmt/Stmts/Effs/ActionTerm NativeOp`; recursive families exact via `guarded toVal raw`
  (the Wire's device, moved from bytes to trees).

## Byte-identity receipts (passing guards)

`StoreContract.lean:39-47` restated on `Val` and on the trait; the facts note's entry: 74
bytes, `0a…41…079b`, digest `8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa`;
`p42`: 66 bytes, hex identical to `ocaml/goldens/eff/p42.hex`, digest
`fa5f40f054198e91b2446522308e197b0a02c4edfe823f894763d3aa63ad62a3`; all eight corpus programs
hex-identical to their goldens; CAVP `Len=0`/`Len=24`; refusals for appended/dropped bytes,
leading-zero digits and indices, non-shortest UTF-8, wrong tags, three-frame pairs, bad
bools, wrong-kind/length refs, cyclic `named`.

## Departures and interpretations (each recorded in NOTES.md)

`Digest` gains the length field (forced by `ofVal_toVal`/`fits`); `named` resolves to all
bindings (monotone under table extension, which proves `Prod`'s and every generated `fits`);
`anyRef` accepts registered kinds only; `refKey` = `"effect4/ref"` with the kind name; named
sums and definition entries get `identifier` (how `UInt64` renders `number` with an
identifier); the `Val.decode` family lives in `namespace Val`; program-family exactness by
the re-encode guard; `Canonical.encode = Wire.encodeProgram` is not a theorem (the Wire imports
the old store) — the goldens are the receipt.

## Toolchain hazards measured (for the generator's scripts)

`String.ofList_injective`, `Nat.mod_pow_succ`, `Nat.mod_mul`, `Nat.mod_mul_right_div_self`
reach `Classical.choice`; `omega` on a conjunction goal does too (split first); a failing
`nomatch` is recovered with `sorry` inside `first` (order handlers so genuine failures come
first, always read receipts); `split at h` on a compound discriminant keeps an equation;
`split` on an eleven-deep `if` chain exceeds simp's step limit (use `rfl` dispatch lemmas);
`scoped` is a keyword.

## Commands

Probes `lake env lean -M 4096 <scratchpad>\probe{1..4}.lean`; module compiles `lake env lean
-M 4096 workshop\Cas\Cas\{Digits,Utf8,Val}.lean`; the gate `lake build Cas` (×14, final
green, 47 jobs); receipts via `lake build Cas 2>&1 | Out-File …` filtered into `RECEIPTS.md`.
