# The CAS-trait spike — lane briefs

Written 2026-09-04 ~22:25 by the coordinator seat (the CAS-trait session). The design is
ruled; nothing here is open for redesign. If a ruling cannot be implemented as stated, stop
at that point, write the reason in `NOTES.md`, and continue with the rest.

## Read first, in this order

1. `docs/research/2026-09-04-cas-trait-facts.md` — §5 the eight rulings (Q1–Q8), §6 the
   illustrations with real bytes and addresses, §2 the census of what is being replaced.
2. `docs/research/2026-09-04-cas-trait-plan.md` — §2 the modules, §3 the kind table, §4 the
   generator, §8 the order (this spike is step 1).
3. `AGENTS.md` (the router), `ocaml/STANDARDS.md` (the library standard: rules 1–7 apply to
   Lean here as they did to OCaml), `docs/ARCHITECTURE.md` (the store rows).
4. The code being generalised: `src/Effect4/Store/Canonical.lean`, `src/Effect4/Store/Digest.lean`,
   `src/Effect4/Program/Wire.lean` (the decoder, lines 174–420: `readFrame`, `readNat`,
   `readBool`, `utf8Chars`, `readString`, `readCtor`, the fuel pattern),
   `Test/Store/StoreContract.lean` (the primitive bytes that must not change).
5. Proof discipline to copy: Foldlab's proved node codec at
   `C:\Users\kokok\Dev\foldlab\.claude\worktrees\effect4-cli-store-cas-2fa7f9\library\cas\Cas\Codec\NodeCodec.lean`
   (stage readers with `_append` and `_exact` lemmas; "no composition exceeds two stages",
   because the kernel's cost explodes with the third) and `Core\Canonical.lean` (the class
   with laws as fields, the address lattice proved once).

## Rules that are not negotiable

- Windows. **PowerShell only**; the Bash tool is denied. Paths with backslashes.
- **Never** `git add`, `git commit`, `git stash`, `git checkout`. **Never edit** `lakefile.toml`,
  anything under `src/`, `Test/`, `docs/`, or `COORDINATION.md`. Your files live under
  `workshop/Cas/` only (the directory is untracked by design).
- **One `lake` on the machine, and it is yours**: `lake build Cas` (the targeted library the
  coordinator declared; it imports `Effect4.*` modules through the same package). Never
  `lake build` anything else, never `lake clean`, `lake update` or `lake exe`. Probes:
  `lake env lean -M 4096 <file>`. If a `lean.exe` runs past ten minutes or its working set
  passes ~5 GB, kill its process tree (`Get-CimInstance Win32_Process -Filter "name='lean.exe'"`
  then `Stop-Process -Id <pid> -Force`) and write what happened in `NOTES.md`. Two runaway
  `lean.exe` processes crashed this PC on 2026-09-04; the `-M` cap is why they no longer can.
- **The axiom ceiling**: every declaration prints `[propext]`, `[propext, Quot.sound]`, or no
  axioms. No `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern`,
  `implemented_by`, `Classical.choice`. Known traps on this toolchain (measured 2026-09-04):
  `String.toList`, `String.foldr`, `String.splitOn`, `String.toNat?`, `String.fromUTF8?`,
  `ByteArray.validateUTF8`, `ByteArray.validateUTF8_eq_true_iff` all reach
  `Classical.choice`. Clean and useful: `String.fromUTF8 a h` (it is the structure
  constructor `⟨a, h⟩`), `ByteArray.IsValidUTF8.intro (m : List Char) (h : b = m.utf8Encode)`,
  `List.utf8Encode_nil/_singleton/_cons/_append`, `List.toByteArray_asString :
  (String.ofList l).toByteArray = l.utf8Encode`, `String.toByteArray_inj`,
  `String.ofList_injective`, `String.utf8EncodeChar` (four branches, `Init/Prelude.lean:3483`),
  `String.toUTF8 s = s.toByteArray` (`rfl`), `ByteArray.toList` (`[propext]`),
  `List.toByteArray`. Receipt: a `/-! ## Receipts -/` section at the end of every module with
  `#print axioms` for every theorem and every executable definition.
- `set_option autoImplicit false` in every file. Doc comments in the house voice of the store
  modules: what the thing is, why it is shaped so, and the law it keeps; no filler, no
  headings inside doc comments, `path:line` citations where a fact comes from a file.
- **Report as you go** in `workshop/Cas/NOTES.md`: a dated entry per milestone (what is
  defined, what is proved with its axioms, what is open and why, the tactic templates). The
  coordinator reads it to start the next lanes. Final report in `workshop/Cas/REPORT.md`.
- Byte identity is a hard constraint: the bytes of every primitive (`Test/Store/StoreContract.lean`
  lines 39–47) and of a constructor frame (`Wire.ctor`) are unchanged; the facts note's §6
  numbers are the receipts (`8fab16…61fa` for the entry's structural payload,
  `fa5f40…62a3` for `p42`'s payload digest, the `p42` bytes listed there).

## Lane S1 — the codec layer (Fable, from 2026-09-04 ~22:30)

Namespace `Effect4.Store` throughout; modules `Cas.*` under `workshop/Cas/Cas/`; the root
`workshop/Cas/Cas.lean` imports every module. Import from `src/Effect4` only what does not
import the old store: `Effect4.Data.Json`, `Effect4.Schema.Authoring` and its closure are
clean (checked 2026-09-04); `Effect4.Program.{Eff,Native}` are clean; `Effect4.Evidence.*`,
`Effect4.Surface.*`, `Effect4.Program.Wire` and `Effect4.Store.*` are **not** (a second
`Effect4.Store.Canonical` in one environment is a clash).

1. **`Cas/Digits.lean`.** `Bytes := List UInt8`; `be64`, `natBytes`, `natOfDigits`
   (big-endian) with the bytes of today's definitions (`Canonical.lean:42-53`, `Wire.lean:177`).
   Theorems: `natOfDigits_be64 : natOfDigits (be64 n) = n % 2^64`; `be64_natOfDigits :
   bs.length = 8 → be64 (natOfDigits bs) = bs`; `natOfDigits_natBytes : natOfDigits (natBytes n)
   = n`; `natBytes_natOfDigits : ds.head? ≠ some 0 → natBytes (natOfDigits ds) = ds`;
   `natBytes_head : (natBytes n).head? ≠ some 0`; `length_be64`. A generic `toDigits width`
   / `ofDigits` pair with its two round trips is the intended proof route; the exported
   definitions may be that pair specialised, as long as the bytes are identical (guards).
2. **`Cas/Utf8.lean`.** `utf8Chars` (the Wire's strict decoder: shortest forms only, no
   surrogates, at most `0x10FFFF`; fuel or structural). `utf8Chars_sound : utf8Chars b = some
   cs → (cs.utf8Encode).toList = b`; `utf8Chars_complete : utf8Chars ((cs.utf8Encode).toList)
   = some cs`, through a per-character lemma over the four branches of
   `String.utf8EncodeChar`. `decodeString : Bytes → Option String` built as `String.fromUTF8
   b.toByteArray (.intro cs h)` from the soundness proof, so no `Classical.choice` and no
   re-encode guard; `decodeString_exact : decodeString b = some s → s.toByteArray.toList = b`;
   `decodeString_encode : decodeString s.toByteArray.toList = some s` (destructure
   `s.isValidUTF8` in the proof; it is a `Prop`, so no choice is needed).
3. **`Cas/Val.lean`.** `Tag` 1–11 (`bool 1, nat 2, string 3, list 4, pair 5, none 6, some 7,
   bytes 8, unit 9, ctor 10, ref 11`); `framed`; `inductive Val | unit | bool | nat | str |
   bytes | list (xs : List Val) | pair | none | some | ctor (index : Nat) (args : List Val) |
   ref (kind : UInt8) (digest : Bytes)`; `Val.WF` (every frame's payload shorter than `2^64`,
   decidable); `encode` (the bytes of the facts note §6: a `ctor` is `framed 10 (encode (nat
   i) ++ (args.map encode).flatten)`, a `ref` is `framed 11 (kind :: digest)`); `readFrame`
   with `readFrame_append` and `readFrame_exact`; `decodeOne : Nat → Bytes → Option (Val ×
   Bytes)`, `decodeSeq`, `decode : Bytes → Option Val` (the whole input, nothing left).
   Theorems: `decode_encode (h : v.WF) : decode (encode v) = some v`; `decode_exact : decode b
   = some v → b = encode v ∧ v.WF`; `encode_injective` on well-formed values; the fuel lemma
   (the byte length is enough fuel because every frame costs at least nine bytes). Refusal
   guards: a byte appended, a byte dropped, a leading-zero digit, a non-shortest UTF-8
   sequence, a wrong tag, a `pair` with three frames.
4. **`Cas/Digest.lean`.** Today's `Digest.lean` (same `sha256`, `Digest.hex`,
   `sha256_length`) plus the one hex codec: `hexOfBytes`, `bytesOfHex : List Char → Option
   Bytes` (accept both cases, print lowercase), `Digest.ofHex?`, round trips.
5. **`Cas/Kind.lean`.** `Kind` per the plan's §3 with `byte : Kind → UInt8`, `ofByte? : UInt8
   → Option Kind`, `ofByte?_byte`, `byte_injective`, `name : Kind → String`; bytes 1–15 exactly
   as tabled, `type`/`entry`/`query`/`result`/`chunk`/`manifest`/`fiber` present as reserved
   constructors.
6. **`Cas/Shape.lean`.** `Shape`, `ShapeDoc {root, defs}`, `accepts : ShapeDoc → Val → Bool`
   (fuel by the value's size; `named` resolves in `defs`; `ref k` accepts exactly `Val.ref
   k.byte d` with `d.length = 32`), `ShapeDoc.document : Document` per the Q5 table (import
   `Effect4.Schema.Authoring`; the `identifier` annotation through the existing key if
   reachable without the old store, else a local key of the same shape; the `ref = kind`
   annotation as a typed key of the same shape as `Effect4.Surface.Annotate`'s), and
   `ShapeDoc.print : Val → Json` (the same table; `Json.ofNat` and `binary64OfNat` copied from
   `src/Effect4/Store/JsonCanonical.lean:61-81` for now).
7. **`Cas/Canonical.lean`.** `class Canonical (α : Type) where shape : ShapeDoc; toVal : α →
   Val; ofVal : Val → Option α; ofVal_toVal : ∀ a, ofVal (toVal a) = some a; ofVal_exact : ∀ {v
   a}, ofVal v = some a → v = toVal a; fits : ∀ a, shape.accepts (toVal a) = true`. Derived once:
   `encode`, `decode`, `decode_encode (h : (toVal a).WF)`, `decode_exact`, `encode_injective`,
   `digest : α → Digest` (the payload digest, `sha256 ∘ encode`), `ne_of_encode_ne`. Instances
   with all three laws: `Unit`, `Bool`, `Nat`, `Int` (two constructors over `nat`), `UInt8`,
   `UInt64` (as `nat`), `String`, `Bytes`, `Digest` (as `bytes`, length 32 checked in `ofVal`),
   `List α`, `Option α`, `α × β`. The primitive bytes are today's (guards from
   `StoreContract.lean:39-47`).
8. **`Cas/Templates.lean`.** The hand instances the generator will emit, written as the
   generator would, with their tactic scripts copied into `NOTES.md`: a local `ExportKind`
   (six nullary constructors, the shape an all-nullary sum), a local `Entry {module, name,
   kind, line}` (a structure; its `toVal` must give the facts note's `0a…41…079b` bytes and
   digest `8fab16…61fa`), `Json` from `Effect4.Data.Json` (nested recursion through `List`),
   and a small local mutual pair. Each instance: `shapeDoc`, `toVal`, `ofVal`, the three laws.
9. **Stretch, only after 1–8 are green:** `Eff NativeOp` from `Effect4.Program.Native` as
   `toVal`/`ofVal` with the three laws (the Wire's encoders, lines 40–170, are the `toVal`;
   its decoders the `ofVal` over trees), byte-identical to the Wire on the corpus (copy
   `Wire.Corpus` locally; `p42`'s bytes and digest are in the facts note §6).

Milestones, each an entry in `NOTES.md`: **M1** `Val`, `Shape` and `Canonical` definitions
compile and their statements are fixed (the other lanes start here; do not change a
signature after M1 without saying so in `NOTES.md`); **M2** the codec laws proved; **M3**
the instances and templates proved; **M4** the stretch. Gate for every milestone: `lake
build Cas` green, the receipts sections present.

## Lane S2 — the node, the store, the word, the traits (after M1)

`Cas/{Node,Store,Word,Traits}.lean` per the plan's §2 rows, against S1's definitions.

## Lane G — the generator (after M1)

`tools/Effect4Gen/` per the plan's §4, against S1's `Templates.lean`.
