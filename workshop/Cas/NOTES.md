# Lane S1 notes — the codec layer

Running notes of lane S1 (the codec layer of the CAS-trait spike). One dated entry per
milestone; decisions the brief left to the lane are recorded where they were taken. The
coordinator starts lanes S2 and G from the M1 entry.

## 2026-09-04 22:45 — start; toolchain facts measured before writing

Read in the brief's order: the facts note, the plan, `AGENTS.md`, `ocaml/STANDARDS.md`,
`docs/ARCHITECTURE.md`, `Store/Canonical.lean`, `Store/Digest.lean`, `Program/Wire.lean`,
`Test/Store/StoreContract.lean`, Foldlab's `NodeCodec.lean`, `Codec/Bytes.lean`,
`Codec/Nat32.lean`, `Codec/Hex.lean`, `Core/Canonical.lean`; then `Data/Json.lean`,
`Schema/{Payload,Representation,Document,Annotations,Authoring}.lean`,
`Store/JsonCanonical.lean:61-81`, `Surface/Annotate.lean`, `Evidence/StdLib/Entry.lean`
(for the `Entry`/`ExportKind` shapes the templates reproduce).

Machine state: no `lean.exe`/`lake.exe` running at start; oleans for `Effect4.Data.Json`,
`Effect4.Schema.Authoring`, `Effect4.Program.{Eff,Native}` present from the 20:53 gate; the
`Cas` lakefile hunk is in place (`lakefile.toml:35-40`).

Toolchain facts pinned by `#check`/`#print axioms` probes (`scratchpad/probe1..4.lean`,
`lake env lean -M 4096`, ~1 s each), v4.33.1:

- Arithmetic: `Nat.mod_pow_succ`, `Nat.mod_mul` and `Nat.mod_mul_right_div_self` **reach
  `Classical.choice`** (`probe3`); `Nat.div_add_mod`, `Nat.mod_lt`, `Nat.mod_eq_of_lt`,
  `Nat.div_eq_of_lt`, `Nat.add_mul_div_left`, `Nat.add_mul_mod_self_left`, `Nat.mul_add_div`,
  `Nat.div_lt_iff_lt_mul`, `Nat.le_div_iff_mul_le`, `Nat.pow_le_pow_right`, `Nat.pow_pos`,
  `Nat.shiftRight_eq_div_pow` are at or under `[propext, Quot.sound]`. `UInt8.toNat_ofNat' :
  (UInt8.ofNat n).toNat = n % 2^8`, `UInt8.toNat_ofNat_of_lt'`, `UInt8.toNat_lt`,
  `UInt8.toNat_inj`, `UInt8.ofNat_toNat`; `UInt8.ext` does not exist.
- UTF-8: `String.utf8EncodeChar c` branches on `v := c.val.toNat` at `≤ 0x7f`, `≤ 0x7ff`,
  `≤ 0xffff` (`Init/Prelude.lean:3483-3509`); `List.utf8Encode l = (l.flatMap
  String.utf8EncodeChar).toByteArray` (noncomputable, `:3514`); `ByteArray.IsValidUTF8` is an
  inductive `Prop` with one constructor `intro (m : List Char) (hm : b = m.utf8Encode)`
  (`:3522-3527`); `String.fromUTF8 a h = String.ofByteArray a h` (`String/Defs.lean:69`), so
  `(String.fromUTF8 a h).toByteArray = a` is `rfl`; `String.isValidUTF8 s :
  s.toByteArray.IsValidUTF8`; `String.toByteArray_inj` (no axioms); `String.toByteArray_ofList
  : (String.ofList l).toByteArray = l.utf8Encode` (the live name of
  `List.toByteArray_asString`, `[propext]`); `List.toList_data_toByteArray :
  l.toByteArray.data.toList = l`; `Char.ofNat n` is `dite (n.isValidChar) (Char.ofNatAux n) _`
  and `Nat.isValidChar n = n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000)`. **`String.ofList_injective`
  reaches `Classical.choice`** on this toolchain (`probe3`), contrary to the brief's list; it is
  not used anywhere. `ByteArray.toList` is a loop-defined def (`[propext]`), so every byte-array
  statement here is spelled `.data.toList`, the projection today's `Canonical String` reads.
- Options and lists: `Option.bind_eq_some_iff`, `Option.map_eq_some_iff`, `Option.bind_some`,
  `Option.map_some`, `List.take_left`, `List.drop_left`, `List.take_append_drop`,
  `List.append_inj_right`, `List.flatten_cons`, `List.mem_cons`, `List.any_eq_true`,
  `List.find?_some`. `List.not_mem_nil` takes the membership proof as its explicit argument;
  `List.length_pos_of_ne_nil` and `Char.toNat_ofNat` do not exist.
- Elaboration: `deriving Repr` on a `List`-nested inductive yields an axiom-free instance;
  `deriving DecidableEq` does not apply to one (as `Data/Json.lean` records), so `Val` gets a
  hand-built `beq` + `beq_iff` + `decidable_of_iff`, proved as mutual structural theorems
  (`termination_by structural`); `deriving instance DecidableEq for Tree, Forest` works for a
  plain mutual pair. A fuel decoder may pass its own recursive call partially applied
  (`decodeSeq (decodeOne fuel) n rest`) and stay structural on the fuel with no axioms.
  `simp` decides `UInt8` literal (in)equalities (`(1 : UInt8) = 9 ↔ False`).

Hazards met and how each was closed (every one is a rule for the generator's scripts):

- `omega` on a **conjunction** goal reaches `Classical.choice` (its by-contradiction step);
  split the conjunction first (`exact ⟨by omega, by omega⟩`). Single (in)equalities are clean.
- `subst` of a payload-bits equation inside the UTF-8 branch proofs exceeded the recursion
  depth; the `bytes_*` lemmas take the `contBits` equations as hypotheses instead and `omega`
  uses them as hypotheses.
- `split at h` on the eleven-deep `if` chain of `decodeBody` exceeds simp's step limit; the
  exactness proof dispatches by `by_cases` on the tag and rewrites with one `rfl` equation per
  tag (`decodeBody_unit` … `decodeBody_ref`, `decodeBody_unknown`).
- `simp only [hframe]` normalised `Tag.nat = Tag.nat` to `True` before `if_pos` could fire;
  the `ctor` case of `decodeBody_encode` uses `rw`/`show` and never unfolds the `Tag` constants.
- A failing `nomatch h` is **recovered with `sorry`**, not thrown: `first | exact nomatch h |
  …` never backtracks. Put the genuinely-failing handler first and `nomatch` last, and read
  the receipts for `sorryAx` after every build. `nomatch h, fun … => …` parses the comma as a
  second discriminant: parenthesise components of an anonymous constructor.
- `split at h` on a compound discriminant (`Val.ctor i args`) keeps an equation `heq` instead
  of substituting; handlers start with `rename_i … heq; injection heq with hi hargs; subst hi
  hargs`.
- Inside `namespace Val`, bare `some`/`none` are the constructors `Val.some`/`Val.none`; the
  `Val.decode` block spells `Option.some`/`Option.none`.

## 2026-09-04 ~23:55 — M1, M2, M3 together: `lake build Cas` green, 8 modules, every receipt at the ceiling

Gate: `lake build Cas` from the repository root, 29 jobs, "Build completed successfully".
Receipt census over the eight `/-! ## Receipts -/` sections (`scratchpad/cas-receipts.log`):
225 `#print axioms` lines — 45 `does not depend on any axioms`, 77 `[propext]`, 103 `[propext,
Quot.sound]`, none other; no `sorryAx`, no `Classical.choice`. Every `#guard` passes (byte identity and refusals, listed under M2/M3).

### What is defined (the signatures lanes S2 and G build against; not to change without a note here)

`Cas/Digits.lean` (namespace `Effect4.Store`): `abbrev Bytes := List UInt8`; `natOfDigits :
Bytes → Nat` (the Wire's, verbatim); `toDigits : Nat → Nat → Bytes` (width, then number;
digit at level `w` is `n / 256^w % 256`); `digitCount : Nat → Nat`; `be64 n := toDigits 8 n`;
`natBytes n := toDigits (digitCount n) n`.

`Cas/Utf8.lean`: `utf8Bytes : List Char → Bytes` (the computable `List.utf8Encode`);
`contBits : UInt8 → Option Nat`; `utf8Chars : Nat → Bytes → Option (List Char)` (the Wire's
strict reader, fuel = byte count); `decodeString : Bytes → Option String` built as
`String.fromUTF8 b.toByteArray (.intro cs (toByteArray_eq_utf8Encode h))`.

`Cas/Val.lean`: `framed (tag : UInt8) (payload : Bytes) : Bytes`; `namespace Tag` with `bool 1,
nat 2, string 3, list 4, pair 5, none 6, some 7, bytes 8, unit 9, ctor 10, ref 11`;
`inductive Val | unit | bool (b) | nat (n) | str (s) | bytes (bs) | list (xs : List Val) |
pair (a b) | none | some (a) | ctor (index : Nat) (args : List Val) | ref (kind : UInt8) (digest
: Bytes)` deriving `Repr, Inhabited`, with `instance Val.instDecidableEq`; `Val.encode`,
`Val.encodeList`, `Val.tag`, `Val.payload`, `Val.children`, `Val.ind` (membership-form
induction principle), `Val.WF : Val → Prop` / `Val.WFList` (payload shorter than `2^64` at
every frame), `Val.wf : Val → Bool`, `instance Val.decWF : DecidablePred Val.WF`; the stage
readers `readFrame : Bytes → Option (UInt8 × Bytes × Bytes)`, `decodeSeq (p : Bytes → Option
(Val × Bytes)) : Nat → Bytes → Option (List Val)`, `decodeBody (dec) (tag : UInt8) (payload :
Bytes) : Option Val`, `decodeOne : Nat → Bytes → Option (Val × Bytes)`; **`Val.decode : Bytes →
Option Val`** (whole input, nothing left; fuel `b.length + 1`); `sampleEntry : Val` (the facts
note's entry). The `decode` family is in `namespace Val` (`Val.decode`, `Val.decode_encode`,
`Val.decode_exact`, `Val.encode_injective`, `Val.ne_of_encode_ne`) so that `Canonical.decode`
does not shadow it.

`Cas/Digest.lean`: **`structure Digest where bytes : Bytes; length_eq : bytes.length = 32`** —
a departure from today's `Digest` (which admits a 31-byte value), forced by the laws: with the
length checked in `Canonical Digest`'s `ofVal` (the brief's rule), `ofVal_toVal` and `fits`
are false for a short value unless the type excludes it (Foldlab's `Addr32`). `Digest.ext`,
hand `DecidableEq` and `Repr` instances; `sha256 : Bytes → Digest`; `hexDigit`, `hexVal`,
`lowerHex : Nat → Nat`; `hexCodes : Bytes → List Nat`; `bytesOfHexCodes : List Nat → Option
Bytes`; `hexOfBytes : Bytes → List Char`; `bytesOfHex : List Char → Option Bytes` (both cases
accepted); `Digest.hex : Digest → String` (today's characters); `Digest.ofHex? : String →
Option Digest`, reading `s.toByteArray.data.toList` (a hex digit is one ASCII byte, so the
bytes are the code points) and never `String.toList`.

`Cas/Kind.lean`: `inductive Kind | source | «export» | type | schema | program | annotation |
entry | query | result | chunk | tree | manifest | component | vector | fiber` (bytes 1–15 in
this order; `export` is a keyword, hence `«export»`, its `name` is `"export"`); `Kind.byte`,
`Kind.name`, `Kind.all`, `Kind.ofByte? b := all.find? (·.byte = b)`, `Kind.ofName?`.

`Cas/Shape.lean`: `inductive Shape | unit | bool | nat | string | bytes | digest | list (item) |
option (item) | pair (fst snd) | struct (name : String) (fields : List (String × Shape)) | sum
(name : String) (cases : List (String × List (String × Shape))) | ref (kind : Kind) | anyRef |
named (name : String)`; `structure ShapeDoc where root : Shape; defs : List (String × Shape)`;
`lookupAll`, `candidates (defs) : Shape → List Shape` (a `named` shape's bindings, any other
shape itself), `allNullary`; **`acceptsAt (defs) : Val → Shape → Bool`** (structural on the
value; children checked against the candidates of their shapes), `acceptsList`,
`acceptsFields`, `acceptsIn (defs) (s : Shape) (v : Val) : Bool := (candidates defs s).any
(acceptsAt defs v)`, **`ShapeDoc.accepts (doc) (v) : Bool := acceptsIn doc.defs doc.root v`**;
`identifierKey : AnnotationKey String` (name `"identifier"`, the shape of
`Surface/Annotate.lean:73-91`), `refKey : AnnotationKey Kind` (name `"effect4/ref"`, payload
`Json.str kind.name`); `hexPattern`, `digestPattern`; `render : Shape → Representation`,
`renderFields`, `renderCases`, `renderDef`, **`ShapeDoc.document : ShapeDoc → Document`**;
`highestBit`, `binary64OfNat`, `Json.ofNat` (copied from `JsonCanonical.lean:61-81`),
`hexString`, `headShape`, `kindJson`, `printIn`, `printList`, `printFields`, **`ShapeDoc.print
: ShapeDoc → Val → Json`**; `entryDoc : ShapeDoc`.

`Cas/Canonical.lean`: **`class Canonical (α : Type) where shape : ShapeDoc; toVal : α → Val;
ofVal : Val → Option α; ofVal_toVal : ∀ a, ofVal (toVal a) = some a; ofVal_exact : ∀ {v a},
ofVal v = some a → v = toVal a; fits : ∀ a, shape.accepts (toVal a) = true`**, with `export
Canonical (shape toVal ofVal ofVal_toVal ofVal_exact fits)`. Derived in `namespace Canonical`:
`toVal_injective`, `encode a := Val.encode (toVal a)`, `decode b := (Val.decode b).bind ofVal`,
`decode_encode (a) (h : (toVal a).WF)`, `decode_exact`, `encode_injective (ha hb)`,
`ne_of_encode_ne`, `digest a := sha256 (encode a)`, `digest_congr`, `document (α)`, `print`.
The shape-lemma toolkit for generated `fits` proofs: `acceptsFields_nil`, `acceptsFields_cons`,
`acceptsAt_struct`, `accepts_struct`, `acceptsAt_sum`, `accepts_sum`, `acceptsIn_named`,
`accepts_option_none`, `accepts_option_some`, `accepts_list`, `accepts_pair`,
`acceptsList_of_forall`, `mem_lookupAll`, `mem_candidates_of_subset`,
`acceptsIn_mono_of_subset`, `accepts_named_of_mem`. Instances, each with the three laws:
`Unit` (`unit`), `Bool`, `Nat`, `String`, `Int` (`sum "Int" [ofNat, negSucc]` over `nat`, in
`namespace IntCanonical`), `UInt8` and `UInt64` (`nat` under `{root := named "UInt8", defs :=
[("UInt8", nat)]}`), `Digest` (`digest`, length checked in `ofVal`), `List α` (`list`, defs
inherited), `Option α` (`option`), `α × β` (`pair`, defs appended), and `Bytes` last, so that
`List UInt8` still frames as `bytes` now that `UInt8` has an instance.

`Cas/Templates.lean`: `Templates.ExportKind` (all-nullary sum), `Templates.Entry`
(structure), `Float64Canonical` + `instCanonicalFloat64`, `JsonCanonical` + `instCanonicalJson`
(nested recursion), `Templates.Tree`/`Templates.Forest` (mutual pair), `Templates.entry`,
`Templates.json`, `Templates.forest`.

### Interpretations of the rulings taken by this lane (not redesigns; each reversible)

1. `named` resolution is by **all** bindings of the name (`candidates`), a value fits if it fits
   one; one step only (a definition whose body is itself `named` accepts nothing). For a
   document with unique names — every document the generator writes — this is the single
   lookup Q5 describes. The reason for the wider statement is `acceptsIn_mono` /
   `acceptsIn_append_left/right`: acceptance survives appending definitions on either side,
   which is what proves `fits` for `α × β` with the two components' tables appended, and lets a
   generated `fits` lift a field type's law by `acceptsIn_mono_of_subset`. A class field cannot
   carry a "names are unique" side condition.
2. `anyRef` accepts `Val.ref b d` only for a **registered** kind byte (`Kind.ofByte? b` is
   `some`) and `d.length = 32`; `ref k` accepts exactly `k.byte`. The printer prints the kind
   name, so an unregistered byte could not print; the alphabet grows by spec version anyway.
3. The `ref = kind` annotation is `refKey`, name `"effect4/ref"`, payload the kind's **name**
   as a JSON string (lawful: `refKey_lawful`). Q5 says "a typed `ref = kind` annotation" and
   the Surface module's branded key is `"effect4/surface"`; the name is the lane's choice.
4. A named `sum` is annotated `identifier` like a `struct` (Q5 names the annotation for
   `struct` only; a `sum` carries a `name` for the same reason). Every definition entry whose
   shape is not already a named struct or sum is annotated with its key as `identifier`
   (`renderDef`), which is how `UInt8`/`UInt64` render `number ∘ Check.int` **with an
   identifier** (their docs are `{root := named "UInt64", defs := [("UInt64", nat)]}`): Q5's
   "fixed-width scalars encode as `nat`, render `number` with an identifier".
5. The printer follows the value's structure and reads only names from the shape; a value that
   does not fit still prints (under `_ctor`/`args`) rather than failing — `ShapeDoc.print : Val
   → Json` is total as the brief states it.
6. `be64` is `toDigits 8` with `be64_eq_shifts` proving byte identity to `Canonical.lean:42-43`;
   `natBytes` is guarded on `0, 1, 255, 256, 1947, 65536` (the old accumulator shape resists a
   direct proof; the new shape has both round trips as theorems).

### What is proved (axioms in brackets; `∅` = no axioms)

Digits: `length_be64` [propext]; `natOfDigits_toDigits`, `toDigits_natOfDigits`,
`be64_eq_shifts`, `natOfDigits_be64 : natOfDigits (be64 n) = n % 2^64`, `be64_natOfDigits :
bs.length = 8 → be64 (natOfDigits bs) = bs`, `natOfDigits_natBytes`, `natBytes_head :
(natBytes n).head? ≠ some 0`, `natBytes_natOfDigits : ds.head? ≠ some 0 → natBytes (natOfDigits
ds) = ds`, `digitCount_spec`, `digitCount_unique`, `mod_mul_decomp` (the constructive
replacement for `Nat.mod_pow_succ`) [propext, Quot.sound].

Utf8: `utf8Chars_sound : utf8Chars fuel b = some cs → utf8Bytes cs = b` (and `utf8Chars_sound'`
in the `cs.utf8Encode.data.toList` spelling), `utf8Chars_complete : utf8Chars (utf8Bytes
cs).length (utf8Bytes cs) = some cs` (and `'`), the per-branch lemmas `encodeChar_one..four`,
`utf8Chars_one..four`, `bytes_one..four`, `utf8Chars_encodeChar`, `decodeString_exact :
decodeString b = some s → s.toByteArray.data.toList = b`, `decodeString_encode : decodeString
s.toByteArray.data.toList = some s`, `decodeString_toUTF8` — all [propext, Quot.sound] or
below.

Val: `framed_length`, `framed_inj`, `encode_eq`, `Val.ind`, `wf_iff`, `WF_payload_lt`,
`WF_child`, `length_encode_child : c ∈ v.children → (encode c).length + 9 ≤ (encode v).length`
(the fuel argument), `length_le_encodeList` (the count argument), `readFrame_append : payload
.length < 2^64 → readFrame (framed tag payload ++ rest) = some (tag, payload, rest)`,
`readFrame_exact : readFrame b = some (tag, payload, rest) → b = framed tag payload ++ rest ∧
payload.length < 2^64`, `decodeSeq_encodeList`, `decodeSeq_exact`, `decodeBody_encode`,
`decodeBody_exact`, `decodeOne_encode : v.WF → (encode v).length < fuel → decodeOne fuel
(encode v ++ rest) = some (v, rest)`, `decodeOne_exact`, **`Val.decode_encode (h : v.WF) :
Val.decode (encode v) = some v`**, **`Val.decode_exact : Val.decode b = some v → b = encode v ∧
v.WF`**, **`Val.encode_injective (ha hb)`**, `Val.beq_iff` — all [propext, Quot.sound] or
below.

Digest: `hexVal_hexDigit`, `hexVal_some`, `bytesOfHexCodes_hexCodes`,
`hexCodes_of_bytesOfHexCodes : bytesOfHexCodes cs = some bs → hexCodes bs = cs.map lowerHex`
(exact up to case), `bytesOfHex_hexOfBytes`, `hexOfBytes_bytesOfHex`, `utf8Bytes_map_ofNat`,
`Digest.sha256_length`, `Digest.hex_bytes`, **`Digest.ofHex?_hex : ofHex? d.hex = some d`**,
`Digest.ofHex?_exact`.

Kind: `ofByte?_byte`, `byte_ofByte?`, `byte_injective`, `ofName?_name`, `name_ofName?`,
`name_injective`, `mem_all`, `all_length`, `byte_pos`, `byte_le`.

Shape: `acceptsAt_mono`, `acceptsList_mono`, `acceptsFields_mono`, `acceptsIn_mono`,
`acceptsIn_append_right/left`, `acceptsIn_of_not_named`, `identifierKey_lawful`,
`refKey_lawful`.

Canonical: the derived layer and every instance law above; `Templates`: every template's three
laws (`JsonCanonical.exact_aux`, `TreeForest.exact_aux` by `Val.ind`).

### Byte identity and refusals, guarded (the receipts)

- `Test/Store/StoreContract.lean:39-47` restated on `Val` (`Val.lean`) and on the trait
  (`Canonical.lean`): `encode () = [9,0,0,0,0,0,0,0,0]`, `encode true = [1,…,1,1]`, `encode
  (0 : Nat) = [2,…,0]`, `encode (256 : Nat) = [2,…,2,1,0]`, `encode "A" = [3,…,1,65]`, `encode
  "é" = [3,…,2,0xc3,0xa9]`, `encode ([] : List Nat) = [4,…,0]`, `(encode ["a","b"]).length =
  29`, `(framed 7 [1,2,3]).length = 12`; a `ref` frame is 42 bytes.
- The facts note §6 entry: `Canonical.toVal Templates.entry = sampleEntry`, 74 bytes, first ten
  `0a 00…00 41 02`, last eleven `02 00…00 02 07 9b`, payload digest
  `8fab161870afe7d35c681679cf5dced52845b5ebef2b84b6c85e4b49d00661fa` (`Digest.lean`,
  `Templates.lean`).
- CAVP `Len = 0` and `Len = 24` digests through `sha256`/`Digest.hex` (`Digest.lean`).
- Refusals (`Val.lean`): a byte appended, a byte dropped, a leading-zero digit (`framed Tag.nat
  [0, 17]`), a non-shortest UTF-8 sequence (`framed Tag.string [0xc0, 0x80]`), a wrong tag
  (`framed 12 []`), a `pair` with three frames, a bool byte `2`, a payload under `unit`, an
  empty `ref`, a leading-zero constructor index. UTF-8 refusals (`Utf8.lean`): a lone
  continuation byte, overlong two- and three-byte forms, a surrogate, a value above `0x10FFFF`,
  a truncated sequence.
- Shape (`Shape.lean`): `entryDoc.accepts sampleEntry`, four mismatches refused, `entryDoc.print
  sampleEntry` is the JSON of `Entry.json` (`Entry.lean:63-68`) with `Json.ofNat 1947`; `ref`
  refusals by kind and by length; `anyRef` refuses byte 16; `digest` refuses 33 bytes; a cyclic
  `named` chain accepts nothing.

### Open

- The stretch (M4, `Eff NativeOp`) is next; the Wire's own `readString` re-encode guard is
  replaced here by `decodeString`'s constructive validity proof, so the `Eff` instance's string
  frames decode without the guard.
- `deriving Repr` is used on `Val` and `Shape` (axiom-free); `Digest`'s `Repr` is by hand
  because of the `Prop` field.
- Nothing is admitted by name; no declaration reaches `Classical.choice`.

### Tactic templates for lane G (verbatim from `Templates.lean`)

All-nullary sum `T` (`ExportKind`):

```lean
theorem ofVal_toVal (a : T) : ofVal (toVal a) = some a := by cases a <;> rfl
theorem ofVal_exact {v : Val} {a : T} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  all_goals first
    | (injection h with h; subst h; rfl)
    | exact nomatch h
theorem fits (a : T) : shapeDoc.accepts (toVal a) = true := by cases a <;> decide
```

Structure `T` with fields `f₁ … fₙ` (`Entry`; `shapeDoc.defs` is the fields' tables appended):

```lean
theorem ofVal_toVal (e : T) : ofVal (toVal e) = some e := by
  obtain ⟨f₁, …, fₙ⟩ := e
  simp [toVal, ofVal, Canonical.ofVal_toVal]
theorem ofVal_exact {v : Val} {e : T} (h : ofVal v = some e) : v = toVal e := by
  unfold ofVal at h
  split at h
  · next v₁ … vₙ =>
    split at h
    · next f₁ … fₙ h₁ … hₙ =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h₁, …, Canonical.ofVal_exact hₙ]
    · exact nomatch h
  · exact nomatch h
theorem fits (e : T) : shapeDoc.accepts (toVal e) = true := by
  obtain ⟨f₁, …, fₙ⟩ := e
  apply accepts_struct
  refine acceptsFields_cons _ _ _ _ _ _ ?_ (… (acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_nil _)))
  · exact acceptsIn_mono_of_subset (fun p hp => by simp [shapeDoc, hp]) _ _ (Canonical.fits f₁)
  …
```

Nested recursion (`Json`): companions `toValList/toValEntries`, `ofValList/ofValEntries`;
`ofVal_toVal` mutual with `termination_by structural`; exactness through `Val.ind` with the
motive `Exact v ∧ (∀ vs, v = .list vs → ∀ x ∈ vs, Exact x ∧ ∀ k w, x = .pair k w → Exact w) ∧
(∀ k w, v = .pair k w → Exact w)`, the `ctor` case `unfold ofVal at h; split at h; all_goals
first | ⟨handler per alternative, each starting `rename_i … heq; injection heq with hi hargs;
subst hi hargs`⟩ | exact nomatch h`; `fits` mutual with `fitsList`/`fitsEntries`, the root
`accepts_named_of_mem _ _ jsonShape _ mem_defs` then `acceptsAt_sum _ _ _ i "case" _ _ rfl
(acceptsFields_cons …)`, list fields by `accepts_list _ _ _ (fitsList xs)`, pair fields by
`accepts_pair`. Mutual pair (`Tree`/`Forest`): the same with `ExactT ∧ ExactF` as the motive
and `List.Mem.head _` / `List.Mem.tail _ (List.Mem.head _)` for the table memberships.

Generated `ofVal` shape: `| .ctor i [v₁, …, vₙ] => match Canonical.ofVal (α := F₁) v₁, … with |
some f₁, …, some fₙ => some ⟨f₁, …, fₙ⟩ | _, … => none | _ => none`; nested self-references go
through the companions, never through the instance being defined.

## 2026-09-05 ~00:40 — M4, the stretch: `Eff NativeOp` and its family, byte-identical to the goldens

Gate: `lake build Cas`, 47 jobs (the `Effect4.Program.Native` closure enters the build),
green; `Cas/Program.lean` compiles in 12 s; every receipt at the ceiling (`RECEIPTS.md`).

### What is defined (`Cas/Program.lean`, namespace `Effect4.Store.ProgramCanonical`)

Instances with the three laws for `Lit`, `Effect4.Machine.FnName`, `Effect4.FinalizerStrategy`,
`Effect4.Supervision.{MaskMode, ObserverMode, ForkOptions}`, `Effect4.Program.NativeOp`,
`Term`, `Terms`, `CauseTerm`, and the five-type block `Eff NativeOp`, `Stmt NativeOp`, `Stmts
NativeOp`, `Effs NativeOp`, `ActionTerm NativeOp` (`instCanonicalEff` and kin). Constructor
indices are the Wire's (`Wire.lean:40-167`): declaration order, a structure is constructor 0,
the mutual list types `nil = 0`/`cons = 1`; `Option Term` is the derived `Canonical (Option
Term)`, so `interrupt none` frames as tag 6 and `interrupt (some t)` as tag 7 (`encOptTerm`).
Shapes compose as the generator would write them: a member of a mutual block by `named`, any
other type by `(shape F).root` inline with `(shape F).defs` appended (`EffC.defs` is the five
block shapes followed by the tables of `Term`, `CauseTerm`, `NativeOp`, `Nat`, `ObserverMode`,
`ForkOptions`, `Option Term`). The corpus of `Wire.lean:576-618` is copied as
`ProgramCanonical.Corpus`.

### How the laws are proved

- The alphabets without recursion (`Lit`, `FnName`, `FinalizerStrategy`, `MaskMode`,
  `ObserverMode`, `NativeOp`, `ForkOptions`) use the template scripts of M3; `NativeOp`'s
  `fits` is `cases a; all_goals first | decide | (rename_i x; cases x <;> decide)`.
- The recursive families (`Term`/`Terms`, `CauseTerm`, the `Eff` block) read through
  **`guarded toVal raw`** (`Canonical.lean`): `raw` is the structural reader, the guard
  compares the re-encoding; `guarded_toVal` needs only the left inverse `raw (toVal a) = some
  a` (one mutual structural induction, one `simp [toVal, raw, Canonical.ofVal_toVal, ih…]` per
  constructor — fifty constructors for the block), and `guarded_exact` is free. This is the
  Wire's own device for its string frame (`Wire.lean:254-262`) and `Surface/Annotate.lean`'s
  for `markKey`, moved from bytes to trees; the structural exactness route (`Val.ind`) is
  demonstrated on `Json` and `Tree`/`Forest` in `Templates.lean` and remains available to the
  generator for small types. Price: one re-encoding per decode.
- `fits` for every recursive family is a mutual structural theorem: `accepts_named_of_mem` for
  the root, `acceptsAt_sum _ _ _ i "case" _ _ rfl` per constructor, `acceptsFields_cons` down
  the fields, the field types' laws lifted into the block's table by seven `lift_*` lemmas
  built from `acceptsIn_mono_of_subset` and `List.Mem`/`mem_append_of_left/right` chains (no
  string comparison anywhere in a proof).
- `scoped` is a Lean keyword: the `cases … with` alternative is spelled `| «scoped» b =>`.

### Byte identity and refusals, guarded

`hexOf p = <golden>` for all eight corpus programs against `ocaml/goldens/eff/{p42, pBind,
pFork, pAwait, pGen, pLoop, pCatch, pScope}.hex` (copied literally into the module); `(encode
p42).length = 66`; `(digest p42).hex = fa5f40f054198e91b2446522308e197b0a02c4edfe823f894763d3aa63ad62a3`
(the facts note §6); round trip `decode (encode p) = some p` on the corpus; a byte appended
and a byte dropped refused on the corpus; a leading-zero constructor index inside a program
refused (`Wire.lean:628`, restated); every corpus tree fits `shape (Eff NativeOp)`.

Final census (`RECEIPTS.md`, generated from the replay of the green build): 251 `#print
axioms` lines over the nine modules — 45 with no axioms, 86 `[propext]`, 120 `[propext,
Quot.sound]`, none other. No `lean.exe` or `lake.exe` left running.

The lane's final report is delivered as its closing message to the coordinator (the tool
harness refused to write `REPORT.md` as a file); its content is this file's four entries plus
the command log in the M4 section and the byte-identity receipts above.

### Open after M4

Nothing of the brief's lane S1 list is open. Not done, by design: a proof that
`Canonical.encode = Wire.encodeProgram` as a theorem (the Wire imports the old store, so it
cannot be imported into the spike; the goldens are the receipt, and the equation is one
structural induction once the Wire is rewritten onto these `toVal`s at the landing).
