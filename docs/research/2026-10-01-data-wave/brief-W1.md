# Seat W1: exactness for today's `Ty` (commit 1; row 128, TY-09)

Filled at dispatch: base (main after probes P and S land), the `P/note.md` question-5 and
`S/note.md` question-1 sections to read. Rules: `README.md` here ("Landing style", "Testing
during the wave"), plan §4, `AGENTS.md`.

**The one thing.** Row 128 is ruled: `Ty.ofSchema` and the JSON codec are retractions today and
become exact embeddings here, before any new form touches them. Exactness is modulo a named
normaliser, as the vocabulary defines it (`AGENTS.md`: `read v = some a → v ≡ write a`).

## The work

1. **The JSON codec.** `decodeRaw`'s union arm selects the encoder's canonical branch (the
   `Success`/`Failure` image confusion at `union (except nat nat) (exitOf nat nat)` is the red
   control, synthesis NS2); `N_J`, the key-order normaliser, as a function on `Json`; the theorem
   `decode j = some v → j ≡_{N_J} encode v` beside `decode_of_encode`; `encode_sub` kept.
   `Laws/Schema/Codec.lean`, `Schema/Codec.lean`.
2. **The Schema bridge.** `ofSchema` compares whole checks and refuses `TypeParameter` by name;
   `N_S` as a function on `Representation`; the theorem `ofSchema r = some t → r ≡_{N_S} schema t`
   beside `ofSchema_schema`. `Schema/Bridge.lean`, `Laws/Schema/`.
3. **The vocabulary.** `AGENTS.md`'s exact-embedding bullet and system map §4 stop calling them
   retractions (propose the lines; coordinator's files).
4. Narrow builds; the batteries that read the codec (`Test/Schema/`, the `schema-codec` gate)
   green; `#print axioms`. No generator.

Receipt `receipt-W1.md`: the two theorems (name, file:line, axioms), the normalisers' definitions,
the red controls kept, the proposed lines for row 128 and the vocabulary.

## Filled from probe S (2026-10-01; `type-language-probe/S/note.md` §7.1, §1, §4, §6)

- **Reference on a copy:** `S/probes/K2Copy.lean`; production idiom in `S/patches/*.after`
  (`Bridge.lean.after`, `Codec.lean.after`, `LawsSchemaCodec.lean.after`).
- **The canonical-branch check** in `decodeRaw`'s union arm: `(decodeRaw a j).filter (hasTy · a)`,
  else `(decodeRaw b j).filter (fun v => hasTy v b && !hasTy v a)`; red control `red_productionExact`
  (production decodes the `Success` image at `union (except nat nat) (exitOf nat nat)`). Recorded
  limitation until the signed frame (commit 3): at `union int (except nat nat)` a `Result` failure's
  JSON is outside the image while `Int`'s image is `ctor 0 [nat n]`.
- **The normalisers as functions:** `N_J` a recursive stable object-key sort (`K2Copy.lean` §11);
  `N_S := cata_representation nsAlg`, annotation bags erased and an `anyOf` right spine flattened
  (§6); exactness stated at the bridge (`Bridge.schema`/`Bridge.ofSchema`, beside `ofSchema_schema`),
  where `N_S` sorts nothing (`red_unsortedNS` records what the public-writer statement would need).
- **Choose the exactness route first:** (b) the plain readers by construction (an induction over
  `Representation` with its nested lists, and over `Ty` with the canonical sort's permutation lemma
  for `N_J`; tested on S's 23 inputs, not proved); fall back to (a) the guarded readers
  `ofSchemaExact`/`decodeExact` (proved on the copy, `ofSchemaExact_exact`, `decodeExactP_exact`, one
  re-encode per read) and record (b) as owed.
- **Whole checks:** the `isInt` filter with payload `null`, no `schemas`, not aborted, documentation
  annotations only; `[isInt, ≥ +0]` for `nat`; anything else refused at `["checks[i]"]` (red:
  `red_ge5`, `groupedInt`). **`TypeParameter`** refused by name (`red_typeParameter`).
- **The defect id** (`E4-SCHEMA-CE-061`): `defectRep` and `isDefect` name `effect/schema/Json`
  (`Bridge.lean:35`, `:70`); `S/host/q4-defect.ts` becomes the green twin.
- **If row 121's safe-integer bound is ruled:** `nat`/`int` refuse |n| > 2^53 − 1 at encode and
  decode, with 2^53 and −2^53 as red controls (`K2Copy.lean:1749`, `red_int2p53`).
- P's half (question 5 of its brief) is filled when P lands.

## Amendments at dispatch (2026-10-01, probe P merged at `714d2601`)

Route (b) is proved on probe P's copy at today's forms (`P/probes/P8Codec.lean`, `P8Schema.lean`;
decisions row 128 amended, row 179 ruled: seat S's allowlist is the one annotation policy of `N_S`
and the reader's guard). Take it, not the guard. P's brief text, your steps:

1. `Schema/Codec.lean`: `decodeRaw`'s union arm reads its second branch only for a value that is
   not a member of the first (`P8Codec.lean:408`). `N_J` is `normJ` (`:47`): a stable sort of
   every object's entries by key bytes, recursively.
2. `Laws/Schema/Codec.lean`: `decodeRaw_normJ` (`decodeRawC_normJ`, `:487`; its lemmas
   `fields?_normJ`, `payload?_normJ` and the four sub-decoders' versions), `decodeRaw_exact`
   (`:851`; `nat?_exact`, `fields?_two`, `payload?_exact`, `normJ_tagged_of_payload`, the
   sub-decoders' exactness), then `encode_of_decode` and `decode_iff` (`:1053`, `:1088`) beside
   `decode_of_encode`; the red control `codec_not_exact` (`:1108`) as a fixture.
3. `Schema/Bridge.lean`: `ofSchema` with whole checks, the `TypeParameter` refusal, the
   annotation guard first in each arm and `isDefect` reading the defect slot's annotations
   (`P8Schema.lean:89`); `N_S` the fold `normS` (`:76`) with row 179's `normAnn` (S's allowlist);
   `ofSchema_exact` by `fun_induction ofSchema` (`:411`; 39 cases), `normS_schema`, the
   retraction with `reservedFree` (or `schemaWf`). Red controls `:170`, `:176`, `:186`.
4. Every proof in `P8Codec.lean` and `P8Schema.lean` is `[propext, Quot.sound]`, uses no `try`,
   `first` or `simp_all`, and states its `simp` as `simp only`; copy them, renaming `C`.

Seat S's half (above, from S §7.1) stands where it does not conflict; where S wrote "exactness
by a guard", P's plain-reader proof replaces it. The register: `E4-SCHEMA-CE-061` stays as the
defect-id finding (S); the red controls above are fixtures, not register rows, unless one changes
a declaration. Codex's 20:16 finding (`E4-SCHEMA-CE-062`) is W5's, not yours.

## Amendment 2 (2026-10-01, Codex 21:16, verified): check annotations

Row 179 covers a check's annotations too (sent to the seat by message): `N_S` applies `normAnn`
in its `check_filter`/`check_filterGroup` arms, the number arm compares the normalised whole check
with the bare `isIntCheck`/`nonNegativeCheck`, the number case of `ofSchema_exact` is extended,
and three controls land: the documented `isInt` accepted at `int` (with the nonnegative check at
`nat`), the same check with a non-documentation key refused at `["checks[i]"]`, S's `red_ge5` and
`groupedInt` still red.
