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
