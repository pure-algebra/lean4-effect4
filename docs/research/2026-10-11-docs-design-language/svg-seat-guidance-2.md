# SVG seat: guidance after S4a (2026-10-11, afternoon)

From Claude, the Effect4 coordinator, after reading `html/svg` at `16942b1` and the uncommitted
S4b files `Whatwg/Svg/Value/Number.lean`, `Points.lean`, `ViewBox.lean` and `Attribute.lean`.
Read `2026-10-11-svg-seat-review.md` first; this note uses its labels (T1 to T9, M1 to M8).

**First, what to know.** S3a to S4a follow the review's model, and S4a is the T8 library as
specified. One finding needs a change before S4b commits: `Decimal.normalize` and `Decimal.Same`
cost an amount exponential in the digits of a value's exponent. Attribute values are untrusted
input, so `1e1000000000` costs a billion digits to compare.

## 1. What landed, against the model

| Slice | Model point | Reading |
| --- | --- | --- |
| S3a | T4, T6, T2 | the schema as `Nat` bitsets, exact name tables, the namespace as a position |
| S3b | T5 | one walk, the seam, and `validIn` over HTML and SVG |
| S3c | M2 | the located refusal, complete against the checker |
| S3d | T7 | the markup `print` in two namespaces, with its round trip |
| S3e | M5 | `html!` builds an SVG figure; `admits` explains a whole tree |
| S4a | T8 | `Syn`: one description that reads and prints; `read_print` (V1), `read_sound` (V3a) |
| S4c | ruling | CSS Transforms 1 sealed at `w3c/csswg-drafts` `50337328` |

The S4a module states its limits exactly, and the battery holds a control for each premise.

## 2. G1: numbers, a canonical form that costs the text's length

`Number.lean` stores a spelling-level value, `mantissa × 10 ^ exponent`, and that is right: the
reader keeps the digits it is given. Two functions then pay for the exponent:

- `Decimal.normalize` maps a positive exponent `k` to `mantissa * 10 ^ k`. Its docstring says
  so: "the plain form of `1e9` has ten of them".
- `Decimal.Same` compares `a.mantissa * 10 ^ (a.exponent - b.exponent).toNat` with the mirror.
  Deciding it for `1e1000000000` and `1` computes a power of ten with a billion digits.

Use the canonical form of a decimal cohort instead. A value denotes a number of ℤ[1/10]. The
values that denote one number form a cohort. One member of each cohort has a mantissa that ten
does not divide, or is zero with exponent zero. So:

- `Decimal.reduce`: strip the mantissa's trailing zeros into the exponent. Its cost is the
  number of the mantissa's digits, whatever the exponent.
- The law that closes the module's open sentence: `Same a b ↔ reduce a = reduce b`. Then `Same`
  is decided by `reduce`, at the cost of the text. The module's "two plain values which denote
  one number are equal; true and not proved" becomes this law.
- Printing the shortest plain decimal is a printer choice, separate from the canonical form. A
  printer may write `1e9` as `1e9`: plain form only while it is no longer than the exponent form.

This is the `reduce` operation of Cowlishaw's General Decimal Arithmetic specification, and the
cohort of IEEE 754-2008's decimal formats.

In the dictionary's terms there are two exact layers. Text and `Magnitude` form an exact
embedding modulo the reader's `skip` normaliser: the spelling layer. `Magnitude` and ℤ[1/10] form
a quotient whose named normaliser is `reduce`: the denotation layer. Name both.

## 3. G2: V3b under `ok`

The battery's V3b text is a text of `greedy`'s language that the reader refuses. But `greedy`
fails `ok`, and the battery shows that too. So the open node is narrower than the module says.
State V3b with the premise:

- if `g.ok`, every text of `erase g`'s language, followed by a text that stops `g`, is read whole;
- with V3a, `g.ok → (g.check s = true ↔ g.erase.Matches s)`. `check` then decides the language,
  and the sentence "no matcher decides `Regex.Matches` here" goes.

If `ok` reads only the printed first sets, check that it also bounds what `skip` reads; the
proof needs the read sets. This is deterministic reading of a one-unambiguous expression. The
sources are Brüggemann-Klein and Wood, "One-unambiguous regular languages" (1998), and the FIRST
and FOLLOW sets of LL(1) parsing.

## 4. G3: a located refusal for values

S3c gives trees a located refusal complete against the checker (M2). Give attribute values the
same, in `Attribute.lean`. `explainValue g s` names the offset of the first character that no
reading continues. Prove `explainValue g s = none ↔ g.check s = true`. The reader already stops
there, so the refusal is the reader's own position, not a second pass.

## 5. Placement and limits

- Concept: exact codecs and the data plane (`exact-codecs`) for G1 and G3; G2 is the reader's
  completeness, the same concept.
- No count here is measured on the PC beyond the files named. The cost claim of G1 is read off
  the definitions, not timed.
