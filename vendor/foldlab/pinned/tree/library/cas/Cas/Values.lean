import Cas.Values.Cut
import Cas.Values.Digits
import Cas.Values.Json
import Cas.Values.JsonInj
import Cas.Values.JsonParse
import Cas.Values.Markdown

/-!
# CasValues — the substrate every address is computed over

This is the bottom of the library, and the published root of the
`CasValues` stratum. Everything here is about VALUES and how they are
spelled as bytes. Nothing here knows that a store exists.

It rests on one type and one function. `Value` (`Json`) is the
canonical JSON value — null, booleans, integers, strings, arrays,
objects, and deliberately no float. `renderCompact` is its canonical
spelling: object keys sorted by codepoint, no whitespace, one number
form. `JsonInj` proves that spelling INJECTIVE, so two different values
never print the same bytes, and `JsonParse` proves the parser accepts
exactly the printer's image and inverts it there. `Digits` is the
decimal spelling those proofs stand on, inverted through `Nat.repr`
injectivity. `Markdown` is the typed emitter behind the human-facing
surfaces — ledgers, briefings, manifest docs — which are byte-compared
gate surfaces and so need a total renderer rather than string
concatenation. `Cut` is the other direction on the same object: how a
spelling is taken APART and put back — `IsCutting cut` says the pieces
join to the string, with one proved fixed-size cutter — which is what a
streaming lane owes the exchange node's verbatim promise before it
writes an answer in segments.

Why a reader above should care: an address is a hash of bytes, so
whatever decides the bytes decides identity. The injectivity proved
here is what makes "same address" mean "same value" instead of "same
value, probably". Every content address in this library is computed
over a rendering proved correct in this stratum, and no layer above
re-opens that question.

## What belongs here

Value machinery that needs nothing but Lean: the value type, its
renderers, its parser, and the arithmetic those proofs rest on. The
test is mechanical rather than a matter of taste — a module belongs
here only if it compiles with no `import Cas.*` outside `Cas.Values`.

## What never belongs here

Anything that mentions the model. Nodes, stores, addresses, admission,
schemas, grammar, programs: all of that is the `Cas` stratum and above.
A module that reaches for `Cas.Core` has stopped being substrate and
become a consumer of the store, whatever directory it happens to sit
in.

Publishability: this stratum stands alone. `lake build CasValues`
builds it with nothing else in the package behind it, so it could ship
as its own package without dragging the store along.

## The two neighbours that left

`Cas/Values/Canonicalize.lean` and `Cas/Values/Refs.lean` used to sit
in this directory and were never in this stratum: both import
`Cas.Core`. They MOVED at the meta-home migration, each into the
`Cas` stratum beside what it actually consumes —

- `Cas/Core/Canonicalize/Json.lean` — the key-sorting normalizer
  packaged as the store's `Canonicalizer Value` instance, now beside
  the class it instantiates. It keeps the `Cas.Json` namespace: the
  directory names the stratum, the namespace names the object;
- `Cas/Core/Refs.lean` — the typed-reference marker grammar and the
  `Root` type, which state store semantics outright (up to
  `Root.closed_deref` over `Store.Closed`), now beside `Core.Store`.

Their debt markers (`values-canonicalize-misfile`, `values-refs-misfile`)
were struck and replaced by `discharges(…)` rows in the moved files, so
the obligation ledger carries the paired lifecycle and the debt ledger
carries neither.

The library's globs still name this stratum's modules one by one rather
than globbing the `Cas.Values.*` subtree. The reason survived the move:
an explicit list refuses the next misfile at the boundary instead of
admitting it and its whole import closure.

The declared strata order, and the rule that keeps it, are written at
the head of `library/cas/lakefile.toml`, where the boundaries are
actually declared.
-/
