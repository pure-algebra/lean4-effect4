# Seat W7: error payloads (commit 7; row 120 as probe T amends it)

Filled at dispatch: base (main after W4 and W6 merge), P's laws for the payload carrier, R's Q3
class forms. Rules: `README.md` here, plan §4, `AGENTS.md`.

**The one thing.** A program may fail with a handle-free record or variant payload: the carrier
with its exact embedding into `Val` (row 120), `Err`'s image, `FitsCause` unchanged in form, the
six handle-freeness lemmas kept true (`Err.image_handleFree`, `Defect.image_handleFree`,
`causeImage_handleFree`, `Val.keys_exitErr`, `valOfErr_keys`, `keys_of_cause`), the truth wire's
`errJson`, the engine's `Err` through LCNF; a payload field typed `unknown` admitted only with
the handle check the carrier needs, or refused by name (row 120 (a)); message-only and no-field
classes as today (c). The face (commit 8) prints one `Data.TaggedError` class per tagged payload
type, named by its tag, constructed with `new` (b).

## The work

1. The carrier and its embedding; the six compile-forced `Err` definitions (`Err.image`,
   `instReprErr.repr`, `Defect.ofError`, `valOfErr`, `Codec.encodeErr`, `RunnerGen.ErrC.toVal`);
   the lemmas re-proved; `errJson`; the engine's `Err` regenerated in the fixed order.
2. `FitsExit`'s failure arm with H2 part one's exclusions kept; DI-62 amended (propose the line).
3. Narrow builds; `dune build`, `make check-ocaml`; the batteries for p1, p2, p3, p5's error
   fields as red/green pairs.

Receipt `receipt-W7.md`: the carrier, the lemmas (axioms), the generated files, the lines for row
120 and DI-62.
