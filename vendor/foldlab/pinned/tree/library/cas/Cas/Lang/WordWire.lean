import Cas.Lang.Worded
import Cas.Schema.Ast

/-!
# The word's wire records — the receipt and the history document

The word's registry presence. The word already has a registered
spelling as a CONFORMANCE surface — `Cas.Vectors.Wire.VectorBinding`
carries `(address, node)` and a vector's `word` field is a list of
them, emitted and byte-gated through `emitwire`. What had none was the
RUNNING system's word: the per-store log a host appends at admission
time, and the history document `cas history --json` answers. These are
those two records, as ordinary Lean structures; `tools/EmitWord.lean`
derives their canonical schema codes and emits the Effect Schema
mirrors (`WordLogSchema.ts`), byte-identity-gated in `check:cas` —
the same discipline as every other wire shape.

A `LogEntry` is one RECEIPT: the store's own note that one admission
happened. It deliberately carries less than a binding — the address
names the content and the store already holds it, so persisting the
node here would be a second byte plane. What it carries beyond the
address is exactly what rendering a history row needs without a load
(`tag`, `size`) plus the two host-side facts the Lean word does not
model:

- `seq` — THE MARK's registered spelling: the entry's zero-based word
  index. `WordE.since (mark)` consumes it; `History.next` returns the
  next one. Dense by construction (append-only, no deletes), so the
  log's `seq` order IS admission order.
- `at` — epoch milliseconds on the admitting host's clock. Time is
  host territory (the model has no clock), and the timestamp is
  per-device honest: it says when THIS store learned the content,
  which is all a word ever claims (the word does not sync).

`History` is the document `since` answers on the wire: the entries
from the mark, in admission order, and `next` — the cursor the client
never computes itself. The full binding a consumer may want is
`log ⋈ store`: every logged address is resident (the host appends
AFTER bytes land — the crash-safe direction), so joining a receipt to
`load` recovers the `VectorBinding` shape without this record ever
duplicating content.
-/

namespace Cas.Lang.WordWire

/-- One receipt: the persisted record of one admission, in the word's
order. `seq` is the mark (zero-based word index), `at` epoch
milliseconds on the admitting host's clock, `size` the payload's byte
count, `tag` the node's kind tag. -/
structure LogEntry where
  address : String
  -- `at` is a Lean keyword, so the field name is escaped; the wire
  -- spelling is the unescaped `at`.
  «at» : Schema.SafeInt
  seq : Schema.SafeInt
  size : Schema.SafeInt
  tag : Schema.SafeInt

/-- The history document: the word's suffix from a mark, in admission
order, and `next` — the mark of the next entry to be admitted, so the
client never computes its own cursor. -/
structure History where
  next : Schema.SafeInt
  word : List LogEntry

end Cas.Lang.WordWire
