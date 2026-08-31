/-!
# The cut law — a segmented answer is still the answer

An exchange node promises its `answer` verbatim: "the bytes are kept as
spoken and are never normalized here" (`Cas/Schema/Exchange.lean`).
A streaming lane cannot honour that promise by writing one node at the
end — it writes the answer in pieces as they arrive, and the pieces are
what the store holds. Nothing in this library said the pieces
CONCATENATE BACK, and until something does, a buffer change can falsify
the verbatim claim without failing a gate.

That statement is this module, and it is one line:

```text
IsCutting cut  ⇔  ∀ s, String.join (cut s) = s
```

## Who consumes it

The streaming lane — `QUERY-ENGINE.md` adoption 7, ruling ask QE-4 —
takes `IsCutting` as its entry condition, paired with a HOST rule the
model deliberately does not state: the ingest buffer runs the
`suspend` strategy, never `dropping` or `sliding`. The pairing is the
whole design. A dropping buffer loses pieces, and a cutter that never
sees a piece cannot put it back; `IsCutting` is a property of the
CUTTER and is powerless against a lossy transport. Together they say
what the exchange node claims: the answer the store holds is the answer
that was spoken, in order, entire.

What stays host discipline, and should be said to stay: WHICH cuts are
taken. Size, stall timeout, boundary heuristics, cadence — the model
needs only that the cuts concatenate, never where they fell, which is
what keeps the scheduling policy free to change without touching a
theorem.

## Boundary decency — what `IsCutting` does NOT buy

`IsCutting` protects the JOIN. It says nothing about whether a single
piece is meaningful on its own, and the streaming lane needs both.

On this toolchain (`leanprover/lean4:v4.33.1`) the estate's `String` is
a `ByteArray` carrying a proof that its bytes are valid UTF-8, so a
cutter of type `String → List String` cannot split a codepoint: the
type refuses to hold the fragment. Codepoint safety is therefore a TYPE
fact here, not a theorem, and `chunkAt` inherits it for free — it cuts
by CODEPOINT COUNT.

The hazard lives one level down, at the seam this model does not
describe. A host buffer works in BYTES; a cutter that slices a byte
buffer at a fixed byte offset can land mid-codepoint, and the resulting
fragments still satisfy the byte-level join — the answer is recovered
verbatim — while no individual fragment is a well-formed string.
Anything that reads a piece ALONE (a streaming render, a per-piece
annotation, a search over run nodes) then sees a broken character. So
the real cutter owes one guarantee beyond `IsCutting`: **every cut falls
on a codepoint boundary**, which is a decency property of the piece, not
of the join, and is not implied by anything below. It is stated here as
a note rather than proved because the byte seam has no carrier in this
library; when it gets one, this is the statement it owes.

## Where this module sits

The `CasValues` stratum, whose membership test is mechanical: a module
belongs here only if it compiles with no `import Cas.*` outside
`Cas.Values`. This one imports nothing at all. It is value machinery in
the same sense the printers are — how a value is spelled, and here how
a spelling is taken apart and put back — and it knows nothing about
nodes, addresses, or the exchange kind that motivated it.

## The axiom note, measured

`IsCutting` and `String.join` are clean (`propext`). The reference
cutter is not, and the cause is core rather than this file: on v4.33.1
`String.toList`, `String.foldl` and `String.length` each depend on
`Classical.choice`, because the character view of a `ByteArray`-backed
`String` is built through it. Any cutter that inspects characters
inherits that dependency, so `chunkAt` and its proof carry
`Classical.choice` and no spelling in this module avoids it. The
statement of the law does not.
-/

namespace Cas.Values.Cut

/-! ## The law -/

/-- A cutter is CUTTING when its pieces concatenate back to what it was
given. `String.join` is core's own fold — `foldl (· ++ ·) ""` — so this
is the estate's spelling of `concat (cut s) = s` and not a second one.

The quantifier is over every string, deliberately: a property that held
only on the strings a particular model emitted would protect nothing,
since the whole risk is the answer nobody anticipated. -/
def IsCutting (cut : String → List String) : Prop :=
  ∀ s : String, String.join (cut s) = s

/-! ## The bridge to characters

`String.join` folds with an accumulator, so it needs a seed lemma before
it reads as a concatenation — the same shape `Aggregator.foldr_seed`
plays for the query layer, and for the same reason: the identity laws
are consumed in exactly one place. -/

/-- Folding into a seed prepends the seed. The one lemma the join needs,
and the only place `String`'s append laws are used. -/
theorem toList_foldl_append (l : List String) (init : String) :
    (l.foldl (· ++ ·) init).toList
      = init.toList ++ (l.map String.toList).flatten := by
  induction l generalizing init with
  | nil => simp
  | cons s rest ih =>
    show (rest.foldl (· ++ ·) (init ++ s)).toList = _
    rw [ih, String.toList_append, List.append_assoc]
    rfl

/-- The join, read as characters: a list of strings joins to the
flattening of their character lists. Every cut-law proof goes through
here. -/
theorem toList_join (l : List String) :
    (String.join l).toList = (l.map String.toList).flatten := by
  show (l.foldl (· ++ ·) "").toList = _
  rw [toList_foldl_append, String.toList_empty, List.nil_append]

/-! ## One reference cutter

Fixed-size chunking, the simplest cutter a streaming lane would actually
run: emit a piece every `n+1` characters. The size is spelled `n+1`
rather than `n` so that it is POSITIVE by construction — a zero-size
cutter emits infinitely many empty pieces and is not a cutter at all,
and refusing it in the type is cheaper than refusing it in a
precondition every theorem then carries. -/

/-- Fixed-size chunking of a character list, pieces of `n+1` and a
shorter remainder. Well-founded on the list's length: each step consumes
at least one character because the piece size is positive. -/
def chunkChars (n : Nat) : List Char → List (List Char)
  | [] => []
  | c :: cs => (c :: cs).take (n + 1) :: chunkChars n ((c :: cs).drop (n + 1))
termination_by l => l.length
decreasing_by
  simp only [List.length_drop, List.length_cons]
  omega

/-- The chunks of a character list flatten back to it — the cut law one
level below `String`, where it is `List.take_append_drop` at every
step. -/
theorem flatten_chunkChars (n : Nat) (l : List Char) :
    (chunkChars n l).flatten = l := by
  induction l using (chunkChars.induct n) with
  | case1 => simp [chunkChars]
  | case2 c cs ih =>
    rw [chunkChars]
    show (c :: cs).take (n + 1)
        ++ (chunkChars n ((c :: cs).drop (n + 1))).flatten = c :: cs
    rw [ih, List.take_append_drop]

/-- The reference cutter: pieces of `n+1` CODEPOINTS. Cutting by
codepoint rather than by byte is what makes each piece independently
well-formed; see the boundary-decency note on the module. -/
def chunkAt (n : Nat) (s : String) : List String :=
  (chunkChars n s.toList).map String.ofList

/-- THE REFERENCE CUTTER IS CUTTING. One proved inhabitant, so
`IsCutting` is satisfiable and not a definition nothing meets — and so
the streaming lane has a cutter it may adopt outright rather than a
shape it has to invent. -/
theorem chunkAt_isCutting (n : Nat) : IsCutting (chunkAt n) := by
  intro s
  apply String.ext
  rw [toList_join]
  show (((chunkChars n s.toList).map String.ofList).map String.toList).flatten
      = s.toList
  rw [List.map_map]
  have hid : String.toList ∘ String.ofList = id := by
    funext l
    exact String.toList_ofList
  rw [hid, List.map_id]
  exact flatten_chunkChars n s.toList

end Cas.Values.Cut
