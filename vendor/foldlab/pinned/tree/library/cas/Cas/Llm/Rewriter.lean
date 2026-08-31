/-!
# The rewriter — a frozen text transformer

A REWRITER is one pinned completion call read as a plain
`String → String`. This is the app-architecture kind: at the host an
LLM call is an async string transformer and NOTHING SPECIAL; frozen —
the reading `Judge` already takes — it is a pure function.

A `Rewriter` is deliberately NOT a `Judge`, and neither kind is
defined in terms of the other. Verdicts SELECT; rewrites PRODUCE. A
judge partitions strings that already exist and mints none; a rewriter
emits a string that was not there before. Fusing them would hang
production off a predicate's trust story, so the two kinds stay
apart.

Everything below is composition, and that is the whole content:

- **A pipeline is `andThen`** — a monoid on `Rewriter` with
  `Rewriter.id` as unit (`andThen_assoc`, `id_andThen`, `andThen_id`),
  so stages regroup without changing what the pipeline produces.
- **Schema-forced output is `Into`.** The production harness
  constrains decoding to a JSON schema; as a law that is exactly
  "every output lands in the sublanguage `Q`". The LAST stage decides
  the output language (`Into.andThen_left`), staged contracts chain
  (`Into.andThen_chain`), and an `Into` is a fortiori a `Preserves`
  (`Into.preserves_of`).
- **A canonicalizer is an `Idempotent` rewriter** — re-running it is
  inert (`Idempotent.andThen_self`).

Idempotence is STATED, never assumed, because the estate's own
canonicalizer failed exactly there. CX-003 (audit finding F-40) was an
INVOLUTION where an idempotent was required: field canonicalization
reversed duplicate-key runs, so a PALINDROMIC duplicate-key record was
byte-equal to its own re-canonicalization and the
re-canonicalize-and-compare admission check waved it through.
`R (R s) = R s` is the canonicalizer's law; `R (R s) = s` is a
different law that survives the same casual reading.

Pinning discipline: the mathematics is free of it, the practice is
not. A real rewriter enters gated work only as a pinned artifact, in
the judge-pin schema shape (decision 36f) — architecture and decoding
parameters, corpus and its collectors, checkpoint digest, verbatim
prompt, who pinned it and when — with its provenance surfaced to the
human (decision 36d). The uninterpreted function is what is proved
about; the pin is the only place anything is claimed about a
particular one.

Like `Judge`, this module imports nothing: a text transformer is
prior to the store, and every theorem holds of an arbitrary one.
-/

namespace Cas.Llm

/-- One FROZEN completion call: a pinned model, prompt and parameters,
read as the transformer it is. The same input always produces the same
output. A real LLM is a DISTRIBUTION over rewriters; the distribution
is never modeled here. -/
def Rewriter : Type := String → String

/-! ## The pipeline monoid -/

/-- The rewriter that changes nothing — the pipeline unit, and the
degenerate canonicalizer. -/
def Rewriter.id : Rewriter := fun s => s

/-- Pipeline composition in READING order: `R` runs first, then `S`
consumes what it produced. -/
def Rewriter.andThen (R S : Rewriter) : Rewriter := fun s => S (R s)

/-- Staging is associative: how a pipeline is bracketed is not
observable in its output, so a three-stage rewrite may be built as a
prefix pair or a suffix pair at will. -/
theorem Rewriter.andThen_assoc (R S T : Rewriter) :
    (R.andThen S).andThen T = R.andThen (S.andThen T) := rfl

/-- Left unit. -/
theorem Rewriter.id_andThen (R : Rewriter) :
    Rewriter.id.andThen R = R := rfl

/-- Right unit. With `andThen_assoc` and `id_andThen`, `Rewriter` is a
monoid under composition — the same shape the free monoid of names
carries, and the reason a pipeline is data rather than control flow. -/
theorem Rewriter.andThen_id (R : Rewriter) :
    R.andThen Rewriter.id = R := rfl

/-! ## Output contracts -/

/-- SCHEMA-FORCED OUTPUT as a law: every output lands in the
constrained sublanguage `Q`. This is what a JSON-schema-constrained
decode buys, stated of the transformer rather than of the harness that
enforces it — the property a caller may then reason from. -/
def Rewriter.Into (Q : String → Prop) (R : Rewriter) : Prop :=
  ∀ s, Q (R s)

/-- Invariant preservation: what went in holding `P` comes out holding
`P`. Weaker than `Into` and the right statement for a rewrite that
must not destroy a property it did not establish. -/
def Rewriter.Preserves (P : String → Prop) (R : Rewriter) : Prop :=
  ∀ s, P s → P (R s)

/-- The LAST stage decides the output language: whatever a pipeline
does upstream, a final schema-forced stage constrains the whole of it.
No hypothesis on `R` at all. -/
theorem Rewriter.Into.andThen_left {Q : String → Prop} {R S : Rewriter}
    (h : S.Into Q) : (R.andThen S).Into Q := by
  intro s
  exact h (R s)

/-- Staged pipelines CHAIN their contracts: `R` lands in `P`, `S`
carries `P` to `Q`, so the pipeline lands in `Q`. This is how a
multi-stage rewrite earns a contract its last stage cannot state
alone — the second stage only has to be right on the first's
image. -/
theorem Rewriter.Into.andThen_chain {P Q : String → Prop} {R S : Rewriter}
    (hR : R.Into P) (hS : ∀ s, P s → Q (S s)) : (R.andThen S).Into Q := by
  intro s
  exact hS (R s) (hR s)

/-- An `Into` is a fortiori a `Preserves`: a rewriter that always
lands in `Q` in particular never leaves it. The input hypothesis is
discarded, which is exactly why the two are distinct statements. -/
theorem Rewriter.Into.preserves_of {Q : String → Prop} {R : Rewriter}
    (h : R.Into Q) : R.Preserves Q := by
  intro s _
  exact h s

/-! ## Canonicalization -/

/-- The CANONICALIZER'S LAW: a second pass changes nothing. Stated,
never assumed — `R (R s) = s` is the involution that passed for this
once (CX-003) and is a different property entirely. -/
def Rewriter.Idempotent (R : Rewriter) : Prop := ∀ s, R (R s) = R s

/-- An idempotent rewriter absorbs itself in a pipeline, so a
canonicalization stage may be inserted anywhere downstream of itself
without cost. The converse of the CX-003 defect: under the real law,
re-canonicalization is inert as a PIPELINE and not merely
pointwise. -/
theorem Rewriter.Idempotent.andThen_self {R : Rewriter}
    (h : R.Idempotent) : R.andThen R = R := by
  funext s
  exact h s

end Cas.Llm
