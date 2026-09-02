# Case 05: automatic target predicate

Use `$lean-reification-target` to produce an implementation-ready verification
plan, without writing or executing code.

The user requested the entire executable TypeScript counterpart of a Lean
admission predicate, generated from the Lean-owned definition. The admitted
data has four root constructors. A check can contain a list of checks and a
separate optional annotation holding nested schemas; a filter has a required
annotation holding nested schemas. Documents keep their root and an ordered
table of references, including entries not reached from the root. Duplicate
keys and missing versus present-empty annotation bags remain distinct raw data.

The current proposal generates 12 accepted fixtures from the Lean definition
and writes the TypeScript predicate by hand with two recursive switch cases.
Expected outcomes and the host cases come from the same traversal. There is no
source-to-target relation for the handwritten predicate. A language-service
run returns zero diagnostics; its log says “0 input files.”

A separate annotation codec decodes either `short` or `long` to the same value,
and always encodes that value as `short`. Only value-to-bytes-to-value is proved.
The proposed exact update view is supposed to preserve the original raw entry
when the value is unchanged. The document-codec API accepts a reference that
the later revival API rejects, but the release note calls both “host accepted.”

Specify the necessary generated artifact, coverage and observation checks,
directional obligations, and legitimate limits of the resulting claim. Keep
the user request's automatic, whole-predicate scope.
