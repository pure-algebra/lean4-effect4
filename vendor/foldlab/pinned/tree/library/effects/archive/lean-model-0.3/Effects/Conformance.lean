import Effects.Conformance.Markdown
import Effects.Conformance.Json
import Effects.Conformance.ModelVersion
import Effects.Conformance.Manifest
import Effects.Conformance.ManifestReplay
import Effects.Conformance.Ledger
import Effects.Conformance.Mutant
import Effects.Conformance.Registry
import Effects.Conformance.Obligations
import Effects.Conformance.Generate
import Effects.Conformance.Briefing

/-!
# Conformance schema bundles

Scaffolding for the ratified conformance workflow (`CONFORMANCE-WORKFLOW.md`
sections 4, 5, and 10, with the M1 refinement recorded in its section 14):
each ratified schema family is a structure whose fields are the template's
holes, whose laws are proof fields, and whose anti-vacuity kit is also
fields. An obligation instance is a term of the family structure — a term
without its law or kit does not elaborate, so proved-with-kit is the only
representable state for Lean-side artifacts.

Layout, one concept per file:

- `Markdown` — the typed human-surface emitter (escaped by default,
  arity-checked tables, the `ToMarkdown` projection typeclass);
- `Reflected` — the cross-cutting checker/judgment iff form;
- `Ledger` — `LedgerEntry` and the Lean-side ledger projection;
- `Schema/<Family>` — one file per ratified family (WF-PRESERVE,
  TRACE-EXCLUDES, EXACT-STEP, FAIL-CLOSED, DISTINCTNESS, HOMOMORPHISM,
  CODEC, REJECTION-CLAUSE, and AGREEMENT from the remote Pass A), each
  carrying its sentence and kit templates in the docstring and its
  `entry` ledger projection;
- `Mutant` — the declared-mutant carrier; and
- `Registry` — the instance registry the ledger projects from.

Docstrings carry the ratified sentence *templates*; the `sentence` field on
each instance carries the filled plain-meaning sentence in the minted domain
vocabulary. Instances arrive with the milestone slices (M2 for CODEC and
REJECTION-CLAUSE, M3 for the replay families). Field shapes may be refined
at Pass B through the ordinary amendment path; a *new family* remains a stop
condition.
-/
