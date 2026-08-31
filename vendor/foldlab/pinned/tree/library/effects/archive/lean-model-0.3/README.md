# Retired: the effects-model@0.3.0 dual-lane conformance corpus

Retired 2026-08-28 by operator ruling, archived in place — nothing
deleted. This directory holds the complete Lean lane of the effects
library at its last green state: the model (`Effects/`), the generated
conformance manifests and ledger, the mutant quarantine (34 declared
mutants), the four gate executables, and the two lane-specific gate
scripts. The tag `archive/effects-model-0.3` marks the last commit
where this corpus lived at the package root.

It remains a self-contained Lake project: `lake build` here still
builds it, and the archived mise tasks (`check:effects:archive`,
`gen:effects:archive`) still run its gates. The manifests bind to
`effects-model@0.3.0` and are frozen with it; regeneration under this
version must stay byte-identical.

Why retired: the library pivoted to the seam-shaped CAS design
(`@foldlab/cas` — byte-plane seams, typed references, three planes),
and the fresh Lean lane models the new shape's types first. That model
lives at `library/cas`, seeded from this corpus's carriers (node,
codec, store, address, admission), its canonical JSON model, and the
typed-reference marker grammar. The Merkle modules
(`Effects/Merkle/*`) are preserved here intact and are the first
candidates for resurrection when the reconciliation program resumes.
