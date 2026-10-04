# Kripke/TAPL adoption receipt — 2026-10-01 (local)

**For the coordinator:** this changes documentation and the next proof brief only. The owner
ratified row 176(b) and row 184(a). The layer representation repair is still owed; the historical
resume/write probes are not witnesses against the consolidated revision. Gemini's active source,
registry and generated outputs were left untouched. Adopt the packet at a coherent slice.

Base: `01e3118065e64ddc5f9d28f0a0d982b5f8c647cd`. Branch: `codex/metaprogramming` in
`/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4`. The exact resulting head and
clean-status check are recorded after commit in
`/private/tmp/codex-second-eyes-2026-10-01/kripke-adoption/completion.json`.
Main and Gemini's branches were not moved; no push or integration merge was performed.

## Changes

- `docs/core/decisions.md`: only the status cells of 176 and 184, recording the human rulings and
  retaining the outstanding layer evidence and implementation requirements.
- `docs/STATE.md` and `brief-gemini-proofs.md`: remove the obsolete requests for those rulings and
  point the existing M5/M6/M7 sequence to `kripke-adoption/brief.md`.
- `docs/core/semantics.md`: a TAPL/PLF responsibility map, precise Kripke interpretation and
  finite structural justification, and a denotation summary that retains its actual premises.
- `docs/core/system-map.md`: align the weakest-precondition, universal-monotonicity and
  non-halting descriptions with the definitions. Its S1 criterion now requires the actual
  transport conditions and transition proofs rather than a false universal monotonicity claim.
- This folder: a bounded adoption brief, two read-only reviewer notes, and byte-identical copies
  of two historical probes with their passing logs and command receipts. No production Lean
  declaration was added or changed.

The tasks are K0 (interpretation/role corrections), K1 (restricted resume transport at a real M6
consumer), and K2 (existing store adequacy used by M5/M6). A subsequent progress question reuses
the already-open `scheduler-progress` claim. The helper adoption is conditional on verification
at the implementation revision. Existing closed goals are not reopened or counted twice.

## Verification

- `python3 docs/research/2026-10-01-semantics/check-gemini-drafts.py docs/core/semantics.md`
  returned exit 0 / PASS: 60 document locators. Its legacy draft registry check counted 51
  claims and repeated 14 already-pending literature-key links; it does not validate the current
  57-claim report or replace environment validation.
- `python3 /private/tmp/codex-second-eyes-2026-10-01/kripke-adoption/finalize.py` returned exit 0:
  10 exact declaration locators, 4 PLF source locators, both retained probe hashes and all 21
  historical printed axiom footprints checked. See `validation.json`.
- `git diff --check` returned exit 0. Tracked changes were restricted to the five named documents;
  the registry and generated reports were compared byte-for-byte against the base and are unchanged.
- No compiler, generator, target-runtime test or full build ran this turn. Earlier probe exits
  and times are historical, explicitly pinned to `845ce06e`, with their original commands retained.

## Remaining work and limits

Gemini's next slice owns the two registry role corrections and regeneration; this documentation
patch does not silently mark any claim proved. Its first term adapter was already committed on
`gemini/proofs` at `a8cc8866` when inspected. Do not repeat it. Recheck the relevant imported
artifacts and probes before adopting the resume helpers against the changed definitions.

Decisions text is a semantics-check input. On integration, refresh/check through the existing
semantics producer after preparing that revision's artifacts, even though these two rows are not
selected cuts in the current registry. This receipt does not claim an updated producer check.

TAPL contents were verified from the author's site; theorem-level detail was read from the
separately vendored PLF text. The Pierce-informed critique is our interpretation, not attributed
personal advice. No result here establishes full metatheory coverage, scheduler progress,
runtime safety, contextual equivalence or target correctness.
