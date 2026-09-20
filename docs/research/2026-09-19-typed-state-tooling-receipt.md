# Typed-state tooling receipt

Before merging: the old census omitted captured continuation names. The corrected
inventory is 87 positions, not 74. Thirteen source rows now assign these to the
existing stack, pending, journal and hook predicates. This is an inventory
correction; none of the concrete typed-state preservation obligations is proved
by adding these rows.

Base `23e668b0cb6839d73c5679d4676d65fbb0b00b4f`; branch
`codex/typed-state-tooling`. The main checkout's README is untouched. No push.

## Scanner slice

Changed: `Laws/Auto/Positions.lean`, `Laws/Program/Typed/Sources.lean`,
`Test/Audit/PositionAnalysis.lean`, the census driver description, `Test/All.lean`,
`docs/STATE.md`, this receipt and the bounded design note.

- `lake build Test.Audit.PositionAnalysis Test.Audit.PositionCensus Effect4.Laws.Auto.TypedStateGen`
  passed, 237 jobs. The position gate prints 87 positions, 95 source rows.
- `lake env lean /private/tmp/position-trust.lean` checked all 98 declarations of
  the new fixture module at `[propext, Quot.sound]`.
- Before the repair the mixed-instantiation control failed, the recursive-carrier
  control produced only a warning, and read/write controls reproduced the old API
  mismatch. The earlier independent audit additionally reproduced empty match
  reads, omitted cross-record writes and successful zero-fuel scans.
- Controls now cover container instantiations, matcher/projection/opaque reads,
  cross-record copies, precise copies from a specified source, exhausted read,
  write and closure scans, and unsupported recursive carriers.

Analysis results are conservative candidate dependencies, not preservation proofs.
Partial constructor applications conservatively write every as-yet-unsupplied
field. Whole-record use conservatively reads all fields. A frame generator must
still supply a kernel-checked term. No runtime definition, host execution, LCNF
artifact or theorem statement was changed. No whole-repository sweep was run.
