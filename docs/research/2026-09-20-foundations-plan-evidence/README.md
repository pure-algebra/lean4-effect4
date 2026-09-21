# Evidence for the foundations plan note (2026-09-20)

Scratch probes run with `lake env lean <file>` from the repository root against the compiled
tree at `10d5c009` (editor language-server workers were the only other Lean processes).

| file | what it showed |
| --- | --- |
| `IncludeProbe.lean` (`lean` alone, no imports) | `include h` binds `h` into the theorem, not the def |
| `IncludeAudit.lean` | obligation/theorem binder counts: `fork_rel` 15/18, `forkIn_rel` 16/19, `raceAll_rel` 11/14, `actionAt_fork` 6/8, `actionAt_forkIn` 7/9, `actionAt_not_forkScoped` 6/8, `actionAt_raceAll` 6/7 |
| `AdjacentProbe.lean` | `actionAt_fork` and `actionAt_forkIn` hold without the source-location premise (the only residual goals are reflexive equalities left by the `first` combinator); `actionAt_not_forkScoped` closes |
| `PredsProbe.lean`, `PredsProbe2.lean` | kernel prints of the generated `*Ok` predicates and `Columns.*` at HEAD |

These are research probes, not batteries; slice 1 promotes the counterexample and the binder
audit into `test/`.
| `CertProtocolProbe.lean` (2026-09-21) | layer 0 with a ghost certificate per node (`Protocol.Cert`, `Typed.vis cert …`): `mono`, `bind`, `widen`, `inl`, `inr_inv` all check with no axioms; `Protocol.plain` recovers the landed protocol. Backs decision D12 of the slices 3–6 brief |
