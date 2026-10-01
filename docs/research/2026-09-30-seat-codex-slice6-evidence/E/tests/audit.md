The ValueMembership candidate retains the old predicates without weakening the load refutation. It also carries the connector from production `Live` to the local `Reviewed.HandlesLive` under `WorldValid`.

These checks compare saved text and theorem statements. Lean compilation and axiom output remain pending; no compiler or git command ran during this audit.

The `Reviewed` block is the concatenation of the following pre-E source spans, byte for byte, between the local namespace delimiters. The shared `ProgramSource` record remains the production record; the copied point, body, protocol and state judgments resolve their retired predicates inside `Reviewed`.

| Source span (inclusive lines) | SHA-256 of extracted span |
| --- | --- |
| `src/Effect4/Laws/Program/Typed/Admission.lean:20–81` | `a4873841d0e521de7033be607415e3114093f69fb5daa7f5ebafc348331bf634` |
| `src/Effect4/Laws/Program/Typed/Admission.lean:90–112` | `181633f1b7b4d1011c96f96eb3460662093ca3f46066595bbefde4b2941981f0` |
| `src/Effect4/Laws/Program/Typed/Residual.lean:27–309` | `a402073cd138e7250b97355f91af8846b1400a9aed3ef65a9ae18f5e9c708cf9` |
| `src/Effect4/Laws/Program/Typed/Assembly.lean:27–73` | `b52168302a1b085f9e0a2d4d3c34420632b33e7f29fb60f07822a0da516d6e9c` |

The concatenated block has SHA-256 `b8616b11d97f07961320e71da9bee3073a912e91116b996407a05f43963f37fe`. Equality was checked with a Python string comparison and an assertion of this digest. Each span includes its trailing blank lines and excludes the next declaration's leading comment.

The source-file digests at this audit were:

- `src/Effect4/Laws/Program/Typed/Admission.lean`: `b6775a9395345000870973e0b19690b9faf99599f939e9e30dd372f50f72bf29`.
- `src/Effect4/Laws/Program/Typed/Residual.lean`: `016a157c0f9995223c3be38f33ed9c2c55c6e940d0e3f99696f87e519fec4673`.
- `src/Effect4/Laws/Program/Typed/Assembly.lean`: `11a0b09ca39df7d686ff74596cf7e99fbecf1407f5fc47597c1d95c88c035290`.

The `ExactSpelling` block matches `docs/research/2026-09-30-pass/membership/Gaps.lean:29–164` byte for byte, with span SHA-256 `05a27735242719193ceea72a4b5a03f88e0c814f20ea0da7eaff83d06dce1cae`. Its equality-based invariance remains confined to the test. Production `RefDeclared` and `PromiseDeclared` use `Equiv`, defined as subtyping in both directions.

The old load-refutation block comes from `docs/research/2026-09-30-pass/membership/Gaps.lean:501–574`. Only `TypedProg`, `TypedState` and `Ψ_S` are qualified with `Reviewed`; one `simpa` is replaced by an explicit conversion from the lookup's Boolean equality. The resulting block matches the candidate exactly, with SHA-256 `877871a5626b9be3e1f293b79586d90eb308f579d1d51a9bbc6115b8a80db2b5`. Its statement adds no hypothesis: it still refutes the old initialization claim for `Ref.make(5)` from the program's checked type and closed columns. Heap emptiness and cell absence are derived from `WorldValid`, not assumed by that claim.

G1–G6 each retain the old acceptance, the new rejection and an honest-value acceptance. G7 retains the full equality-based model and `fitsEq_not_closed_under_sub`; `natCell_equiv_spelling` supplies the corresponding production acceptance. The allocation controls `typedStateF_load_ref` and `typedStateF_load_get` use production `TypedProg` and `TypedState`.

The connector `live_iff_handlesLive` is ported from `docs/research/2026-09-30-pass/membership/Fits.lean:629–660`. Its statement names production `Effect4.Program.Typed.Live` and local `Reviewed.HandlesLive`; the proof uses the same heap, promise and state fields of `WorldValid`. The candidate includes its axiom print. The connector is later than Admission and retains no old production API.

Membership's twelve named item-E laws and `fold_of Effect4.Program.Typed.Fits` are present. D1 uses `Equiv`; D2 requires native cell/deferred declarations at `nat`/`(nat, nat)`; D3 reads declaration tables; D4 reads `Live` for `unknown`. The runtime `fitsAt` remains absent. The cutover candidate includes the two monotonicity adapters, their obligation associations, and ceiling 1. These are source checks, not accepted proof results.

The heap-extension bank test retains the research's `aesop (rule_sets := [Effect4.TypedState])` positive and `fail_if_success aesop` negative before an explicit proof. It adds no bank registration.

The first integration build exposed an ambiguous `World` name in the relocated historical block. The test now declares `abbrev World := Effect4.Program.Typed.World` immediately before `Reviewed`, and `W` aliases that local name. This restores the original namespace resolution without changing any copied declaration or the concatenated block digest above. Tactic references to production `Fits` are fully qualified to distinguish the separate program-environment predicate. The two other test fixes remove obsolete explicit arguments from `List.mem_cons_self` and qualify that same `Fits` tactic reference. All three saved candidates match their active test files. Recompilation remains pending.
