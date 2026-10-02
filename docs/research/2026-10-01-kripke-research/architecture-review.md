# World-indexed architecture: bounded source review

**Recommendation:** a focused investigation is warranted. World extension is an implemented proof discipline with concrete reuse and counterexample-driven repairs. Investigate which facts transport and which transitions establish new validity; avoid treating the whole machine invariant as a modal proposition or introducing a second world framework.

Snapshot: HEAD `26c7be34e6fea61fe2d13c4fa80d9bcd80d414d5`; observed `2026-10-02T03:21:48.242116+00:00`. Read-only review, no compiler or fresh axiom audit. Paths below are relative to `/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4`; `Typed/` abbreviates `src/Effect4/Laws/Program/Typed/`. Hashes bind the inspected working bytes, including comments, rather than asserting every file equals HEAD. Findings concern source definitions and registered proof claims.

## Implemented dependency map

| Owner | Definition and consumed proof boundary |
| --- | --- |
| Machine handle world | `src/Effect4/Laws/Machine/Handles.lean:868–870,909–911`: ids plus stores; extension preserves old ids and satisfies `Stores.le`. Typed.World extends this parent, not a competing representation. |
| Typed world | `Typed/World.lean:52–66,123–142`: Γ fibers, Π deferreds, Ρ references, Θ resume tokens, fixed service types. `TableExtends` preserves existing declarations, permits new declarations. `CellCompatible` additionally carries coarse stored-cell preservation implications. |
| Validity and host extension | `Typed/Validity.lean:19–39,124–126`: `WorldValid` supplies exact support, machine/store equality, freshness bounds, closed declarations and coarse cell typing. `leHost` adds preservation of each external spelling at its index. Actual `hostOrder` uses `leHost`; World's `protocol_order` (`World.lean:447–448`) supplies the weaker order. |
| Strong membership | `Typed/Membership.lean:50–69,778–788,885–888`: `Fits` reads declarations, external spelling, scope presence and service types. `fits_map` exposes these smaller premises; `fits_mono` packages them through `leHost`. It uses neither Θ nor `CellCompatible`. No arrow clause or step index is claimed (`docs/core/system-map.md:275`). |
| Residual program typing | `Typed/Residual.lean:266–307,731–756`: operations demand present-world preconditions and continuations typed at every admitted future world/answer. `typedProg_mono` transports leaves/preconditions/guard body and composes world extensions for continuations. Generic `Typed.mono` (`src/Effect4/Laws/Effects/Protocol.lean:68–76`) has the shared shape but is a different judgment. |
| Saved code and stacks | `Typed/Contracts.lean:43–92,112–144`: `FrameAccepts` quantifies over future worlds; `StackAccepts` composes through a shared intermediate type. `SavedOk` joins current code, stack and interrupt provenance. Stack transport needs only transitivity; saved-code transport additionally needs program transport. Conditional `ResumeOk` has no unrestricted weakening theorem. |
| Hook interpretation | `Typed/Stack.lean:30–46,293–315,472–481`: resumed iterator/loop produces **one** intermediate type with its protocol valid at every later world. `popR_typed` consumes the current-world instance and repushes the future-closed protocol. M4Stack and M5Hooks have source ledger ceilings zero. |
| Machine and route | `Typed/Assembly.lean:95–119,128–142,253–267`: generated `preds.SavedOk` owns a saved *position* (stack/provenance), while LiveCode/ReadCode own current code. J is MachineTyped; I adds queued code and QueueOk. `StepPreserves:444–448` produces a later world **and a new I**. `reachable_of_ledger:1250–1261` consumes load/decision preservation via hostOrder. `m7_of_capstone:1551–1576` transfers typed observation and stuck status through ReplayRel; modal transport is not rerun for M7. |

## Five material findings

1. **Separate persistence from state preservation.** `CellCompatible` is an explicit assumption: “`∀ key ty, HeapTypedAt w key ty → HeapTypedAt newer key ty`” (`World.lean:133–135`). Its mono theorem projects that assumption; it does not show arbitrary reference writes preserve typing. `WorldValid.cells` uses coarse `ValueOk`/`CompletionOk`, while machine heap/promise leaves use `Fits`/`CompletionStrong` (`World.lean:74–75,96–111`; `Assembly.lean:114–116`). Strong preservation and whole new-world validity remain transition work. Possible redundancy on valid destination worlds is a lemma candidate, not a reason to remove the condition on arbitrary worlds.

2. **New declarations can invalidate formerly vacuous conditional premises.** Exact support makes WorldValid/J/I unsuitable for unrestricted upward closure. `ResumeOk` explicitly warns about a newly declared token (`Contracts.lean:86–92`). `preds_savedOk_mono` requires old-position declaredness (`Assembly.lean:1213–1226`). Actual bookkeeping transport additionally assumes equal Γ and Θ (`Commands/Bookkeeping.lean:950–958,1126–1133`); `storesOk_world` has further unchanged-table premises. These are intentional boundaries, not missing generic monotonicity.

3. **The repairs demonstrate why quantifier placement matters.** Historical one-world frames accept a bad continuation before allocation, then reject it afterward; current frames reject it initially and have a positive loop control (`Test/Program/FramesNotKripke.lean:15–41,942–962`). A per-world intermediate hook type also fails: the fixed existential must precede the future-world universal (`:1115–1125,1153–1167`). Current HookLaws and stack proofs implement this repair. Preserve these controls; do not report the old failures as current.

4. **Modal closure does not deliver generic composition or complete M5–M7.** `TypedProg` has non-local control markers; generic `Typed.bind` cannot replace construct-specific compatibility. Current `seq_typed` covers exactly `(guardR .onSuccess a).bind (seqR k)`, future-typed value continuations and equal error columns (`Typed/Seq.lean:10–28,62–66`). Source ledgers still request the general M5 denotation/load/term results (`Assembly.lean:1838–1842`), M6's final command-module ceiling is nine (`Commands/Observe.lean:1353–1357`), and M7's ceiling is four (`Assembly.lean:1854–1859`). These are inspected declarations, not a newly executed ledger report. In particular `Live` accepts scope/memo keys unchecked at unknown (`Membership.lean:50–55`); the stronger exit-handle-validity target remains open (`Assembly.lean:1520–1527`).

5. **Status prose has drifted behind repairs.** Assembly still calls CE-018 open (`:1744–1747`), but the five scope-answer posts require `Fits … Ty.scope` (`Residual.lean:111,118,122,126,223`), and current positive controls include `forkAfterMake_typed`, `forkAfterMake_denotes`, `makeThenClose_typed` (`Test/Counterexamples/Machine/Semantics/ScopePresence.lean:328,360,399`). Decisions row156 records the landed repair, while ratification remains owed (`docs/core/decisions.md:249`). System-map's old M6 count20 (`:280`) also differs from the last command module's ceiling9. Update status links from the existing ledger/register; create no parallel status registry.

## Focused investigation and expected efficacy

Audit three representative transitions: declaration-preserving store restatement, fresh allocation, and token/resume delivery. For each, list separately old-fact transport, new declaration/cell typing, validity/freshness, and code/queue correlation. The existing proof already demonstrates reuse: `leHost_restate` establishes cell compatibility from unchanged refs/deferred cells (`Commands/Bookkeeping.lean:1511–1533`); drainDue transports produced completion code with `typedProg_mono` (`:1915–1941`). Keep `fits_map`, existing world orders and concrete command proofs as the seams.

Measure benefit only after a controlled proof experiment: reused assumptions/lemmas, remaining obligations, proof-search time under identical settings, and unchanged statements/trust outputs. This review establishes structural reuse and specific boundaries, not an empirical speedup. The most useful outcome is a small transport-premise map plus one completed transition; broad modal machinery would obscure the remaining state obligations.

## Snapshot hashes (SHA-256)

| Source | SHA-256 |
| --- | --- |
| `src/Effect4/Laws/Machine/Handles.lean` | `339872525682b32d607cc07f281aed559924dc9d182d6cc2f763b35156656ec1` |
| `src/Effect4/Laws/Effects/Protocol.lean` | `1cc3421f077e574aade645e382a70567e943f3f0d8be7f56e8600f9b785661e4` |
| `src/Effect4/Laws/Program/Typed/World.lean` | `32be5194574dcf8af29f51e2c6898548a079599f1404d7c49848e1cfdb637bd7` |
| `src/Effect4/Laws/Program/Typed/Validity.lean` | `9290cfedb230bf663718ef5addbf0fd6ca8da87d466646806dbf33c7dcb7c558` |
| `src/Effect4/Laws/Program/Typed/Membership.lean` | `09beeaef665e37201c7c2a22b195080962b41a88c0534d79796bf963917db8dd` |
| `src/Effect4/Laws/Program/Typed/Residual.lean` | `1fa50a31814a35d367fd2995a08d4c62db370114f3631b8f2825831032e05c12` |
| `src/Effect4/Laws/Program/Typed/Contracts.lean` | `5c9be58b61f1ecfa4be8c0732c637f3cf8ac0df0ab3aada1b33abf1fcf3a7f8f` |
| `src/Effect4/Laws/Program/Typed/Stack.lean` | `255c3a9099dd3e520d841a42dd4920e201eba8c257812440a2b54dd2d5cdb204` |
| `src/Effect4/Laws/Program/Typed/Assembly.lean` | `faef0661ca1133feea62eba944b75185fdd03851e6a7a50e530e598a8c3cfa10` |
| `src/Effect4/Laws/Program/Typed/Seq.lean` | `29ab3023f1e7407132805d2e1c51670aadcde2010b6d22b0ad7f7aa29e6af56d` |
| `src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean` | `bb660b01c204370af0076f3ac85066039f8e72e3627c2a920c262c2a55ff4e29` |
| `src/Effect4/Laws/Program/Typed/Commands/Observe.lean` | `4efdaaf5cea864839318f94f4568c7460920f6352e0dd4250d9f27403452bdd2` |
| `Test/Program/FramesNotKripke.lean` | `3e417ae423a221db965de102f7dfa799ea64da47147f69a9c092dd9bb6bb2950` |
| `Test/Counterexamples/Machine/Semantics/ScopePresence.lean` | `fd66360634d040bfea24c9d969f7c4585d32c15874dd59cb1e68f4f601e7a634` |
| `docs/core/system-map.md` | `d15e7f14f845d8cbc00f11cb45dbd7093fa1b08c155b12285a82df95d0242752` |
| `docs/core/decisions.md` | `3858ca648316a4fc397f722cce0ca17becff1a255ead2435755233535b9ded58` |
