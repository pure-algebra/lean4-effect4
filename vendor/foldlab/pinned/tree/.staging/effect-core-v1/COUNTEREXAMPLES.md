# Effect Core v1 — counterexample register

Status: **PRE-GRADE / AUTHORED REGISTER**, 2026-08-31

Claim gate: none. A row records evidence against a statement; it does not by
itself establish the replacement design.

This is the central index for every counterexample that can change an Effect
Core v1 declaration, theorem, classifier transfer, source-admission rule, or
cutover decision. Proofs and executable witnesses remain beside the code they
exercise; this file gives them one stable identity and one place from which a
fresh session can find their exact force.

The existing estate's counterexamples are not copied here. They remain in
`library/cas/contracts/attacks/`, the `Cas.Lang.Falsifier` namespace, and the
modules that own the law they protect. This register links those owners and
records how Effect Core v1 uses them.

## 1. Vocabulary

These words are not interchangeable:

- A **counterexample** is concrete data plus a derivation showing that a
  quantified statement is false. It names the exact quantifier or missing
  premise it defeats.
- A **falsifier** is an executable challenge attached to a proposed law. It may
  be a counterexample to a weakened law, or a mutation designed to turn a gate
  red. A falsifier that currently passes does not establish completeness.
- A **negative fixture** is an input the checker is required to reject. It is
  not a counterexample unless some claim says the input must be accepted or
  classified differently.
- A **mutant** is a deliberately damaged implementation used to show that a
  gate can fail. It attacks the gate, not normally the semantic statement.
- A **boundary witness** separates two concepts without necessarily refuting a
  claim, for example `await` versus `join` or operation count versus world
  change.

Every registered counterexample has one `EC1-CE###` ID. IDs are never reused.
If a law is repaired by adding a premise, the row remains and records the
premise it forced.

## 2. Evidence states

| State | Meaning |
| --- | --- |
| `VERIFIED-KERNEL` | The witness source is in this tree, its exact Lean command was rerun, and its axiom output is recorded. |
| `VERIFIED-TOOL` | A deterministic local command reproduced the witness; its conclusion is limited to the tool/evidence plane. |
| `REPORTED` | A detailed report records a witness, but the witness source is not yet in the packet or has not been independently rerun here. |
| `RED` | A source file claims to be evidence but its required check currently fails. It supplies no admissible conclusion. |
| `OWED` | The attacked statement is identified, but no accepted concrete witness exists yet. |
| `SUPERSEDED` | A stronger row replaced the attacked statement; the historical witness remains discoverable. |

No prose review upgrades `REPORTED`, `RED`, or `OWED` to a verified state.

## 3. Verified semantic counterexamples

| ID | Exact statement defeated | Minimal witness | Evidence owner and command | State / consequence |
| --- | --- | --- | --- | --- |
| `EC1-CE001` | EffHOL's `⟨x ← p⟩ φ` can be identified with total-correctness `wp`. | A refusing CAS program satisfies `wlp ⊥`, while `wp ⊥` is impossible for every program. | `workshop/exhibits.lean`: `wlp_bot_derivable`, `wp_bot_never`; run `cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/exhibits.lean`. | `VERIFIED-KERNEL`; the modality is existing `wlp`, with totality added separately by existing `wp_iff_wlp_and_total`. |
| `EC1-CE002` | A fixed-fuel result algebra can satisfy a general bind/composition law for `run`. | The existing universal witness where a composite run finishes although the two fixed-fuel component results do not determine it. | Canonical owner `Cas/Backend/Universal.lean`: `run_has_no_composition_law`, `run_composite_outruns_its_parts`; exact receipt in `workshop/counterexamples/FixedFuel.lean`, run from `library/cas`. | `VERIFIED-KERNEL`; the boundary theorem reports `[propext, Quot.sound]` and its witness `[propext]`. Compositional coherence is stated at `interpretRef`/the big-step face, never at fixed fuel. |
| `EC1-CE003` | Fuel exhaustion may be encoded as `Refusal.failed` without changing coherent meaning. | The smallest completing graph: fuel zero yields the invented failure, while one unfolding performs a put that can never refuse with `.failed`, for every address function. | `workshop/exhibits.lean`: `exhausted_is_not_a_refusal`; same command as `EC1-CE001`. | `VERIFIED-KERNEL`; fuel, pending external answers, and scheduler decisions remain live frontiers outside refusal and cause. |
| `EC1-CE004` | Sequential dataflow composition is union or plain append. | A one-line prefix followed by a suffix reading answer `0`: the suffix edge moves from `(0,0)` to `(1,0)`. | `.staging/agent-reports/2026-08-31-effect-core-classification-anchors.lean`: `div1_dataflow_seq_is_not_union`; run `cd library/cas && lake env lean ../../.staging/agent-reports/2026-08-31-effect-core-classification-anchors.lean`. | `VERIFIED-KERNEL`; the right dataflow graph must be reindexed through `dataflowFrom`. |
| `EC1-CE005` | Dataflow closure is homomorphic under a componentwise sequential join. | A suffix open in isolation becomes closed when its answer reference is supplied by the prefix. | Same Lean file: `div1_closure_not_seq_homomorphic`. | `VERIFIED-KERNEL`; closure is recomputed after composition, not joined from two booleans. |
| `EC1-CE006` | The ordered world effect of sequence can be modeled by a commutative frame union. | Two puts in opposite orders leave different words. | Same Lean file: `div2_world_seq_is_not_commutative`. | `VERIFIED-KERNEL`; a set-valued frame may be a conservative upper bound, but it is not the sequential denotation. |
| `EC1-CE007` | Operation footprint and realized world delta are one classification dimension. | Two put operations execute, while duplicate insertion yields only one new binding. | Same Lean file: `div3_op_footprint_ne_world_footprint`. | `VERIFIED-KERNEL`; D1 operation events and D2 world change remain separate. |
| `EC1-CE008` | Empty reads plus closed dataflow bounds the possible CAS error row. | One operand-free put at a colliding address refuses with `.collision`. | Same Lean file: `div4_envelope_does_not_bound_the_error_row`. | `VERIFIED-KERNEL`; exact `E` is synthesized from admitted operations and handlers, never inferred from `PProg.envelope`. |
| `EC1-CE009` | The current envelope contains exact write addresses. | `PutShape` contains no address and the address is handler-dependent through `H`. | Same Lean file: `div5_write_addresses_not_in_envelope`. | `VERIFIED-KERNEL`; the envelope owns write shapes only; address facts require the handler/world relation. |
| `EC1-CE010` | The CAS observation mask includes the partial word on refusal. | Two programs produce the same refusal and different partial words. | Same Lean file: `div6_refusal_word_outside_the_mask`. | `VERIFIED-KERNEL`; `ObsEq` deliberately forgets the refusal-side word, and any finer mask is a new observation. |
| `EC1-CE042` | Full Effect Core has a globally unique denotation without fixing choices. | One admitted program asks for one Boolean answer and then loads the selected address. At the same initial word, tapes `[true]` and `[false]` permit distinct observations: one succeeds and one refuses, for every address function. | `workshop/counterexamples/Nondeterminism.lean`: `denotes_is_not_unique`, `no_choice_free_denotation`, and `EC1_CE042`, with positive boundaries `denotes_unique_given` and `denotes_unique_on_the_askFree_fragment`; run `cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/counterexamples/Nondeterminism.lean`. | `VERIFIED-KERNEL`; 29 receipts, ceiling `[propext]`, 12 axiom-free, no `Quot.sound`, `Classical.choice`, or `sorryAx`. Public meaning is relational: `Runs p initial decisions observation : Prop`. Uniqueness is available only for one fixed complete tape or the ask-free deterministic fragment. The witness models direct-handler answers only; it proves nothing about scheduler fairness, race ties, clocks, interruption, external-request frontiers, or replay selection. |

Reproduced axiom ceiling for the classification file: the first two rows are
axiom-free; the remaining counterexamples use `propext`; no `sorryAx` or
`Classical.choice` was reported.

The nondeterminism witness (`EC1-CE042`) prints 29 receipts at a `[propext]`
ceiling; 12 of those theorems are axiom-free.

## 4. Verified source/tooling counterexamples

| ID | Tooling claim defeated | Witness | Evidence | State / boundary |
| --- | --- | --- | --- | --- |
| `EC1-CE020` | The old 359-module runtime bank is an exhaustive public Effect package census. | `effect/unstable/http/MultipartParser/HeadersParser` and `/Search` resolve publicly with source and declarations but are absent from the old bank. | `workshop/effect-surface-probe.ts`; run `bun .staging/effect-core-v1/workshop/effect-surface-probe.ts --summary`. | `VERIFIED-TOOL`; it proves the old walk incomplete at `effect@4.0.0-rc.112`, not semantic classification completeness. |
| `EC1-CE021` | An empty Effect diagnostic set alone proves a generated project was actually analyzed as Effect v4. | A plain path alias was reported to typecheck while Effect was unknown and Effect diagnostics disappeared. | The repaired harness in `workshop/tsgo/run-probes.ts` checks exact file-set equality, package-version equality, and detected/supported `v4`; the original false-green fixture was not retained. | `REPORTED`; the repaired positive/mutant harness is verified separately as `EC1-M001`–`M004`, but it does not retroactively verify this historical witness. |

## 5. Verified packet-local anchor counterexamples

The four local-anchor contradictions are consolidated in
`workshop/counterexamples/LocalAnchors.lean`. The packet keeps the report as the
explanation and the Lean file as the executable evidence; it does not duplicate
the estate witnesses that inspired them.

| ID | Statement defeated | Witness | Owner | State / forced repair |
| --- | --- | --- | --- | --- |
| `EC1-CE030` | `rowEq r s -> norm r = norm s` for arbitrary keyed rows. | A permutation with duplicate keys selects different last values. | `workshop/counterexamples/LocalAnchors.lean`: `normalizeRow_forward_is_false`, with repaired `normalizeRow_with_nodup`; run its packet command. | `VERIFIED-KERNEL`; add a duplicate-free premise or make row validity supply it. The proof uses `propext`, `Classical.choice`, and `Quot.sound`. |
| `EC1-CE031` | A fail-fast checker returns a diagnostic for every condemning clause. | One reference list violates dangling and wrong-kind clauses; the checker returns only the first. | Same file: `diagnostic_local_is_false`, `checker_reports_only_the_first`. | `VERIFIED-KERNEL`; specify a separate accumulating census or use first-error soundness plus existential rejection completeness. |
| `EC1-CE032` | Full observational equality determines every field of the syntactic classification product. | Two `ObsEq` tables have different answer-dependence graphs. | Same file: `classifier_semEq_is_false`, `runs_agree`; independently strengthened by `breaker-exhibits.lean`: `load12_ObsEq`, `load12_dataflow_differs`. | `VERIFIED-KERNEL`; replace equality with concretization soundness/overlap or enumerate genuinely semantic-invariant fields. |
| `EC1-CE033` | Every raw `PProg` meaningfully injects into a well-formed `CheckedProgram`. | Empty and dangling-answer tables are representable but fail the proposed admission conditions. | Same file: `injectCas_cannot_be_total`; exact raw witnesses are checked. | `VERIFIED-KERNEL`, with a scope caveat: an arbitrary input-ignoring function is not refuted. The theorem must require meaning preservation and restrict its domain to admitted `PProg`, or the checker returns `Option`/`Except`. |

## 6. Verified breaker counterexamples

All rows in this section were rerun together with:

```text
cd library/cas
lake env lean ../../.staging/effect-core-v1/breaker-exhibits.lean
```

The command exits zero and prints 40 receipts. Their ceiling is `propext` and
`Quot.sound`; no `sorryAx`, `Classical.choice`, or `native_decide` occurs.

| ID | Exact statement defeated | Witness | State / consequence |
| --- | --- | --- | --- |
| `EC1-CE040` | `toPProg` is a semantic projection of every CAS-only graph. | `unreachableTail` and `entryNotZero` are denotationally equal to the injected table but `toPProg` returns `none`; `toPProg_is_not_semantic`, `toPProg_is_not_entry_stable`. | `VERIFIED-KERNEL`; `toPProg` is only a sound recognizer for one literal normal form. Projection requires an admitted canonical graph domain or a distinct semantic quotient theorem. |
| `EC1-CE041` | A `Handler ScopeSig (ReaderT Env (Prog CasSig))` can implement recovery merely because such a handler value typechecks. | `no_scoped_catch_clause` and `no_handler_into_ScopeM_catches` prove no clause in that target satisfies the catch law; `scopeHandler_does_not_catch` exposes the scratch clause. | `VERIFIED-KERNEL`; retain existing `Handler` and first-order `BlockId` children, but interpret them into an adequate target with observable state/error/machine structure. `scopeHandlerR_catches` and `scopeHandlerR_recovers` exhibit that repair without introducing `HHandler`. |
| `EC1-CE045` | Sequencing a finalizer with ordinary `Prog.bind` runs it when the body refuses; and the catch-adequate target `ReaderT EnvR (StateT Word (Except Refusal))` repairs finalization. | `ensuring_never_finalises_a_refusal` and `ensuring_witness` defeat the first clause. `workshop/counterexamples/EnsuringRepair.lean` defeats the second with `scopeHandlerR_ensuring_still_skips_the_finalizer`, `reraise_is_finalizer_blind`, and `reraise_blindness_is_not_vacuous`: an `Except.error` has no word slot, so every clause that preserves the refusal is blind to finalizer state on that path, even for two finalizers with observably different words. Run `cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/counterexamples/EnsuringRepair.lean`. | `VERIFIED-KERNEL`; 44 receipts, ceiling `propext`/`Quot.sound`. `Prog.bind` remains refusal-strict, and the catch target remains sufficient for catch only. The forced information contract is state outside error: `ExceptT Refusal (StateT Word Id)` retains the partial word on failure. `interpretRef_forget` and `run_interpretRefW` connect that target to existing semantics; the repair proves finalization on success and refusal, preservation of the original refusal, LIFO order, and exactly-once dependence. `scopeHandlerW_catch_agrees` is conservative for catch. No `HHandler` is introduced. Scope remains the exhibited one-level, `.ret`-block carrier; nested and multi-block scoped control are not established here. |
| `EC1-CE046` | EffHOL's (Mod-E) transfers unconditionally to `PProg` with `++` and existing `wlp`. | The empty prefix satisfies every `wlp` postcondition by refusal while its appended suffix need not; `wlp_falsifier_empty_prefix`, `modE_unsound_at_the_empty_prefix`. | `VERIFIED-KERNEL`; the new `EC1-T130` theorem must retain a nonempty-prefix premise and derive from shipped `wpAux_append`; the paper rule does not transfer verbatim. |
| `EC1-CE047` | A nonempty-prefix premise alone makes the table-only reading of (Mod-E) valid. | A suffix with answer references refuses when restarted alone but succeeds under the prefix history; `modE_unsound_at_a_restarted_history`. | `VERIFIED-KERNEL`; `EC1-T130` must index the suffix by the prefix-produced answer history. The scratch `wlp_append` proof exhibits the corrected statement but is not an inherited estate theorem. |
| `EC1-CE048` | Existence of a successful finite denotation fixes a stable refusal result at every other fuel. | `denotes_does_not_determine_the_refusal` exhibits two pre-completion fuels with different refusal texts while the later result is unique. | `VERIFIED-KERNEL`; uniqueness applies to stable non-exhausted outcomes, not to invented frontier labels. Frontier/exhaustion remains a separate sum arm. |

## 7. Owed attacks

| ID | Attack | Current evidence state | What blocks cutover |
| --- | --- | --- | --- |
| `EC1-CE043` | Stock rc.112 `Cause` preserves the project's ordered `then`/`both` topology. | Required witness: distinct ordered internal causes with the same projected reasons. `OWED`. | Generated stock Effect claims only the explicit lossy quotient; topology-preserving targets use project-owned code. |
| `EC1-CE044` | A finite scheduler probe establishes fairness or liveness. | Required pair: same safe program under a fair and an unfair schedule. `OWED`. | Safety theorems stay fairness-free; liveness quantifies over a declared fairness predicate. |

`EC1-CE042` is discharged in §3. It does not discharge either owed row above:
in particular, the direct-handler choice witness contains no scheduler or
fairness model.

## 8. Negative fixtures and mutants (separate register)

These are required controls, but they are not semantic counterexamples:

| Control ID | Kind | Expected result | Owner |
| --- | --- | --- | --- |
| `EC1-M001` | generated TS positive | exactly one file, Effect v4, zero diagnostics | `workshop/tsgo/positive/` |
| `EC1-M002` | floating-effect mutant | exactly `floatingEffect` and strict nonzero exit | `workshop/tsgo/floating-effect/` |
| `EC1-M003` | missing-error mutant | exactly `missingEffectError` and strict nonzero exit | `workshop/tsgo/missing-effect-error/` |
| `EC1-M004` | hidden-Promise mutant | exactly `lazyPromiseInEffectSync` and strict nonzero exit | `workshop/tsgo/lazy-promise-in-sync/` |

The future generated register joins every `EC1-F*` contract falsifier and every
type-closure edge to these IDs. It must not silently coerce an invalid-input
fixture into a refutation of the model.

## 8b. Provisional-ID reconciliation (breaker report -> register)

The breaker lane assigned working IDs before this register existed. The register
is the authority; those numbers are **provisional and superseded**. Recorded here
because §1 forbids reusing an ID, and `EC1-CE045`-`CE048` currently denote
different statements in `2026-08-31-effect-core-breaker.md` than they do here.

| Breaker report (provisional) | Canonical row | Statement |
| --- | --- | --- |
| `EC1-CE045` | **`EC1-CE040`** | `projectCas` is a projection out of the CAS-only fragment |
| `EC1-CE046` | **`EC1-CE041`** | scoped operations need no new handler target |
| `EC1-CE047` | **`EC1-CE045`** | the exhibited `ensuring` clause finalizes |
| `EC1-CE048` | **`EC1-CE046`** | EffHOL's (Mod-E) is unconditionally satisfied by `wlp` |
| `EC1-CE051` | folded into **`EC1-CE003`** | `exhausted_is_not_a_refusal`'s second conjunct holds generally; witnesses `loop_exhausts_at_0_1_2`, `loop_run_exhausts` remain in `breaker-exhibits.lean` and narrow `CE003` rather than opening a row |
| `EC1-CE052` | folded into **`EC1-CE032`** | `SemEq` under the CAS mask read at a fuel the mask has not fixed; witness `load12_differ_at_fixed_fuel` |

No provisional number is reissued to a new statement. Any document citing a
left-column ID is citing the breaker report's internal numbering and must be read
through this table.

## 9. Existing estate witnesses reused by the packet

The following owners remain canonical and should be linked, not copied:

- `Cas/Lang/Wp.lean`, namespace `Falsifier`: partial versus total correctness,
  nonempty-family, threaded-history, nonempty-prefix, and tight-fuel witnesses;
- `Cas/Backend/Universal.lean`: freeness/initiality boundary, pin vacuity,
  handler-law adversaries, and the fixed-fuel no-composition theorem;
- `Cas/Backend/SumAlgebra.lean`: swapped, dropped, doubled, and bad-oracle
  signature/handler adversaries;
- `Cas/Backend/Canon.lean`: duplicate-key permutation and door witnesses;
- `Cas/Lang/Defun.lean`: envelope GAP 1/GAP 2, address-separation necessity,
  and foreign-oracle dependence;
- `library/cas/contracts/attacks/<packet>/`: independent attack sources and
  verdict records for promoted CAS contracts.

An Effect Core theorem row that specializes one of these witnesses records the
existing theorem name and its changed premises. It does not mint a second
counterexample with a new name merely to make the packet look self-contained.

## 10. Mechanical completeness contract

The future `COUNTEREXAMPLES.json` is generated from this register's accepted
schema, `CONTRACT-PACKET.md`, `PROOF-DAG.md`, and the per-type closure rows. Its
gate computes at least:

```text
unregisteredContradictionClaims
orphanCounterexamples
duplicateCounterexampleIds
missingAttackedQuantifier
missingConcreteWitness
missingEvidenceCommand
verifiedRowsWhoseCommandFails
falsifierRowsWithoutCounterexampleOrOwedAttack
proofEdgesIgnoringActiveCounterexamples
resolvedRowsWhoseForcedPremiseWasDropped
mutantsNeverObservedRed
```

All sets must be empty for a slice to close. An `OWED` row is an explicit open
edge and blocks only the slice whose claim needs it. A `RED` row cannot be cited
as evidence anywhere.

Counterexamples participate in per-type closure as follows:

1. each type edge lists every counterexample that attacks it;
2. the amended statement names the premise, restriction, quotient, or carrier
   split forced by the witness;
3. the witness is rerun against the frozen declaration snapshot;
4. a stronger statement reopens the row even if the old witness no longer
   applies; and
5. full cutover is refused while any required row ignores an active verified
   or reported contradiction.

This register is authored during the current pre-grade packet. The JSON/Lean
projection and its zero-counter gate are proposed work; they do not exist yet.
