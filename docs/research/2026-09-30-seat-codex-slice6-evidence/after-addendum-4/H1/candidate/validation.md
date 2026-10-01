# H1 narrow validation plan (not run by this seat)

Read at worktree HEAD `e5cc184ba820ab4ea79b38fd32820421514812b9`, 2026-10-01. Root is running C. These are commands for the later H1 phase, after C/F/G and after applying the final reviewed candidate. Run one command at a time in `/Users/pooks/Dev/lean4-effect4-slice6`, recording each exact invocation, output and exit status in H1's receipt. This seat ran no Lean/lake/build/make command.

## Direct dependency inventory

The live tree has exactly thirteen files directly importing Guard.Core:

1. Effect4.Laws.Api.TraceOrigin
2. Effect4.Laws.Program.Guard.ControlRemainder
3. Effect4.Laws.Program.Guard.Finish
4. Effect4.Laws.Program.Guard.Handshake
5. Effect4.Laws.Program.Guard.MemoIds
6. Effect4.Laws.Program.Guard.NativeState
7. Effect4.Laws.Program.Guard.Observer
8. Effect4.Laws.Program.Guard.RegistrationQueue
9. Effect4.Laws.Program.Guard.ReturnCommands
10. Effect4.Laws.Program.Guard.ReturnFields
11. Effect4.Laws.Program.Guard.ReturnTasks
12. Effect4.Laws.Program.Guard.Settle
13. Effect4.Laws.Program.Guard.Single

New Scheduler is the fourteenth direct importer of Guard.Core in the candidate. The registration-tail amendment also changes Guard.RegistrationQueue. Its six existing direct importers are FinishQueue, Observer, RegistrationNested, Contract, SettleQueue and ControlRemainder; Observer/ControlRemainder are already above, leaving four additional direct consumers. Scheduler is its seventh importer in the candidate. Assembly directly imports Scheduler. Existing Assembly direct consumers are Test.Program.TypedStack, the two changed batteries, and the Laws umbrella. The umbrella is an import root rather than a narrow behavioral consumer; building the entire Laws/Test roots is not included in this bounded validation plan.

Exact inventory command:

```sh
rg -n '^import Effect4\.Laws\.Program\.Guard\.Core([[:space:]]|$)' src Test tools --glob '*.lean'
rg -n '^import Effect4\.Laws\.Program\.Typed\.Assembly([[:space:]]|$)' src Test tools --glob '*.lean'
rg -n '^import Effect4\.Laws\.Program\.Guard\.RegistrationQueue([[:space:]]|$)' src Test tools --glob '*.lean'
```

## Sequential commands

First establish the generalized native helpers, then the new declarations. These Lake targets inherit the repository's `-DwarningAsError=true` and 6 GB limit from lakefile.toml.

```sh
lake build Effect4.Laws.Program.Guard.Core Effect4.Laws.Program.Guard.RegistrationQueue
```

```sh
lake build Effect4.Laws.Program.Typed.Scheduler Effect4.Laws.Program.Typed.Assembly
```

Then compile the direct native consumers. Repeating Core/Scheduler/Assembly is unnecessary unless a fix changes one of them after its successful build.

```sh
lake build Effect4.Laws.Api.TraceOrigin Effect4.Laws.Program.Guard.ControlRemainder Effect4.Laws.Program.Guard.Finish Effect4.Laws.Program.Guard.Handshake Effect4.Laws.Program.Guard.MemoIds Effect4.Laws.Program.Guard.NativeState Effect4.Laws.Program.Guard.Observer Effect4.Laws.Program.Guard.RegistrationQueue Effect4.Laws.Program.Guard.ReturnCommands Effect4.Laws.Program.Guard.ReturnFields Effect4.Laws.Program.Guard.ReturnTasks Effect4.Laws.Program.Guard.Settle Effect4.Laws.Program.Guard.Single Effect4.Laws.Program.Guard.FinishQueue Effect4.Laws.Program.Guard.RegistrationNested Effect4.Laws.Program.Guard.Contract Effect4.Laws.Program.Guard.SettleQueue
```

Run the changed batteries and the direct Assembly test consumer:

```sh
lake env lean -DwarningAsError=true -M6144 Test/Counterexamples/Machine/Semantics/M6Capstone.lean
```

```sh
lake env lean -DwarningAsError=true -M6144 Test/Counterexamples/Machine/Semantics/ValueMembership.lean
```

```sh
lake env lean -DwarningAsError=true -M6144 Test/Program/TypedStack.lean
```

The candidate's `/private/tmp/h1-candidate/Axioms.lean` should be copied by root to the authorized retained H1 evidence directory before the next command. The exact proposed destination is below. Its output is separate from the battery outputs so production local laws are easy to audit.

```sh
lake env lean -DwarningAsError=true -M6144 docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/H1/Axioms.lean
```

Keep the previously planned case gate as a separately limited check:

```sh
make check-cases
```

**Coverage correction:** the current cases policy lists only Ty, Eff, NativeOp, RowKind, RowShape, Registration, Lit, Term and CauseTerm. Observer, Cmd, Supervision.ObserverMode, Resume, and Effects.Program are not policy families. Its config imports only Effect4, not the Laws graph. Therefore `make check-cases` does not check the new Scheduler matches, and a pass must not be reported as such. The exact standing rule asks for this gate after a new match on a policy family; the H1 matches alone do not trigger that wording. Root explicitly requested it in this validation plan, so it is retained here without changing the policy. `scripts/check-conform.py cases` internally runs `lake build Conform Effect4.Laws.Program.Typing.Check` and then the configured audit, serially; do not run another lake beside it.

The Make check is stamped at `.lake/check/cases`. If `make check-cases` reports up-to-date rather than running the profile, record that fact. If a fresh profile is wanted, run `python3 scripts/check-conform.py cases` once rather than claiming a new check occurred. Neither is a whole Test or trust-gate sweep.

No generator input changes in the initial H1 candidate; no generator run is proposed merely for the new Laws module. No make check/check-full, lake build Test, root-closure sweep, host runtime lane or push is included.

## Concrete elaboration issues and limited checks

- **Fixed before compilation:** pinned Lean v4.33.1 has no `List.nodup_singleton`; Scheduler now uses the exact native guard proof `List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩`.
- **Fixed defensively:** observer_exitValue_typed now cases on mode, rather than asking unification to move a variable-mode match through `.pure`.
- **Checked from pinned library:** Option membership exists (`Init/Data/Option/Instances.lean:26`) and is equality to `some`; the finite winner/accepted/cleanup predicates need no custom instance. `List.mem_of_find?_eq_some` exists (`Init/Data/List/Find.lean:304`).
- **Inference-sensitive, not a known error:** in requestOfR_load_none, if the inferred list of `List.mem_of_find?_eq_some hf` remains stuck behind fiber?, add the explicit type `found ∈ (loadR program fuel compileFuel).fibers`. This is the exact actual-lookup membership fact, not a semantic amendment.
- **Inference-sensitive:** Guard.Core generalized Code/Saved/Event inputs must still resolve all native `flatMap taskKeys` and `filterMap commandOwner` uses. The seventeen existing direct-consumer builds detect signature inference fallout across Core and RegistrationQueue. Do not weaken meanings or add ambient Classical instances to repair these.
- **Generated-predicate projections:** the new `forget_new_state` fixture depends on c0/c1/c2's current generated meaning. c1 is the race list slot. Its proof must transport the stronger race payload to the historical isSome clause while keeping c0/c2 unchanged. A failed projection is a proof adaptation, not grounds to redefine the historic statement.
- **Finite replay budget:** retained early queue/dispatcher controls still use the original budget 80 and exact original commands. Their `decide` reductions run under the test's explicit limits. A heartbeat/recursion limit failure is inconclusive, not a passing counterexample.
- **Trust:** new public local lemmas and the negative/positive fixture roots print axioms. Expect at most `[propext, Quot.sound]`; `Classical.choice` is not acceptable here. The production command obligations remain `ProofGraph.Obligation` wrappers, not proofs.

## Register before and after

At the inspected current tree:

- CE016 exists at REGISTER.md:202 and is **SEEDED 2026-09-30**.
- CE017 is **absent**, despite being named as an authorized addition in addendum 3.
- CE018 is **absent**, despite being named as an authorized addition in addendum 4.
- CE015 remains **REPAIRED 2026-09-30 for host answers only** at line196 and is not changed by H1.

`register.deferred.patch` updates only CE016 and inserts CE017/018. Its REPAIRED statuses are conditional on the named H1 controls passing after the final semantic review. `prepare-register.py` rereads the current tree, asserts exactly one still-SEEDED CE016 and absent CE017/018, and emits the candidate/diff only under /tmp. Rerun it after C/F/G to preserve any register edits they make. It intentionally stops if these row assumptions changed. Update the repair date if H1 lands after 2026-10-01.

Do not apply register.deferred.patch while the new registration/queue candidate amendments are still being prepared and tested.

## Registration amendment now in the /tmp candidate

RegistrationState adds a finite direct-marker correlation to TypedState: the actual current raceRegister id must resolve to a race on the same fiber, and its token's result must meet that fiber's saved StackAccepts continuation. Loaded-state helper proofs now take a finite no-direct-marker premise; the existing pure/sleep/ref/get controls discharge it by reduction. This avoids assuming a recursive code-site scanner or typing an entire transition result. The new registrationState_load axiom print is in Axioms.lean. RegistrationQueue's generic helper amendment adds a queue tail obligation; two dangling launch/enroll refusals and a matching registration-tail green are in the test fragment.

## Further finite delivery controls and pending stop audit

CommandDeliveryOk now checks the administrative continuation boundaries for afterInterrupt, raceCancel and closeParAwait. These add no import targets. The matching/mismatched direct registration fixtures and administrative unit-versus-nat stack controls are inside M6Capstone, so its exact command above covers them. IteratorProtocol for closeParAwait has the same aggregate error on input and output.

Before applying any H1 source or register status, root will run h2_review's exact final-predicate probe for the suspected SavedOk terminal-frame mismatch. This seat does not repair that pre-existing contract. A checked refutation triggers the brief's stop rule even if its cause predates H1.
