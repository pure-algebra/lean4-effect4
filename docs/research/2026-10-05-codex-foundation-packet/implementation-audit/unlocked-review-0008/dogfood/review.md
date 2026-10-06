# DOGFOOD refresh at 6bfc1649

The routing scenario tests meaningful composition. Its retained report keeps two general behavior claims open.

Evidence status: source inspection, retained Lean outputs, and six finite Python metadata controls. No Lean or target command ran during this review.

The reviewed committed change is c27d5745..6bfc1649 in `/Users/pooks/Dev/lean4-effect4-lower`.
Active lowered artifacts remain unfinished. Their absence from acceptance is not a finding.

## Findings to carry forward

### The gate still accepts an unrelated top claim

Source: `Scenario.claim`, `Scenario.claims`, and `expandScenarioGate`, in `Test/Dogfood/Scenario.lean`.

The record says its top theorem assembles its clauses. The gate checks each declaration independently, without checking this dependency connection.

Replacing the workers top claim with `receipt_inert` still passes those predicates and all unchanged controls. The chosen top then has no cleanup-goal dependency.

The real `workers` theorem remains correctly reported as modulo cleanup. This finding concerns validation and reporting, not a false kernel theorem.

The workers record includes `replays` outside its top conjunction. Routing now includes `submit_success_prepared_fits` outside its top conjunction too.

Smallest correction: distinguish associated control laws from assembled clauses. Check the latter through existing proof dependencies, and add the unrelated-top refusal control.

Placement: decisions rows 203 and 254. Consumer: `#scenario_gate` and scenario reports. No new proof framework is needed.

### The module-prefix placement exception is now committed

Source: `expandScenarioGate`, in `Test/Dogfood/Scenario.lean`, committed at 6bfc1649.

Every theorem from an `Effect4.Laws` module passes placement without consulting the registry or measuring an inherited requirement connection.

`Effect4.Run.step_id` supplies a concrete untagged helper accepted by this rule. It has no own placement attribute or direct registry row.

It participates in `Run.journal_replays`; this review does not claim it lacks inherited placement. The prefix predicate does not verify that connection.

Smallest correction: reuse the registry or measured dependency relation for inherited placement. Keep a registered-law positive and an unplaced-law refusal fixture.

This finding strengthens the earlier in-progress warning: the bypass now belongs to the committed slice.

### The active empty-table flag overstates its observation

Sources: `Lowered.readsTable` and `Lowered.text`, in `Test/Dogfood/Scenario/Lowered.lean`; S4 in `ocaml/engine/test/scenarios/test_scenarios.ml`.

The flag compares finite machine views after replacing the row table with an empty table. It does not measure whether execution reads the table.

`Program.prepareExternalAnswer`, in `src/Effect4/Program/Compile.lean`, consults a nonempty table through `externalRow` and `externalValue` for successful replies.

A handle-free admitted answer may produce the same value after those reads. An empty-table fallback can therefore leave every observed view unchanged.

Smallest correction: name the flag `observedTableDifference`, or describe exactly that finite comparison. Use equal/different labels instead of unread/read.

Do not add a new gate merely because these worker and routing fixtures lack handles. The later handle scenario can supply its planned positive witness.

This is active-work guidance about evidence wording, not a finished acceptance defect or an incorrect current comparison.

## What the routing slice establishes

`tagIs_pair` states the exact Boolean result for a pair-shaped tagged value. Its retained axiom output is `[propext]`.

`infrastructure_escapes` remains a planned goal. It quantifies tags and messages on one authorized script, at default budgets.

`unauthorized_calls_nothing` remains a planned goal. It quantifies driver scripts, assuming no submitted configuration carries the request token.

Its observation records calls the host held. It does not independently record every unbound repository request the machine could expose.

That premise scans all submitted rows, including refused ones. Keep the exact premise visible; do not restate it as accepted configuration alone.

Direct answer controls cannot bypass the session: `HostSession.advance` refuses every `answerAsync` decision with `directAnswer`.

The top `routing` theorem combines the exact tag lemma with those two goals. Retained status is modulo both goals, with `[propext, sorryAx, Quot.sound]`.

The finite controls cover normal success, absent users, denied tokens, misnamed handlers, catch-all handlers, infrastructure failures, and exact error admission.

They also reject a wider successful record. The eager-lookup mutant demonstrates why authentication must precede repository access.

The predicate lemma alone does not prove full handler routing. The source explicitly preserves this limit.

## Retained verification and bounds

The retained slice-3 build completes 923 jobs. Its audit checks 678 modules and 83797 declarations.

The goal gate reports 17 planned goals and nine declarations resting on goals. No other declaration reaches `sorryAx`.

`FuzzR.lean` uses 14 moves, script depth five, one request token and a scratch copy of the program.

Its output counts 579194 scripts, 541984 satisfying its bounded hypothesis test, no violation, and 440 outside-premise scripts reaching the repository.

The hypothesis test searches configuration page sizes below 40. This is finite evidence; it is not the universally quantified planned theorem.

The retained escape probe checks 96 selected cases and two business-tag negatives. Both negatives differ from the escape conclusion as intended.

The review reruns six Python metadata controls. Workers and placed-theorem positives pass; unknown names and unplaced battery declarations fail.

The wrong top and the untagged law helper pass the committed gate mirror. These runs do not execute Lean or inspect its live environment.

`git diff --check c27d5745..6bfc1649` passes. Source and retained-output hashes accompany this note.

## Active lowered work

The new machine tape separates progressed controls and applied replies from binding, receipt and refusal rows. Frontier rows stop tape extraction.

The planned `tape_replays` theorem states machine equality under complete tape extraction, with the same table and budgets. It excludes session-ledger equality.

The engine fixture compares a machine projection. Session receipt, consumption and retirement remain Lean-only in this route.

Keep that split explicit when reporting row 254 progress. It does not close the complete scenario observation on OCaml or the host.

No completion claim is made for active `Lowered.lean`, its fixture files, the OCaml adapter, or the later handle scenario.
