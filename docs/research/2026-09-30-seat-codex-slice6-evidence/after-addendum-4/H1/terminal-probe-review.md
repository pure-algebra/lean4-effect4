# H1 final-predicate terminal probe review

**The witness is a plausible direct refutation of the final proposed `StepPreserves`, not a refutation of an older weak queue definition. It is still uncompiled. If Lean proves the file with the final H1 modules and the allowed axioms, the brief requires stopping H1 and recording the smallest needed amendment. Do not implement a repair from this review.**

## Predicate and premise check

`/private/tmp/h1-candidate/src/Effect4/Laws/Program/Typed/Assembly.lean:78–80` has all six TypedState conjuncts; the witness constructs exactly those at `H1TerminalSavedWitness.candidate.lean:124–151`. QueueOk has nine fields (`Assembly.lean:114–126`), all supplied at witness lines155–182. RegistrationState, RegistrationQueue and CommandDeliveryOk are included. The file defines no local TypedState, QueueOk or StepPreserves and assumes neither a preservation theorem nor M5 initialization.

The witness has one active root, no park, pending payload, observer, race or dispatcher task. Its current code returns Nat42; its one `.answer` continuation returns unit. `SavedOk` explicitly permits this Nat→Unit changing intermediate type (`Typed/Contracts.lean:37–39,50–55,66–69`), so witness `saved_typed:118–122` is the positive control. The actual `WorldValid` proof reuses only initial validity for unchanged state/ids and supplies its own vacuous park condition; validity does not require the current program to equal the loaded source.

For `.deliver`, generated RCmdOk has no carried payload (`Typed/Sources.lean:63–66` identifies the payload-bearing constructors), CommandDeliveryOk's actual final arm is True (`Scheduler.lean:213–225`), and authority requires an actual active fiber (`Scheduler.lean:227–230`, generalized `Guard/Core.lean:1158–1162`). The witness proves the latter by lookup/running/park equations. The singleton owner list is unique, the registration tail is True, and the key/observer/enrollment conditions apply to empty data. These are not hidden assumptions or a replacement whole-transition premise.

## Actual result claimed, and why it matters

`Machine/Fibers.lean:1861–1864` delivers through the chosen `termEvaluatorFor`; `EvaluateR.lean:97–101` consumes a pure answer continuation by recursively delivering its new exit while retaining the previous current program. The empty-stack case at line67 only writes stack=[] and returns the exit. `deliverR:133–142` returns that saved frame; `prepareIterR:329–339` prepares the same pure current code. `settle`'s finished arm (`Fibers.lean:1821–1824`) stores the returned fiber and queues finish.

The witness's equations at lines189–194 therefore claim the precise expected boundary: current=pure Nat42, stack=[], queue=[finish root unit], **exit=none**. These equations are source-consistent. The stale-current contradiction happens before publication; changing only exited-fiber treatment would not address this case.

The refutation at lines198–211 uses WorldValid.root to force unit at the output root in every proposed output world. Empty StackAccepts forces the intermediate type to equal that final type, and TypedProg.pure_inv then produces the impossible FitsExit unit (success Nat42). It does not rely on the output queue failing, world growth, reachability or host answers. The pending finish carries the correct unit value; the mismatch is the saved state.

`M6Ledger.step_deliver` at final candidate Assembly:206–207 is a `ProofGraph.Obligation` wrapper, not a proved StepPreserves. The probe correctly attacks the underlying proposition via `¬ StepPreserves`, not the trivially inhabited wrapper itself. Exact rfl equations, constructor/projection details and the final False reduction remain Lean checks; a failed elaboration would be inconclusive, not a checked counterexample.

## H1 scope and exact stop authority

H1 does **not** require proving deliver preservation now. Addendum3:109–110 and addendum4:124–128 explicitly leave all18 command proofs to the M5–M7 brief. It does require freezing the revised statement those proofs will target: addendum2:201–206 says to restate StepPreserves and retain quantification over every pending list meeting the queue fact; addendum3:79–110 strengthens that same statement. The final candidate implements it at Assembly:132–136, universally over any TypedState and QueueOk, with no reachability premise.

The stop authority is the original tracked `docs/research/2026-09-30-codex-brief-slice6-and-fixes.md:228–231`: “Stop the item, record the smallest amendment in the receipt, and go on with the next item when: … a checked counterexample refutes a statement this brief asks for”. Addendum4:101–105 expressly treated an earlier refutation of the statement as a design blocker before any proof; its statements-only provision does not waive this rule. Addendum5:122 says its new rulings do not change H1.

Thus a checked version would stop H1's proposed statement landing, even though this particular SavedOk behavior predates H1 and the known token/finish/observer controls may pass. Preserve the candidate and smallest witness; name the required delivery/terminal saved-state alignment for an owner ruling. Do not silently strengthen away the legitimate changing-type stack, weaken SavedOk, or change the evaluator. No claim of reachable-program failure is established by this arbitrary-typed-state witness.

## Root's eventual checks

First make the **final candidate** Assembly/Scheduler/Guard definitions available through fresh compiled modules in the designated worktree. Running the probe against current pre-H1 Assembly would be a different test. Copy the unchanged probe into the H1 evidence folder, then from `/Users/pooks/Dev/lean4-effect4-slice6` run, alone:

```sh
lake env lean -DwarningAsError=true docs/research/2026-09-30-seat-codex-slice6-evidence/after-addendum-4/H1/TerminalSavedWitness.candidate.lean
```

Expected successful evidence is Lean exit0 with all named positive premises, exact result equations and `step_deliver_false` proved. Reject sorry/choice or any unrelated elaboration failure. The file currently prints12 of its15 authored theorem axioms. Add these three receipt lines when root stages it (they change no theorem):

```lean
#print axioms H1TerminalSavedWitness.no_requests
#print axioms H1TerminalSavedWitness.result_current
#print axioms H1TerminalSavedWitness.result_stack
```

`/private/tmp/h1-final-probe-review-static.json` pins the exact Assembly, Scheduler and witness hashes, field order, theorem list and three omitted prints. Static field-order and no-shadow-predicate checks passed. No Lean/build/generator, worktree write or repair was performed.
