# D production integration: static review

The staged production layout has no static blocker after the two expected-red message placeholders are replaced by root's checked Lean output. This is a static review of `/private/tmp/d-integration/staged/final`; production compilation, the obligation commands, positive/negative bank controls, and axiom probe remain root's serialized checks.

## Checked boundaries

- The combined overlay has no missing local imports, library-to-Test import, or local import cycle. The two new library modules and new Test modules are all reachable from their respective roots. The scanner's reported unreachable modules belong to the separate OCaml5 tool root, outside this Effect4/Test scan.
- After stage 3, the library contains no `forkedOf`, `AgreesUpdates`, or `TraceFacts.Agrees` reference. The diagnostic definitions, laws, helper bank registrations, and agreement proofs move together to `Test/Api/TraceOrigin.lean`. `Test/Api/SupervisionContract.lean` and the red-control file import that new module. `Effect4.Laws` stops importing the removed source TraceOrigin module.
- The generic invariant module imports only Machine.ForkLedger and Machine.Lift. Its new StepInv bank declaration is supplied transitively by the separately compiled Laws.Auto.RuleSets module, not declared locally. The native invariant module imports this generic module and Guard.Core, and is reachable through Guard after MemoIds. It has no trace-agreement dependency.
- Namespace relocation is consistent: the 47 generic theorem names live under `Effect4.Machine.ForkLedger.Invariant`, and the 29 native/load/control names use that namespace and its Native child. References to the old draft namespace and research bank module do not remain.
- All 30 declarations removed from source Supervision are present in the new Test module under their retained names. The four explicit existing M1Trace proof references are retained. The load/step/reachable agreement obligations each receive their new concrete proof reference. The old TraceFacts.M1Trace ceiling becomes zero; it still covers all three original obligations. Source Api.M1Trace retains the two status-with-erased-trace obligations at zero; the Test gate sees the full 15-obligation namespace after adding back its 13 diagnostic obligations.
- The invariant split omits only the two intentionally conditional convenience wrappers `steppedBy_ok_of` and `reachable_ok_of`. It retains the final native command proof and the four reachable lookup consequences with no extra command-preservation assumption.

## Rule-bank controls

The trace positive theorem asks the named bank to preserve agreement on `emit` under its actual no-fork premise. The ledger positive asks it to preserve the allocation view on `update`. The corresponding Test fixtures omit the bank, use matching statements, and use `#guard_msgs (error)`. The staged message bodies are currently explicit placeholders, so the patch is not ready to apply as a passing test until root records and inserts the exact failures. Both positives and both fixtures must be checked again after relocation because their available imports/rules change. No broader generic transitivity or reverse allocating rule is registered in the bank.

## Complete theorem axiom receipt

`axioms/ProductionTheorems.lean` covers every authored theorem in the three new/relocated modules: 175 total = 47 generic invariant + 29 native invariant + 99 diagnostic module. The diagnostic total includes 29 existing moved obligations/laws and 70 new agreement/control theorems. There are 174 explicit public `#print axioms` commands, plus one exact private-name lookup for `ViewOk.nodup_snoc`, constrained to its owning production module, followed by its axiom collection and ceiling check. The normalization lemmas and both new positive bank controls are included. This probe is not an exemption from the repository's full declaration gate.

`axioms/manifest.json` records each production theorem, source line, privacy, and the input source hashes. `prepare_axioms.py` regenerates it from the staging tree and fails if its source parser misses or duplicates a theorem. `candidate-print-coverage.json` also checks the current checked candidate files: invariant 77 declarations/77 print commands, trace 69/69, with no missing theorem. These are actual command counts, not line counts of an old appendix.

## Remaining receipt detail

The staged Test SupervisionContract header still says origins are stored on each fiber, although its actual checks read the machine ledger. Update this stale sentence to name the ledger when finalizing the move; it describes the architecture changed by C and is within the touched file. No proof or runtime change is needed.

No repository writes, Lean, lake, builds, or generators were run for this review. Python source inventory/import checks passed.
