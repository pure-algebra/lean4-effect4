# Independent final H2 source review

Static source review passes with the race failure-buffer amendment now present in `/private/tmp/h2-after-h1-d554cd71/source/repaired`. This is a review of the proposed contract and proof changes, not a Lean execution receipt. Root owns the serialized checks.

The candidate is pinned to landed H1 `d554cd7194f54c1ed2ffd020b4dc59d573bc1c34`. Its 72 recorded substitutions are **source occurrences**, including repeated theorem/obligation signatures, rather than 72 distinct machine fields: Admission 4, Residual 25, Stack 26, Assembly 6, Scheduler 11. Scheduler has ten FitsExit substitutions and one additional cause-buffer strengthening. I independently counted those occurrences and verified the live Membership file matches the manifest's unchanged SHA-256.

The missed race buffer is now `ExitOk w resultTy (.failure ⟨race.state.failures⟩)`. This is required: `raceComplete_failure_last` packages previously accumulated reasons into the accepted exit, even when the last callback contributes an admitted empty cause. `RaceFailureBuffers.lean` retains the old whole payload predicate, two old-admitted/new-refused defect examples, interrupt/user-defect/missing-service positives, and that actual packaging equality. Its 13 theorem declarations each have an axiom print; root must supply the checking result.

`NoShapeDefect` retains but ignores the effect-type parameter and excludes only badName/notImplemented. Base Fits/FitsExit and both base Scheduler embedding helpers remain unchanged. Encoded exits and causes remain ordinary data; no blanket value exclusion was added. Recorded interruptions, sanitized causes, iterator halts, buffered race/countdown results, queued exits, saved stacks and deferred/owed completions use the strengthened relation at their relevant typed boundaries. Named hook contracts remain required. The proof repair uses the incoming exclusion and existing interruption provenance, with no reachability premise, arbitrary transition certificate, runtime change or new axiom.

Historical negative tests must remain labeled **historical contract refutations** when they use retained old definitions. Their successful checks establish the old counterexample and its contrast with the new positive/refusal; they do not establish admission by the live strengthened predicate. The old test-helper signatures that accepted arbitrary clean defects or untyped decoded values must likewise be retained as historical evidence, rather than described as current library contracts. Fresh controls use the actual new predicates. Copied five-module harness checks and production module/test checks need separate receipts.

Remaining boundaries are unchanged and must stay explicit:

- M5 source initialization and operation/protocol certification remain open, including the existing source/continuation connections. Local repaired stack/hook facts do not discharge them.
- All eighteen M6 command obligations, the decision obligation and the reachable-state capstone remain open. H1's lift adapters still require the command family as hypotheses. Neither these edits nor the finite controls establish that every admitted run avoids the two defects.
- The reference code-site scan and the explicitly refused stored scope-exit/external source rows remain open. No claim covers every raw machine payload.
- H2 part two remains held: missingService is admitted even at an empty requirement row. Its exclusion still requires the separate operation and saved-frame requirement-transport amendment; part one adds none of those assumptions.

No further source-contract defect was found within this review's five-module scope after the race-buffer repair.
