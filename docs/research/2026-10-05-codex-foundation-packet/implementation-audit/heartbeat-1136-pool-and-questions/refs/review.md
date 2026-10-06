# REFS consumer and battery review

## Cut and disposition

This review freezes consumer commit `525c78b3` and battery commit `8a5352dc`.
It also checks the joint status pin in `8aaf5460`, already present at the observed seat head `ca41bd6a`.
The seat receipt is an active draft, copied separately.
No main integration or final handoff is inferred.
No new semantic defect appears in the reviewed changes.

## Exact statement changes

`typeOfProgram_expandRefs` loses only `hempty`, the Boolean fact that expansion contains no references.
It retains `p.layerRefsWF = true`, arbitrary operation alphabet and signature, and the same checker-result equality.
`checkTypedProgram_of_hasTy` loses only `expanded`, the corresponding list equation.
It retains reference formation and `HasTy sig [] program.expandRefs ty`, and returns the same exact typing certificate.
The new `typeOfProgram_eq_if_refsWF` supplies the common equation used by both consumers.
Neither equation implies typing success without the retained typing derivation.

Seven full declaration comparisons cover the consumers, top theorem and four PathOrder facts.
The comparison starts at each declaration keyword and retains every binder and the complete conclusion.
Changed-assumption and changed-conclusion controls are refused.
`statement-comparison.json` retains both full versions.

## Actual saved acceptance

The exact consumer tree builds successfully: 983 jobs, exit zero (transcript result 556).
The battery tree builds successfully: 984 jobs, exit zero (result 562).
The joint status-pin tree also builds successfully: 984 jobs, exit zero (result 599).
Result 590 and the copied census log contain 21 allowed-axiom queries.
The four public statements are proved, with no next goals.
The measured dependency edges connect the checker equation to the expansion theorem and both consumers to that equation.

The battery contains five accepted shapes and four malformed-reference controls.
The diamond grows from six sites to nine before reaching zero.
The forward-reference control shows why the formation premise cannot be dropped from checker-result agreement.
It also demonstrates that successful elimination alone does not establish reference formation.
Nineteen deliberately changed checks produce nineteen errors, with exit one (result 596).
These are finite controls beside the universal proof, not a run or target comparison.

## Proof style and import disposition

The two new PathOrder proofs retain their exact statements and allowed axioms.
They use the existing order definition's cases and explicit counting induction.
The seat first tried proof search; an added import exposed an older linter error in ReferenceTyping.
The retained reproduction changes only `import Aesop`: the plain file succeeds and the imported file fails at `unnecessarySeqFocus`.
This is a source-maintenance issue, not a reason to weaken the axiom policy.

The baseline edit deletes one obsolete permission for bare `simp` in `typeOfProgram_expandRefs`.
It adds no exception; the saved proof-style gate passes.
The coordinator should accept that exact deletion as the necessary consequence of replacing the proof.
Avoid recording a permanent prohibition on importing Batteries as an architectural rule.
A later, bounded rewrite of the seven legacy reference-free identity proofs can remove that constraint.
No such rewrite is needed to claim this slice's stated result.

## Remaining choices and recommendation

1. Register `reference-expansion-complete` under `initial-algebras-folds`, R5, with role `substitution`.
   Point it at `expanded_refs_nil_of_wf`; add the module default and required-property text already proposed by the seat.
   Regenerate the existing semantics report at integration; create no parallel status table.
2. Keep the redundant runtime check for this merge.
   If its removal is selected next, change `typeOfProgram` and the matching `Api.explain` branch together.
   Preserve `explain_none_iff`, the certificate laws, signature transport and the looped checker connector.
   Do not import the Laws graph into the runtime root.
3. Treat the seven legacy identity proofs as optional maintenance, with a real import consumer.
   Do not block this reference-elimination result on a general proof-infrastructure campaign.

The cases check passes for its current configured population (231 subjects, result 581).
Its configuration imports `Effect4`; it does not establish coverage of every new Laws or Test case split.
LayerTerm is outside its nine named policy families.
Do not promote that finite scoped pass into whole-program case coverage, or broaden its policy within this merge.

## Limits

Reference elimination under formation is proved; execution agreement, sharing, scope preservation and lowering remain separate properties.
The runtime expander and checker definitions do not change in this slice.
This review reads sources and retained results only; it runs no Lean, compiler, runtime, generator or project gate.
