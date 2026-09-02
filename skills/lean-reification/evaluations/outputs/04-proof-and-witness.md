# Proof-repair and executable-witness handoff

The frozen determinism theorem cannot be repaired within the allowed fence: the supplied admitted program is a counterexample. The existing existential theorem can remain valid, but it does not yet provide a program that can be saved and executed. The useful work completed here is the decisive refutation and the two upstream handoffs below.

## Decisive evidence against the frozen theorem

The frozen claim compares the final natural numbers of every checked program from the same initial state across arbitrary compatible, complete answer tapes. Keep the admitted program and any one initial state fixed. The program asks for a bit, then returns 2 for false and 3 for true.

| Fixed program and initial state | Complete compatible answer tape | Final number |
| --- | --- | --- |
| askBit followed by the supplied branch | [false] | 2 |
| The same program from the same state | [true] | 3 |

The checker admits this program and both tapes satisfy the hypotheses. Instantiating the frozen theorem with these two runs would imply 2 = 3, which is false in the natural numbers. The contradiction does not depend on a missing answer, incomplete execution, an inadmissible program, or a different initial state.

This is a mathematical refutation from the complete supplied data. It is not a Lean-checked counterexample receipt; the exercise permits no implementation or Lean execution.

## What fits inside the fence

No proof-body change or proved private helper can establish this false statement while retaining its definitions, admitted programs, and hypotheses. Further tactic search cannot resolve the contradiction. A helper asserting answer independence would simply repeat the false obligation.

Rejecting the program changes the admitted language and is outside the authorized fence. Adding a private axiom for deterministic answers changes the trust assumptions, remains a dependency of any theorem using it, and would contradict the supplied two compatible runs. Calling that axiom private does not make it a proved helper. Neither proposed quick fix is authorized.

Within this documentation-only task, the statement, checker, public declarations, and source files remain unchanged. The refutation and amendment proposal are ready for the contract owner. No proof is reported as repaired.

## Upstream handoff A: amend the determinism contract

**Owner:** the frozen semantic contract owner, followed by the independent breaker and then the proof builder under the repository's normal approval process.

**Old meaning:** final results are identical even when complete compatible tapes supply different answers.

**Smallest proposed amendment:** compare runs using the same fixed complete compatible answer tape, leaving the checker and admitted program unchanged. The proposed agreement statement is: for every checked program, initial state, and complete compatible tape, any two executions from that state using that same tape that reach final natural numbers have equal final numbers. Preserve the other frozen premises. If the original statement also requires termination, retain that as a separate open requirement rather than silently removing it. Approval must also establish that the tape fixes every relevant decision, or state the remaining decision assumptions. The counterexample proves the original statement false; it does not itself prove this replacement for the entire language.

**Expected behavior to retain:** with [false], the admitted example returns 2; with [true], it returns 3. Those are valid outcomes under different answers. Agreement is requested only when the relevant decisions are the same.

**Decision required:** approve the fixed-tape statement, or explicitly choose a different contract. If the intended theorem is instead about programs independent of answers, that domain restriction must be stated and approved as a different theorem obligation; it must not be hidden by changing the checker under the old statement.

**Next evidence after approval:** the breaker should save the two-tape counterexample against the old statement and freeze positive cases preserving both admitted outcomes, plus the revised obligation. The builder then proves the revised statement without changing that packet. Acceptance requires the exact saved theorem and definition identity, relevant narrow checks and required gates, transitive dependency receipts, and the required independent review. No such commands or receipts are available in this paper exercise, so none are asserted to have passed.

This handoff does not authorize the amendment or an implementation. The original obligation remains refuted and cannot be marked closed by proving a differently scoped statement.

## Upstream handoff B: provide a computational witness using the existing program data

**Current evidence:** there is an existing proof of an existential proposition, schematically “there exists p in Program such that p realizes F.” This establishes existence under that proof's assumptions. It does not expose a runtime program through a computational interface.

Lean's general existential proposition lives in Prop. Pattern-matching on that existential proof cannot generally return a witness in the data-bearing type Program: unrestricted elimination from this proof into computational data is unavailable, and proofs are erased for execution. This is specific to the proposed existential extraction; it is not a blanket claim that every elimination from Prop is forbidden.

Classical choice may legitimately select a witness for mathematical reasoning when allowed by the project's declared policy. Such a noncomputable selection is not an implemented executable witness interface. Preserve the existing existence proof, including any classical reasoning and dependencies already approved under the project's policy. Do not relabel approved classical reasoning as an error, and do not add a new choice exception or unrelated deterministic-answers axiom under cover of that approval.

**Owner and scope:** the author of the existence argument and the owner of the existing canonical program representation must supply a computational construction. The target/runtime owners handle the later save-and-execute connection. A new syntax is unnecessary and would contradict the stated preference.

**Smallest useful requested deliverable:** for this formula F, expose a concrete program value in the existing first-order Program type, together with a proof that this exact value realizes F. If the existential proof was originally obtained from such a construction, recover that computational construction and expose it separately; do not try to recover erased data merely by matching on the proof. This is proposed upstream work, not a claim that the construction has been inspected or already exists.

If the existing existence argument supplies no effective construction, the owner must develop one or explicitly state the extra effective input or restricted domain it needs. An arbitrary existential proof alone does not guarantee a uniform extractor. If the intended interface translates source proofs into programs, it needs an inspectable, computational source-proof input and a checked translation into the existing Program representation, with a realization theorem. Neither that interface nor its correctness evidence has been implemented in the supplied scenario.

Keep the three deliverables separate:

| Deliverable | Present status | Evidence needed to close it |
| --- | --- | --- |
| Theorem existence | Supplied existential theorem; no fresh proof/dependency inspection | Retain its exact statement, assumptions, saved proof, and permitted dependency receipt |
| Program construction and saving | Open; no computational witness interface | An actual canonical Program value or effective constructor, a proof for that exact value, and evidence that the saved representation encodes that value |
| Host execution | Open; no executable artifact or run was supplied | A named interpreter/generation path, its relation to the proved program under stated assumptions, exact runtime/artifact identity, and an observed execution with inputs and answers recorded |

Constructing or saving a program is not evidence that a host executed it. A successful host example is an observation of that run, not a universal realization proof. The theorem about F does not certify generated bytes or an external runtime by itself. A future fixed-decision theorem would have the same separate host boundary.

## Verification and change record

- The frozen statement and admitted example are unchanged. No repository files, proof bodies, helpers, axioms, or public declarations were edited.
- The two tapes were checked on paper against the supplied branch definition and compatibility/completeness premises. They yield distinct natural numbers and refute the frozen claim.
- The existential result was kept separate from a computational Program value and from host execution. No extraction, serialization, interpretation, or generation was performed.
- Source/import/instance snapshots, toolchain and dependency pins, exact exported declaration names, transitive axiom output, and executable artifacts were not supplied or inspected. No Lean commands, build gates, host tests, or independent compiled-proof checks were run.
- The only saved work product is this written handoff. It contains no new Lean proof receipt and claims no successful repair.

No workflow ambiguity blocked a useful result. The task expressly replaces the proof skill's normal source-editing and execution steps with a written assessment. The determinism repair needs an approved contract amendment; obtaining an executable witness needs a computational construction beyond the supplied existential proposition.

## Files used

- /Users/pooks/Dev/lean4-effect4/AGENTS.md
- /Users/pooks/Dev/lean4-effect4/COORDINATION.md
- /Users/pooks/Dev/lean4-effect4/skills/lean-reification/evaluations/cases/04-proof-and-witness.md
- /Users/pooks/Dev/lean4-effect4/skills/lean-reification-proof/SKILL.md
- /Users/pooks/Dev/lean4-effect4/skills/lean-reification-proof/references/proof-and-trust.md
- /Users/pooks/Dev/lean4-effect4/skills/lean-reification-proof/assets/proof-receipt.md
- /Users/pooks/Dev/lean4-effect4/skills/lean-reification/references/evidence.md
