# External completion contract

D6: external `RunDecision.answerAsync` carries the existing `Completion` family:
an exit or a Ref key to read when resumed. The type is parameterized by the
value and cause alphabets and has no program-code parameter. Internal task and
command answers still carry the chosen code type.

`RunInterp.answerCode` interprets the data. The stores instance uses
`completionPrim`; the compiled-program instance embeds that same code. Both
retain the existing resume-token guard. The Layer profile has no Ref heap:
`D6-FB-LAYER-REF` returns its existing unsupported-operation defect for a Ref-read
answer, and accepts exit answers.

`CompletionContract` checks successful and failed exits, Ref reads against the
state at resumption, wrong tokens and duplicate answers. It also records
`E4-HANDLE-CE-001`: a well-typed source program can receive an external completion
containing a nonexistent fiber or Ref handle. The answer format itself certifies
neither typing nor handle validity. The owner has been asked to choose between a
valid-input premise for the handle theorem and changing replay admission; that
choice is separate from D6, whose Completion format is already selected.

`D6-FB-AVATAR-ANSWER`: the OCaml bridge's success-answer parser constructs the
selected Completion data. The separate OCaml avatar still has an exit-only
answer tape. Its regenerated description exposes that mismatch, pinned by name
in `git:14e6835:src/OCaml5/Avatar/Check.lean` (the avatar is archived on branch
`archive/ocaml5-avatar`); the projection report now has 47 of 58 matching
descriptions. This slice does not widen that host's answer protocol.

No host execution or later term-scheduler correspondence is asserted. Receipts:
`Test/Machine/Runtime/CompletionAxiomReport.lean`; whole-tree axiom ceiling
`[propext, Quot.sound]`, with no new exceptions.
