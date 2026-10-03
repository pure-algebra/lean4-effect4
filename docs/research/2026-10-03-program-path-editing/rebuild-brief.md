# Slice B2: rebuild an edited program with its existing host setup

Base: `f1bce7dd` on `codex/program-path-editing`. Authorized by coordinator after
slice B's checked commit. This brief precedes changes or proof work.

## Contract and edit fence

Add `Built.rebuild (b : Built) (candidate : Api.Program) : Except BuildRefusal Built`.
It runs the existing complete admission procedure on the candidate against
`b.table`, retaining `b.rowNames`. On successful admission it carries the newly
checked program and certificate. It uses the same located typing explanation and
fallback refusal as `Author.build`; no new refusal kind, codec, or checker.
Extract that existing final branch to `Author.Internal.finishBuild`, shared by both callers.
The helper retains supplied row-name metadata but does not admit or validate that
metadata; the original module build establishes its declaration correspondence.
A private helper was opaque to the separate Laws module. Local Lean 4.33.1
source (`Lean/Elab/MutualDef.lean:1363-1370`) says `@[expose]` has no effect
outside a `module` file and is meaningful only on public definitions within one.
The shared helper therefore lives in the implementation namespace `Author.Internal`
for its compatibility proofs; it is not another advertised authoring operation.

The operation accepts an entire candidate program. It does not itself navigate a
path or turn a structural edit failure into a typing refusal. Callers use the
existing `Option` result of `Node.replaceAt` before calling rebuild. No relation
to the old program's type, references, behavior or running session is promised.
A changed result type is a useful successful edit.

Files: `src/Effect4/Api/Author.lean`,
`src/Effect4/Laws/Program/Author.lean`, `Test/Program/AuthorContract.lean`, and
`docs/research/2026-10-03-program-path-editing/{rebuild-brief,rebuild-receipt}.md`.
The laws may import the existing `Laws.Program.CheckedTyping` to reuse
`admitProgram_eq_ok`; no new root import is required. No coordinator authorities,
generated outputs, syntax, runtime or checker change.

## Five-part proof placement

1. **Concept/property:** Concept 2, Residual Program Typing, supplies the checked
   input to `denote-typed` and `load-typed`. Proposed required API compatibility
   property `rebuild-admission`: rebuilding retains the host setup and admits the
   exact candidate using the existing admission judgment.
2. **Question/consumer:** proposed registry compatibility claim `rebuild-admission`,
   witnessed by `Authoring.rebuild_spec`: success identifies the candidate, original
   table and names; its returned admission certificate is indexed by those data.
   A completeness helper for an already admitted candidate and `rebuild_self`
   serve this claim. Existing `Authoring.build_table` remains the original build
   consumer; author fixtures use the new helper after `Node.replaceAt`.
3. **Reach:** arbitrary previously built program and arbitrary candidate. Success
   means `AdmittedProgram candidate b.table`, with all its existing checks, not
   merely local typing. Same-input rebuilding reuses `admitProgram_eq_ok`.
   Decisions 153/170 and DB-12 retain the existing layer-reference checks and path
   identity; external positions keep the same table (DI-22).
4. **Excluded:** no behavioral equality, preservation of the old answer/error
   type, scope or reference relocation, progress, liveness, or M5/M6/M7 proof.
   Declared-service agreement has already been checked during the original
   module build; rebuilding does not invent or alter declarations. No target or
   host implementation guarantee follows from admission.
5. **Unlock:** R8 authoring/composition: edited first-order syntax can be checked
   into the existing Built consumer path without the caller reconstructing
   certificates or its host setup. Its certificate supplies existing M5 input;
   it does not extend the M5 fragment or infer closed requirements.

## Finishing criteria

The real author fixture edits the nonempty key-value package program and rebuilds
it: successful edit changes answer type, preserves table and rowNames, and uses
the original external request before the edited return. An out-of-scope variable
is refused with its location. A same-local-type layer edit that deletes a target
is refused by complete checking. Existing Author.build controls still pass.
Narrow builds and axiom reports of every new theorem/definition pass before an
explicit-path commit. The receipt supplies exact registry/property proposals.
