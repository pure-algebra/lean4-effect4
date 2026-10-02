# A1 receipt — use Lean’s typed authoring-sequence reader

**Before merging:** the new `Lean.Parser.Do` import is permitted by the owner’s DI-18 ruling
at `8c9be258`. This changes authoring syntax processing; stored Eff data is unchanged.

Base `8c9be258`, preceding A2 commit `0cdd8c98`, branch `codex/metaprogramming`.
This receipt’s commit contains the implementation. Production file:
`src/Effect4/Program/Authoring/Sugar.lean`; controls:
`Test/Program/AuthoringScope.lean` (already reachable from Test.All).

`getDoSeqElems` delegates to `Lean.Parser.Term.getDoElems` (Lean 4.33.1,
`Lean/Parser/Do.lean:52–59`) while retaining its List interface. `unnestElems` uses a typed
quotation for exactly one nested do wrapper. Expansion bodies, public helper signatures,
keyword scoping and existing diagnostics are unchanged. Independent source review confirmed
the parser-produced node cases and the one-level behavior.

## Verification

Exact commands, bounds and logs are retained in `evidence-A1/`. One compiler ran at a time,
with `-j1 -M4096 -DwarningAsError=true`. All final checks passed:

- The five new controls passed against both the original and revised macro: three accepted
  forms (braced binding, indented return, unit return) and two existing refusals.
- Sugar and its four non-umbrella direct consumers compiled: Authoring.Services,
  Authoring.Loops, Codegen.Authoring.Forms and Laws.Program.Authoring.Sugar.
- AuthoringScope, BlameContract and TestClockContract passed.
- All 28 unchanged authoring-only guards from AuthoringContract passed, including parsing,
  exact elaborated trees, bounded runs, printed output, nested conditionals and refusals.
  The retained extraction removes only the LayerSharingContract import and selects the
  prefix before the unrelated layer-sharing section, adding the namespace end.
- The cache verification checked 1,004 source/artifact hashes in a 361-module scoped closure:
  zero mismatches. Recompiled modules have fresh command receipts instead of old traces.
- Axiom inspection: getDoSeqElems, unnestElems and expandDoElems each depend on `[propext]`.
  No theorem statement or proof body was changed.

The original experiment first lacked the necessary parser import; after adding it, compilation
passed. A first refusal fixture expected a more specific final-binding error than the original
macro actually produces. The fixture was corrected to the existing generic diagnostic and
then passed against both versions. An initial cache-check invocation omitted its manifest;
the complete invocation passed. These unsuccessful commands are retained, not counted as tests.

The full AuthoringContract includes LayerSharingContract, whose copied artifact came from a
dirty integration source differing from this base. That artifact was not used as evidence:
the clean authoring-only prefix was tested separately. No whole Test/Laws build or full trust
gate ran. The run/output guards are finite tests, not a new runtime equivalence theorem.
