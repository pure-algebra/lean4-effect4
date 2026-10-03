# Slice B2 receipt: rebuilding edited programs

**Coordinator first:** cherry-pick after slice B. The application addition is
`Built.rebuild`; its shared final-admission implementation is under
`Author.Internal`. The exact candidate is completely checked against the existing
table. A successful edit may change its type; no behavioral relation is asserted.
Add the Concept 2 compatibility property/registry claim below during integration.

Base: `f1bce7dd`. Code head: `1819dbee503a566b5f7f4e6581bd1208581a0186`.
Branch: `codex/program-path-editing`.
Worktree: `/Users/pooks/.codex/worktrees/program-path-editing/lean4-effect4`.

## Changes and evidence

- `src/Effect4/Api/Author.lean`: extract the existing final admission branch into
  `Author.Internal.finishBuild`; both original `Author.build` and new
  `Built.rebuild` use it. No second checker, refusal kind or codec.
- `src/Effect4/Laws/Program/Author.lean`: retain `build_table`'s statement and prove
  rebuilding's candidate/table/names equation, acceptance of an admitted
  candidate, and same-input rebuilding. Reuse `admitProgram_eq_ok`.
- `Test/Program/AuthorContract.lean`: a real key-value package program with five
  external rows is edited through `Node.replaceAt` and rebuilt. Its answer becomes
  string, its original external request remains, and its table, row names and
  named position remain. Rebuilding rejects an out-of-scope variable at `[1]`, an
  equal-local-type layer edit that removes a reference target, and a reserved
  integer annotation using the existing non-typing admission refusal.
- The prior brief and this receipt. All sources/tests already have root imports;
  coordinator files, generated codecs, schema and checker logic are untouched.

| Final command | Result |
| --- | --- |
| `lake build Effect4.Api.Author Effect4.Laws.Program.Author Test.Program.AuthorContract` | Passed, 310 jobs |
| `lake build Effect4.Api.RefusalsDerived Test.Program.AuthoringScope` | Passed, 125 jobs |
| `git diff --check` | Passed |

Every new/changed theorem and both new definitions have retained `#print axioms`
commands in the fixture. All reported exactly `[propext, Quot.sound]`, including
`Author.Internal.finishBuild`, `Built.rebuild`, `build_table`, `rebuild_spec`,
`rebuild_admitted` and `rebuild_self`. The controls are finite; the three new laws
are checked universal statements at their stated scope. No whole-tree sweep,
host execution, or backend agreement is claimed.

Two proof attempts exposed the private helper visibility issue documented in the
brief. Lean's local `Elab/MutualDef.lean:1363-1370` says `@[expose]` is meaningful
only for public definitions in module files and has no effect outside a module
file; this source is not a module file. The coordinator agreed to an internal
namespace. The first fixture run also caught a nonexistent integer literal
constructor in an extra refusal control; it now uses the existing reserved
integer annotation. Final checks above ran after both corrections. No contract
or theorem statement was weakened.

The moved admission refusal match introduces no new policy-family case;
`tools/Conform/Effect4/cases-policy.json` has no `AdmitRefusal`, `BuildRefusal`, or
`Node` family. No case-policy or traversal census change is needed.

## Five-part theorem placement

All three new laws are in `Effect4.Program.Authoring`, Concept 2
(`residual-program-typing`), proposed compatibility claim `rebuild-admission`.
They supply checked candidate data for the existing `denote-typed` / `load-typed`
consumers and serve R8 authoring/composition, without advancing M5/M6/M7 itself.

| Theorem | Exact reach and consumer |
| --- | --- |
| `rebuild_spec` | For any successful rebuild, returned program equals the candidate, table equals the original table, and row names equal the original names. The returned admission certificate is indexed by those fields. Registry witness and editor consumer. |
| `rebuild_admitted` | Every candidate already carrying `AdmittedProgram candidate before.table` rebuilds with that certificate and original metadata. Reuses the existing admission-completeness theorem; consumed by same-input rebuilding. |
| `rebuild_self` | Rebuilding a Built value's own program returns that Built value. Consumer sanity law with no new execution claim. |
| `build_table` (existing statement) | Original author module still yields its own table/names through the shared final-admission step. |

Assumptions and cuts: the current `AdmittedProgram` judgment, DI-22's table-relative
external positions, DB-12's path identity, decisions 153/170's layer reference
checking. No preservation of the previous type or behavior, binder/reference
relocation, running-session editing, progress, liveness, target execution or host
implementation guarantee follows. Row-name metadata is retained; rebuilding does
not make new claims about arbitrary manually constructed metadata.

## Exact coordinator additions proposed

At Concept 2's Required Properties, after `denote-typed`:

> **Rebuild admission (`rebuild-admission`)**: successful `Built.rebuild` contains
> the exact candidate program, retains the original host table and declared row
> names, and carries the existing complete admission certificate for those data.
> Already admitted candidates succeed and rebuilding the original program returns
> the original Built value. This supplies checked input to the existing typing
> results; it asserts no relation between old and new program behavior or types.

Registry entry adjacent to `denote-typed`:

```lean
    { id := "rebuild-admission", concept := "residual-program-typing", role := .compatibility
      title := "Successful rebuilding checks the exact candidate under the retained host table and row names"
      pointer := .witness `Effect4.Program.Authoring.rebuild_spec },
```

No decisions row is proposed: this operation reruns the settled checks and makes
no new semantic choice. Further editing APIs can compose the separate structural
`Option` with this admission `Except`; missing paths are not typing errors.
