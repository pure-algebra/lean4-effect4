# Slice B: structural program path replacement

Base: `8913519b`. Branch: `codex/program-path-editing`.

## Settled contract

Generalize the existing layer-only path update to
`Node.replaceAt : Node Op → List Nat → Node Op → Option (Node Op)`.
A replacement succeeds exactly when the path exists and the replacement has the
same `Node` sort as the addressed node, including at the empty path. Recurse on
the path through generated `Node.child` and `Node.setChild`; do not duplicate
constructor cases or introduce a second tree representation. The operation is a
structural edit only: no variable rebinding, reference relocation, type admission,
behavioral equality, or mutation of a running program is inferred.

The existing `Node.replaceLayerAt` interface and all results remain unchanged.
Its implementation becomes a wrapper over `replaceAt`, with an equality connector
against its existing recursion equation and unchanged structural consumer laws.
Layer placement, `Eff.hoistAll`, and `Eff.restoreAll` are the real existing consumers.
No whole-program editing convenience is required in this slice.

## Edit fence

- `src/Effect4/Program/Refs.lean`: generic operation and layer wrapper.
- `src/Effect4/Laws/Program/References.lean`: structural laws, layer connector,
  reuse in existing layer theorems, and explicit automation import if needed.
- `Test/Codegen/ReadContract.lean`: finite path-edit controls, layer compatibility,
  hoist/restore consumer controls, and exact axiom reports.
- `docs/research/2026-10-03-program-path-editing/{brief,receipt}.md`.

No root imports, decisions, generator outputs, signature, checker or runtime edits.
Theory/register addition is proposed below for coordinator integration, because
those files have concurrent owner changes.

## Proof placement, before proof work

1. **Concept/property:** Concept 7, Initial Algebras and Catamorphic Folds. Proposed
   required property `addressed-replacement`: generated child access/update lifts
   to sort-preserving, reversible addressed tree editing. This is structural
   compatibility, not an interpreter relation.
2. **Question/consumer:** proposed registry claim `addressed-replacement`, role
   `compatibility`, witnessed by `Node.replaceAt_spec` (get, root-sort and undo).
   Helpers for existence, self replacement, overwrite and independent branches
   serve that claim. The compatibility connector and unchanged layer laws feed
   `Eff.restoreAll_hoistAll` and `Eff.hoistAll_restoreAll`, the existing module
   printer/reader reconstruction path. The receipt will propose exact registry text.
3. **Reach:** arbitrary operation type `Op`, all seven existing `Node` sorts,
   finite child-index paths, successful same-sort replacement. No typing premise
   is needed for these structural equations. Layer identity remains its path
   (DB-12; decisions 153/170 constrain checking/reference interpretation).
4. **Excluded:** same local type does not imply global reference well-formedness;
   a replaced ancestor may erase a referenced descendant. No typing, termination,
   scheduling, host, allocation or observation claim is made. Terms remain outside
   the `Node` path language. Host boundary remains unchanged.
5. **Unlock:** R8's exact module representation/reader connection gains one common
   editing primitive used by the existing hoisting path. It supplies a foundation
   for later source transformations without claiming a new M5/M6/M7 result.

## Finishing criteria

- General replacement has the stated missing-path/wrong-sort behavior.
- Get, undo, self, overwrite, and disjoint-path facts are checked on the saved source.
- Layer replacement keeps its existing public signature and structural behavior;
  existing hoist/restore and shared-module reader tests still pass.
- Narrow builds of the touched modules and their direct consumer laws pass.
- The fixture passes, every new theorem's axioms remain within `[propext, Quot.sound]`,
  and new authored proofs contain no silent fallback tactics.
- Explicit-path commit plus receipt records commands, results and limitations.
