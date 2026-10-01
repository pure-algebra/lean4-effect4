# Seat W0: the lean4-typescript bump (row 164, as probe R amends it)

Written 2026-10-01 by the coordinator. The package: `pure-algebra/lean4-typescript`, pinned in
this tree's `lakefile.toml` at `6afc9b84` ("v0.6.0 carrier: structural type annotations and
retained source bindings"). Your worktree is a worktree OF THAT PACKAGE, not of Effect4:
`/Users/pooks/Dev/lean4-typescript-wave`, branch `wave/typescript-0.7`, base `6afc9b84`. Never
edit the Effect4 tree; read it for the consumers and probe R's measurements (main checkout
`/Users/pooks/Dev/lean4-effect4`, read-only): `docs/research/2026-10-01-type-language-probe/R/note.md`
(Q2 "The printed image per name class", Q3 "The printed type forms", "The forms table"),
`R/probes/Q2Faces.lean`, `Q3PrintedTypes.lean` (the model `PExpr.index`, `PExpr.objectComputed`),
`R/host/names/` (tsgo and node controls), probe T's note §4; the consumers in Effect4:
`src/Effect4/Codegen/{Types,Print,Read,SourceBindings,Schema}.lean`, `Test/Codegen/ExprContract.lean`.

**The one thing.** The wave's faces (commit 8) print optional fields, bracket access by name
class, computed keys for `__proto__`, payload classes constructed with `new`, and object spread,
none of which the vendored syntax can say today (`TypeScript/TypeRef.lean:18`: `object (fields :
List (String × Bool × TypeRef))` has no optional flag; `TypeScript/Syntax.lean`: `Expr` has
`member` but no element access, no computed keys, no `new`, no spread). Add exactly those forms,
version 0.7.0, with the renderer, the equality, the source-binding and identifier rules and the
tests the package keeps for its other forms, so Effect4 can pin the new revision at commit 8.

## The forms (each: constructor, renderer arm, `beq` arm, bindings arm, a test with the exact
rendered text, a red twin where the package has that pattern)

1. **Optional fields on object types.** `TypeRef.object`'s field carries `optional : Bool` beside
   `readonly` (a field record `{ name, readonly, optional, type }` if the package prefers names to
   a triple; keep the existing constructors' meaning for current consumers). Rendered
   `{ readonly a?: number }`; with an explicit `undefined` member the consumer writes the union.
2. **Element access with an expression key.** `Expr.index (target : Expr) (key : Expr)`, rendered
   `t["a-b"]`, `t[2]`, `m[k]`; the bindings rule treats the key as an expression; no identifier
   check on a string key.
3. **Computed object keys.** Object literals whose keys may be computed: `{ ["__proto__"]: v,
   ["a"]: 1 }` (R's rule: one computed key computes all; the renderer never emits the plain
   `{ __proto__: v }`, which creates no own property; keep R's node control as the test's reason).
   Quoted keys (`{ "a-b": 1 }`) stay as the package renders them.
4. **`new`.** `Expr.new (callee : Expr) (args : List Expr)`, rendered `new NotFound({ id: 2 })`.
5. **Object spread.** `{ ...t, b: y }` as an object-literal entry (rendered in order), for the
   record update form R names.
6. **The class declaration.** `ClassDecl` exists; confirm it renders `export class NotFound extends
   Data.TaggedError("NotFound")<{ readonly id: number }> {}` with a type-argument list on the
   heritage expression, or add the form; one test with that exact text.

Rules: the package's own conventions (read its README, its tests and its last three commits before
writing); no `sorry`, `partial`, `unsafe`; every rendered string in a test checked by `#guard` or the
package's own test style; the package's trust and style gates green (`lake build`, its test target);
version `0.7.0` in its manifest and changelog as the package records versions; a commit per form and
a final commit "v0.7.0: ..."; nothing pushed (the coordinator pushes and pins). TypeScript checks of
the rendered text, if you run any, with `/opt/homebrew/bin/tsgo` 7.0.0-dev.20260629.1 on files in
your worktree, versions logged. One compiler at a time in your worktree.

## Receipt

`RECEIPT-0.7.0.md` at the package root (the package's practice for notes may differ; follow it):
base and head; the forms with their rendered text and tests; the consumers in Effect4 each form
serves (by file); what changed for existing consumers (nothing, or the exact constructor change);
the commands and results. Hand back with the one thing first, the head commit, and the receipt's
path.
