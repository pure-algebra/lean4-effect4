# Retained TypeScript target fragment contract

Status: retained port, 2026-08-31; structural source carrier amendment, 2026-09-16

Implementation: `the TypeScript.Syntax module in the pinned typescript package` and
`the TypeScript.Render module in the pinned typescript package`

Lean battery: `Test/Codegen/ExprContract.lean`

Counterexamples: `E4-TARGET-CE-001` through `E4-TARGET-CE-004`

Proof graph: the TypeScript target DAG note (not retained)

## Source and boundary

The source is Foldlab `library/cas/Cas/Backend/Ts.lean`, lines 1-252, at the
repository pin recorded in `PORT-MANIFEST.md`. Its SHA-256 is
`cdae7c93f5f62a2800bfee9497f4ec33c369e7be8ad71b2c1879b966741ecc15`.

Effect4 retains the syntax constructors and fixed-layout rendering behavior,
but not Foldlab's namespace or CAS-specific ownership claims. Syntax lives in
`TypeScript.Expr`; rendering lives in
`TypeScript.Render`. Foldlab consumers remain downstream until
the later compatibility phase.

This is target-only data. It is not Effect4 program syntax, a denotation, a
typing derivation, or evidence that rendered bytes pass TypeScript, Effect v4,
or the language service. Those are later `Type`, `Lower`, `Decode`,
`Simulation`, and host-harness obligations.

## Existing-type dispositions

| Public type | Role | Duplicate-prevention relation | Assurance route |
| --- | --- | --- | --- |
| `TypeScript.Expr` | canonical retained expression syntax | target-only; not `Effect4.Program`, `Effect4.Flow`, or `Lean.Expr` | `TS-PG-RETAINED-RENDER` |
| `TypeScript.Stmt` | retained straight-line generator statement syntax | child syntax of `Expr`; no second effect program | same graph, construction edge |
| `TypeScript.ConstDecl` | passive declaration record | contains the canonical target `Expr` | same graph, construction edge |
| `TypeScript.ProgDecl` | retained generator declaration record | contains `Stmt`; not an Effect4 semantic program | same graph, construction edge |
| `TypeScript.Decl` | retained module-declaration sum | owns the compatibility-only `raw` arm | same graph, construction and counterexample edges |
| `TypeScript.Import` | passive import alphabet | one target-only owner | same graph, construction edge |
| `TypeScript.Module` | passive module record | contains the declaration and import owners above | same graph, construction edge |
| `TypeScript.Style` | passive rendering-value record | one renderer style; no semantic or typing role | `TS-LEAF-STYLE`, attached to the graph's representation edge |

`Style` is a trivial passive record and does not receive its own proof graph.

The upstream text renderer reaches `Classical.choice`: Lean's standard UTF-8
character fold carries that dependency in its proof implementation. Downstream
rendering declarations are admitted by exact name in the Effect4 axiom gate;
there is no module-wide exemption. Structural type conversion and comparison,
semantic Schema admission and predicate laws retain the tighter
`propext`/`Quot.sound` ceiling, while exact emitted bytes are checked by Lean
reductions and the independent host harness.

## Historical port surface

The original retained expression constructors are `ident`, `str`, `int`, `float64Bits`,
`bool`, `jsNull`, `call`, `object`, `objectML`, `objectQuoted`,
`objectQuotedML`, `objectFromEntries`, `arr`, and
`arrow`, in that order. The two additive constructors are consumer-driven by
raw Schema generation: `float64Bits` preserves an exact binary64 datum without
trusting lossy decimal formatting, while `objectQuoted` and `objectQuotedML`
treat property names as data rather than target identifiers.
Statements are `constYield` and `ret`; declarations are `const`, `prog`, and
`raw`; imports are `all`, `named`, and `types`.

Revision 0.7.0 (pinned 2026-10-01 at `f5878bf879bd5712db964c2cd12802748c707605`, seat W0's
receipt in the package worktree) adds three expression constructors: `index` (element access
with an expression key, `t["a-b"]`, `t[2]`, `m[k]`), `new` (a constructor call), and
`objectWith` (an object literal with one `KeyForm` for every key, `plain | quoted | computed`,
over `ObjectEntry`s, `property | spread`; every key of a literal with a computed key is
computed). The binding analysis collects both halves of `index`, treats `new` as `call`, and
requires identifier bytes only of a `plain` property name; the style pass's `mentions` reads
inside all three.

The printer retains these equations:

- string escaping belongs to the printer and covers the selected quote,
  backslash, newline, carriage return, and tab;
- ordinary objects and arrays render inline exactly when all rendered children
  are newline-free;
- quoted objects use the same sole string-escaping owner for every key;
- entry-built objects retain their field list in syntax while rendering
  through `Object.fromEntries`;
- binary64 values reconstruct from eight big-endian bytes through `DataView`;
- `objectML` always renders one field per line when nonempty;
- arrows render their body at the current depth;
- module headers render blank paragraph lines without trailing whitespace;
- imports are contiguous and declarations have one blank line between them;
- output depends only on the syntax tree and explicit `Style`, never on a
  width budget or host formatter.

## Structural source carrier amendment

The dependency revision in `lakefile.toml` owns the current target carrier.
`TypeScript.TypeRef` stores qualified names and generic arguments, string literals,
tuples, unions, object fields and function types. It has no raw-text alternative.
Since 0.7.0 an object field is the record `TypeRef.Field` (`name`, `readonly`, `optional`
with default `false`, `type`), rendered `readonly a?: T` when optional, in place of the
triple `(name, readonly, type)`.
`Parameter` retains its optional annotation; arrows retain result annotations;
initialized and definite locals retain declared types. Imports retain imported and
local names and both type-only markers; declarations retain export presence.
`Import.types` is now a compatibility builder over the named-import carrier.

`TypeRef.beq_iff` relates its executable comparison to structural equality.
`Codegen.Types` converts existing core types and supported legacy spellings without
calling the text renderer. The explicit partial domain and changed declaration
adequacy premise are owned by `Test/contracts/faces.contract.md` §2. Equal rendered
bytes need not identify arbitrary target trees, and structurally well-formed types
need not resolve or typecheck under TypeScript. Neither stronger claim is made.

## Deliberate open boundary

`Decl.raw` is retained for source compatibility with Foldlab's generated local
helpers. It is not part of the future checked lowering image. No theorem or
coverage claim may describe every `Decl` as typed Effect4 output until the
lowering packet either excludes this arm by construction or admits a checked
replacement. This is registered as `E4-TARGET-CE-003`.
