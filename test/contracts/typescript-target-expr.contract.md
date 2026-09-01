# Retained TypeScript target fragment contract

Status: implemented port, 2026-08-31

Implementation: `Effect4/Target/TypeScript/Expr.lean` and
`Effect4/Target/TypeScript/Render.lean`

Lean battery: `Effect4Test/Target/TypeScript/ExprContract.lean`

Counterexamples: `E4-TARGET-CE-001` through `E4-TARGET-CE-003`

Proof graph: `docs/TYPESCRIPT-TARGET-DAG.md`

## Source and boundary

The source is Foldlab `library/cas/Cas/Backend/Ts.lean`, lines 1-252, at the
repository pin recorded in `PORT-MANIFEST.md`. Its SHA-256 is
`cdae7c93f5f62a2800bfee9497f4ec33c369e7be8ad71b2c1879b966741ecc15`.

Effect4 retains the syntax constructors and fixed-layout rendering behavior,
but not Foldlab's namespace or CAS-specific ownership claims. Syntax lives in
`Effect4.Target.TypeScript.Expr`; rendering lives in
`Effect4.Target.TypeScript.Render`. Foldlab consumers remain downstream until
the later compatibility phase.

This is target-only data. It is not Effect4 program syntax, a denotation, a
typing derivation, or evidence that rendered bytes pass TypeScript, Effect v4,
or the language service. Those are later `Type`, `Lower`, `Decode`,
`Simulation`, and host-harness obligations.

## Existing-type dispositions

| Public type | Role | Duplicate-prevention relation | Assurance route |
| --- | --- | --- | --- |
| `Effect4.Target.TypeScript.Expr` | canonical retained expression syntax | target-only; not `Effect4.Program`, `Effect4.Flow`, or `Lean.Expr` | `TS-PG-RETAINED-RENDER` |
| `Effect4.Target.TypeScript.Stmt` | retained straight-line generator statement syntax | child syntax of `Expr`; no second effect program | same graph, construction edge |
| `Effect4.Target.TypeScript.ConstDecl` | passive declaration record | contains the canonical target `Expr` | same graph, construction edge |
| `Effect4.Target.TypeScript.ProgDecl` | retained generator declaration record | contains `Stmt`; not an Effect4 semantic program | same graph, construction edge |
| `Effect4.Target.TypeScript.Decl` | retained module-declaration sum | owns the compatibility-only `raw` arm | same graph, construction and counterexample edges |
| `Effect4.Target.TypeScript.Import` | passive import alphabet | one target-only owner | same graph, construction edge |
| `Effect4.Target.TypeScript.Module` | passive module record | contains the declaration and import owners above | same graph, construction edge |
| `Effect4.Target.TypeScript.Style` | passive rendering-value record | one renderer style; no semantic or typing role | `TS-LEAF-STYLE`, attached to the graph's representation edge |

`Style` is a trivial passive record and does not receive its own proof graph.

## Frozen port surface

The retained expression constructors are `ident`, `str`, `int`, `bool`,
`jsNull`, `call`, `object`, `objectML`, `arr`, and `arrow`, in that order.
Statements are `constYield` and `ret`; declarations are `const`, `prog`, and
`raw`; imports are `all`, `named`, and `types`.

The printer retains these equations:

- string escaping belongs to the printer and covers the selected quote,
  backslash, newline, carriage return, and tab;
- ordinary objects and arrays render inline exactly when all rendered children
  are newline-free;
- `objectML` always renders one field per line when nonempty;
- arrows render their body at the current depth;
- module headers render blank paragraph lines without trailing whitespace;
- imports are contiguous and declarations have one blank line between them;
- output depends only on the syntax tree and explicit `Style`, never on a
  width budget or host formatter.

## Deliberate open boundary

`Decl.raw` is retained for source compatibility with Foldlab's generated local
helpers. It is not part of the future checked lowering image. No theorem or
coverage claim may describe every `Decl` as typed Effect4 output until the
lowering packet either excludes this arm by construction or admits a checked
replacement. This is registered as `E4-TARGET-CE-003`.
