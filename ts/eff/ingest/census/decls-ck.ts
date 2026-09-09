// Vendored from foldlab experiments/parser-census/src/decls-ck.ts at 4005d34f.
/**
 * The ck leg's declaration enumerator — `typescript@5.9.2`, syntax only.
 *
 * The same pin, and the same trust unit, as the admitted Stage-1 extractor
 * instrument (`foldlab@4005d34f:docs/lab-core/TOOLS.md`): `createSourceFile` with no program
 * and no checker, so nothing here trusts type resolution. It reads the
 * definition in `census-contract.ts` off that one tree.
 *
 * DELIBERATELY shares nothing with `decls-oxc.mjs` but the vocabulary. Two
 * enumerators that shared code would agree by construction and the twin
 * would testify to nothing.
 */
import ts from "typescript";
import { ANONYMOUS_DEFAULT, DESTRUCTURED, type Decl } from "./census-contract.ts";

const hasModifier = (node: ts.Node, kind: ts.SyntaxKind): boolean =>
  ts.canHaveModifiers(node) &&
  (ts.getModifiers(node) ?? []).some((m) => m.kind === kind);

/** D1 — an `in`/`out` type-parameter modifier anywhere on the declaration. */
function hasVariance(node: ts.Node): boolean {
  const tps = (node as { typeParameters?: ts.NodeArray<ts.TypeParameterDeclaration> }).typeParameters;
  if (!tps) return false;
  return tps.some((tp) =>
    (tp.modifiers ?? []).some((m) =>
      m.kind === ts.SyntaxKind.InKeyword || m.kind === ts.SyntaxKind.OutKeyword));
}

/** The name of a module/namespace block. `declare global` has no name node
 * at all, so it is spelled explicitly rather than allowed to fall through to
 * an empty string that the other leg would have to guess. */
function moduleName(d: ts.ModuleDeclaration): string {
  if (d.flags & ts.NodeFlags.GlobalAugmentation) return "global";
  return ts.isStringLiteral(d.name) ? d.name.text : d.name.text;
}

/** Every top-level declaration of a source file, in source order. */
export function ckDecls(sf: ts.SourceFile): Decl[] {
  const out: Decl[] = [];
  for (const st of sf.statements) {
    const exported = hasModifier(st, ts.SyntaxKind.ExportKeyword) ||
      hasModifier(st, ts.SyntaxKind.DefaultKeyword);
    const ambient = hasModifier(st, ts.SyntaxKind.DeclareKeyword);

    if (ts.isVariableStatement(st)) {
      for (const d of st.declarationList.declarations)
        out.push({
          kind: "variable",
          name: ts.isIdentifier(d.name) ? d.name.text : DESTRUCTURED,
          exported, ambient, variance: false,
        });
      continue;
    }
    if (ts.isFunctionDeclaration(st)) {
      out.push({
        kind: "function",
        name: st.name ? st.name.text : ANONYMOUS_DEFAULT,
        exported,
        // A function with no body is a signature, not an implementation —
        // whether or not the file bothered to write `declare`. That is the
        // same language fact the oxc leg reads off `TSDeclareFunction`, and
        // reading it off `st.body` here is what lets the two agree without
        // either of them copying the other. (Found by the twin: every
        // `export function f(): void;` in a `.d.ts` was a disagreement while
        // this leg looked only at the modifier.)
        ambient: ambient || st.body === undefined,
        variance: hasVariance(st),
      });
      continue;
    }
    if (ts.isClassDeclaration(st)) {
      out.push({
        kind: "class",
        name: st.name ? st.name.text : ANONYMOUS_DEFAULT,
        exported, ambient, variance: hasVariance(st),
      });
      continue;
    }
    if (ts.isInterfaceDeclaration(st)) {
      out.push({ kind: "interface", name: st.name.text, exported, ambient, variance: hasVariance(st) });
      continue;
    }
    if (ts.isTypeAliasDeclaration(st)) {
      out.push({ kind: "typeAlias", name: st.name.text, exported, ambient, variance: hasVariance(st) });
      continue;
    }
    if (ts.isEnumDeclaration(st)) {
      out.push({ kind: "enum", name: st.name.text, exported, ambient, variance: false });
      continue;
    }
    if (ts.isModuleDeclaration(st)) {
      out.push({ kind: "module", name: moduleName(st), exported, ambient, variance: false });
      continue;
    }
    // `export default <expression>` declares nothing; a class or function
    // after `export default` is a ClassDeclaration/FunctionDeclaration and
    // was handled above. Bare `export { … }` / `export * from` re-export
    // names declared elsewhere. `import x = require(…)` binds an import.
    // All are non-declarations, and the oxc leg drops them the same way.
  }
  return out;
}
