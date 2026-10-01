// Vendored from foldlab experiments/parser-census/src/decls-ck.ts at 4005d34f.
/**
 * The ck leg's declaration enumerator — syntax only, over the tree the ck recognizer
 * (`../ck.ts`) already produced; it never re-parses.
 *
 * Until decisions row 168 (seat J2, 2026-10-01) that tree was `typescript@5.9.2`'s
 * `createSourceFile`, the same trust unit as the admitted Stage-1 extractor instrument
 * (`foldlab@4005d34f:docs/lab-core/TOOLS.md`): no program, no checker. tsgo 7 is the one
 * TypeScript compiler and its API serves source files to node only, so the ck recognizer now
 * reads the ingest's one parse (`parseTypeScript` in `../oxc.ts`, oxc-parser 0.147.0), and so
 * does this leg. It still reads the definition in `census-contract.ts` the way the TypeScript AST
 * held a declaration: `export`/`export default` are modifiers of the declaration (here the
 * wrapper around it), `declare` makes it ambient, a function with no body is a signature,
 * `in`/`out` mark variance, a dotted namespace is named by its first segment.
 *
 * It shares nothing with `decls-oxc.mjs` but the vocabulary and, since row 168, the parse: the
 * two enumerators are two implementations over one tree, so they no longer test the
 * modifier-versus-wrapper asymmetry the twin was built on (receipt J2 records the loss). Its
 * `hasVariance` (D1) remains a cross-check of the variance table that
 * `tools/Tools/Variances.lean` reads off rc.112's declarations.
 */
import type { Class, Directive, ExportDefaultDeclarationKind, Function as FunctionNode, Program, Statement, TSInterfaceDeclaration, TSTypeName, TSTypeParameterDeclaration } from "oxc-parser";
import { ANONYMOUS_DEFAULT, DESTRUCTURED, type Decl } from "./census-contract.ts";

/** D1 — an `in`/`out` type-parameter modifier anywhere on the declaration. */
function hasVariance(typeParameters: TSTypeParameterDeclaration | null | undefined): boolean {
  if (!typeParameters) return false;
  return typeParameters.params.some((tp) => tp.in || tp.out);
}

/** The name of a module/namespace block. `declare global` has no name node at all, so it is
 * spelled explicitly rather than allowed to fall through to an empty string that the other leg
 * would have to guess. `namespace A.B {}` is the declaration of `A` (TypeScript nests `B`
 * inside it). */
function moduleName(d: Extract<Statement, { type: "TSModuleDeclaration" }>): string {
  if (d.global) return "global";
  let id: typeof d.id | TSTypeName = d.id;
  while (id.type === "TSQualifiedName") id = id.left;
  if (id.type === "Identifier") return id.name;
  if (id.type === "Literal") return id.value;
  return "";
}

const isDefaultDeclaration = (d: ExportDefaultDeclarationKind): d is FunctionNode | Class | TSInterfaceDeclaration =>
  d.type === "FunctionDeclaration" || d.type === "TSDeclareFunction" || d.type === "ClassDeclaration" || d.type === "TSInterfaceDeclaration";

/** Every top-level declaration of a source file, in source order. */
export function ckDecls(program: Program): Decl[] {
  const out: Decl[] = [];
  for (const top of program.body) {
    // `export` and `export default` are modifiers in the TypeScript AST: the declaration under
    // them is the statement, and it is exported.
    let st: Directive | Statement = top;
    let exported = false;
    if (top.type === "ExportNamedDeclaration" && top.declaration) { st = top.declaration; exported = true; }
    else if (top.type === "ExportDefaultDeclaration" && isDefaultDeclaration(top.declaration)) { st = top.declaration; exported = true; }
    const ambient = "declare" in st && st.declare === true;

    if (st.type === "VariableDeclaration") {
      for (const d of st.declarations)
        out.push({
          kind: "variable",
          name: d.id.type === "Identifier" ? d.id.name : DESTRUCTURED,
          exported, ambient, variance: false,
        });
      continue;
    }
    if (st.type === "FunctionDeclaration" || st.type === "TSDeclareFunction") {
      out.push({
        kind: "function",
        name: st.id ? st.id.name : ANONYMOUS_DEFAULT,
        exported,
        // A function with no body is a signature, not an implementation —
        // whether or not the file bothered to write `declare`. That is the
        // same language fact the oxc leg reads off `TSDeclareFunction`, and
        // reading it off the body here is what lets the two agree without
        // either of them copying the other. (Found by the twin: every
        // `export function f(): void;` in a `.d.ts` was a disagreement while
        // this leg looked only at the modifier.)
        ambient: ambient || st.body === null,
        variance: hasVariance(st.typeParameters),
      });
      continue;
    }
    if (st.type === "ClassDeclaration") {
      out.push({
        kind: "class",
        name: st.id ? st.id.name : ANONYMOUS_DEFAULT,
        exported, ambient, variance: hasVariance(st.typeParameters),
      });
      continue;
    }
    if (st.type === "TSInterfaceDeclaration") {
      out.push({ kind: "interface", name: st.id.name, exported, ambient, variance: hasVariance(st.typeParameters) });
      continue;
    }
    if (st.type === "TSTypeAliasDeclaration") {
      out.push({ kind: "typeAlias", name: st.id.name, exported, ambient, variance: hasVariance(st.typeParameters) });
      continue;
    }
    if (st.type === "TSEnumDeclaration") {
      out.push({ kind: "enum", name: st.id.name, exported, ambient, variance: false });
      continue;
    }
    if (st.type === "TSModuleDeclaration") {
      out.push({ kind: "module", name: moduleName(st), exported, ambient, variance: false });
      continue;
    }
    // `export default <expression>` declares nothing; a class or function
    // after `export default` is a declaration and was handled above. Bare
    // `export { … }` / `export * from` re-export names declared elsewhere.
    // `import x = require(…)` binds an import. All are non-declarations, and
    // the oxc leg drops them the same way.
  }
  return out;
}
