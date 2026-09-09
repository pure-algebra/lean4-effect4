// Vendored from foldlab experiments/parser-census/src/decls-oxc.mjs at 4005d34f.
// The oxc leg's declaration enumerator — an ESTree walk, INDEPENDENT of the
// ck leg. Deliberately untyped `.mjs` for the same reason
// `../../lift-harness/src/oxc-engine.mjs` is: this leg must not acquire a
// shape from the ck leg's contract, because then the twin would be testing
// one implementation twice.
//
// It shares exactly one thing with `decls-ck.ts`: the DEFINITION in
// `census-contract.ts`, which it re-implements against a different tree.
//
// THE TREES ARE NOT THE SAME SHAPE, and that asymmetry is the whole point of
// running both. TypeScript keeps `export` as a MODIFIER on the declaration;
// ESTree makes it a WRAPPER node (`ExportNamedDeclaration`,
// `ExportDefaultDeclaration`) around one. So this file unwraps where the ck
// leg reads a modifier, and the two arrive at the same row — or they do not,
// and the disagreement is a finding rather than a silent difference in what
// "exported" meant on each side.

const ANONYMOUS_DEFAULT = 'default';
const DESTRUCTURED = '«destructured»';

/** D1 — an `in`/`out` type-parameter modifier. oxc spells variance as two
 * booleans on the type parameter; TypeScript spells it as modifier tokens.
 * Same fact, different spelling, read independently on each side. */
function hasVariance(node) {
  const tps = node && node.typeParameters;
  const params = tps && (tps.params || tps.parameters);
  if (!Array.isArray(params)) return false;
  return params.some((p) => p.in === true || p.out === true);
}

/** A module/namespace block's name. `declare global` carries no meaningful
 * id, so it is spelled explicitly — the ck leg does the same. */
function moduleName(node) {
  if (node.global === true) return 'global';
  const id = node.id;
  if (!id) return '';
  if (id.type === 'Identifier') return id.name;
  if (typeof id.value === 'string') return id.value;      // Literal module name
  return '';
}

const ambientOf = (node) => node.declare === true;

/** Push the rows one declaration node contributes. `exported` is decided by
 * the CALLER (the wrapper it was unwrapped from), never by this function —
 * that is the asymmetry with the ck leg made explicit. */
function pushDecl(out, node, exported) {
  const ambient = ambientOf(node);
  switch (node.type) {
    case 'VariableDeclaration':
      for (const d of node.declarations)
        out.push({
          kind: 'variable',
          name: d.id && d.id.type === 'Identifier' ? d.id.name : DESTRUCTURED,
          exported, ambient, variance: false,
        });
      return;
    // `TSDeclareFunction` is an ambient function declaration — the same
    // language construct TypeScript hands back as a body-less
    // FunctionDeclaration with a `declare` modifier.
    case 'FunctionDeclaration':
    case 'TSDeclareFunction':
      out.push({
        kind: 'function',
        name: node.id ? node.id.name : ANONYMOUS_DEFAULT,
        exported,
        ambient: ambient || node.type === 'TSDeclareFunction',
        variance: hasVariance(node),
      });
      return;
    case 'ClassDeclaration':
      out.push({
        kind: 'class',
        name: node.id ? node.id.name : ANONYMOUS_DEFAULT,
        exported, ambient, variance: hasVariance(node),
      });
      return;
    case 'TSInterfaceDeclaration':
      out.push({ kind: 'interface', name: node.id.name, exported, ambient, variance: hasVariance(node) });
      return;
    case 'TSTypeAliasDeclaration':
      out.push({ kind: 'typeAlias', name: node.id.name, exported, ambient, variance: hasVariance(node) });
      return;
    case 'TSEnumDeclaration':
      out.push({ kind: 'enum', name: node.id.name, exported, ambient, variance: false });
      return;
    case 'TSModuleDeclaration':
      out.push({ kind: 'module', name: moduleName(node), exported, ambient, variance: false });
      return;
    default:
      // Not a declaration under the census definition. Notably
      // `TSImportEqualsDeclaration` and every expression statement.
      return;
  }
}

/** Every top-level declaration of an ESTree Program, in source order. */
export function oxcDecls(program) {
  const out = [];
  for (const st of program.body) {
    if (st.type === 'ExportNamedDeclaration') {
      // `export { a, b }` re-exports names declared elsewhere: no declaration.
      if (st.declaration) pushDecl(out, st.declaration, true);
      continue;
    }
    if (st.type === 'ExportDefaultDeclaration') {
      // `export default <expression>` declares nothing; a class or function
      // after it does.
      if (st.declaration) pushDecl(out, st.declaration, true);
      continue;
    }
    if (st.type === 'ExportAllDeclaration' || st.type === 'ImportDeclaration') continue;
    pushDecl(out, st, false);
  }
  return out;
}
