// Retargeted from foldlab experiments/parser-census/src/legs.ts at 4005d34f.
// Both enumerators inspect each engine's existing parse; this module never reparses. Since
// decisions row 168 both engines read the ingest's one parse (`parseTypeScript`, `../oxc.ts`).
import type { Program } from "oxc-parser"
import { ckDecls } from "./decls-ck.ts"
import { oxcDecls } from "./decls-oxc.mjs"
import { decodeDecls } from "./census-contract.ts"
export const compilerDeclarations = (tree: Program) => ckDecls(tree)
export const oxcDeclarations = (tree: unknown) => decodeDecls(oxcDecls(tree))
