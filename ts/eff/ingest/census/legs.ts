// Retargeted from foldlab experiments/parser-census/src/legs.ts at 4005d34f.
// Both enumerators inspect each engine's existing parse; this module never reparses.
import { ckDecls } from "./decls-ck.ts"
import { oxcDecls } from "./decls-oxc.mjs"
import { decodeDecls } from "./census-contract.ts"
import type ts from "typescript"
export const compilerDeclarations = (tree: ts.SourceFile) => ckDecls(tree)
export const oxcDeclarations = (tree: unknown) => decodeDecls(oxcDecls(tree))
