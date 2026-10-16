// The TypeScript face of recursive declarations, checked by tsgo 7 (decisions row 400's probe).
// The three aliases are Recursive.lean's printed output, verbatim. Run from this folder:
//   node_modules/.bin/tsgo --noEmit --strict --target es2022 --moduleResolution bundler --module esnext faces.ts
type Int = number
type Num = number

export type Tree = { readonly _tag: "leaf" } | { readonly _tag: "node"; readonly children: ReadonlyArray<Tree>; readonly label: string }
export type IntList = { readonly _tag: "nil" } | { readonly _tag: "cons"; readonly head: Int; readonly tail: IntList }
export type Json = string | boolean | ReadonlyArray<Json> | Readonly<Record<string, Json>> | null | Num

// the probe's samples
export const tree3: Tree = { _tag: "node", label: "root", children: [{ _tag: "leaf" },
  { _tag: "node", label: "mid", children: [{ _tag: "leaf" }] }, { _tag: "leaf" }] }
export const list: IntList = { _tag: "cons", head: 1, tail: { _tag: "cons", head: -2, tail: { _tag: "nil" } } }
export const json: Json = [null, true, 3, "x", [{}, { k: "v" }]]

// red controls: each must be refused
// @ts-expect-error a child that is a string
export const treeBad: Tree = { _tag: "node", label: "root", children: [{ _tag: "leaf" }, { _tag: "node", label: "mid", children: ["oops"] }] }
// @ts-expect-error a list that ends in a string
export const listBad: IntList = { _tag: "cons", head: 1, tail: "end" }
