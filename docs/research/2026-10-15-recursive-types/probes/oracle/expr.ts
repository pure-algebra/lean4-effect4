// Recursive.lean's printed `Expr` and `Stmt`, verbatim: the `lit` record printed as a payload
// class name (decisions row 120's class rule), which no declaration declares.
export type Expr = lit | { readonly _tag: "block"; readonly body: ReadonlyArray<Stmt> }
export type Stmt = { readonly _tag: "let"; readonly name: string; readonly value: Expr } | { readonly _tag: "eval"; readonly expr: Expr }
