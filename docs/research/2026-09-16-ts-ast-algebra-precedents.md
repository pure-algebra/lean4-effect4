# TS AST algebra: precedents, compiler internals, and a design for printer, reader and positions

Research seat, 2026-09-16, at `353b7960` on `refactor/phase1-phase3`. Read-only: nothing in the
repository was changed except this file. No `lake` and no `make` were run.

Evidence words are used exactly. **Tested** means I ran it on this Mac and the output is quoted
or summarised below. **Reproduced** means I ran two independent tools and compared. **Read**
means I read the source and cite it as `path:line`. **Recalled** means it comes from my own
knowledge of the literature and I could not verify it from a fetched source in this session;
every recalled claim is marked. Nothing here is proved in the Lean sense.

Where the brief's questions are answered: Q1 in §2, Q2 in §3, Q3 in §5 and §5b, Q4 in §6,
Q5 in §7, Q6 in §8, Q7 in §12 and §13, Q8 in §4 and §4b, Q9 in §9, Q10 in §10. §1 is what the
repository does today, §11 is the corpus measurement, §14 is where I disagree with the
derivation I was given.

---

## 0. The thirteen findings that change the design

1. **`tsgo` ships a JavaScript API with an AST, a checker and diagnostics carrying offsets.**
   `@typescript/native-preview` exports `./unstable/sync`, `./unstable/ast`,
   `./unstable/ast/factory`, `./unstable/ast/visitor`, `./unstable/ast/scanner`. A `Diagnostic`
   carries `pos`, `end`, `code`, `text`, `messageChain`, `relatedInformation`. A `Checker`
   answers `getTypeAtPosition`, `getTypeAtLocation`, `getResolvedSignature`,
   `isTypeAssignableTo`. Tested. This is the "deterministic integration with TypeScript"
   the owner asked for, and it is native.
2. **`tsgo` has no printer in its JS API.** There is `factory.create*` and a scanner, but no
   `createPrinter` / `printNode` / `EmitHint` anywhere in `dist`. Tested (grep over the whole
   package). `typescript` 5.9.2 does have `createPrinter`. So "render with TypeScript's own
   printer" and "check with the native compiler" are two different hosts, not one.
3. **`tsgo` 7.0.0-dev and `tsc` 5.9.2 agree character for character** on every probe and every
   compiler-option set I tried, including the message text, the line and the column.
   Reproduced.
4. **Diagnostic offsets are UTF-16 code-unit indices into `sourceFile.text`, not UTF-8 bytes.**
   Tested with a file containing `é` and an emoji. Lean's `String.Pos` is a byte offset, so a
   Lean-side position table and a TypeScript-side span are in different units unless the
   printed image is ASCII.
5. **The Lean checker and `tsgo` agree on 383 of the 408 corpus programs, with zero
   disagreements in the dangerous direction.** Not one program that Lean types is refused by
   TypeScript. All 25 disagreements are Lean refusing what TypeScript accepts, and the dominant
   class is the error alphabet (`Effect.fail(true)`, `Effect.fail(undefined)`,
   `Effect.fail(pair(19, 18))`). Tested; the method is in §11.
6. **The printed corpus type-checks in 0.2 seconds** as one native run of 408 modules.
   Tested. There is no reason to build a batching or caching layer for the diagnostics harness.
7. **`print` is not one template per constructor.** Three constructors print through a guard on
   a non-recursive argument (`catchIf` on `test = true`, `provideLayer` on `isLocal`, rows on
   `shape`), one constructor is not injective (`yieldError` prints as `Effect.fail`), and
   `branch`, `whileLoop` and `suspend` all print under the head `Effect.suspend`. Read. The
   template table is indexed by constructor **and** a decidable classifier of the non-recursive
   arguments, and disjointness holds on the image of `print`, not on all of the target syntax.
8. **The house fragment is not isomorphic to a TypeScript parse.** `Expr.ident "Effect.succeed"`
   is one node in the house fragment and a three-node `PropertyAccessExpression` in TypeScript;
   `call (generic (ident f) ts) args` is two house nodes and one `CallExpression` with
   `typeArguments` in TypeScript. Read and tested.
9. **`forEachChild` flattens named fields, type arguments and punctuation tokens into one
   child stream.** `Deferred.make<number, number>()` has children `[callee, number, number]`
   and `Deferred.make()` has `[callee]`. Tested. A path built from `forEachChild` ordinals is
   not stable under an optional field. Paths must be by named field.
10. **`tree-sitter-typescript` is stale.** Latest tag and npm version `0.23.2`, published
    2024-11-11, while `tree-sitter` core is at 0.25 (node) and 0.27 (web). Tested via `npm view`
    and a fetch of the releases page. It is pinnable, but it is not a living pin the way
    `vendor/effect-4.0.0-rc.112` is.
11. **The owner's Lean tree-sitter binding already vendors TypeScript, and its "typed grammar
    schemas" are not what the name suggests.** `treeSitterTypescript`, `parser.c` and
    `scanner.c` are already in the lakefile at `tree-sitter-typescript` rev `75b3874`
    (`ffi/language_definitions.json`). But `TreeSitter/Grammars/TypeScript.lean` is a
    **hand-written enumeration of fourteen declaration-bearing node types**, not a model of the
    324 node types in `node-types.json`, and `GrammarSpec` is a code-outliner interface
    (`toDeclarationType`, `declarationNodes`, `nameNodes`, a tree-sitter `queryString`). Read.
12. **That binding's `SourceRange` throws away the byte offsets the FFI already has.** The FFI
    exposes `TSNode.startByte` / `endByte` *and* `startRow` / `startColumn` / `endRow` /
    `endColumn` and `childByFieldName`, but `TreeSitter.SourceRange` is line and column only
    (`TreeSitter/Types/CodeLocation.lean`), so `Extract` and `SourceMap` are built on a weaker
    position type than the parser offers. Read.
13. **Three offset units are in play and they are all different, but on our image they
    coincide.** `tsc`/`tsgo` report UTF-16 code units, `oxc` and tree-sitter report UTF-8 bytes,
    Lean `String.Pos` is UTF-8 bytes, and a terminal column is none of those. Tested for the
    first two; the third is by definition. But all 408 printed corpus programs are pure ASCII
    (tested), and the only non-ASCII byte in an emitted module is an em-dash in the header
    comment `harness/truth/run-truth.ts:168` writes. Fix that one character and the units agree
    exactly, and the measure monoid can carry the distinction without anyone having to use it.

---

## 1. What the repository does today

### 1.1 `print` is a natural transformation, with three caveats the derivation misses

`print` (`src/Effect4/Codegen/Print.lean:317`) is one clause per constructor. Each clause builds
a `TypeScript.Expr` from (a) the non-recursive arguments through `printTerm` / `printCause` /
`printKey` / `printLit`, and (b) the already-printed children. That is exactly
`sigma : F X -> G*(X)` followed by substitution, and the derivation's reading of it is right in
outline. Three things it gets wrong in detail.

**(a) The carrier is exponential, not `G*`.** `print` threads `n : Nat`, the environment
length, and the recursive calls are at `n`, `n + 1` or `n + 2` depending on how many binders
the shape introduces (`Print.lean:329` for `bind`, `:377` for `acquireRelease` at `n + 2`). So
the fold's carrier is `Nat -> Except PrintRefusal Expr`, an inherited attribute. This is the
same exponential carrier the universal-algebra refactor already found for `scopedAt`, and it is
why `cata_ctx` was rejected from `docs/UNIVERSAL-ALGEBRA-REFACTOR.md` (`docs/STATE.md`, "the
universal-algebra refactor"). The binder count per (constructor, child) already exists as data:
`tools/Effect4Gen/binders.json` feeding `Node.binders` and `childLevel`
(`src/Effect4/Program/Binders.lean`). A template table would restate the same numbers, so it
must be generated from `binders.json` or checked against it, not written twice.

**(b) One constructor, several templates.** `catchIf test body handler` prints as
`Effect.catch(b, (aN) => h)` when `test = .lit (.bool true)` and as
`Effect.catchIf(b, (aN) => test, (aN) => h, undefined)` otherwise (`Print.lean:342-350`).
`provideLayer` prints with two or three arguments on `isLocal` (`Print.lean:406-410`).
`perform` and `callback` print through `printRow` (`Print.lean:271`), which branches on
`RowShape` (`.value`, `.call`, `.tupleCall`, `.method`) and on whether `row.request = Ty.unit`.
So the table is indexed by a pair: the constructor, and a decidable classifier of its
non-recursive arguments. That is still finite data; it is not "one template per constructor".

**(c) `print` is not injective and the templates are not pairwise non-unifiable.**
`yieldError e` and `fail e` both print `Effect.fail(e)` (`Print.lean:323`, comment at `:320`),
and `readable` excludes `yieldError` for exactly that reason (`Read.lean:781`). Separately,
`suspend body`, `branch test a b` and `whileLoop i t s b` all print under the head
`Effect.suspend`: `Effect.suspend(() => B)`, `Effect.suspend(() => t ? a : b)` and
`Effect.suspend(() => { let aN = i; return Effect.whileLoop({ ... }) })` (`Print.lean:333`,
`:353`, `:356-366`). These three templates unify syntactically. They are told apart only because
no printed `Eff` body is ever a bare `.cond` or a bare `.arrowBlock`, which is a property of the
**image** of `print`, not of the templates. The correct condition is therefore

> the templates are pairwise disjoint *after restriction to the image*, i.e. the image of
> `print` is an unambiguous grammar,

which is precisely Danielsson's hypothesis (see §2) and precisely what `readable` plus
`read_exact` establish today by hand. Any generic layer-inverse machinery has to carry the same
side condition, so the work does not vanish; it moves from 3500 lines of clause-by-clause proof
into one decidable check on a table plus one lemma that the image is in the grammar.

### 1.2 The reader and the two theorems

`readEff` is the hand-written inverse (`src/Effect4/Codegen/Read.lean`, 3531 lines). Two
theorems bound it:

- `read_print` (`Read.lean:1750`): `LawfulSpelling sig spell -> readable sig spell n e = true ->
  print sig n e = .ok x -> readEff sig spell n x = .ok e`.
- `read_exact` (`Read.lean:2908`): `readEff sig spell n x = .ok e -> print sig n e = .ok x`.

`read_exact` has no `readable` premise, which is the stronger and more useful half: the reader's
image is exactly the set of trees the printer emits, so `print` and `readEff` are a section and
retraction pair between `{e | readable e}` and `{x | readEff x succeeds}`. That is a *partial
isomorphism* in the Rendel and Ostermann sense, stated on the nose. `readable`
(`Read.lean:779`) is the domain restriction: variables in scope, the row's kind matched, no
`yieldError`, no internal fiber action, no non-daemon `forkScoped`. `LawfulSpelling`
(`Read.lean:894`) is the injectivity of the row table on `(spelling, trailing)`.

### 1.3 The house renderer

`TypeScript.Render.expr` (`.lake/packages/typescript/TypeScript/Render.lean:122`) has **no
parenthesisation anywhere**. `.call fn args` renders `expr fn ++ "(" ++ ... ++ ")"`, `.cond`
renders `t ++ " ? " ++ a ++ " : " ++ b`, `.member` renders `t ++ "." ++ name`. It is a correct
renderer only on the image of `print`, where heads are always `.ident` or `.generic` and `cond`
only occurs as an arrow body. Read.

Layout is decided by two things and no width: the constructor (`object` inline vs `objectML`
always multi-line) and `containsNewline` applied to the **already rendered** children
(`Render.lean:113`, used at `:130`, `:161`, `:186`). So the render fold's carrier needs a
`hasNewline` measure, which is the derivation's `multiline : M -> Bool`. That part of the
derivation is right, and it is cheap: `M = String x Bool` with `(s, b) <> (s', b') =
(s ++ s', b || b')` is a monoid and `hasNewline` is a monoid homomorphism out of it, so the
measure is exact, not an approximation.

The fragment also mixes syntax with layout (`object` vs `objectML`, `objectQuoted` vs
`objectQuotedML`) and carries Effect-specific statement shapes (`scopedGen`,
`scopedGenMasked`, `.lake/packages/typescript/TypeScript/Syntax.lean:106-113`) that the Effect4
printer never emits. That is real debt, and it is the reason the house fragment cannot simply
be declared to be "the TypeScript syntax signature".

### 1.4 The generator reads the Lean environment

`tools/Effect4Gen/Fold.lean:44` calls `getConstInfoInduct root` and walks `iv.all` and
`fv.ctors`, reading argument types with `forallBoundedTelescope` and `inferType`. The
constructor declarations are **Lean meta reflection of the environment, not a data table**.
Read. Consequence for the design: if `G` (the TypeScript syntax) is to be fed to the same
generator, `G` must be a Lean inductive in the environment. The owner has said `G` is not
generated by us. Those two facts together mean `G` must either be a hand-written Lean inductive
(as today), or an **imported table** with its own emitter, which is a second generator, not this
one. §12 recommends the second, and says what the emitter takes as input.

---

## 2. Q1. Invertible printing and parsing: the precedents and the theorem shape

**Rendel and Ostermann 2010, "Invertible syntax descriptions: unifying parsing and pretty
printing"** (Haskell Symposium 2010). One description, interpreted twice. The interface is
built from *partial isomorphisms* `Iso a b` with `apply : a -> Maybe b` and
`unapply : b -> Maybe a`, and the combinator classes are `IsoFunctor`, `ProductFunctor`,
`Alternative`. The correctness claim is informal in the paper: the two interpretations are
inverse *if* the isomorphisms supplied are genuine partial isomorphisms and the grammar is
unambiguous. Verified by search; the Haskell packages `invertible-syntax` and
`partial-isomorphisms` are the artifacts.

**Matsuda and Wang, FliPpr** (ESOP 2013; journal version New Generation Computing 36(3),
173-202, 2018, "FliPpr: a system for deriving parsers from pretty-printers"). You write only
the pretty-printer, in a linear, treeless functional language, and the system *inverts the
program* to produce a context-free grammar parser. The key restriction is linearity: every
argument is used exactly once, which is what makes the inversion a grammar rather than a search.
Verified by search. This is the closest precedent to "the template table is the single source of
truth and the reader is derived", and its linearity condition is exactly the derivation's
"each hole once".

**Danielsson 2013, "Correct-by-construction pretty-printing"** (DTP 2013, Workshop on
Dependently Typed Programming). This is the precedent whose theorem we should copy. Grammars are
monadic and potentially infinite; a pretty-printer for a value is indexed by that value; and the
theorem proved is: *if a value is pretty-printed and the resulting string is parsed with respect
to the same unambiguous grammar, the original value is obtained.* Verified by search. The
statement form is `x ∈ parse (pretty x)` with unambiguity as an explicit hypothesis, which maps
onto `read_print` plus `read_exact` exactly.

**Delaware et al. 2019, "Narcissus: correct-by-construction derivation of decoders and encoders
from binary formats"** (PLDI 2019). A *format* is a relation between values and bit strings; an
encoder and a decoder are each derived and each proved *against the relation*, not against each
other. Verified by search (it surfaced beside Danielsson). This is the right shape for §8's
question about what the statement of correctness should be across Lean and the host: one
relation, three implementations.

**Boomerang and lenses** (Foster, Greenwald, Moore, Pierce, Schmitt, "Combinators for
bidirectional tree transformations", POPL 2005; Bohannon, Foster, Pierce, Pilkiewicz, Schmitt,
"Boomerang: resourceful lenses for string data", POPL 2008). Recalled. Lenses are the wrong
tool here: a lens is for a *lossy* view that must be updated, with `put`/`get` round-trip laws
in both directions. Our printer is lossy only in a small, named set of places (`yieldError`,
unit requests, the `daemon` flag) and the estate's answer to that is to *shrink the domain*
(`readable`) rather than to carry a complement. Shrinking the domain is what a partial
isomorphism does and what a lens does not.

**Ott and Lem** (Sewell et al., "Ott: effective tool support for the working semanticist", ICFP
2007; Owens et al., Lem). Recalled. These generate the AST, the printer and the LaTeX from one
grammar description. They are a precedent for "the description is the artifact", not for a
round-trip theorem: Ott does not prove parse ∘ print = id.

**Holes under binders.** `Forms.Template.argument (slot cutOffset insertions)`
(`src/Effect4/Codegen/Forms.lean:31`) is a hole that says "this argument is inserted under
`insertions` extra binders, cut at `n + cutOffset`", and `Template.expand` implements the
insertion by iterating `Eff.weaken` (`Forms.lean:56-60`). This is a **first-order metavariable
with an explicit weakening**, which is the de Bruijn presentation of the second-order notion.
The standard names for the general notion:

- **Fiore, Plotkin, Turi 1999, "Abstract syntax and variable binding"** (LICS 1999), and
  **Fiore and Hur, "Second-order equational logic"** (CSL 2010): syntax with binding is an
  initial algebra in presheaves over the category of contexts, and a *metavariable of arity n*
  is a hole that may use `n` of the ambient variables. Recalled.
- **Hamana, "Free Σ-monoids: a higher-order syntax with metavariables"** (APLAS 2004): the
  precise object is the free Σ-monoid, whose multiplication is capture-avoiding substitution,
  and metavariables with binding arity are its generators. Recalled.
- **Hygienic macro systems** (Kohlbecker et al. 1986; Clinger and Rees 1991; Herman and Wand,
  "A theory of hygienic macros", ESOP 2008). Recalled. The "template with binders" notion in
  `syntax-rules` is the practical ancestor; Herman and Wand's contribution is a *binding
  specification* attached to each macro, which is literally `binders.json`.

So the honest statement is: our `Template.argument (slot cut ins)` is the first-order de Bruijn
shadow of a second-order metavariable of arity `ins`, with the cut recording where in the
context the new binders land. No precedent I found spells it the same way, because most work in
the area either uses named binders with a hygiene condition or uses presheaves; the estate's
choice of positional variables (decision D1) forces the explicit `weaken`. That is fine and it
is already proved sound for the nineteen forms by the per-form guard
(`Forms.lean:196`, `all.all (fun f => [0,1,2,5].all f.checkExample)`).

**The name for "a finite set of linear templates whose images are disjoint".** There is no
single accepted term. The three that name the parts:

- **Linear** (FliPpr's condition; each hole used exactly once).
- **Non-erasing / non-collapsing** (no template is a bare hole). In term rewriting this is the
  condition that the left-hand side is not a variable.
- **Unambiguous** (the union of the template images is a disjoint union). In parsing terms,
  the grammar is *LL(1) after left factoring* if in addition the first token decides the
  template. Our table is stronger than LL(1) in the easy direction (the head identifier decides
  the constructor for 24 of 27) and weaker in one place (the three `Effect.suspend` templates
  need one more token of lookahead into the arrow body).

Term-rewriting people would call a table with these three properties a **constructor system
with pairwise non-overlapping, linear, non-collapsing left-hand sides**, and the inverse is then
a deterministic matching automaton. That is the phrase I would put in the design note.

---

## 3. Q2. TypeScript compiler internals. All of this section was tested

### 3.1 The `tsgo` JavaScript API

`/opt/homebrew/lib/node_modules/@typescript/native-preview/package.json` exports:

```
"./unstable/sync": "./dist/api/sync/api.js"       "./unstable/ast": "./dist/ast/index.js"
"./unstable/async": "./dist/api/async/api.js"     "./unstable/ast/is": "./dist/ast/is.js"
"./unstable/fs": "./dist/api/fs.js"               "./unstable/ast/factory": …factory.generated.js
"./unstable/proto": "./dist/api/proto.js"         "./unstable/ast/utils", "…/scanner",
                                                  "…/visitor", "…/clone"
```

The shape that matters:

```
new API({ cwd })
  .updateSnapshot({ openProjects: ["/abs/tsconfig.json"] })   // or { fileChanges: { changed: [...] } }
  .getProjects()[0].program
     .getSemanticDiagnostics(file?)  -> readonly Diagnostic[]
     .getSyntacticDiagnostics / getBindDiagnostics / getSuggestionDiagnostics / …
     .getSourceFile(fileName)        -> SourceFile
  .getProjects()[0].checker
     .getTypeAtPosition(file, pos) / getTypeAtLocation(node) / getResolvedSignature(node)
     .isTypeAssignableTo(source, target) / typeToTypeNode(...)
```

`Diagnostic` is
`{ fileName?, pos, end, code, category, text, reportsUnnecessary?, reportsDeprecated?,
messageChain?, relatedInformation? }`
(`/opt/homebrew/lib/node_modules/@typescript/native-preview/dist/api/sync/types.d.ts:276`).
Note `text` is already the localised string, so there is no `flattenDiagnosticMessageText` step;
chains arrive as nested `Diagnostic`s.

Tested output on my probe project:

```
{"file":"p2345.ts","pos":234,"end":236,"code":2345,"text":"Argument of type 'string' is not assignable to parameter of type 'number'."}
{"file":"p2554.ts","pos":196,"end":199,"code":2554,"text":"Expected 2 arguments, but got 1."}
{"file":"p2304.ts","pos":240,"end":242,"code":2304,"text":"Cannot find name 'a3'."}
```

The AST is the familiar `Node` shape:
`{ kind: SyntaxKind, flags, parent, forEachChild, getSourceFile, getStart, getFullStart, getEnd,
getWidth, getFullWidth, getLeadingTriviaWidth, getFullText, getText }`
(`dist/ast/ast.d.ts`). `SourceFile` carries `statements`, `text`, `fileName`, `path`.
`dist/ast/astnav.d.ts` adds `getTokenAtPosition`, `getTouchingToken`, `findPrecedingToken`,
which is the containment lookup the diagnostics harness needs, ready-made.

`dist/ast/utils.d.ts` exports `formatSyntaxKind(kind) -> string`, so the kind table can be
dumped rather than transcribed.

There is **no printer**. Tested by grepping `printer`, `Printer`, `createPrinter`, `printNode`,
`EmitHint` over the whole `dist` tree: no match outside source maps. `factory.createSourceFile`
takes already-parsed statements, so there is also no standalone text-to-AST entry point in the
JS API; parsing happens on the Go server and comes over the wire, cached by content hash
(`dist/api/sourceFileCache.d.ts`).

### 3.2 Offsets, trivia, and `forEachChild`

**Offsets are UTF-16 code units.** Tested on a file whose first line is
`// é😀 multi-byte leading comment`: `sourceFile.text.length` is 63 (the JS string length) and
the end-of-file token ends at 63, while the file is 66 bytes of UTF-8. A diagnostic at `pos: 47`
lines up with `text.slice(47, 48)`, not with the 47th byte.

**`pos` includes leading trivia; `getStart()` does not.** Tested: a `VariableStatement` preceded
by a comment reports `[0, 62)` with `getStart() = 34`. Every span we compare must use
`getStart()`, or equivalently `skipTrivia`.

**`forEachChild` flattens.** Tested on the same probe:

```
CallExpression  Deferred.make<number, number>()
  PropertyAccessExpression   Deferred.make
  NumberKeyword              number         <- typeArguments[0]
  NumberKeyword              number         <- typeArguments[1]
```

and on an arrow function:

```
ArrowFunction  (a0) => body
  Parameter    a0
  EqualsGreaterThanToken  =>
  <body>
```

Punctuation tokens (`=>`, `?`, `:`, `*`, `=`) and modifiers (`export`) are children. So a path of
`forEachChild` ordinals is not stable when an optional field appears or disappears. The `Node`
interfaces in `ast.generated.d.ts` do have the named fields (`expression`, `typeArguments`,
`arguments`, `parameters`, `body`), so a path should be `(fieldName, index)` pairs.

The whole house fragment maps to a small set of kinds. Tested, from a probe covering every
`TypeScript.Expr` and `Stmt` former the Effect4 printer uses:

| house former | TypeScript `SyntaxKind` |
| --- | --- |
| `ident "Effect.succeed"` | `PropertyAccessExpression(212)` over two `Identifier(79)` |
| `ident "add"` | `Identifier(79)` |
| `call f args` | `CallExpression(214)` |
| `generic f ts` + `call` | one `CallExpression(214)` with `typeArguments` |
| `member t n` | `PropertyAccessExpression(212)` |
| `method t n args` | `CallExpression(PropertyAccessExpression(...))` |
| `object fields` | `ObjectLiteralExpression(211)` of `PropertyAssignment(303)` |
| `arrow none b` | `ArrowFunction(220)` with no `Parameter` |
| `lambda ps b` | `ArrowFunction(220)` with `Parameter(170)` |
| `arrowBlock ps stmts` | `ArrowFunction(220)` with `Block(242)` body |
| `generator stmts` | `FunctionExpression(219)` with `AsteriskToken(41)` |
| `cond t a b` | `ConditionalExpression(228)` |
| `str` / `int` / `bool` | `StringLiteral(10)` / `NumericLiteral(8)` / `TrueKeyword(111)` |
| `constYield n v` | `VariableStatement(244) > VariableDeclarationList(262) > VariableDeclaration(261)` with a `YieldExpression(230)` initializer |
| `yieldDiscard v` | `ExpressionStatement(245) > YieldExpression(230)` |
| `ret v` | `ReturnStatement(254)` |
| `letInit n v` | `VariableStatement(244)` (`let`) |
| `assign n v` | `ExpressionStatement(245) > BinaryExpression(227)` with `EqualsToken(63)` |
| `ifElse c a b` | `IfStatement(246)` with two `Block(242)` |
| `whileTrue b` | `WhileStatement(248)` |
| `breakTo none` | `BreakStatement(253)` |
| a module declaration | `VariableStatement(244)` with `ExportKeyword(94)` |

That is 24 kinds plus five punctuation tokens. The target signature is small.

### 3.3 The `tsc` 5.9.2 printer: parenthesisation and idempotence

Tested against `ts/eff/node_modules/typescript`:

```
call(arrow)    -> "(() => 1)()"
cond(cond,..)  -> "(true ? 1 : 2) ? 3 : 4"
member(1,'x')  -> "1..x"
arrow => obj   -> "() => ({ a: 1 })"
```

`createPrinter().printNode` **inserts parentheses automatically** (this is
`parenthesizerRules`). The parser **keeps** them: parsing `const x = (1 + 2) * 3` produces a
`ParenthesizedExpression` node. Tested. So print-then-parse is not the identity on trees; it is
the identity *after erasing outer expressions* (`ParenthesizedExpression`, `AsExpression`,
`TypeAssertion`, `NonNullExpression`, `SatisfiesExpression`, `PartiallyEmittedExpression`),
which TypeScript itself names `OuterExpressionKinds` and `skipOuterExpressions`.

At the text level it stabilises after one round: `printFile(parse(printNode(e)))` reprinted
again is byte-identical. Tested. `printFile` also adds the statement semicolon, which the house
renderer does not, so the two printers are not interchangeable byte for byte.

Numeric and string literal spelling survives, because `factory.createNumericLiteral` takes the
*text*: `1e3` and `0x10` print back as written, and `createStringLiteral(s, true)` chooses single
quotes. Tested. So literal forms are a printer input, not a printer decision, which is good news
for determinism.

### 3.4 Incremental

- `tsc` 5.9.2: `ts.updateSourceFile(sourceFile, newText, textChangeRange)` (`typescript.d.ts:9202`),
  `TextChangeRange = { span: TextSpan; newLength: number }` (`:8183`), `IScriptSnapshot` with
  `getChangeRange` (`:10017`) and `ScriptSnapshot.fromString`. Read.
- `tsgo`: `api.updateSnapshot({ fileChanges: { changed, created, deleted } })`. Tested (I
  rewrote a file and took a second snapshot; the diagnostics changed). Source files are cached
  by `(path, parseOptionsKey, contentHash)` and unchanged entries are retained across
  snapshots (`dist/api/sourceFileCache.d.ts`). This is coarser than `updateSourceFile`: the
  unit is a file, not a text range.

### 3.5 The `--pretty false` CLI format

`file(line,col): error TSnnnn: message`, one line, with chained messages on following lines
indented by two spaces per level. Line and column are **1-based**, and the column counts UTF-16
code units. Tested. There is no flag to emit offsets, and `tsgo --help --all` lists no JSON or
SARIF output. Tested. That is the reason to use the API rather than to parse the CLI.

### 3.6 `oxc`

`ts/eff/read.ts:48` uses `parseSync(filename, source, { sourceType: "module", lang: "ts" })` and
reads ESTree with `start`/`end` byte offsets (`ts/eff/ingest/oxc.ts:26`, `const offset = (n, k)`).
Two differences from TypeScript's AST that matter. First, oxc's offsets are **UTF-8 byte**
offsets into the source, where TypeScript's are UTF-16 units, so the two position spaces differ
on any non-ASCII file. Second, oxc is ESTree: `CallExpression.callee` and `.arguments`,
`MemberExpression.object`/`.property`, `ArrowFunctionExpression.params`/`.body`, and
`ParenthesizedExpression` appears and is explicitly unwrapped (`ingest/oxc.ts:30`). ESTree has
no `SyntaxKind` numbers; node types are strings. Read.

---

## 4. Q8. Tree-sitter as the syntax layer

**Node types and fields.** `tree-sitter-typescript`'s `node-types.json` is machine-readable and
has named fields. Reproduced: I fetched it from the repository and then checked the same file in
the owner's local clone at
`/Users/pooks/Dev/foldlab/.staging/treesitter/clones/tree-sitter-typescript/typescript/src/node-types.json`,
which has **324 node types, 183 of them named**, and whose `call_expression` entry matches the
fetch exactly. The ones our fragment needs:

| node type | fields |
| --- | --- |
| `call_expression` | `function` (req), `arguments` (req), `type_arguments` (opt) |
| `member_expression` | `object` (req), `property` (req), `optional_chain` (opt) |
| `arrow_function` | `body` (req), `parameter` (opt, bare identifier), `parameters` (opt, `formal_parameters`), `return_type` (opt), `type_parameters` (opt) |
| `generator_function` | `body` (req), `name` (opt), `parameters` (req), `return_type` (opt), `type_parameters` (opt) |
| `yield_expression` | one unnamed child, the expression |
| `ternary_expression` | `condition`, `consequence`, `alternative` (all req) |
| `object` | children: `pair` \| `method_definition` \| `shorthand_property_identifier` \| `spread_element` |
| `pair` | `key` (req), `value` (req) |
| `array` | children: `expression` \| `spread_element` |
| `string` | children: `string_fragment` \| `escape_sequence` |
| `number` | no fields |
| `template_string` | children: `string_fragment` \| `escape_sequence` \| `template_substitution` |
| `lexical_declaration` | `kind` (req: `const`\|`let`), children: `variable_declarator` (req, multiple) |
| `variable_declarator` | `name` (req), `type` (opt), `value` (opt) |
| `export_statement` | `declaration` (opt), `source` (opt), `value` (opt), `decorator` (opt, multiple) |
| `if_statement` | `condition` (req, a `parenthesized_expression`), `consequence` (req), `alternative` (opt, `else_clause`) |
| `while_statement` | `condition` (req, `parenthesized_expression`), `body` (req) |
| `break_statement` | `label` (opt) |
| `return_statement` | one optional unnamed child |
| `expression_statement` | one required unnamed child |
| `statement_block` | children: `statement` (multiple) |
| `formal_parameters` | children: `required_parameter` \| `optional_parameter` |
| `type_arguments` | children: `type` (multiple) |
| `identifier`, `property_identifier` | no fields |

**The advantages over `forEachChild`.** Type arguments are a *separate named field*, not
flattened into the child stream, so a `(field, index)` path is stable whether or not a call
carries type arguments. This directly fixes finding 9.

**The disadvantages, and they are real.**

- It is a **concrete** syntax tree. `if_statement.condition` is a `parenthesized_expression`,
  not the expression; parentheses, commas and braces are nodes. A tree-sitter tree of our
  printed text has more structure than the house `Expr`, and the map back is a normalisation,
  not an inverse. This is not fatal but it is a second normal form to define and maintain.
- `arrow_function` has **two** spellings of parameters (`parameter` for `x => e`, `parameters`
  for `(x) => e`). Our printer always emits parentheses, so we only ever produce `parameters`,
  but a foreign reader has to handle both.
- The grammar is **stale**. `tree-sitter-typescript` latest tag and npm version is `0.23.2`,
  published 2024-11-11, against `tree-sitter` core 0.25 (node bindings) / 0.27 (web). Tested via
  `npm view`. You can pin it, but you are pinning something that is not tracking the language.
  `vendor/effect-4.0.0-rc.112` pins a library that moves every week and the pin is a decision;
  pinning `0.23.2` is inheriting a two-year gap.
- Tree-sitter's grammar is a **parser**, not a printer. It gives no way to render a tree back to
  text other than concatenating the source ranges of an existing parse. For synthesised trees
  (which is what `print` produces) there is nothing to concatenate. So tree-sitter cannot be the
  renderer; it can only be the recogniser.
- Error recovery: tree-sitter always returns a tree and marks unparseable regions with `ERROR`
  and `MISSING` nodes. On well-formed printed text there should be none, but the only way to
  know is to run it, and I could not: tree-sitter is not installed on this machine and there is
  no network package install in this session. **Unverified.** The check is one line
  (`tree.rootNode.hasError`) and belongs in the harness on day one if this route is taken.

**Bindings.** For TypeScript: `web-tree-sitter` 0.27.0 (WASM, works in node and in a browser)
and `tree-sitter` 0.25.1 (native node bindings). Tested via `npm view`. For OCaml:
`semgrep/ocaml-tree-sitter-core` is a code generator plus runtime that derives a **typed OCaml
CST from `grammar.json`**, with `ocaml-tree-sitter-languages` publishing the per-language
libraries. Verified by search. So the owner's "generatable in TypeScript/OCaml" property is
genuinely available: one `node-types.json` gives a Lean table, a TypeScript matcher and an OCaml
typed CST.

**Incremental.** `ts_tree_edit(tree, &TSInputEdit)` with `{start_byte, old_end_byte,
new_end_byte, start_point, old_end_point, new_end_point}`, then `ts_parser_parse(parser,
old_tree, input)` reuses the unchanged subtrees; `ts_tree_copy` is a refcount bump. Positions are
**byte offsets** plus `(row, column)` points, where column is also in bytes. Verified from the
tree-sitter documentation. Note this is a *third* offset unit in play: tsgo is UTF-16, oxc is
UTF-8 bytes, tree-sitter is UTF-8 bytes.

**Verdict on Q8.** Tree-sitter is the right shape for the *data* (`node-types.json` is exactly
the kind-and-field table the design wants, and it is importable) and the wrong shape for the
*text* (it cannot render, and its CST is not the AST our templates are written against). I would
take the table and not the parser, and I would take the table from TypeScript's own
`ast.generated.d.ts` instead if we are going to depend on tsgo anyway. See §12(a).

---

## 4b. The Lean tree-sitter binding the owner has used

Read at `/Users/pooks/Dev/foldlab/.staging/treesitter/clones/lean4-tree-sitter`, version
`v0.2.4`, toolchain `leanprover/lean4:v4.32.0`. 1246 lines of Lean in 32 modules. The grammar
clones are beside it: `tree-sitter` core and `tree-sitter-typescript` with
`typescript/src/node-types.json`.

### (1) What the typed grammar schemas are, and where they come from

**They are hand-written, and they are not a syntax model.** `TreeSitter/Types/GrammarSpec.lean`
is twelve lines:

```lean
class GrammarSpec (Node : Type) where
  toDeclarationType : Node → Option DeclarationType
  declarationNodes  : List Node
  nameNodes         : List Node
  queryString       : String
  decl_nodes_total  : ∀ n, n ∈ declarationNodes → (toDeclarationType n).isSome = true
```

`DeclarationType` is a fixed fourteen-constructor enumeration (`class_`, `interface_`, `enum_`,
`struct_`, `function_`, `method_`, `constructor_`, `field_`, `property_`, `constant_`,
`typeAlias`, `module_`, `package_`, `annotation_`). Every grammar module is one inductive of
between fourteen and twenty node names, a `toDeclarationType` mapping, and a tree-sitter query
string. `TreeSitter/Grammars/TypeScript.lean` is 58 lines listing `class_declaration`,
`interface_declaration`, `enum_declaration`, `type_alias_declaration`, `function_declaration`,
`method_definition`, `public_field_definition`, `function_signature`,
`abstract_method_signature`, `module`, plus three name node types.

None of our fragment's node types appear: no `call_expression`, no `arrow_function`, no
`member_expression`, no `yield_expression`, no `lexical_declaration`. The README's nine
supported grammars are nine outliners, which is a legitimate and useful thing to have and is not
a syntax algebra. The `decl_nodes_total` proof obligation is discharged by `decide`; it says
"every node I listed as a declaration maps to a declaration type", and nothing about the
grammar.

So: **not generated from `node-types.json`**. Read. If we wanted a model of the 324 node types
we would write the generator ourselves, and it would be a different generator from
`GrammarSpec`.

### (2) What it would take to add TypeScript

**Nothing. It is already there.** `ffi/language_definitions.json` pins
`tree-sitter/tree-sitter-typescript` at rev `75b3874edb2dc714fb1fd77a32013d0f8699989f`,
`directory: "typescript"`, `has_scanner: true`, and the lakefile already has targets
`ts_typescript.o` and `ts_typescript_scanner.o` compiling `parser.c` and `scanner.c` against
`tree-sitter` core `v0.24.7`, with `treeSitterTypescript : IO TSLanguage` exported from
`TreeSitter/FFI/Language.lean`. `tsx`, `javascript`, `go`, `rust`, `csharp` and `ruby` are
vendored the same way. Read. The vendoring mechanism is `ffi/vendor_grammars.sh` reading that
JSON, so a re-pin is a one-line rev change plus `make vendor-grammars`.

Note the core pin: `tree-sitter` `v0.24.7`, which is older than the 0.25 the node bindings ship,
and the grammar rev is a commit, not the `v0.23.2` tag. Both are pinnable facts; neither is
current.

### (3) Is `SourceMap`/`Extract` the positions structure we want

**No.** `Extract/Extract.lean` (265 lines) walks the tree with the grammar's query, produces
`Array Declaration` where `Declaration = { name, declType, source : SourceRange, children,
modifiers }`, and `SourceRange = { startLine, startColumn, endLine, endColumn }`
(`Types/CodeLocation.lean`). `SourceMap` then maps each declaration's `SourceRange` to a
`LeanLocation = { module, line, column }` and the proofs in `Proofs/SourceMap.lean` are about
lookup totality and composition of two such maps.

That is a **symbol-to-symbol** map for a code generator: "this Java class became that Lean
declaration". It is not a **node-to-span** table for a printed image. Three concrete mismatches:

- The positions are line and column, not offsets, although `TSNode.startByte`/`endByte` are
  right there in the FFI. Converting back to offsets needs the line table, and the columns are
  in bytes (tree-sitter's convention), not UTF-16, so they do not line up with `tsgo`.
- The unit is a `Declaration`, filtered to the fourteen declaration kinds. Our printed image has
  one declaration per module and everything interesting is inside its initializer expression,
  which `Extract` never descends into.
- There is no path. A `Declaration` has `children`, but nothing addresses a node by the
  `Node.child` index path that `blame`, the layer references and the authoring refusals all use.

What we want from that layer is exactly two functions that already exist at the FFI and are
discarded above it: `TSNode.startByte`/`endByte` and `TSNode.childByFieldName`. A driver that
walks the tree once and emits `(path, kind, startByte, endByte, fieldName)` is perhaps forty
lines on top of `TreeSitter.FFI` and does not touch `Extract`, `SourceMap`, `Types` or
`Grammars` at all.

### (4) The trust-gate split: parse in `Tools`, model in `src/Effect4`

`AGENTS.md:62` is unambiguous: "No `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`,
`extern`, `implemented_by`. The gate audits every `Effect4.*` and `Test.*` declaration at
`[propext, Quot.sound]`". Every function in `TreeSitter/FFI` is `opaque` with `@[extern …]` and
every one of them returns `IO`. So the binding can never be imported by `src/Effect4` or by
anything under `Test/`.

**The split is workable, and it is the split the estate already uses for everything else.** The
existing pattern is exactly this: `make corpus` is a `Tools` driver
(`tools/Tools/Corpus.lean`) that writes `.lake/corpus/*.ts`, `*.json`, `*.eff` and
`generated/corpus-index.tsv`; the truth harness writes `harness/truth/corpus.json` and reads
`result.json`; the pure model consumes files as data. A tree-sitter parse is the same shape:

```
Tools driver (extern, IO)                  src/Effect4 (pure, gated)
  parse text with treeSitterTypescript  ->  TsTree, a first-order kinded tree
  walk once, emit JSON                      read from the file as data
```

**What the interchange should be.** One JSON array per file, one record per named node, in
preorder:

```json
{ "path": [0, 1, 2], "kind": "call_expression", "field": "arguments", "index": 0,
  "startByte": 175, "endByte": 678, "text": null }
```

with `text` filled only for leaf tokens (`identifier`, `number`, `string`, `property_identifier`)
and `null` otherwise, since the source text is already on disk. `path` is the named-child path,
`field` and `index` are the named field the node occupies in its parent and its index within
that field, and both byte offsets come straight from the FFI. That record set determines the
tree, so `src/Effect4` can rebuild a `TsTree` from it with a total function and a `#guard` that
rebuilding and re-flattening is the identity. That is the same discipline as the wire corpus.

The pure side then owns: the `TsTree` type, the template table, the reader, the renderer, the
position marks, and every theorem. The `Tools` side owns: running the parser, and comparing its
spans against the marks. Neither side can drift, because the comparison is a lane.

### Toolchain

Ours is `leanprover/lean4:v4.33.1` (`lean-toolchain`); the binding says `v4.32.0`. Read. That is
one minor version and the binding is 1246 lines of plain Lean with no Mathlib and no unusual
elaboration, so the risk is low, but it is untested: I did not build it, because building it
would start a second Lean process and `docs/STATE.md` forbids that. The honest statement is
**unverified**, and the check is one `lake build` in the binding's own directory with our
toolchain pinned.

### Does it match rowan

Partly, and not where it counts. tree-sitter's own C tree *is* the rowan pattern: an untyped
kinded tree with byte spans, node kinds as small integers, named fields, and incremental reuse.
The Lean binding sits on top of that and immediately projects to `Declaration`, which is neither
the green tree nor a typed view of it. So the rowan-shaped object we want is one level *below*
this binding, at `TreeSitter.FFI`, and the binding's own Lean-level types are a different
abstraction aimed at a different job.

---

## 5. Q3. Positioned rendering precedents

- **Wadler 2003, "A prettier printer"**, and **Leijen's** `wl-pprint`. A `Doc` denotes a *set*
  of layouts and the renderer picks the best one that fits a width. Recalled. Our renderer has
  no width and picks the layout from the syntax, so we are using the degenerate case where the
  set is a singleton. That is a feature: byte determinism is what the goldens rely on.
- **Haskell `prettyprinter`'s `Doc ann`** and `SimpleDocStream ann` with `annotate ::
  ann -> Doc ann -> Doc ann`, and the stream constructors `SAnnPush`/`SAnnPop`. Recalled. This
  is exactly the derivation's `mark : path -> M -> M`: a renderer that emits a stream of text
  plus push/pop of annotations, from which spans fall out by counting characters between a push
  and its pop. `Text.PrettyPrint.Annotated` (the `pretty` package) has the same idea with
  `AnnotDetails`. This is the cheapest correct design and I recommend it.
- **OCaml `Format` semantic tags** (`pp_open_stag`, `pp_close_stag`): same idea, side-effecting.
  Recalled.
- **Roslyn red/green trees.** The green tree is immutable, position-free and shareable, storing
  only *widths*; the red tree is a lazily built facade that computes absolute positions by
  accumulating widths from the root. Trivia is attached to tokens. Recalled. The consequence
  worth copying: *a node stores its width, not its position*, so an edit deep in the tree does
  not invalidate the nodes above it.
- **rust-analyzer's `rowan`.** The same red/green split, but the green node is *untyped and
  kinded*: `SyntaxKind` is a `u16`, children are a list of green nodes or tokens, and typed
  views (`ast::CallExpr`) are thin wrappers that assert a kind and project children by
  position. Recalled. This is the design the owner's phrasing points at: "a uniform kinded rose
  tree with typed views".
- **SwiftSyntax / libSyntax**: same red/green architecture, with the syntax tree generated from
  a declarative node description file. Recalled. Relevant because their node description file is
  the analogue of `node-types.json`.
- **tree-sitter**: byte spans stored on every node, incremental reparse, tree edits. Covered in
  §4.

**Which one matches "tree, text and positions as separate structures"?** `rowan`, exactly:
green tree (structure plus widths), source text (a separate `String`), and positions computed on
demand rather than stored. And the `prettyprinter` annotation stream is the way to get positions
out of a renderer that was written as a fold.

**A Lean version, small.** Two definitions and one instance:

```lean
/-- A rendered fragment: the text, whether it contains a newline, and the marks it carries. -/
structure Marked (P : Type) where
  text  : String
  width : Nat                 -- UTF-16 code units, so host offsets line up (finding 4)
  nl    : Bool
  marks : List (P × Nat × Nat)   -- path, start, end, relative to this fragment

instance : Append (Marked P) := ⟨fun a b =>
  { text := a.text ++ b.text, width := a.width + b.width, nl := a.nl || b.nl,
    marks := a.marks ++ b.marks.map (fun (p, s, e) => (p, s + a.width, e + a.width)) }⟩

def Marked.at (p : P) (m : Marked P) : Marked P :=
  { m with marks := (p, 0, m.width) :: m.marks }
```

`Marked P` is a monoid (associativity is `List.append_assoc` plus `Nat.add_assoc`), `text` and
`width` and `nl` are monoid homomorphisms out of it, and `String` with `nl` is the quotient you
get by forgetting `marks`. So "one definition, two projections" is a theorem, not a convention:
`render = fold into Marked` and `Render.expr = text ∘ render`, provable by `foldMap` fusion once
the renderer is an algebra. That is about forty lines with the fusion lemma.

---

## 5b. The `Doc` question, against `docs/ALGEBRAIC-LAYOUT-*.md`

The repository has two untracked design documents for a visual layout engine:
`docs/ALGEBRAIC-LAYOUT-SPECIFICATION.md` (607 lines) and `docs/ALGEBRAIC-LAYOUT-ENGINES.md`
(375 lines). Read both. Section 2.3 of the engines document states the Wadler-Leijen-Bernardy
laws we would need (monoid of concatenation, `nest` homomorphism, horizontal distributivity of
`nest`, and `group(D) = flat(D) ⊓ D` as the choice semilattice); §3.3 of the specification has a
`VisualConfig` record with `viewportWidth`, `badnessThreshold`, `timeScale` and so on; §3.4
names `Projection.ContainmentTree` over the `Eff` AST with path coordinates. The Lean API
section (§5) has `Glue`, `Envelope`, `Tile`, `FiberSpan` and no `Doc` at all. Nothing is
implemented.

### (1) Bernardy 2017 and `prettyprinter`'s annotations

Bernardy, "A pretty but not greedy printer" (ICFP 2017). Recalled; I could not fetch it in this
session. The contribution is that Wadler's and Leijen's printers are *greedy* and therefore not
optimal, and that if you keep, at each subdocument, only the Pareto frontier of
`(lastWidth, maxWidth, height)` measures, you get an optimal layout in time polynomial in the
document size. The measure is a *monoid* and the pruning is by a partial order on measures.
So the shape is: `Doc = a set of layouts`, each layout carrying a monoid measure, with a
domination order used to prune.

`prettyprinter`'s `Doc ann` and `SimpleDocStream ann` with `SAnnPush ann` / `SAnnPop` is the
annotation mechanism, and it is the right one: annotations survive layout, and spans fall out by
counting the text emitted between a push and its matching pop. Recalled. Together they say:
**exact positions from annotations require only that the renderer emit a stream and that
annotations nest**, which is true of an AST by construction.

**Is a deterministic policy just the trivial choice function?** Yes, and this is the cleanest
part of the whole picture. The choice semilattice `⊓` is a binary operation on documents;
a *policy* is a function that resolves `⊓` given a state (remaining width, current column). The
house style's policy is
`resolve (flat d) d = if syntacticallyMultiline d then d else flat d`,
which never reads the width and never reads the column. It is a legitimate resolution of the
same algebra, it makes `⊓` a projection (`d ⊓ d = d`, and the choice is determined by `d`
alone), and everything the elastic policy proves about the algebra still holds. In Bernardy's
terms, the house policy keeps exactly one element of the Pareto frontier at every step, chosen
by a syntactic predicate rather than by a measure comparison. So a `Doc` with `group`/`flat` and
two policies is not a compromise: **the deterministic policy is a homomorphism that factors
through the general one**, and "positions never depend on a viewport" is the statement that our
policy ignores its state argument, which is a one-line proof obligation on the policy, not a
property that has to be re-established per document.

### (2) One `Doc`, or only a shared measure monoid?

One `Doc` type, honestly, **if and only if** the choice operator is in the type and the policy is
a parameter. Concretely:

```lean
inductive Doc (A : Type)          -- A is the annotation, for us a path
  | empty
  | text   (s : String)
  | line                          -- a break that `flat` turns into a space (or into nothing)
  | cat    (a b : Doc A)
  | nest   (i : Nat) (d : Doc A)
  | choice (flat wide : Doc A)    -- the semilattice; `group d = choice (flatten d) d`
  | annot  (a : A) (d : Doc A)
```

Two policies over it:

- `Policy.syntactic : Doc A → Bool` picks `wide` exactly when the subdocument contains a hard
  break. This is the house style and it reproduces `Render.expr`'s `containsNewline` decision
  exactly, because that decision *is* "did any rendered child contain a newline".
- `Policy.knuth : VisualConfig → …` picks by the Bernardy measure and the badness threshold of
  `docs/ALGEBRAIC-LAYOUT-SPECIFICATION.md` §3.3.

What the two must **not** share is `Glue`, `Envelope`, `Tile` and `FiberSpan`. Those are
two-dimensional diagram algebras for the score and string-diagram projections and they have
nothing to do with linear text. Putting them in the same type as `Doc` would be the mistake.
The honest layering is: `Doc` for one-dimensional text (printed programs and the containment
tree), the diagram algebras for two-dimensional projections, and a **shared measure monoid**
underneath both, because both need to know how wide something is.

Where I would push back on the main session's phrasing: the containment tree is a *view of the
same tree* with a different rendering, not a different document type. If `Doc` carries path
annotations, `Projection.ContainmentTree` is one more `Doc`-valued fold over `Eff` beside
`print`, and its path coordinates (`§1.2.1` in the spec) are the same `List Nat` that `blame`
uses. That is a real unification and it costs nothing.

### (3) The right home, and the laws

**Home.** The `Doc` belongs in its own small Lean package, below both consumers:

```
Doc  (new, ~300 lines)
 ├── lean4-typescript   (TypeScript.Render becomes Doc-valued; `Style` becomes a policy)
 └── lean4-effect4      (positions for blame, and the containment-tree projection)
```

It must not live in `lean4-typescript`, because the containment tree and the trace projections
have nothing to do with TypeScript; and it must not live in `lean4-effect4`, because the
TypeScript renderer already lives outside and the dependency would invert. It is the same
argument that put `Effects` in its own package (DI-90). It has no dependencies beyond core, so
it is cheap to stand up and cheap to pin.

**Laws it should carry**, in the order they are needed:

1. `Doc` is a monoid under `cat` with `empty` (associativity, two units).
2. `nest` is a monoid homomorphism: `nest i empty = empty`,
   `nest i (cat a b) = cat (nest i a) (nest i b)`, and `nest i (nest j d) = nest (i + j) d`.
   These are laws 1 to 3 of `docs/ALGEBRAIC-LAYOUT-ENGINES.md` §2.3 and they are what makes the
   renderer a fold rather than a traversal with state.
3. `choice` is idempotent, commutative and associative where both sides are layouts of the same
   document, i.e. the *set of layouts* is a semilattice and `group d = choice (flatten d) d`.
   Wadler's `flatten` laws (`flatten (cat a b) = cat (flatten a) (flatten b)`,
   `flatten (nest i d) = flatten d`, `flatten line = text " "`) are the ones to state.
4. The **measure is a monoid homomorphism**: `measure (cat a b) = measure a <> measure b`. This
   is the load-bearing law, because it is what makes incremental re-measurement after an edit
   cost the depth and not the size (§7), and it is what makes `text ∘ render = Render.expr`
   provable by fusion (§5).
5. **Annotation nesting**: in the rendered stream every `SAnnPush` has a matching `SAnnPop` and
   the spans they delimit form a tree ordered by containment. This is the theorem that says a
   position table is a tree and not a list, and it is what lets "map a diagnostic offset to a
   path" be a well-defined descent.
6. **Policy independence**: `text (render p d) = text (render p' d)` is *false* in general and
   must not be claimed; what is true and worth proving is
   `Policy.syntactic` ignores its state, so `render Policy.syntactic` is a function of `d`
   alone. That single lemma is the whole "byte determinism" claim, relocated.

### (4) UTF-16 versus bytes versus columns

This is the subtlety the main session is right about and the precedents mostly duck.

- `prettyprinter` measures in `Int` "columns" and is explicit in its documentation that it
  counts `Char`s, so it is wrong for astral-plane characters and for combining marks, and
  wrong again for East Asian wide characters. Recalled.
- Wadler's and Bernardy's papers assume one character is one column throughout. Recalled.
- `tsc` and `tsgo` count UTF-16 code units for both offsets and columns. Tested.
- `oxc` and tree-sitter count UTF-8 bytes for both offsets and columns. Read (`ingest/oxc.ts`)
  and read (tree-sitter documentation).
- Lean's `String.Pos` is a UTF-8 byte index. By definition.
- A terminal column is a display width: zero for combining marks, two for East Asian wide
  characters, and undefined for emoji in practice.

**None of the precedents solves this; they all pick one and live with it.** The fix that costs
nothing is a product measure:

```lean
structure Measure where
  bytes   : Nat     -- Lean String.Pos, oxc, tree-sitter
  utf16   : Nat     -- tsc, tsgo
  columns : Nat     -- terminal display width, for the layout engine only
  lines   : Nat     -- hard breaks, so `nl` is `lines > 0`
  last    : Nat     -- columns since the last break, for the Bernardy measure
deriving DecidableEq, Repr
```

A product of monoids is a monoid, each projection is a homomorphism, and `bytes`, `utf16` and
`columns` all coincide on ASCII. So the whole question collapses to one guard: **is the printed
image ASCII?** For the printed image it should be, and a `#guard` on the corpus makes it a
checked fact rather than an assumption. For the layout engine, which will render user strings
and box-drawing characters, it is not, and there the product measure earns its keep.

I would not compute `columns` in the first version. Carry the field, define it as `utf16` until
someone needs east-Asian widths, and say so in the docstring; that is honest and it does not
block anything.

**And the guard already passes.** Tested: all 408 printed corpus programs in `.lake/corpus` are
pure ASCII, 0 of 408 containing a byte outside `0x20..0x7e` plus tab. The only non-ASCII byte
anywhere in the emitted modules is an em-dash in the header comment that
`harness/truth/run-truth.ts:168` writes ("GENERATED by … from … — do not edit"), which appears in
all 36 modules under `harness/truth/generated`. Change that one character to a hyphen and every
emitted module is ASCII, at which point byte offsets, UTF-16 offsets and columns coincide
exactly and finding 4 stops being a hazard. That is a one-character fix that removes a whole
class of position bug, and it should be done in S0.

---

## 6. Q4. Structural diffing

- **Chawathe, Rajaraman, Garcia-Molina, Widom 1996, "Change detection in hierarchically
  structured information"** (SIGMOD). The classic tree edit script with `insert`, `delete`,
  `update`, `move`, matched by a bottom-up/top-down heuristic. Recalled.
- **Falleri et al. 2014, GumTree** ("Fine-grained and accurate source code differencing", ASE
  2014). Chawathe plus a greedy bottom-up isomorphism match with similarity thresholds.
  Recalled. It is a *heuristic*: no theorem, tuned constants, and it is the tool everyone
  actually uses for source diffs.
- **Lempsink, Leather, Löh 2009, "Type-safe diff for families of datatypes"** (WGP 2009). A
  generic diff over a mutually recursive family, where a patch is typed by its source and target
  and `patch` is total on well-typed patches. Recalled. The algorithm is an edit script over the
  *preorder traversal*, which is quadratic and produces long scripts.
- **Miraldo and Swierstra 2019, "An efficient algorithm for type-safe structural diffing"**
  (ICFP 2019, PACMPL 3(ICFP)). Verified by search. A patch is a **pattern-expression pair**:
  a pattern with metavariables matched against the source, an expression over the same
  metavariables producing the target. Sharing is maximised via a hash-consed common-subtree
  oracle and the algorithm is linear. `hdiff` is the tool; the follow-up is "Concise, type-safe,
  and efficient structural diffing" (PLDI 2021).
- **Derivatives and zippers.** McBride, "The derivative of a regular type is its type of one-hole
  contexts" (2001); Huet, "The zipper" (JFP 1997). Recalled. The derivative of our signature is
  already realised: `Node.child` / `Node.setChild` (`src/Effect4/Program/NodeLenses.lean`) is
  the zipper's one-step focus, and `List Nat` paths are its iterated form.
- **TypeScript's own `textChanges`** (internal, not exported) and `TextChangeRange`. Read the
  public half in `typescript.d.ts:8183`.

**The simplest correct "differ combinator" over our signature, given what already exists.**
Miraldo and Swierstra's shape is the right one and it is one definition on top of `Node`:

```lean
/-- A patch is a list of (path, replacement) with the paths pairwise non-prefix. -/
structure Patch (Op : Type) where
  edits : List (List Nat × Node Op)

def Patch.apply (p : Patch Op) (n : Node Op) : Option (Node Op) :=
  p.edits.foldlM (fun acc (path, node) => Node.setAt acc path node) n
```

where `Node.setAt` is the iterated `setChild` we already generate. `diff` is then the obvious
top-down recursion: if two nodes are equal, emit nothing; if their heads differ, emit
`(path, right)`; otherwise recurse into the children pairwise, and where the arities differ emit
the whole node. Two theorems, both easy:

- `Patch.apply (diff a b) a = some b` (correctness).
- `diff a a = ⟨[]⟩` (no spurious edits).

Merging two patches is a *pairwise-disjointness* check on the paths: if no edit path of one is a
prefix of an edit path of the other, the union applies and the result is independent of order.
That is the whole merge story and it is honest, unlike GumTree's heuristics. What this design
deliberately does not do is detect *moves*; a moved subtree costs a delete and an insert. Moves
matter for a human-facing code diff and do not matter for what the owner asked about (recomputing
positions and re-rendering after an authoring edit).

---

## 7. Q5. Incremental folds

- **Attribute grammars and incremental evaluation** (Reps, Teitelbaum, Demers 1983,
  "Incremental context-dependent analysis for language-based editors"). Recalled. Optimal
  incremental re-evaluation of a synthesised attribute after a subtree replacement costs
  time proportional to the number of attribute instances that actually change, which for a
  synthesised-only attribute is the path from the edit to the root.
- **Adapton** (Hammer et al., PLDI 2014) and **Salsa** (rust-analyzer's query engine, no paper).
  Recalled. Demand-driven memoisation with change propagation; the unit of reuse is a query,
  keyed by its inputs.
- **Finger trees** (Hinze and Paterson, JFP 2006). A sequence annotated by a monoid measure,
  with `O(log n)` split and concatenate and `O(1)` amortised access at the ends. Recalled.

**The least machinery that gives "re-render only the changed subtree and shift positions".**
Less than any of the above, because our render is a *synthesised* attribute into a monoid:

1. Cache, per node of the tree, its rendered `Marked P` value (or just its `width` and `nl`).
2. On a patch at path `p`, re-render the replaced subtree, then walk `p` from the bottom back to
   the root re-combining with the cached siblings. Cost is the depth times the arity, not the
   size of the tree.
3. Every mark under a sibling to the right of the edit shifts by
   `newWidth - oldWidth`, which is one `Int` added to a range of the position table.

That is the Roslyn "store widths, not positions" trick and nothing else. Finger trees buy
`O(log n)` splicing of the *text*; we do not need that until the text is large enough that
`String.append` dominates, which for a 300-character printed program it never is. **Do not build
Adapton or Salsa for this.**

---

## 8. Q6. The "message" semantics and the statement of correctness

The owner's phrase, "an effect or some representation of a future message that could be there,
or could include that set of chars", reads to me as: a node denotes a *set* of texts, and a
printer is a choice function on that set. That is Wadler 2003 exactly (a `Doc` denotes a set of
layouts and `best` picks one). Recalled.

The formalisation I would adopt is **not** a Galois connection and **not** a lens. It is the
Narcissus shape (Delaware et al., PLDI 2019), which is also the shape `read_exact` already has:

> A **format** is a relation `Fmt ⊆ Eff × String`. A **printer** is a function
> `print : Eff ⇀ String` with `print e = some s → (e, s) ∈ Fmt`. A **reader** is a function
> `read : String ⇀ Eff` with `read s = some e → (e, s) ∈ Fmt`. The format is **unambiguous**
> when `(e, s) ∈ Fmt` and `(e', s) ∈ Fmt` imply `e = e'`.

From those three you get the round trip for free: if `print e = some s` and `read s = some e'`
then both `(e, s)` and `(e', s)` are in `Fmt`, so `e = e'` by unambiguity. And the same relation
serves the host: a TypeScript reader is *another* function into the same `Fmt`, so "the Lean
reader and the TS reader agree" becomes a corollary of unambiguity rather than a separate
409-program comparison. That is the single biggest structural win available, and it is the
answer to the owner's "no shortcuts": state `Fmt` once, prove three functions against it.

Concretely `Fmt` factors as `Eff --(templates)--> TSTree --(render)--> String`, so
`Fmt = { (e, s) | ∃ t, Tmpl e t ∧ Render t s }` with `Tmpl` the template relation and `Render`
the rendering relation. Then:

- Lean's `print` and `Render.expr` are the composite choice function.
- Lean's `readEff` inverts `Tmpl`; the host's `read.ts` and `ck.ts` and any tree-sitter reader
  invert `Tmpl` too, on their own spelling of `TSTree`.
- `tsc`'s parser inverts `Render` (up to `skipOuterExpressions`).

Unambiguity of `Tmpl` is the decidable table check of §2. Unambiguity of `Render` restricted to
our image is the statement that our renderer is injective on printed trees, which is provable by
the same disjointness argument on heads.

---

## 9. Q9. "Should each AST node be effectful?" The free-monad reading

The main session's reading is: the TypeScript syntax is a signature, TS trees are terms of the
free monad over that signature, a template is a term with free variables, substitution is
monadic bind, so `print` is a fold from `F` into `Free G`, and rendering, `ts.factory`
construction and tree-sitter node construction are *handlers* of the syntax effect.

**This is correct as mathematics and it is not a renaming.** It buys three things:

1. `Free G X = X + G (Free G X)` is exactly "a TS term with holes labelled in `X`", and its
   `bind` is exactly hole substitution. Swierstra, "Data types à la carte" (JFP 18(4), 2008) is
   the canonical statement, and the monad law `(t >>= f) >>= g = t >>= (λx. f x >>= g)` is
   substitution composition, which is the lemma every template-expansion proof needs and which
   we would otherwise prove by hand per template.
2. `print = cata_F (λ layer. σ layer >>= id)` makes the printer a fold whose algebra is
   `G*`-valued, and the fusion law `handler ∘ cata = cata (handler ∘ σ)` gives
   `render ∘ print = cata_F (render ∘ σ)` for free. That is the theorem that makes the
   positioned renderer and the plain renderer provably the same traversal (§5).
3. Three back ends (Lean's renderer, `ts.factory`, tree-sitter node construction) become three
   `G`-algebras, and "they agree" is the statement that each is a homomorphism, which the
   existing `EffHom` / `hom_eq_cata_*` generator already knows how to emit
   (`src/Effect4/Program/Fold.lean:1103`, `:1178`).

**Where it does not buy anything, and where it would cost.**

- **Do not reuse `Effects.Program`.** `.lake/packages/effects/Effects/Algebra/Program.lean:34`
  is `Program (signature) (A) | pure | vis (op) (next : signature.Answer op → Program …)`, a
  free monad with **Lean functions as continuations**, and its own docstring says it
  "intentionally has no decidable equality, serialization, or content identity". The TS tree
  must have `DecidableEq` (the separation-4 gate at `src/Effect4/Program/Eff.lean:548`) and must
  serialise. So the right object is a *first-order* free monad, and the `Effects` package's one
  is not it. Reusing it would be a real regression, not a reuse.
- **The binder-aware hole does not force a second-order signature.** `Free G X` with
  `X = Nat × ...` and an explicit `weaken` is enough, and it is what `Forms.Template` already
  does. A genuine second-order signature (Fiore and Hur) would index the carrier by the context,
  making `Free G : (Nat → Type) → (Nat → Type)`, which turns every carrier into an exponential
  and every proof into a presheaf argument. Given that the estate has already rejected an
  inherited-attribute carrier once (`cata_ctx`, `docs/STATE.md`), I would not introduce one.
  Keep the hole first-order and carry `(cut, insertions)` as data, as today.
- **"Effectful nodes" in the handler sense is a misfit for the reader.** A handler eliminates a
  free monad; a reader *builds* one from text. The clean statement of the reader is **not** an
  algebra and not a coalgebra of `G`. It is the *partial inverse of one layer*:
  `match : μG ⇀ G (μG)` extended to `unTmpl : μG ⇀ F (μG)` by the template table, and then
  `read = ana`-style recursion on the subterm order, total because the argument shrinks. In Lean
  that is a structural recursion on the `Expr` argument, which is what `readEff` already is.
  There is no coalgebra here worth naming.

**The smallest Lean formulation I recommend.**

```lean
/-- The TypeScript syntax signature: a kind and the named fields of that kind. -/
structure TsSig where
  kinds  : List String
  fields : String → List (String × Mult)     -- field name, and one / optional / many

/-- A TypeScript term with holes labelled in `X`. First-order: `DecidableEq` when `X` has it. -/
inductive Tm (X : Type)
  | hole  (x : X)
  | node  (kind : String) (fields : List (String × List (Tm X)))
  | token (kind : String) (text : String)     -- identifiers, literals
deriving DecidableEq

def Tm.bind : Tm X → (X → Tm Y) → Tm Y            -- substitution
def Tm.close : Tm Empty → TsTree                  -- a term with no holes
```

`Tm` is the free monad; `Tm Empty` is `μG`; a template is a `Tm Slot` where
`Slot = { index : Nat, cut : Nat, insertions : Nat }`; `Template.expand` is `Tm.bind` with the
weakening baked into the substitution for slots. The whole thing is maybe eighty lines plus the
two monad laws. **This is the one abstraction I would actually add.**

---

## 10. Q10. The tsconfig is part of the fold

The owner is right, and it is measurable. I ran the same probe under five option sets with
`tsgo`, and three of them with `tsc` 5.9.2. Tested.

| option set | TS2322 site | TS2345 site | TS2304 | TS2554 | extra |
| --- | --- | --- | --- | --- | --- |
| harness (`strict`, `exactOptionalPropertyTypes`, `noUncheckedIndexedAccess`) | **2375** | 2345 | 2304 | 2554 | none |
| `strict` only | **2322** | 2345 | 2304 | 2554 | none |
| `strict: false` | 2322 | 2345 | 2304 | 2554 | the `number \| undefined` argument error **disappears** |
| `target: ES2015` | 2322 | 2345 | 2304 | 2554 | 2550, 7031 from `lib` |
| `module/moduleResolution: node16` | 2322 | 2345 | 2304 | 2554 | 1287, 1295, 1479 on every import and export |

Findings.

- **`exactOptionalPropertyTypes: true` rewrites 2322 into 2375** whenever the assignability
  failure touches an optional property, which for `Effect.Effect<A, E, R>` is essentially every
  answer-type mismatch. So the harness's own tsconfig already moves a table row.
- **`strictNullChecks` gates a whole class**: with `strict: false`, `Effect.fail(undefined)` and
  reads of a `Ref<number | undefined>` stop being errors. Any claim of the form "Lean refuses ⟺
  TypeScript refuses" is false under a non-strict config.
- **`module`/`moduleResolution` add file-level diagnostics that have nothing to do with the
  program** (1287, 1295, 1479). A diagnostics harness must filter by code class, or it will
  blame the program for the module system.
- **`target`/`lib` change what the prelude compiles at all**, so they are part of the pin even
  though they do not change the program's own codes.
- **`tsgo` and `tsc` 5.9.2 agree exactly** on all three option sets I compared, message text
  included. Reproduced.

**The minimal set the truth harness already fixes.** `harness/truth/tsconfig.json` sets
`target: ES2022`, `module: ESNext`, `moduleResolution: bundler`, `strict: true`,
`exactOptionalPropertyTypes: true`, `noUncheckedIndexedAccess: true`,
`verbatimModuleSyntax: true`, `allowImportingTsExtensions: true`, `noEmit: true`,
`resolveJsonModule: true`, `skipLibCheck: true`, `types: ["bun"]`. Of these, the ones that
change diagnostics for our fragment are `strict`, `exactOptionalPropertyTypes`, `target`, `lib`
(implied by `target`), `module`, `moduleResolution` and `skipLibCheck`. `types: ["bun"]` matters
only because it drags in bun's globals; the corpus run in §11 used `types: []` and was
unaffected.

**How to represent it in Lean.** A small record, emitted to `tsconfig.json` and hashed into
every result:

```lean
structure HostConfig where
  compiler : String          -- "tsgo" | "tsc"
  version : String           -- "7.0.0-dev.20260629.1" | "5.9.2"
  target : String := "ES2022"
  module : String := "ESNext"
  moduleResolution : String := "bundler"
  strict : Bool := true
  exactOptionalPropertyTypes : Bool := true
  noUncheckedIndexedAccess : Bool := true
  verbatimModuleSyntax : Bool := true
  skipLibCheck : Bool := true
  effectVersion : String := "4.0.0-rc.112"
deriving DecidableEq, Repr
```

with `HostConfig.render : HostConfig → String` emitting the JSON and
`HostConfig.digest : HostConfig → Digest` folding into the existing digest. The refusal-to-code
table is then `TypeReason → HostConfig → List Nat` (a set of admissible codes), or, cheaper and
more honest, `TypeReason → List Nat` for the codes that are stable across every config in the
matrix, with the config-sensitive rows named explicitly. Only two rows are config-sensitive
today: anything that goes through the declaration annotation (2322 vs 2375) and anything that
depends on `strictNullChecks`.

---

## 11. The corpus measurement. Tested

Method: I wrote every `.lake/corpus/*.ts` expression into a module with the harness's
`importHeader` (408 modules), pointed a tsconfig with the harness options at them, and ran
`tsgo` once.

```
408 modules, one native run                         0.200 s wall
769 diagnostic lines, 640 error lines, 248 files with at least one error
codes: TS2345 x461  TS2322 x61  TS2769 x32  TS2872 x29  TS2375 x19  TS1107 x12
       TS7005 x7  TS2379 x4  TS2304 x4  TS2873 x4  TS7034 x4  TS2739 x2  TS1345 x1  TS2740 x1
```

Cross-tabulated against `generated/corpus-index.tsv`'s `wellTyped` column:

```
lean typed  & tsgo clean :  135
lean refuse & tsgo errors:  248
lean typed  & tsgo errors:    0
lean refuse & tsgo clean :   25
```

**Zero programs that the Lean checker accepts are refused by TypeScript.** The 25 in the other
direction are, by inspection of the programs: `Effect.fail(true)`, `Effect.fail(false)`,
`Effect.fail(undefined)`, `Effect.fail(isZero(n))`, `Effect.fail(pair(19, 18))`,
`Effect.failCause(Cause.fail(true))`, `Effect.fail(a0)` on a fiber handle, and four programs
(`g133`, `g257`, `g302`, `g341`) whose refusal has some other cause I could not identify without
running Lean. The dominant class is the **error alphabet**: `rawSupportedErrTy`
(`src/Effect4/Program/Eff.lean:74`) admits `never`, `nat`, `string`, string literals, and pairs
of tag types, and refuses `bool`, `unit` and `(nat, nat)`. TypeScript has no such restriction.

So the first honest statement of the relation between the two checkers is:

> `effTy e = some _ → tsgo has no error on print e`, observed on 408 of 408, with a named
> class (`TypeReason.errorNotAdmitted`) accounting for most of the strictness gap.

That is a *soundness* claim in the useful direction, it is checkable by one command, and it is
worth pinning as a lane before any of the deeper design lands. The codes actually observed also
tell you what the mapping table has to cover: 2345 is 72% of all errors, and 2872/2873
("this kind of expression is always truthy/falsy") are a class that has no Lean counterpart at
all and must be filtered or accepted as advisory.

---

## 12. Recommendations

**(a) `G` in Lean: a kinded rose tree with typed views, over an imported table.** Replace the
house `TypeScript.Expr`/`Stmt` for *this* purpose with

```lean
inductive Tree | node (kind : Kind) (fields : List (Field × List Tree)) | token (kind : Kind) (text : String)
```

plus generated typed constructors and projections (`Tree.callExpression`,
`Tree.asCallExpression`), where `Kind` and `Field` come from a **checked-in table**. Take the
table from TypeScript's own `dist/ast/ast.generated.d.ts` field names rather than from
tree-sitter, because (i) we are going to depend on tsgo anyway for the type oracle, (ii)
TypeScript's AST is the abstract tree our templates are already written against, where
tree-sitter's is concrete, and (iii) tree-sitter-typescript is two years stale. Keep the house
`TypeScript.Expr` for what it is good at (the existing renderer and the existing goldens) and
give it one total map into `Tree`; retire it when `Tree` has a renderer with the same bytes.
This is an *imported* table with its own tiny emitter, not an output of `tools/Effect4Gen/Fold.lean`,
which respects the owner's "the TS syntax fragment is not generated".

A note on where the table comes from, now that both candidates are on the table. Both
`node-types.json` (324 node types, named fields, machine-readable, importable, two years stale)
and `ast.generated.d.ts` (TypeScript's own, abstract rather than concrete, in lockstep with the
compiler we already depend on, but a `.d.ts` rather than a data file) are viable imports. I
recommend TypeScript's, for the three reasons above, and I would keep `node-types.json` in mind
as the fallback if we ever need to read foreign code that our profile cannot parse. Either way
the table is checked in as data, with a `#guard` on its shape, and a small emitter turns it into
`Kind`, `Field` and the typed views. Do not hand-write it: 324 rows is exactly the size where
hand-writing produces a table that is 90% right and silently wrong.

**(b) Render in Lean; get positions from the same fold.** Do not move rendering to the host.
`ts.createPrinter` is only in `tsc`, not `tsgo`; it adds semicolons and its own parenthesisation,
which would break every golden; and moving the renderer to the host puts the byte-determinism
claim outside Lean. Instead make the renderer a fold into an annotated, measured carrier
(`Marked P` of §5 as the minimum, the `Doc` of §5b if the layout engine is also wanted) and
define `Render.expr = text ∘ render`. Positions then come out of the same traversal, and the host is
used only to *check* them: parse the Lean-rendered text with tsgo and assert that every marked
span is exactly `(getStart(), getEnd())` of the node the mark names. That check is the
isomorphism statement, executed, without ever depending on a second printer.

**(c) Making Lean's tree and the host's parse comparable.** Three concrete gaps, all fixable in
the table rather than in code:
- **Qualified identifiers.** `ident "Effect.succeed"` must become
  `node PropertyAccess [expression: ident "Effect", name: ident "succeed"]`. Otherwise no span
  for the head sub-identifier exists and the trees are not comparable.
- **Generic calls.** `call (generic f ts) args` must become one `CallExpression` with a
  `typeArguments` field.
- **Parentheses.** Our renderer emits none and our image needs none; state that as a lemma
  (`no printed tree requires parentheses`), and compare host parses modulo
  `skipOuterExpressions` so that a future change is caught rather than silently accepted.
  Numeric and string literal forms are already fixed by the renderer's `quoted` and
  `toString`; add a guard that every printed string is ASCII, which makes UTF-16 offsets equal
  byte offsets and removes finding 4 entirely.

**(d) The template table.** One row per `(constructor, classifier)`, each row a `Tm Slot` over
the `Tree` signature, with `Slot = (argIndex, cut, insertions)` exactly as `Forms.Template`
already does. Generate the binder columns from `tools/Effect4Gen/binders.json` so the printer's
`n + 1` and `n + 2` cannot drift from `Node.binders`. Keep `Forms.all` as it is; it is already
this shape and it already has a per-row guard.

**(e) The theorems to state.** In this order, each one cheap given the previous:
1. `Tmpl` is linear, non-collapsing and pairwise disjoint on the image. Decidable check on the
   table, discharged by `decide`.
2. `unTmpl (tmpl c args) = some (c, args)` per row. One `rfl` per row, generated.
3. `read (print e) = ok e` for `readable e`, by induction using (2). Replaces
   `Read.lean:1750`'s 190 lines with one proof.
4. `print (read x) = ok x` for `x` in the reader's image. Replaces `Read.lean:2908`.
5. `text (render t) = Render.expr t` (fusion), so the positioned and plain renderers are one.
6. `(e, s) ∈ Fmt` unambiguity (§8), from (1) and the renderer's injectivity on the image.

**(f) The diagnostics harness.** Concretely:
- One module per program, the existing `importHeader`, written under `.lake/tsdiag/programs/`.
- One `tsconfig.json` emitted from `HostConfig` (§10), hashed into the result.
- One `node` script using `@typescript/native-preview`'s sync API: open the project, take a
  snapshot, call `getSemanticDiagnostics()` once for the whole program, write TSV of
  `(program, pos, end, code, text)`.
- Map each diagnostic to a `Tree` path by containment using `getTokenAtPosition` /
  `findPrecedingToken` from `dist/ast/astnav.d.ts`, then to an `Eff` path through the template
  table's inverse, then compare with `Api.blame`.
- Report three numbers per program: agree (same `Eff` path), contained (the TS span is inside
  the blamed node's span but not equal), and disagree.
- The starting table, from §10 and §11, with the codes actually observed:

| `TypeReason` | codes | confidence |
| --- | --- | --- |
| `term t` (unbound level) | 2304 | high, stable across all configs |
| `term t` (atom at wrong argument types) | 2345, 2769 | high |
| `term t` (wrong argument count) | 2554 | high |
| `requestNotSubtype` | 2345, 2769 | high |
| `predicateNotBool` | 2345, and 2872/2873 as advisory | medium |
| `notFiber`, `scopeExpected`, `natExpected`, `listOfFibersExpected`, `contextExpected`, `snapshotExpected`, `exitExpected` | 2345 | high |
| `valueNotSubtype` | 2345 | high |
| `errorNotAdmitted` | **none** | TypeScript has no counterpart; this is the 25-program gap |
| `breakOutsideLoop` | 1105 at module level, **1107** inside a function | high; 1105 is unreachable from our printed image, which always nests in `function*` |
| `returnNotLast` | none | unreachable in the printed image |
| `outsideDomain`, `notAsync`, `serviceUnknown`, `layerReference`, `mergeAllEmpty` | none | printer-side or table-side, never reaches the host |
| the declaration annotation | 2322 without `exactOptionalPropertyTypes`, **2375** with it | config-dependent |

  Note that `1105` is the code the brief asked me to verify and it is the *wrong* one for our
  image: a `break` in a printed generator body gives `1107`, because the enclosing function is
  the generator. Tested both ways.

**(g) A `Doc` package, and the containment tree as one more fold.** Stand up a small `Doc`
package (§5b) with `cat`, `nest`, `line`, `choice`, `annot`, a product `Measure`, and two
policies. `lean4-typescript`'s `Render` becomes a `Doc`-valued fold with the syntactic policy,
so the goldens do not move; `lean4-effect4` gets positions from the annotations, and
`Projection.ContainmentTree` of `docs/ALGEBRAIC-LAYOUT-SPECIFICATION.md` §3.4 becomes a second
`Doc`-valued fold over `Eff` sharing the same path annotations. Keep `Glue`, `Envelope`, `Tile`
and `FiberSpan` out of it; those are the two-dimensional algebras and they share only `Measure`.

**(h) Tree-sitter, if at all, at the host boundary only, and below the existing binding.**
The trust gate (`AGENTS.md:62`) forbids `extern` under `src/Effect4` and `Test/`, so a
tree-sitter parse can only run in a `Tools` driver. That is fine and it is the estate's standard
shape (`tools/Tools/Corpus.lean` writes files that the pure model reads). The interchange should
be one JSON record per named node carrying `path`, `kind`, `field`, `index`, `startByte`,
`endByte` and the token text for leaves (§4b(4)). Build that on `TreeSitter.FFI` directly;
`GrammarSpec`, `Extract` and `SourceMap` are a code outliner and solve a different problem.
Confirm the v4.32 to v4.33.1 toolchain step with one `lake build` before depending on it.

**(i) What not to build.** No Adapton, no Salsa, no finger tree, no GumTree-style move
detection, no second printer on the host, no lens framework, no second-order signature, no reuse
of `Effects.Program` as the syntax carrier, no `Declaration`/`SourceMap` layer, and no
`node-types.json` model until something actually needs to read foreign TypeScript that the
profile cannot already read.

---

## 13. Staged plan

**S0. The agreement lane (half a day, no design commitment).** Land the corpus diagnostics run
of §11 as a lane: emit modules, emit the tsconfig from a Lean `HostConfig`, run `tsgo` once,
record the TSV, and pin `lean typed ⇒ tsgo clean` at 408/408 plus the 25 named exceptions.
*Risk: none. This is pure measurement and it protects everything after it.* It also answers
"is `tsgo` native enough" with a number: 0.2 seconds. Two one-line fixes belong in the same
commit: make the emitted header comment ASCII (§5b(4)), and add the guard that every printed
program is ASCII, so the offset-unit hazard is closed before any position work starts.

**S1. `Doc` and the fusion lemma (two days).** Stand up the `Doc` package of §5b with the
product `Measure` and the syntactic policy, make `Render.expr` the `text` projection of a
`Doc`-valued fold, prove the fusion lemma and the policy-independence lemma. No behaviour
changes; the goldens must be byte-identical. *Risk: the `containsNewline` decisions read
rendered children, so the algebra must be over the measure, not over `String`; if any layout
decision turns out to depend on something other than `lines > 0`, the measure grows. I read all
of `Render.expr` and found only that. Second risk: standing up a fourth Lean package has a
fixed cost in the family layout; if that cost is not wanted this week, put `Doc` inside
`lean4-typescript` with a clear note that it will move, and take the smaller `Marked P` of §5
instead of the full `Doc`.*

**S2. The span check against tsgo (one day).** For each printed module, assert that each `Eff`
path's `Marked` span equals `(getStart(), getEnd())` of the corresponding tsgo node. This is
where the qualified-identifier and generic-call mismatches of §12(c) will bite; expect to fix
the mapping, not the renderer. *Risk: the UTF-16 versus byte question. Guard that the printed
image is ASCII and the risk disappears.*

**S3. The blame-to-code map (one day).** Now that spans exist on both sides, map each diagnostic
to an `Eff` path and compare with `Api.blame`. Publish agree/contained/disagree per program.
*Risk: TypeScript often blames a different node than we do (it blames the declaration name for
2322, the argument for 2345). "Contained" is the right relation to aim for, not "equal".*

**S4. `Tree` and the template table (three to five days).** Introduce `Tm`/`Tree` (§9, §12a),
port the printer to a table of `Tm Slot` rows, keep `TypeScript.Expr` and a total map into
`Tree` so the old renderer and goldens still run. Prove (1), (2) of §12(e). *Risk: this is the
big one. `print` has 27 plus 19 plus the row shapes worth of rows; getting the classifier right
for `catchIf`, `provideLayer` and `printRow` is the fiddly part. Mitigation: land the table
beside the existing `print` with a `#guard` that they agree on every corpus program before
deleting anything.*

**S5. The generic reader (three to five days).** Derive `readEff` from the same table. Prove (3)
and (4). This is where the 3531 lines go away. *Risk: `readable` is not going away; it is the
domain restriction and it will still be hand-written, though it should shrink. The `Effect.suspend`
three-way ambiguity needs a deterministic tie-break in the matcher, and that tie-break is the one
place where "non-unifiable templates" is false and a side condition is needed.*

**S6. The host reader from the same table (two days).** Export the table to `ts/eff` and replace
`read.ts`'s hand-written clauses with the generic matcher over oxc or over tsgo's AST. *Risk: the
table is in terms of `Tree` kinds; oxc is ESTree and tsgo is `SyntaxKind`. One normalisation per
engine, which is the honest cost and is smaller than the 1566 lines it replaces.*

**S7. Diff and incremental (two days, only if wanted).** `Patch`, `diff`, `apply`, the two
theorems, and the width-shifting incremental render of §7. *Risk: none technical; the risk is
that it is built before anyone needs it. I would defer it until the authoring surface has an
edit operation.*

**S8. The containment-tree projection (one day, any time after S1).** A second `Doc`-valued fold
over `Eff` producing `Projection.ContainmentTree` with the same path annotations. This is the
cheapest possible demonstration that the `Doc` investment pays for more than one consumer, and
it gives the agent surface a program view it does not have.

Tree-sitter is deliberately absent from the plan. If the owner wants a third recogniser for
foreign code (not for our printed image), it slots in at S6 as one more normalisation, built on
`TreeSitter.FFI` in a `Tools` driver with the JSON interchange of §4b(4), and its
`node-types.json` is worth importing at that point and not before. The prerequisite check is one
`lake build` of the binding under our v4.33.1 toolchain.

---

## 14. Where I disagree with the derivation

1. **"One template per Eff constructor."** False today. It is one template per
   `(constructor, classifier)` and the classifier is a decidable function of the non-recursive
   arguments. Say so, because the classifier is what makes the table finite rather than the
   constructor.
2. **"Templates of distinct constructors are pairwise non-unifiable (a decidable check on the
   finite table)."** False for `suspend` / `branch` / `whileLoop`, which all print under
   `Effect.suspend`. The decidable check that is actually true is disjointness *on the image*,
   which needs the image characterised. This does not sink the plan, but pretending the naive
   check passes would make the first proof attempt fail in a confusing way.
3. **"`print = cata_F (subst ∘ σ)`."** Only after the carrier is fixed as
   `Nat → Except PrintRefusal (Tm ∅)`. The `Nat` is an inherited attribute and this estate has
   already ruled that an inherited attribute is an exponential carrier
   (`docs/STATE.md`, the universal-algebra refactor). Write the equation with the exponential
   carrier explicit or it will be re-derived wrongly.
4. **"Let TypeScript's printer be the reference renderer."** I recommend against it. `tsgo` has
   no printer; `tsc`'s adds semicolons and parentheses; and moving the renderer off Lean moves
   the determinism claim off Lean. Use the host's *parser* as the reference, never its printer.
5. **"The derivative of the signature functor gives one-hole contexts, which are the paths
   already generated."** Right in spirit, but the derivative is `Node.child`/`Node.setChild`
   (already generated, `NodeLenses.lean`) and the paths are its iterate. There is nothing new to
   build for diffing; the whole differ is thirty lines on top of what exists.
6. **"Rows and derived forms are template families indexed by table data, which already exist as
   data."** Right, and stronger than stated: `Forms.all` is already a `Tm Slot` table in
   disguise, complete with per-row example guards. The new table should be a superset of it in
   the same shape, so that `Forms` becomes rows of one table rather than a parallel mechanism.
7. **"Each AST node is an effect / a future message."** The free-monad reading is right and
   useful (§9), but the specific reuse it suggests, `Effects.Program`, is wrong: that free monad
   has functional continuations and by its own docstring has no decidable equality or
   serialisation, both of which the printed tree must have. Build the first-order `Tm` instead.
8. **"Model `G` in Lean from tree-sitter's node types, so a reader or printer in TypeScript or
   OCaml is generated from the same table."** Half right. The *table* is the right idea and the
   generator story is real (`ocaml-tree-sitter-core` generates a typed OCaml CST from
   `grammar.json`). But tree-sitter's tree is concrete, not abstract, so a Lean model of it is a
   model of TypeScript's *surface*, including parentheses and punctuation, which is one more
   normalisation layer between the templates and the text, not one fewer. And the grammar is
   two years stale while the compiler we already depend on ships its own field table in lockstep.
   Take the table from TypeScript, keep tree-sitter for foreign code.
9. **"The lean4-tree-sitter binding gives us typed grammar schemas."** It gives us nine
   hand-written outliner schemas of fourteen to twenty declaration node types each, a vendored
   TypeScript parser, and an FFI with byte offsets and `childByFieldName`. The FFI is genuinely
   useful; `GrammarSpec`, `Extract` and `SourceMap` solve a different problem (symbol-to-symbol
   source maps for a code generator) and should not be adopted.
10. **"One `Doc` for both the house style and the elastic engine."** Agreed, and stronger than
   the main session put it: the deterministic policy is not a compromise, it is the choice
   function that ignores its state, and "positions never depend on a viewport" becomes a
   one-line lemma about the policy. But `Doc` must not absorb `Glue`, `Envelope`, `Tile` or
   `FiberSpan`; those are two-dimensional and share only the measure monoid.

---

## Appendix: evidence log

Executed on this Mac, 2026-09-16:

- `tsgo --version` → `7.0.0-dev.20260629.1`; `tsgo --help --all` flag list (no JSON output, no
  AST dump, no LSP subcommand on the CLI).
- `tsgo -p <cfg> --pretty false` on six hand-written probes; the same probes under `tsc` 5.9.2.
  Identical output.
- The five-config matrix of §10 under `tsgo`, three of them also under `tsc` 5.9.2.
- `node` against `@typescript/native-preview/dist/api/sync/api.js`: snapshot, project, program,
  `getSemanticDiagnostics`, `getSourceFile`, `forEachChild`, `getStart`, a second snapshot after
  a file edit.
- An AST dump with `formatSyntaxKind` over a probe covering every house-fragment former.
- A UTF-16-versus-UTF-8 offset probe.
- `node` against `typescript@5.9.2`: `createPrinter`, `printNode`, `printFile`,
  `createSourceFile`, parenthesisation, idempotence, literal spelling, `ParenthesizedExpression`
  retention.
- The 408-module corpus run and the cross-tabulation of §11.
- `npm view tree-sitter-typescript version time.modified`, `npm view web-tree-sitter version`,
  `npm view tree-sitter version`.

Scratch files are under `/private/tmp/ts-probe` and `/private/tmp/ts-corpus`; nothing was written
into the repository except this note.

Read in the repository: `src/Effect4/Program/Eff.lean`, `src/Effect4/Program/Fold.lean`,
`src/Effect4/Program/NodeLenses.lean`, `src/Effect4/Program/Node.lean`,
`src/Effect4/Program/Typing/Blame.lean`, `src/Effect4/Codegen/Print.lean`,
`src/Effect4/Codegen/Read.lean`, `src/Effect4/Codegen/Forms.lean`,
`tools/Effect4Gen/Fold.lean`, `.lake/packages/typescript/TypeScript/Syntax.lean`,
`.lake/packages/typescript/TypeScript/Render.lean`,
`.lake/packages/effects/Effects/Algebra/{Signature,Program,Universal}.lean`,
`harness/truth/run-truth.ts`, `harness/truth/tsconfig.json`, `harness/truth/prelude.ts`,
`ts/eff/read.ts`, `ts/eff/ingest/oxc.ts`, `generated/corpus-index.tsv`, `docs/STATE.md`,
`AGENTS.md`, `docs/ALGEBRAIC-LAYOUT-SPECIFICATION.md`, `docs/ALGEBRAIC-LAYOUT-ENGINES.md`.

Read outside the repository:
`/Users/pooks/Dev/foldlab/.staging/treesitter/clones/lean4-tree-sitter` at v0.2.4
(`README.md`, `lean-toolchain`, `lakefile.lean`, `ffi/language_definitions.json`,
`TreeSitter/FFI/{Types,Language,Node}.lean`, `TreeSitter/Types/{GrammarSpec,Declaration,CodeLocation}.lean`,
`TreeSitter/Grammars/TypeScript.lean`, `TreeSitter/SourceMap/Types.lean`, the module inventory),
and the `@typescript/native-preview` and `typescript@5.9.2` packages named above. The binding was
not built: that would start a second Lean process.

Fetched: `tree-sitter-typescript` `node-types.json`; the tree-sitter advanced-parsing
documentation; the `typescript-go` `internal/ast/ast.go` node representation
(`type Node struct { Kind; Flags; Loc core.TextRange; id; Parent; data nodeData }`, uniform
kinded node with a data pointer and `ForEachChild` on the data interface); search results for
Rendel and Ostermann 2010, Matsuda and Wang 2013/2018, Danielsson 2013, Miraldo and Swierstra
2019, and `ocaml-tree-sitter-core`.

Recalled and not verified in this session: Wadler 2003; Leijen's `wl-pprint`; Haskell
`prettyprinter`'s `Doc ann` and `SimpleDocStream`; OCaml `Format` semantic tags; Roslyn red/green
trees; `rowan`; SwiftSyntax; Chawathe et al. 1996; Falleri et al. 2014; Lempsink, Leather and Löh
2009; McBride 2001; Huet 1997; Reps, Teitelbaum and Demers 1983; Hammer et al. 2014; Hinze and
Paterson 2006; Swierstra 2008; Plotkin and Pretnar 2009; Fiore, Plotkin and Turi 1999; Fiore and
Hur 2010; Hamana 2004; Herman and Wand 2008; Foster et al. 2005; Bohannon et al. 2008; Sewell et
al. 2007.

Recalled and not verified in this session, added for §5b: Bernardy 2017, "A pretty but not
greedy printer" (ICFP 2017); `prettyprinter`'s `SAnnPush`/`SAnnPop`; Wadler's `flatten` laws.

Not verified, and each worth one command:

- Whether `tree-sitter-typescript` parses our printed image with no `ERROR` or `MISSING` node.
  The clone is at `/Users/pooks/Dev/foldlab/.staging/treesitter/clones/tree-sitter-typescript`;
  the check is `tree.rootNode.hasError` over the 408 corpus modules.
- Whether `lean4-tree-sitter` v0.2.4 builds under `leanprover/lean4:v4.33.1`. One `lake build`
  in its own directory, which needs the single-Lean-process rule to be respected.
(The ASCII question is now tested, not open: 0 of 408 corpus programs contain a non-ASCII byte,
and the only one in the emitted modules is an em-dash in `run-truth.ts`'s header comment.)
