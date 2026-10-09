# JavaScript's syntax hazards in our printer: an audit after js_of_ocaml

The owner's request of 2026-10-09, by voice: audit js_of_ocaml for the JavaScript and TypeScript
semantics that every printer must handle. Do it before more of TypeScript's printing is
formalized. Look for code-as-data practices that make printing foolproof and reusable, and for
metadata that shows how each printed string was made. Then hold the rules as proved laws in our
folds. If the standard can be vendored, prove the printer conforms to it.

This note compares js_of_ocaml's printer with ours, and probes ours on each hazard. It places the
repairs as laws of the TypeScript algebra (`tools/Tools/Code/TypeScript.lean`, slice F of
`docs/research/2026-10-09-view-algebra-audit.md`).

## 1. The source read

js_of_ocaml-compiler 5.7.1, as the opam switch `effect4` installs it
(`~/.opam/effect4/lib/js_of_ocaml-compiler/`). The files read: `javascript.ml` (the syntax),
`js_output.ml` (the printer), `reserved.ml`, `source_map.ml`, `js_traverse.ml`, `js_assign.ml` and
`var_printer.ml`. They are read in place and cited by file and function. Nothing is downloaded or
vendored.

## 2. What js_of_ocaml does, and where we stand

| Concern | js_of_ocaml | Our printer (lean4-typescript `Render.expr`, the house) |
| --- | --- | --- |
| Precedence | each operator has its own level and the levels its operands need (`js_output.ml`, `op_prec`); `expression (l : prec)` prints a child at the level its parent needs, in parentheses when it binds looser | no levels: a child is written as it is |
| An arrow's object body | parenthesized (`js_output.ml`, `EArrow`: "Should not starts with '{'") | written bare: a block |
| A callee of `new` | a call in parentheses (`ECall`: "Need parentheses also if within an expression [new e]") | written bare, and documented as `new f()(x)` |
| Numbers | `Num` keeps the canonical text; `of_float` writes the shortest decimal that reads back to the same float, and `NaN`, `Infinity`, `-0.`; a negative number, or a number before a dot, takes parentheses | integers as text; a float as a `DataView` over its exact bytes: exact, not readable; no parentheses |
| Strings | `\b \t \n \f \r`; `\0` only before a non-digit (else `\x00`, since `\01` is an octal escape); other controls as `\xHH`; `</` as `<\/`; the quote that needs fewer escapes (`pp_string`) | the delimiter, the backslash and the line terminators are escaped; other controls stay raw |
| A statement's first token | an expression statement never starts with `{`, `function`, `class`, `let [` or `async function` (the `Expression_statement` cases) | not checked |
| Automatic semicolons | semicolons written; `return`, `yield`, `throw`, `break`, `continue`, `++` and `--` keep their operand on their line (the note at the head of `js_output.ml`) | no semicolons, as Effect's own source writes it; a statement that starts with `(` or `[` joins the line before |
| Names | an identifier is a source string or an abstract variable (`ident = S of ident_string \| V of Code.Var.t`), named last (`js_assign.ml`, `var_printer.ml`), never a keyword, a strict-mode name or a provided global (`reserved.ml`: `keyword`, `provided`) | a program's variables are de Bruijn indices that the printer names `a0`, `a1`, …: abstract, as js_of_ocaml's are. Other names pass `targetIdentifier`: ASCII, and a reserved list without `eval` and `arguments` |
| Property names | an identifier, a string, a number or a computed key (`property_name`) | `KeyForm`: plain, quoted, computed. The generator routes `__proto__` through a computed key or `Object.fromEntries` (`Effect4.Codegen.Record`, `Effect4.Codegen.Schema`) |
| Provenance | every identifier, call and statement holds a location; the printer writes a source map (`source_map.ml`, `vlq64.ml`) | none yet |
| Traversal | open-recursion classes for map, iteration and folds, with free variables and renaming (`js_traverse.ml`) | the generated fold of the syntax (`TsFold`): an algebra and its uniqueness |

Two of js_of_ocaml's practices we already share: abstract variables, named at the end, so no
generated name is captured; and key forms for property names. Our traversal is stronger than
its classes: a fold with a uniqueness law, from which agreements follow (`flat_fold_expr`).

## 3. The probe: the house on each hazard

A finite probe (scratch, `hazards.lean`) prints each shape through the pinned renderer.

| Shape | Printed | Verdict |
| --- | --- | --- |
| a lambda whose body is an object | `(x) => { a: 1 }` | another meaning: a block, and the lambda returns `undefined` |
| a conditional as callee | `c ? f : g(x)` | another meaning |
| a conditional as a member's target | `c ? a : b.length` | another meaning |
| a lambda as callee | `(x) => x(1)` | another meaning: the call is the body |
| a conditional as a conditional's test | `a ? b : c ? d : e` | another meaning: it nests right |
| a negative number as a member's target | `-1.x` | a syntax error |
| a number as a method's target | `5.toString()` | a syntax error |
| a call as `new`'s callee | `new f()()` | as documented: constructs `f`, then calls the result |
| empty type arguments | `f<>` | a syntax error |
| a generator as a statement | `function* () {` … | a syntax error |
| an object as a statement | `{ a: 1 }` | another meaning: a block with a label |
| a lambda after a `yield*` line | `yield* f` then `(a) => a` | the lines join: `yield* f(a) => a`, a syntax error |
| `__proto__` as a plain object's key | `{ __proto__: 1 }` | another meaning: it sets the prototype |
| an integer-like key | `{ b: 1, 2: 2 }` | its keys enumerate as `2`, `b`, not as written |
| a control character in a string | raw `NUL`, `BEL` | legal, and invisible |
| `eval`, `arguments` as names | accepted by `targetIdentifier` | a syntax error when bound in a module |
| `Effect.void` | refused by `qualifiedIdentifier` | too strict: a member may be a reserved word |

**Live or latent.** A second probe (scratch, `hazardFold.lean`) detects these shapes as a monoid
fold of the generated algebra (`foldMap_expr`). It finds none in the eight corpus modules. The
generator builds conditionals at 15 sites and lambdas at 47 (`src/Effect4/Codegen`). The truth
lane's tsgo checks the printed corpus, and a type error catches many of these shapes. A shape that
no corpus program reaches is unchecked. So the hazards are latent, not proved absent.

## 4. The repairs, as laws of the folds

Each repair is a property of an algebra, proved once by its fold. The house's algebra is the
pinned renderer (`render_eq_expr`), so a repair to the house lands upstream, in lean4-typescript.
The readable layout inherits it through the flat print's map of algebras (`flatHom`).

| Slice | What | Law | Consumer |
| --- | --- | --- | --- |
| J1 | precedence: the house prints each child at the level its parent needs, in parentheses when it binds looser; the levels transcribed from ECMA-262's expression grammar | the printed text reads back to the tree (J9); before J9, a predicate `Grouped` that each printed child meets its parent's level, proved by fold induction | every conditional, lambda, member and call the generator builds |
| J2 | a statement's first token, and automatic semicolons | no printed statement starts with `{`, `function`, `class`, `let [`, `(`, `[` or a template; or a leading `;` where one does | generators and blocks |
| J3 | names: `eval` and `arguments` reserved; a member may be a reserved word; a binding never shadows a provided global | `targetIdentifier` refuses each, and a member's profile is its own | `targetIdentifier`, `qualifiedIdentifier`, the binding check |
| J4 | keys: an integer-like key takes the route `__proto__` takes | a printed object's own keys enumerate in written order | records and schemas |
| J5 | numbers: the shortest decimal that reads back to the same float, with `-0`, `NaN` and `Infinity` in their own forms | reading the decimal gives the bits back (a finite check against the host first) | readable modules |
| J6 | strings: controls escaped as js_of_ocaml escapes them | the escape reads back to the string | readable modules |
| J7 | empty type arguments refused | the generic constructor's arguments are not empty | the printer's input check |
| J8 | provenance: a `tag` in `Doc` that holds a node's program address; the layout writes a source map | every printed character maps to the node that wrote it | the code plane's links to the tree; a browser's tools |
| J9 | the credential: a reader of the printed fragment in Lean, its grammar transcribed from ECMA-262, each rule citing its production | an exact embedding: reading the print gives the tree back, on the fragment | the claim that our printing conforms to the standard |

J9 is the owner's credential. It is an exact embedding in AGENTS.md's sense: total on its
domain, `read (print e) = some e`, and exactness modulo the layout's whitespace. TypeScript has no
current formal grammar, and tsgo stays the oracle for types. J9 covers the expression and
statement syntax that ECMA-262 defines and TypeScript inherits. J1's levels are J9's premise.

The source map format (J8) is the one browsers read, revision 3. ECMA-426 standardizes it
(recalled, not read here). js_of_ocaml writes it with base-64 variable-length numbers
(`vlq64.ml`).

## 5. Rulings and permissions the owner must give

1. **Vendoring ECMA-262** (J9): which edition, from the published HTML or the `tc39/ecma262`
   source, under `vendor/`. A download needs the owner's yes, with its file, source and size.
2. **Readable numbers** (J5): the shortest decimal in a readable module, with the exact bytes kept
   for the checked one; or the exact bytes everywhere.
3. **Upstream** (J1 to J7): repairs to the house land in lean4-typescript, at a new version that
   this repository pins.

## 6. What this note does not establish

- The probes are finite: 17 shapes, and eight corpus modules. Neither proves any shape absent from
  the generator's output.
- The rows about js_of_ocaml describe its 5.7.1 sources as read; they assert nothing about its
  behaviour beyond them.
- No law of section 4 is proved yet. Each is placed with its consumer, as AGENTS.md asks; its
  concept is the exact codecs of `docs/core/semantics.md`, serving R8.
