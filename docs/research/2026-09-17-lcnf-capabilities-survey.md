# The LCNF route today: what it can lower, what it refuses, what a TypeScript target needs (2026-09-17)

Owner's ask, while scouts E and F run: "dig in more into the LCNF and see what our capabilities
are there; make sure it stays apprised of the sugar; our LCNF is really our superpower for
verified semantics." Read off the translator and the rungs, not their docs. Tree at `14f8d4d4`.

## 1. What the route is

Lean's own compiler IR, mono phase, read off the `.olean` (`getMonoDecl?`, `PhaseExt.lean:162`
in Lean; no compilation pass is run here), translated by `OCaml5.Lcnf.translateClosure`
(`src/OCaml5/Lcnf/Translate.lean:1006`, 1,120 lines) into `Ml.Decl` and rendered by
`OCaml5.Ml.Render` into `ocaml/gen/*.ml` (22,104 lines today). Roots are chosen by the driver
(`src/OCaml5/Tools/LcnfGen.lean`); the closure walk enqueues every called global with a cap
(`translateClosure … cap := 60`). The spike record is `ocaml/gen/NOTES.md`: every top-level
function of `Machine/Fibers.lean` — 43 roots, 154 declarations with helpers, 38 types — type-
checks under `ocamlopt` with zero holes. The rule in force: nothing on the OCaml side that is
not made from LCNF (memory `ocaml-only-from-lcnf`).

## 2. What the translator handles (the code walk, `Translate.lean:821-914`)

| LCNF form | target | note |
| --- | --- | --- |
| `let x := v; k` | `let` | `letValueExpr` (`:656`) — constructor applications by `ctorApp` (`:535`, field names from `ctorFieldNames`), projections on structures, calls, literals |
| `fun` / `jp` | local function | `localFun` (`:875`); a join point is a local function, a `jmp` its call |
| `cases` on `Bool` | `if` | both arms or a default (`:848-856`) |
| `cases` on an inductive | `match` with alternative patterns | `altPat` (`:777`); default arm kept |
| `return` / `unreach` | variable / `assert false` | |
| calls to globals | `g' args` and enqueue `g` | the closure; `redArgTarget?`, `wrapperKeep?` strip Lean's wrappers (`:400-431`) |
| builtins | a 50-row table (`builtin?`, `:154`) | `Nat`/`UInt8`/`Bool` arithmetic and comparisons; `Nat.pow` clamped (`powClamped`, `:140`); `Nat.sub` truncated as Lean's |
| stdlib functions | translated from their own mono decls | `List.hasDecEq`, `instDecidableEqProd`, `List.filterTR.loop` came out this way (NOTES §260); a table row only where the stdlib body is an `extern` |
| externs (strings, floats, `IO`) | `Externs.lean` table | a call with no row is a refusal |
| carriers (`List`-like op rows) | `carrierRewrite?` (`:607`), `useAsList` (`:500`) | a carrier without a `to_list` row is a refusal |

Types: `Types.lean` (419 lines) turns inductives and structures into target type declarations,
unboxes trivial structures (`hasTrivialStructure?` read from the persisted verdict), and closes
the type closure with placeholders for types nothing destructs (NOTES §273).

What it refuses, by name (`todo` sites): a projection on a single-constructor inductive that is
not a structure; `cases` on `Bool` with a missing arm; an `extern` with no table row; an
alternative on an unknown constructor; a carrier with no `to_list` op. Six sites. Everything
else in the machine's closure translates.

## 3. The evidence the rungs give (`tools/Conform/**`)

- `Lcnf/Semantics.lean` (561 lines): an evaluator for LCNF itself (`Value`, `Outcome`, `Prim`).
- `Lcnf/SemanticsTarget.lean` (606): an evaluator for the *target* language as read back from
  the emitted syntax (`Expr`, `Pat`, `TValue`, `evalT` at `:424`, `PrimEnv` for the named
  primitive assumptions).
- `Lcnf/Validity.lean` (728), `Lcnf/Rules.lean` (757), `Lcnf/Cases.lean` (721): the validity
  check, the rewrite rules, and the case-site policy — the gate that refused `Run.rowOf` and
  `ServiceDef.receiver` today (`cases-policy.json`).
- `Effect4/LcnfSemantics.lean` (rung 2): the LCNF evaluator against the compiled Lean functions
  on 20,387 vectors. `Effect4/LcnfMl.lean` (rung 3): the emitted OCaml read into the target
  evaluator and run on the same vectors — "the evaluator handles what the translator emits" is
  a checked claim because the reader refuses by constructor name. `Effect4/TargetLeanNative.lean`
  closes the loop against native Lean.

So "verified semantics" today means: a differential on 20,387 vectors between LCNF, the
emitted target, and native Lean — evidence, not a theorem that the lowering preserves the LCNF
semantics. Scout F's question 6 is whether to prove it (CompCert-shaped simulation over
`Semantics` and `SemanticsTarget`, both of which exist as Lean functions) or keep the
differential; the two evaluators being Lean definitions is what makes the theorem statable.

## 4. What a TypeScript target needs that ML did not

Target-independent, reusable as is: the closure walk, `Naming`, `Externs`'s shape, `argsFor`/
`ctorApp`/`altPat`, `Types`' closure, the case-site policy, both evaluators and the vector
lane. Target-specific, to write:

1. **The emitter's syntax.** Emit into the vendored `TypeScript.Expr`/`Stmt` (the `typescript`
   lake package the printer already targets), not strings — then rung 3's reader for the
   TypeScript target is a reader over that AST, as `LcnfMl` reads `Ml.Syntax`.
2. **Sums.** `cases` on an inductive becomes a `switch` on `_tag`, with the *same* tag spellings
   the generated schemas use (`ts/eff/eff.gen.ts`'s `Schema.TaggedUnion` keys are the
   constructor names) — one encoding for the value and for the code that destructs it.
3. **Products.** Structures become objects with `ctorFieldNames` as keys; a trivial structure
   unboxes as in ML.
4. **Join points and tail calls.** JavaScript has no join points and guarantees no tail calls:
   a `jp` becomes a local function (as in ML) but a self-tail-call inside a loop body must
   become a `while (true)` with reassignment, or a trampoline; the machine's stepping functions
   are the case that matters (`Machine/Fibers.lean`'s loops).
5. **Numbers.** `Nat` as `bigint` (exact) or `number` (fast, wrong past 2^53): a policy row, as
   `max_int`/`powClamped` are for OCaml. The wire already fixes `Nat` as JSON numbers with the
   `isInt`/non-negative checks.
6. **Strings and bytes.** OCaml strings are bytes; JavaScript strings are UTF-16. The estate's
   codec is bytes (`Store/Utf8.lean`, strict UTF-8), so string externs need the same rows the
   OCaml table has plus the UTF-16 boundary, or the TypeScript side keeps bytes as `Uint8Array`
   and decodes at the edge.
7. **Externs into Effect.** The `Externs` table for the TypeScript target is where the vendored
   Effect modules enter: a Lean name ↦ an Effect export with its `Entry` (input and output as
   Schema ASTs). This is scout E's Part 4; the table's shape is the OCaml one's.
8. **Laziness.** The machine's functions are pure state transitions (`step`, `advance`,
   `applyReply`), so nothing lowered is an `Effect` value; Effect values appear only where the
   generated code *constructs* programs for the host, through the template table, not LCNF.

## 5. Where the sugar sits relative to LCNF

Upstream, not beside. The authoring sugar, the generated lifts, the forms and any type
generation are metaprograms that *write Lean* (definitions, tables, instances); LCNF lowers the
Lean they wrote. So "apprised of the sugar" means one thing concretely: the roots list. A
metaprogram that adds a definition an agent should be able to call from TypeScript adds it to
the roots, and the closure walk, the case-site policy and the rungs take it from there. The
two powers do not compete: metaprogramming decides *what* exists; LCNF decides that its
TypeScript image *means the same*.

## 6. The three facts to carry into the decisions

- The route is real and total on the machine's closure (six named refusals, none hit by
  `Fibers.lean`); a TypeScript target is an emitter and an externs table on top of shared
  infrastructure, not a second translator.
- The evidence is a 20,387-vector differential between two Lean-defined evaluators; a theorem
  is statable because both evaluators are Lean functions.
- The case-site policy already gates *every* default arm in the compiled code, which is why a
  seat's `| _ =>` was refused today: the LCNF route's gates are already in `make check`.
