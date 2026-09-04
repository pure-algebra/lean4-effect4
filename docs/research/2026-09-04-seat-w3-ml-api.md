# Seat W3 — `OCaml5.Ml` as an API: a clean way to represent OCaml types and generate OCaml code

Status: landed on `main` (base `e1cad67`), 2026-09-04. Not committed.
Seat: W3 of the 2026-09-04 wave. Files owned: `workshop/OCaml5/Ml/*.lean` (new),
`workshop/OCaml5/Render.lean` (refactor), `workshop/OCaml5/MlTest.lean` (new),
`workshop/OCaml5/tools/ml-check.sh` (new), this report.

## 1. Headline

The user asked for "a very clean ability to represent OCaml types / gen OCaml code; clean APIs
for that". What existed was one 1,500-line file grown by a fuzzing spike, in which the OCaml
surface, its renderer, the Lean-description layer, the name mangling and a rewriting pass were
interleaved with the descriptions of one particular avatar.

It is now seven modules with one job each, shaped like the estate's TypeScript target package,
and the descriptions are what is left in `Render.lean`. Two later rulings landed on top of it: the
OCaml-packages plan (`[@@deriving …]` first class, an executable oracle), and the rule that
**everything written in OCaml must be directly representable in the Lean model**, which is now
data — `Ml/Profile.lean` — and a check.

```
$ lake build OCaml5.Render OCaml5.Fuzz OCaml5.MlTest
Build completed successfully (14 jobs).

$ ./workshop/OCaml5/tools/ml-check.sh
ml_fixture 61 declarations, 6546 bytes, 21 rows
ml_deriving 5 declarations
check      OK
profile    OK (carriers-only; 88 values admitted, 15 of 20 modules unmodelled)
laws       the generated carriers depend on:
  Variants.to_rank_declaration_order  unproven — Variants.to_rank is the declaration order …
ocamlc      OK
rows        MATCH (21 rows)
ocamlopt    OK
js_of_ocaml OK
ppxlib      SKIP (no ocamlfind/ppxlib: the effect4 switch is not built yet)
ppx_jane    SKIP (no ocamlfind/ppx_jane: the effect4 switch is not built yet)
ocamlformat SKIP (not installed: the effect4 switch is not built yet)

$ ./workshop/OCaml5/tools/fuzz.sh surface
surface 16 declarations
AGREE surface

$ ./workshop/OCaml5/tools/fuzz.sh avatar
avatar 19 declarations, 2 holes in FrameFiber
ocamlc     OK
ocamlopt   OK
js_of_ocaml OK
run_fiber: IDENTICAL to deep_fibers.ml
frame_fiber: IDENTICAL to deep_fibers.ml
observer: IDENTICAL to deep_fibers.ml
run_event: IDENTICAL to deep_fibers.ml
run_decision: IDENTICAL to deep_fibers.ml
```

Nothing a consumer spells changed. `OCaml5.Fuzz` and `tools/fuzz.sh` are untouched and their
three lanes are green, including the byte diff against the hand-written avatar.

## 2. The API surface

Everything is in `namespace OCaml5.Ml`, so the names a consumer already writes still resolve.

| module | main types | main functions |
| --- | --- | --- |
| `OCaml5.Ml.Identifier` | — | `escString`, `escChar`, `reservedWords` (56), `reservedNames`, `isIdent`/`isLowerIdent`/`isUpperIdent`, `isValuePath`/`isCtorPath`/`isTypePath`/`isModulePath`, `mangleField`, `unmangleField`, `valueName`, `typeName`, `ctorName`, `moduleName`, `tyVarName` |
| `OCaml5.Ml.Syntax` | `ArgLabel`, `Variance`, `PolyKind`, `Ty`, `Pat`, `Expr`, `Arm`, `Effc`, `Param`, `HandlerKind`, `Field`, `Ctor`, `TyBody`, `TyParam`, `TypeDecl`, `Bind`, `ModTy`, `SigItem`, `Decl`, `Module` | `Ty.*` builders, `Pat.*` builders, `Expr.call`/`ignoreE`/`method`, `Param.pos`/`named`/`optional`/`optionalD`, `Ty.beq`, `Ty.mentionsVar`, `Ty.mentionsCon`, `Module.generated` |
| `OCaml5.Ml.Render` | — | `renderTy`/`renderTyAt`, `renderPat`/`renderPatAt`, `renderExpr`/`renderExprAt`, `renderArms`, `renderEffcClauses`, `renderModTy`, `renderSigItem`, `renderDecl`, `moduleText`, **`render : Module → String`**, `opInfo`, `wideAt`, `Module.fileName` |
| `OCaml5.Ml.Reflect` | `LTy`, `Subst`, `FieldKind`, `FieldDesc`, `CtorArg`, `CtorDesc`, `StructDesc`, `InductiveDesc`, `TypeDesc` | `lowerTy`/`lowerTys`, `paramSubst`, `StructDesc.typeDecl`/`decl`/`header`/`holes`/`erasures`/`substitutes`, `InductiveDesc.typeDecl`/`decl`/`header`/`arities`/`erasures`, `TypeDesc.divergences`, **`toTypeDecl`**, `toTypeDecls` |
| `OCaml5.Ml.Check` | `Diag`, `Env`, `TailPosition` | `Env.ofModule`, `patVars`, `checkExpr`, `checkPat`, `checkDecl`, **`checkModule : Module → List Diag`**, `Module.wf`, `WellFormed` (decidable), `checkReport`, `rawSites` |
| `OCaml5.Ml.Passes` | — | **`mutate`**, `residue`, `mutated`, `hasUpdates` |
| `OCaml5.Ml.Profile` | `Law`, `LibVal`, `LibModule`, `Profile`, `Usage` | `laws` (49), `lawOf`, `lawNames`, `unprovenLaws`, `allConstructs`, `admittedModules` (20), `bannedModules` (12), `estateProfile`, `carrierProfile`, `derivedNames`, `derivedFunctions`, `usageOf`, `splitPath`, `Profile.refusals`/`modelled`/`lawNames` |

and, in `Ml.Check`, the profile half: **`Check.profile : Profile → Module → List Diag`**,
`Check.inProfile`, `Check.lawsUsed`, `Check.lawReport`; and, in `Ml.Reflect`, the reverse
direction: `InvSubst`, `leanTypeName`, `leanCtorName`, `liftTy`, `liftFaithful`,
**`ofTypeDecl`**, `ofSigItems`, `ofModTy`.

Seven modules, 4,459 lines, 136 `#guard`s; `MlTest` adds 740 lines and 34 more. `Ml/*.lean`
imports nothing outside `Ml/`; the dependency order is
`Identifier → Syntax → Render → {Reflect, Passes, Profile} → Check`.

### What the surface covers

Types: variables, postfix constructor application, arrows, **labelled and optional arrows**,
tuples, **polymorphic variants** (`[ ]`, `[> ]`, `[< ]`), the anonymous `_`, and `(t as 'a)`.

Patterns: wildcard, variable, int/string/char/float literals, constructor, record, **partial
record** (`{ f = p; _ }`), tuple, list, `::`, `as`, or-patterns, `(p : t)`, **`exception p`**,
polymorphic-variant tags, `lazy`.

Expressions: literals (with the O3 float caveat, below), constructors, application, **labelled
application**, infix operators, `fun` over plain names and over full `Param`s, `function`,
`let`/`let rec … and`/`let` over a pattern, `let open … in`, sequencing, `if`/`if … then`,
`match`, `try`, records, functional update, field get and set, tuples, lists, arrays with `.(i)`
and `.(i) <-`, refs, `raise`, `assert`, `lazy`, `while`, `for`/`downto`, type annotation, a
`hole`, verbatim `raw`, and the effect forms: `Effect.perform`, `Effect.Deep.continue` and
`discontinue`, `match_with` and `try_with`, `Effect.Shallow.continue_with` and
`discontinue_with`, **the `Deep`/`Shallow` handler records as first-class expressions**, and the
raw `%reperform`.

Structure items: types (with `and`-groups, `mutable` fields, GADT constructors, inline records,
abbreviations, abstract, extensible `..`, variance-annotated and phantom parameters,
`[@@deriving]`/`[@@warning]`), exceptions, `type _ Effect.t +=` and the general `type t +=`,
values, externals with primitive names, `open`, `include`, modules, functors, functor
application, module types and signatures, floating attributes, and a `Module` root with
`render : Module → String`.

Every constructor's docstring names the OCaml 5.1.1 manual section it renders.

### The four decisions worth naming

**Precedence, and why it is safe.** Round two parenthesised aggressively, on the stated grounds
that "a wrong precedence table is a silent miscompile". `Ml/Render.lean` now carries a table of
18 levels, read off an operator's **first character** exactly as §11.7 does, so a generator may
invent an operator and the renderer places it correctly. The table is conservative in one
direction: every level is the manual's or lower, and a level that is too low only ever adds a
parenthesis. A bug in it is a redundant parenthesis, never a reparse. The evidence that it is
right is executed: `fuzz.sh surface` compiles and runs the shape probe on all three hosts and its
rows still AGREE, and `ml-check.sh` does the same for a fixture that uses every form.

The visible payoff is the one the P5 report §11.4 complained about: `interruptRecord` now renders
`f.frame.interrupted_cause <- …` where it used to render
`((f).frame).interrupted_cause <- …`, which is A0's own spelling.

**`Expr.float` takes source text, not a `Float`.** OCaml's three backends do not agree on the
decimal spelling of a binary64 and `js_of_ocaml` reconstructs a JavaScript number from the
literal's digits, so a generator that formats a float itself generates a program whose meaning
depends on the host. The constructor therefore takes the literal's characters and the renderer
emits exactly those bytes; a hexadecimal literal (`0x1.8p1`, which the fixture uses) always
round-trips. This is the same reasoning that gave `TypeScript.Expr` a `float64Bits` rather than a
`Float`.

**A declared type parameter beats the substitution table.** `StructDesc.leanParams` and
`InductiveDesc.leanParams` are prepended to the description's `Subst` as
`(p, Ty.var (tyVarName p))`, so `ν` is `'nu` inside a declaration that binds it and whatever the
table says everywhere else. Without this a description could not have parameters at all, because
`lowerTy` has no other way to tell a parameter from a carrier.

**`FieldKind` is four-valued.** `literal` (= `keep`), `substitute`, `erased`, `hole`, from P5
§11. `erased` is new: it is the divergence that obliges nobody, where a `hole` is a promise that
a human writes something. Both are listed (`StructDesc.holes`, `StructDesc.erasures`,
`TypeDesc.divergences`) so a check can insist.

### Attributes and derivers are first class

The plan's ruling is that every generated carrier carries
`[@@deriving sexp, compare, equal, hash, fields, variants]`, so the attribute is not one more
string in a list:

* `TypeDecl.derivers : List String` renders as **one** `[@@deriving a, b, c]`, which is what
  `ppxlib` parses and `ppx_jane` expects, and `TypeDecl.attrs` renders the rest one `[@@…]` each,
  after it. `janeDerivers`, `janeRecordDerivers` and `janeVariantDerivers` are the estate's sets
  (`fields` is only legal on a record and `variants` only on a variant);
* `Field.attrs` and `Ctor.attrs` render the single-`@` form, which is how `[@default 0]` and
  `[@sexp.opaque]` steer the derivers per member;
* `Decl.attrD` wraps any declaration, `Decl.floatingAttrD` is `[@@@warning "-a"]`, and
  `Bind.attrs` is `[@@inline]` on a `let`.

It is also the one place the *checker* had to learn something new. `Profile.derivedNames` says
what each deriver puts in scope for a type of a given name — `compare_point`, `point_of_sexp`,
`hash_fold_color` — and `Env.ofModule` adds them, so a generated call to `compare_run_fiber`
is in scope with nothing declaring it and a call to `compare_run_fibre` is still `unbound-value`.

## 3. The profile: what the Lean model can represent

`Ml/Profile.lean` (922 lines) is the ruling as data. Three lists and a checker.

**The construct set.** `allConstructs` is one tag per syntactic form — `expr.reperform`,
`decl.moduleD`, `ty.polyVariant` — and a `Profile` names the subset it admits. A form outside it
is `profile-construct`. The estate's profile admits all 90 tags, because `Ml.Syntax` is already
the fragment a runtime port needs; a *narrower* profile is what a caller writes when it wants,
say, no `lazy` (`MlTest` uses exactly that to exercise the code).

**The library surface.** 20 modules, 88 values. Each value carries its signature as `Ml.Ty` and
the **stable names** of the laws it is relied on. A qualified name whose module is unlisted is
`profile-module`; a listed module with an unlisted value is `profile-value`.

**The refusals.** 12 modules whose *presence* is the failure — nothing the Lean semantics says
about a value survives them: `Obj`, `Marshal`, `Domain`, `Thread`, `Mutex`, `Unix`, `Sys`,
`Random`, `Gc`, `Weak`, `Printexc`, `Lazy`. Naming one is `profile-banned`.

### Per admitted module: does its Lean semantic carrier exist?

Five of twenty. The other fifteen are **refusal rows**: admitted into generated OCaml because the
port needs them, unmodelled in Lean.

| module | values | Lean semantic carrier |
| --- | --- | --- |
| `Base.Option` | 4 | **`workshop/OCaml5/Value.lean`** — `Value.none`, `Value.some` |
| `Base.Int` | 5 | **`workshop/OCaml5/Value.lean`** — `Value.int` (with `Int.wraps_63`: OCaml's is 63-bit and `Nat` is not) |
| `Effect` | 1 | **`workshop/OCaml5/Effect.lean`** — `Term.perform`, `Machine.step` |
| `Effect.Deep` | 5 | **`workshop/OCaml5/Effect.lean`** — `Stdlib.deepMatchWith`, `deepContinue`, `deepDiscontinue` |
| `Effect.Shallow` | 4 | **`workshop/OCaml5/Effect.lean`** — `Stdlib.shallowFiber`, `shallowContinueWith` |
| `Base.Map` | 8 | none as a *carrier* — but its thirteen laws **are** theorems, in seat W4's `workshop/OCaml5/Lib/Map.lean`, and the names in `Ml.Profile` are cited from that file rather than invented here |
| `Base.Set` | 5 | none |
| `Base.Deque` | 5 | none — and this is the sharpest one: the dispatcher's buckets *are* a `Deque`, and `Deque.fifo` is the law the whole scheduling order rests on |
| `Base.Result` | 3 | none — though `Exit` is exactly its shape |
| `Base.List` | 8 | none |
| `Base.String` | 4 | none |
| `Sexplib0.Sexp` | 3 | none |
| `Fields` (from `[@@deriving fields]`) | 4 | none — and `Fields.fold_once_in_order` is the walk a field-by-field simulation relation would be stated over |
| `Variants` (from `[@@deriving variants]`) | 3 | none |
| `Eio.Switch` | 3 | none — a `Switch` is a scope; the shape exists in `Effect4/Runtime/Scope.lean`, nothing in `workshop/OCaml5` interprets one |
| `Eio.Promise` | 4 | none |
| `Eio.Fiber` | 6 | none |
| `Picos.Computation` | 5 | none |
| `Picos.Trigger` | 4 | none |
| `Picos_std_sync.Ivar` | 4 | none |

The reading: **the model carries the effect handlers and the two base types, and nothing else.**
Everything the port is about to be written in — the ordered map, the queue, the derivers'
generated functions, and every structured-concurrency primitive — is admitted on trust. That is
not an argument against using them; it is the list of what would have to be modelled before a
simulation relation stated over a port that uses them means anything, and it is now a list
rather than an impression.

### The laws, as stable names

55 laws in `Ml.Profile.laws`, each with a stable name, a one-sentence statement and a `site`.
**21 have a site** — the eight effect-handler laws in `workshop/OCaml5/Effect.lean`, and W4's
thirteen `Map.*` in `workshop/OCaml5/Lib/Map.lean` — and 34 do not. Seat W4 is proving those; the
name is stable across that transition, so a module that depends on `Deque.fifo` keeps depending
on `Deque.fifo` whether or not it is yet a theorem.

The `Map.*` names here are **cited from W4's file**, not invented: `Map.lean` carries a "Named
properties (theorem names are stable; cite these)" list and `Ml.Profile` uses it verbatim —
`find_remove_same` and `find_remove_other` rather than one `find_remove`, `toAlist_sorted` rather
than `to_alist_sorted`, `fold_visits_keys_in_order` rather than `fold_order`. That the two files
agree is the point of the interface; when W4 adds `Deque`, this file's `Deque.fifo` should become
a citation the same way.

`Check.lawsUsed` and `Check.lawReport` answer the question the ruling asks: *which laws does this
generated module depend on?* On a two-carrier module that calls `Variants.to_rank`, one:

```
laws       the generated carriers depend on:
  Variants.to_rank_declaration_order  unproven — Variants.to_rank is the declaration order …
```

and on a module that touches the dispatcher's queue and map, six: `Deque.fifo`,
`Map.find_set_same`, `Map.find_set_other`, `Map.find_remove_same`, `Map.find_remove_other`,
`Map.ext_find` — of which five are already theorems and the one that is not is `Deque.fifo`. Both
lists, and that last filter, are `#guard`ed in `MlTest`.

## 4. `Reflect`, both ways

`toTypeDecl` was Lean → OCaml. `ofTypeDecl` is **OCaml → Lean**: given a type declaration as
`Ml.Syntax` data — written here, or, once the switch exists, parsed out of a real `.mli` by
`ml-check.sh`'s ppxlib lane — it produces the `TypeDesc` a Lean carrier would be described by.
That is what lets a library type be *named* in Lean rather than retyped, and the two directions
compose: `toTypeDecl (ofTypeDecl inv d)` renders the same bytes as `d`, `#guard`ed on a record
and on a variant.

Three lossy places, named rather than hidden: `int` lifts to `Int` and not `Nat` (OCaml's is
signed and 63-bit); a form `LTy` cannot spell — an arrow, a tuple, a polymorphic variant — lifts
to a reserved head (`Arrow`, `Tuple`, `PolyVariant`, `Opaque`) and `liftFaithful` decides whether
a lift round-trips; and an abbreviation, an abstract type or an extensible one describes no
members, so `ofTypeDecl` answers `none`.

## 5. What changed for consumers

Nothing. Concretely:

* every name a consumer spells still exists, in the same namespace, with the same meaning:
  `Ml.StructDesc`, `Ml.InductiveDesc`, `Ml.LTy`, `Ml.Avatar.*`, `Ml.render*`, `Ml.moduleText`,
  `Ml.mangleField`, `Ml.reservedNames`, `Ml.mutate`, `Ml.residue`, `Ml.Deep.sample`;
* `Field`, `Ctor`, `TypeDecl` and `Bind` gained fields, all with defaults, so every existing
  record literal still elaborates;
* `Ty`, `Pat`, `Expr` and `Decl` gained constructors; nothing was removed or renamed;
* `Render.esc` is now `Ml.escString` under its old name, byte for byte;
* `OCaml5.Fuzz` and `workshop/OCaml5/tools/fuzz.sh` are **not edited**, and their `surface`,
  `avatar`, `tapes` and `witnesses` lanes are green.

Three `#guard`s in `Render.lean` changed, and all three because the renderer now emits fewer
parentheses: `renderTy (unit -> 'b bucket list)` lost its outer pair, and two mutation checks now
look for `d.buckets <- ` and `f.frame.interrupted_cause <- ` instead of `).buckets <- ` and
`).frame).interrupted_cause <- `.

Two changes are repairs rather than refactoring, both in the descriptions this seat owns:

1. **`run_fiber` had drifted.** A0's round five added a seventeenth field,
   `mutable race_answer : kops option`, and the byte diff was red on exactly that field when this
   seat started. It is now a `FieldKind.substitute` in `Ml.Avatar.runFiber` with A0's own
   three-line comment carried verbatim, and `Avatar.preamble` gained the `kops` declaration the
   isolated compile needs. `run_fiber` is IDENTICAL again. This is the second time the diff has
   caught exactly this, and the second time the answer was a declared substitute — the pattern is
   working.
2. **`Ty.deepHandler` took one argument and `Effect.Deep.handler` takes two**
   (`stdlib/effect.mli`, `('a, 'b) handler`). It was an unused helper, so nothing depended on the
   wrong arity; `Ty.deepEffectHandler` was added for the one-parameter `effect_handler` that
   `Effect.Deep.try_with` actually takes.

## 6. The battery

`workshop/OCaml5/MlTest.lean` (568 lines) and `workshop/OCaml5/tools/ml-check.sh` (83 lines).

**(a) Every syntax form renders text `ocamlc` accepts.** `MlTest.fixture` is one `Ml.Module` of
61 declarations, 6,546 bytes, using every constructor of `Ml.Syntax`. `ml-check.sh` renders it
from Lean, compiles it with `ocamlc`, `ocamlopt` and `js_of_ocaml --enable effects`, runs it, and
diffs its 21 printed rows against `MlTest.expectedRows` pinned in Lean. `ocamlc` runs with
**default warnings**, not `-w -a`; the fixture carries its own `[@@@warning "-a"]` and the script
hides nothing. The rows are offset by constants so a wrong answer is a wrong row rather than a
coincidence.

Two forms are deliberately outside the fixture and say so in its docstring:

* `Expr.reperform`, because the raw `%reperform` is typed over `last_fiber`, which
  `stdlib/effect.ml` does not export — no ordinary compilation unit can name it. The unit that
  can is `OCaml5.Render.fixedPrelude`, and `fuzz.sh witnesses` compiles and runs it on all three
  hosts. What `MlTest` checks about `reperform` is the tail-position rule, in (c);
* `Ty.asVar`, the `(t as 'a)` constraint, which is legal only where the equation is not cyclic.
  It renders, and is `#guard`ed in `Ml/Render.lean`, and is not compiled.

**(b) The five avatar carriers still render byte-identical.** `tools/fuzz.sh avatar`, unchanged.
Not repeated inside Lean: a copy of `deep_fibers.ml` in a Lean file is the thing that check
exists to avoid.

**(c) The checker rejects twelve deliberately bad modules and accepts the good ones.**
`MlTest.badModules` is twelve modules over eleven distinct diagnostic codes, each `#guard`ed to
produce **exactly** its own code and no other:

| code | the fault |
| --- | --- |
| `unbound-value` | an unqualified name with no binder |
| `unbound-ctor` | an unqualified constructor with no declaration |
| `ctor-arity` | a constructor at the wrong arity, in an expression, and again in a pattern |
| `undetermined-param` | a record parameter no field determines and no variance annotates |
| `effc-abstract` | a handler whose answer type mentions `a`, the locally abstract type |
| `effc-unknown` | an `effc` clause on a constructor that is not a declared effect |
| `reperform-position` | a `reperform` as an operand of `+` |
| `duplicate-field` | a record declaration naming a label twice |
| `duplicate-binding` | a `let rec … and …` binding a name twice |
| `bad-name` | a value named `Capital` |
| `duplicate-ctor` | one variant declaring a constructor twice |

and the good side: the fixture, the empty module, a parameter a field does determine, a phantom
parameter with a variance, and `reperform` in tail position — with the same expression as an
operand `#guard`ed to fail.

**(d) The mangling round-trips.** `unmangleField ∘ mangleField = id` on every field name of
`Avatar.runFiber` and `Avatar.frameFiber`, every constructor argument name of the five avatar
inductives, and an adversarial row of nineteen (`aB` vs `a_b`, `exit`, `with`, the empty name,
`ν`, `μ'`, `__`).

### The checker's two deliberate silences

They are in the module docstring and they are real limits, not oversights.

* **Qualified names are not checked.** `M.f` and `Effect.Unhandled` name something in another
  compilation unit and the checker has no way to see it. A typo inside a qualified name reaches
  `ocamlc`.
* **An `open` or an `include` switches `unbound-value` reporting off** for its scope
  (`Env.openScope`). Another unit's unqualified names become visible and this module cannot see
  them, so the check is disabled rather than made to lie. A generator that wants the check should
  qualify instead.

`Expr.raw` is a third: it is not parsed, so nothing inside it is scoped. It is counted rather
than checked — `rawSites fixture == 1` — so a module that leans on `raw` can be told apart from
one that does not.

### The `reperform` rule, and why it is transcribed rather than imported

`Ml/Check.lean` carries its own `TailPosition` and its own table of which subterms inherit the
polarity. That is the same table as `workshop/OCaml5/Compiler.lean`'s `admissibleAt`, and the
duplication is deliberate: `Compiler` decides the rule for `OCaml5.Term`, the untyped machine
language of the P5 spike, and imports the spike's whole effect machinery to do it. A package that
is to stand on its own cannot depend on a spike's term language. The correspondence is stated in
`Check`'s docstring, with the `bytegen.ml` line numbers on both sides, so the two can be diffed
by eye and by a future test.

## 7. The precedent it follows

`.lake/packages/typescript/TypeScript/{Syntax,Render,Identifier,HostPin,Structure}.lean` —
"first-order syntax, deterministic rendering, the generated-identifier profile, and host pins; no
knowledge of any effect system". Followed as:

| TypeScript | here | same reason |
| --- | --- | --- |
| `Syntax.lean` owns syntax only | `Ml/Syntax.lean` | a value of the type is target data, never a denotation |
| `Render.lean` is a total function of the syntax | `Ml/Render.lean` | equal syntax gives equal bytes, which is what a byte diff against a hand-written file needs |
| `Identifier.lean` is a narrow profile, not a model of the language | `Ml/Identifier.lean` | the set a generator actually emits, plus the reserved words |
| hand-written `BEq` for the nested inductive | `Ty.beq`, and list helpers throughout | the deriving handler uses a `partial` helper; this tree has none |
| "no knowledge of any effect system" | `Effect.Deep`/`Shallow` are OCaml **standard library** shapes, cited to `stdlib/effect.ml` | they are part of the target language, not of Effect4 |

The one place this seat went further than the precedent is `Ml/Check.lean`: TypeScript has no
checker, and OCaml needs one because its declaration forms have rules a renderer can decide
(scoping, arity, the undetermined parameter, the locally abstract type) and because the
`reperform` rule is a *compiler* rule that no type system catches.

## 8. What is still missing before it can be a package

Four things, in the order they would have to be done.

1. **A host pin file.** `TypeScript/HostPin.lean` pins the compiler and the options the rendered
   text is claimed to be accepted by. The OCaml equivalent has to pin OCaml 5.1.1, the three
   hosts of ruling 7 (`ocamlc`, `ocamlopt`, `js_of_ocaml --enable effects`), the `stdlib/effect.ml`
   line numbers the `Effect` forms are read against, and the manual edition every docstring cites.
   Today those live in four places: `ml-check.sh`'s environment variables, `fuzz.sh`'s, the
   docstrings, and this report.
2. **A contract.** What `render` promises. The two properties are stated in `Ml/Render.lean`'s
   docstring — total function of the syntax, fixed layout — but neither is a theorem and neither
   is `#guard`ed. `render (m₁) = render (m₂) → m₁ = m₂` is false (a `Decl.blank` and a
   `Decl.rawD ""` render the same), and the honest contract is the other direction plus a
   statement about which syntax the checker admits.
3. **A battery of its own.** `MlTest.lean` is the battery, but it lives in the `OCaml5` library
   and imports `OCaml5.Render` to reach `Ml.Avatar.*` for the mangling round-trip. A package
   would split it: an `OCamlTest` library that imports only `OCaml`, plus the avatar-specific
   `#guard`s left behind in the spike. That import is the only edge from the six modules back
   into the spike, and it runs in the test file only — `Ml/*.lean` imports nothing outside
   `Ml/`.
4. **The elaborator.** `Reflect` is the interface an elaborator would target: something that
   builds a `TypeDesc` from a `Lean.Expr` instead of from a hand-written literal. The P5 report
   §11.7 already enumerated what it would have to compute and what it could not — the
   substitution table, the constructor prefixes and the two name overrides are decisions about
   the target module, not facts about the Lean type — and nothing in this refactor changes that
   list. It is the one piece that would make "generated from the Lean carriers" true without a
   human in the loop.

5. **The library carriers.** Fifteen of the twenty admitted modules have no Lean semantic
   carrier (§3). A package can ship without them — they are a property of the estate's model, not
   of the codegen API — but a *claim* about a port written against Base, Eio or Picos cannot.
   The sharpest single one is `Base.Deque`: the dispatcher's buckets are a `Deque` and
   `Deque.fifo` is the law the whole scheduling order rests on.
6. **The 34 unproven laws.** Named and stable, and seat W4's to prove under
   `workshop/OCaml5/Lib/` — they have `Map` and `Order` already. Until then `Check.lawReport` is
   an honest dependency list and not an assurance. `Deque.fifo` is the one to do next: it is the
   only unproven law the dispatcher's own module depends on.

Two smaller gaps, recorded rather than fixed:

* the surface has no object system, no `class`, no first-class modules, no `let module`, and no
  `constraint` clause in a type declaration; the last is what would make `Ty.asVar` reachable in
  a compiled fixture;
* `Check` has no notion of a *field* being in scope, so `e.nosuchfield` is not reported even
  though the module's labels are collected into `Env.fields`. It is one function away and was
  left out because the false-positive rate under `open` would have made it noise;
* `Check.profile` checks a qualified name's **module** and its **last segment**, not its type.
  `Base.Map.find` used at the wrong arity is `ocamlc`'s business, not the profile's: the
  signatures in `Ml.Profile` are documentation and a checker input, and 50 of the 88 are still
  `Ty.anon` — a signature nobody has written down, which is a smaller admission than a wrong
  one. Every `Base` container's core operations are written; every `Eio` and `Picos` value is
  not.

## 9. Commands

```
lake build OCaml5.Render OCaml5.Fuzz OCaml5.MlTest   # the three targets of the brief
./workshop/OCaml5/tools/ml-check.sh [--keep]         # check (a): the syntax fixture, three hosts
./workshop/OCaml5/tools/fuzz.sh avatar               # check (b): the five carriers, byte diff
./workshop/OCaml5/tools/fuzz.sh surface              # the A0 shape probe, three hosts, rows
./workshop/OCaml5/tools/fuzz.sh tapes 7 20 6         # the RunDecision tape module, three hosts
./workshop/OCaml5/tools/fuzz.sh witnesses            # the Term renderer, unchanged by this seat
```

`ml-check.sh` also runs the profile and the law report on the generated carrier module, so
`OCaml5.Ml.Check.profile` and `Check.lawReport` have a console face and not only a `#guard`.
