# The crowning jewel: how the OCaml runtime is reified from Lean, and how to keep it while the language widens

Research seat, 2026-09-18, read against the working tree at `02e7d4f0`. The tree moved twice
while I wrote and both movements are recorded below rather than smoothed over: the L1 slice
(`src/Effect4/Machine/{Alphabets,Term}.lean` untracked) was already in the working tree when I
started, and **L5's `Ty.unknown` landed mid-seat**, taking `Ty` from 19 constructors to 20 and
bringing with it exactly the interim repair §3(a) recommends (`ocaml/engine/e4_program.ml:139`).
Every count below is stated with the state it was read at. Read-only seat: I ran no `lake`, no
`dune`, no compiler. Every claim below is either **read off a file at a cited line**, or marked **assumed**
where it is an inference that a build would settle. Two claims that a build would settle are
called out as such in §5 and each is given the one command that settles it.

Method: I read `src/OCaml5/**` in full (2,450 lines of `Lcnf/`, 1,270 lines of `Eff/`, the two
drivers), the four generated artefacts' headers and the relevant bodies of
`ocaml/gen/api_gen.ml` (16,432 lines) and `ocaml/engine/api_engine.ml` (15,413), the Makefile's
`gen-*`/`check-*` graph, `scripts/generate.py`, `scripts/generate-engine-structure.py`,
`scripts/lib/program_structure.py`, `scripts/check-conform.py`, the CI workflow, the Conform
LCNF lane, `ocaml/engine/e4_program.ml`, `ocaml/gen/api_check.ml`,
`ocaml/engine/test/test_diff.ml`, `ocaml/engine/tools/gen-check.sh`, `docs/core/lcnf-route.md`,
`docs/core/decisions.md`, `docs/GENERATED.md`, and the plans in `docs/research/2026-09-18-rows-42-43-plan.md`
and `docs/research/2026-09-17-runner-schema-codegen-plan.md`.

**The headline.** The pattern is real, and it is *better* than the docs say in one respect and
*worse* in another. Better: the LCNF route is not a translator for one function — it is a closure
walk with a stale-ledger gate, a carrier-substitution seam whose completeness is an `ocamlopt`
type error, and a name-collision fixpoint. Worse: the only mechanical evidence that the OCaml
means what the Lean means is a differential, the big differential lane is wired to no `make`
target, and there are **three hand-written OCaml files in the load path whose exhaustiveness the
Lean side no longer implies** — one of which has been behind since `7db30c8a`, and a generated
mirror that records the divergence as data instead of refusing it (and that, at the time of
writing, under-reports it: it says `engine 16 / source 19` while the source is at 20).

---

## 1. How the reification works today

### 1.1 There are two pipelines, and only one of them is LCNF

The brief's topic names `Eff/Emit.lean` and `Lcnf/` together. They are different machines and it
matters:

| | **Pipeline A — reflection/staging (`eff`)** | **Pipeline B — LCNF (`lcnf`)** |
| --- | --- | --- |
| reads | the *kernel* environment: `InductiveVal.ctors`, constructor telescopes | the *compiler's* environment: `monoExt`, the persisted mono-phase `Decl .pure` |
| door | `Tools.ProgramStructure.readBlocks` → `OCaml5.Eff.World.readBlocks` (`src/OCaml5/Eff/World.lean:152`) | `Lean.Compiler.LCNF.getMonoDecl?` via `OCaml5.Lcnf.Dump.monoDecl?` (`src/OCaml5/Lcnf/Dump.lean:40`), and `Conform.Lcnf.persistedMonoIndex` (`tools/Conform/Lcnf/Index.lean:9`) |
| lowers | *types and data*: one OCaml variant/record per Lean inductive, plus Lean **values** evaluated at generation time and printed as OCaml literals | *code*: one Lean definition to one OCaml `let` |
| output | `ocaml/eff/eff_{types,wire,json,subterm,native,layout}.ml`, `eff_manifest.txt`, `program-structure.json`, goldens | `ocaml/gen/{machine,fibers,api}_gen.ml`, `ocaml/engine/api_engine.ml` |
| driver | `src/OCaml5/Tools/EffGen.lean` | `src/OCaml5/Tools/LcnfGen.lean` |

Pipeline A's `emitNative` is *partial evaluation*, not translation: `NativeOp.row` is evaluated
in Lean over the finite built-in alphabet and the resulting `Row` values are printed as an OCaml
`row_of` match (`src/OCaml5/Eff/Emit.lean:490-492`). The comment says the design intent plainly —
"Typing remains in Lean; no second atom checker is emitted" (`Emit.lean:482`). That is the right
call and it is the pattern's cheapest half: anything that is a *finite table in Lean* should
cross as data, not as code.

### 1.2 Pipeline B: the roots, and what is in the closure

Roots are chosen by the driver and stored **inside the generated file's own header**
(`ocaml/gen/api_gen.ml:1-2`, `ocaml/engine/api_engine.ml:1-2`);
`scripts/generate.py:110-114` reads the command back out of the file and re-runs it. The four
root sets:

| output | import | cap | roots |
| --- | --- | --- | --- |
| `machine_gen.ml` | `Effect4.Machine.Fibers` | 60 | 10 dispatcher/machine functions |
| `fibers_gen.ml` | `Effect4.Machine.Fibers` | 400 | 43 — every top-level function of `Fibers.lean` |
| `api_gen.ml` | `Effect4.Api` | 2000 | `Effect4.Api.run`, `Effect4.Api.replay` |
| `api_engine.ml` | `Effect4.Api` | 2000 | the same two plus 14 more (`stepDecisionState`, `driveState`, `settled`, the four `FnName.*`, `Scope.make/fork`, `RunFiber.make`, `emptyCtx`, `Program.compile`, `Machine.stores`, `Program.Node.child`) and `--externs`/`--prelude` |

From two roots the walk reaches **659 declarations** (`grep -c "LCNF mono:" ocaml/gen/api_gen.ml`
= 659) and about 80 generated record/variant types. The walk is `translateClosure`
(`src/OCaml5/Lcnf/Translate.lean:1006-1066`): a queue seeded with the roots, each callee enqueued
from `St.calls`, with four stopping conditions it names rather than hides — an extern row
(`:1020`), a builtin (`:1021`), a constructor (`:1022`), the cap (`frontier`, `:1023`) — and
one refusal, `missing` when the constant has no mono decl (`:1028`).

Two facts about the closure that are load-bearing for §3:

* **The checker is not in it.** `grep -c "typeOf\|type_of" ocaml/gen/api_gen.ml` = 0. That is by
  design, not accident: `Api.run`/`Api.replay` are documented as "**Raw** … it checks neither the
  program nor the table" (`src/Effect4/Api.lean:321-323`). The checked face is
  `Api.HostSession`/`Api.Runner`, and neither is a root.
* **Value typing *is* in it.** `Effect4.Program.Val.hasTy` is translated
  (`ocaml/gen/api_gen.ml:9504-9509`) because the external-row admission calls it:
  `program_external_value` at `:9745` (its `hasTy` call at `:9750`) and `program_err_admits` at `:9786`. So `hasTy` is a live
  runtime function of the OCaml engine, and anything done to it lands in the engine.

### 1.3 The accepted fragment of Lean, precisely

The fragment is *mono-phase LCNF*, and the reason is the best paragraph in the estate
(`src/OCaml5/Lcnf/Dump.lean:24-29`): base still carries type arguments and `Decidable`; impure has
already introduced reference counting, boxing and `reset`/`reuse`; mono is where polymorphism is
erased to `◾`, `Decidable` is `Bool`, structure projections have become `cases`
(`StructProjCases`), local functions are lifted (`LambdaLifting`), and the code is still a pure
tree — "exactly the fragment OCaml spells directly". Nothing is compiled at generation time:
`monoDecl?` reads what `saveMono` wrote when the module was built
(`~/.elan/…/Lean/Compiler/LCNF/Passes.lean:66-72`), after `normalizeFVarIds`, so a dump is
deterministic across runs and machines.

The whole surface is 26 constructors and the estate counts them:
`Conform.Lcnf.Validity.constructs` (`tools/Conform/Lcnf/Validity.lean:53-59`) is the fixed
26-element list — 7 `Code`, 5 `LetValue`, 7 `LitValue`, 3 `Arg`, 2 `Alt`, 2 `DeclValue` — with the
note that the 19 impure constructors carry `h : pu = .impure` and *cannot* inhabit the fragment.
That is the right shape for a fragment predicate (§4(i)).

The rules, read off `Translate.lean` (the table at `:42-64` is accurate; I checked each row
against the code):

| form | site | OCaml |
| --- | --- | --- |
| `let x := v; k` | `:823-831` | `let x = v in k`, and `v` by `letValueExpr` (`:656`) |
| `fun`/`jp` | `localFun`, `:875-888` | a local function; `let rec` when the body mentions itself (`:881`); no params → `fun () ->` (`:879`) |
| `jmp j args` | `:828-832` | `j args`; no args → `j ()` |
| `cases` on `Bool` | `:840-857` | `if`; a missing arm is a **refusal** (`:855-856`) |
| `cases` otherwise | `:858-873` | `match (d : (_,…) t) with`, annotated so OCaml's record disambiguation never guesses (`:863`); `default` kept (`:867`) |
| structure arm | `altPat`, `:777-815` | `{ f₁ = f₁; …; _ }` binding **only the fields the arm uses** (`k.collectUsed`, `:871`) |
| inductive arm | `:815` | `C_c (a₁,…)`, `_` for an unused field |
| `List`/`Option`/`Prod`/`Bool`/`Except`/`PUnit`/`Nat` | `Lcnf/Native.lean:17-23` | `[]`, `h::t`, `None`, `Some`, tuples, `Ok`/`Error`, `()`, `0`, `x+1` — one table used for *both* construction and matching |
| `return`/`unreach` | `:836-837` | the variable / `assert false` |
| `proj T i s` | `:669-697` | `s.fᵢ` on a structure; `fst`/`snd` on `Prod`; a **refusal** on a single-constructor non-structure |
| a global call | `:732-771` | `g' args`, `g` enqueued; `_redArg` wrappers folded onto their twin, with eta-expansion when the reference is unsaturated (`:757-767`) |
| a builtin | `builtin?`, `:154-269` | ~70 rows |
| an `extern` | `:952-955` | a hole and a `todo` (fatal at the driver) |

**`Option`/`List`/`String`/`Nat` specifically**, since the brief asks:

* `Option` is OCaml's `option`, natively, both ways (`Native.lean:19,33-34,47-48`); the `do`-block
  `bind` of a Lean `Option` monad has already been compiled to `cases` by mono, so
  `program_eval_terms` comes out as nested `match … with None -> … | Some x -> …`
  (`ocaml/gen/api_gen.ml:2925-2938`) with no monadic residue. `Option.getD`/`map`/`bind`/`isSome`/
  `isNone` are builtin rows (`Translate.lean:247-256`).
* `List` is OCaml's `list`, and **`Array` is also `list`** (`Lcnf/Types.lean:59`) — the "route's
  Array-as-list shim", with 8 `Array`/`USize` rows to match (`Translate.lean:229-247`). The
  comment there is worth quoting because it is the model of a good row: without those four rows
  "`List.setTR.go`'s `Array.foldrMUnsafe.fold` is four `extern` holes, so `List.set` — and
  therefore `DeferredStore.setCell` and `RefHeap.set` — is `assert false` at run time"
  (`:229-232`).
* `String` is OCaml's `string` (bytes). `String.length` becomes `lcnf_utf8_length`, a UTF-8
  code-point count emitted in the prelude (`Translate.lean:1092-1095`), *not* `String.length` — the one
  place where the 8-bit/code-point difference is handled rather than ignored. `String.toUTF8`
  becomes `lcnf_utf8_bytes`, a `char code` list.
* `Nat` is OCaml's 63-bit `int`, and this is the single largest fidelity gap. It is handled in
  three places, all documented: `Nat.sub` truncates as Lean's (`:164-166`), `Nat.div`/`mod` answer
  Lean's values at 0, `Nat.pow` **saturates at `max_int`** via `powClamped` (`:140-151`, row at `:172-175`) and
  `Nat.shiftLeft` clamps too, and a literal ≥ 2^62 becomes `max_int` rather than an
  out-of-range literal (`:661`). The reasoning recorded at `:140-151` is exactly the kind of
  argument this pattern needs: `Store.Val.wf`'s `… < 2 ^ 64` would read as `… < 0` under a
  wrapping `pow` and answer `false` for every value — "a silently wrong `Api.ofBytes`, not a
  compile error" — whereas saturating keeps the guard's meaning because every list OCaml can hold
  is shorter than `max_int`.

**Recursion forms.** Self-recursion is `Translated.recursive` (`:959`). Mutual recursion is
handled by strongly-connected components on the translated-name graph
(`emissionGroups`, `:1100-1110`, using `Lean.SCC.scc`) and emitted as one `let rec … and …` group
per component (`emit`, `:1112-1121`). It works: `evalTerm`/`evalTerms` come out as
`let rec program_eval_term … and program_eval_terms …` (`ocaml/gen/api_gen.ml:2912,2925`), and
there are 123 `and`-continuations in `api_gen.ml`. Well-founded recursion is not a special case —
by mono phase Lean has already compiled it to a structural or fuelled form, or the constant is
`noncomputable` and lands in `missing`.

### 1.4 What it refuses, exhaustively

Six `todo` sites (each becomes an `Expr.hole` rendered `(* HOLE: … *)` *and* a line in
`Closure.todos`, which the driver makes fatal at `LcnfGen.lean:168-169`):

1. `proj` on a single-constructor inductive that is not a structure (`Translate.lean:692`);
2. `proj` on something that is not an inductive at all (`:695`);
3. `cases` on `Bool` with a missing arm (`:846`);
4. an alternative on an unknown constructor (`altPat`, `:813`);
5. a `DeclValue.extern` with no table row (`:953`);
6. a carrier with no `to_list` operation row (`useAsList`, `:505`).

Plus four driver-level refusals: `missing` (a callee with no mono decl, `:166-167`), unresolved
type-name collisions after 4 fixpoint rounds (`:170-171`), a **stale extern ledger** — any `fn`,
`type`, `field`, `elem`, `ops` or `carg` row that no declaration hit (`:201-215`) — and unsettled
carrier parameters after 64 inference rounds (`Translate.lean:1084`).

And one that is *not* a refusal and should be: `Ml.checkModule` runs and its diagnostics are
printed as "informational" (`LcnfGen.lean:172-176`). See §5.4.

### 1.5 How the OCaml is typed

Three independent mechanisms:

**(a) Types from inductives** (`Lcnf/Types.lean`). `typeInfo?` (`:238-331`) reads one inductive
and produces a record, a variant, or a **type abbreviation**. The abbreviation case is the subtle
one and it is right: a *trivial structure* — one constructor, exactly one computationally relevant
field — is what Lean's own compiler erases to its field, so `FiberId` must be `int` and
`Cause ε δ ι α` must be `(…) reason list`, or the generated *code* (which assumes the erased
representation) would not typecheck against the generated *types*. The verdict is not
recomputed by hand: `trivialFieldIdx?` (`:108-126`) asks `Compiler.LCNF.hasTrivialStructure?`
first and only recomputes by the same criterion (`isProp ∨ isTypeFormerType`, `:102-103`, the
predicate `Irrelevant.getRelevantCtorFields?` uses) when the persisted answer is absent.
Field relevance uses the same predicate (`:281`). Closure is by placeholder: a type nothing
destructs becomes a one-nullary-constructor variant `Placeholder_<t>` (`:325-328`), so a generated
file always compiles on its own and a reader sees which types the run did not port.
Unspellable field types become one abstract `lcnf_unknown` and are *listed* (`:288-289`, `:411-412`).

**(b) Annotations from mono types** (`monoTy`, `Translate.lean:76-101`). Arrows are arrows,
`◾`/`lcAny` is `_`, and inductive type arguments are filtered by `typeParameterIndices`
(`Types.lean:146-157`) so the annotation's arity matches the declared OCaml type's — the
`Prop`/value/instance parameters Lean erases are dropped. An all-`_` annotation is omitted.

**(c) The carrier seam** (`Lcnf/Externs.lean`, 52 rows in `ocaml/engine/externs.txt`: 30 `fn`,
2 `fn?`, 9 `field`, 9 `ops`, 1 `type`, 1 `elem`, and **0 hand `carg` rows** — every one is
inferred). This is the cleverest part of the estate. A `field` row changes a struct field's
*type* from `τ list` to a carrier `C.t`, the whole body moves inside
`module Make (M) (T) (L) (D) (P) (E) (F)` (`LcnfGen.lean:142-148`), and then — the argument at
`Externs.lean` "Properties" and `gen-check.sh:19-20` — **a functor body that type-checks with no
instance is the proof that the table is closed**, because any generated site still treating the
carrier as a list is an `ocamlopt` type error. `translateClosureInferring` (`Translate.lean:1069-1086`)
reads the missing inter-procedural `carg` rows off the call sites and iterates to a fixpoint;
`useAsList` reports every O(depth) copy-back so a missing row is visible in the report rather
than only in a benchmark (`LcnfGen.lean:199-200`).

**The layout json is *not* generated from Lean.** `ocaml/engine/e4_program_layout.{ml,json}` is
produced by `scripts/generate-engine-structure.py`, which reads `ocaml/eff/program-structure.json`
(Lean's source shape) **and parses the declarations out of `api_engine.ml` with a regular
expression** (`scripts/lib/program_structure.py:14-51`), then emits the *intersection* as a
`PROGRAM_TYPES` module signature plus two constructor-name tables, and writes the divergences into
a JSON `unavailable` list (`:124-165`). That design decision — record the divergence rather than
refuse it — is the source of the worst finding in this note (§5.1).

### 1.6 `Metadata.lean`'s "one sample per constructor"

`src/OCaml5/Eff/Metadata.lean` is a **triple-witness fixture set for the codec families that the
program corpus cannot reach**. Read it against the driver:

* `Metadata.all` (`:74-84`) builds one `Fixture` per value: a hand `V` tree, `Canonical.encode`'s
  bytes, and the profile-JSON node (`:41-50`). The values are one per `Ty` constructor (`:52-60`),
  every `RowKind`, `RowShape` and `Registration`, a fully populated `Row`, and three `EffTy`s.
* `EffGen` then does three things with them (`src/OCaml5/Tools/EffGen.lean:120-141`): every
  constructor name in the hand tree must resolve in the closed world (`:123-125`); the hand tree's
  bytes must equal `Canonical.encode`'s (`:128-129`, so the hand tree is not an independent
  claim — it is a *cross-check* of the codec against a second spelling); and — the "one sample per
  constructor" part — for every family a fixture mentions, **every constructor must be reached at
  least once or generation fails**: `if count == 0 then throw … "metadata reaches no {c.name}"`
  (`:140`).

So it is a coverage gate, and it is the *reason* the six codec families are not silently
under-tested: the program corpus (`goldens/coverage.txt`, `:184-194`) skips `Ty`, `RowKind`,
`RowShape`, `ServiceName`, `ServiceTypeCode`, `ServiceKey`, `Registration`, `Row` and `EffTy`
(`:185-187`) because a program's bytes never carry them; `Metadata` is what covers exactly those
nine. `goldens/coverage-metadata.txt` is the receipt.

This is *why* `Metadata.lean:59-60` already carries `("refOf", .refOf .nat)`,
`("deferredOf", …)` and `("var", .var 0)`: step 1 could not have landed without adding them, or
`EffGen` would have thrown. That gate worked. Hold that thought for §5.

### 1.7 The pipeline as stages

```
STAGE 0  lake build                       (the only compiler run; it is what persists monoExt)
         in : src/**.lean
         out: .lake/**/*.olean with monoExt entries, and Lake traces the Makefile keys on

── pipeline A ────────────────────────────────────────────────────────────────────────────
STAGE A1 Tools.ProgramStructure.readBlocks   kernel env → 26 Family records (ctors, field shapes)
STAGE A2 OCaml5.Eff.World.projectShape       Family → OTy carriers; an unspellable field THROWS
STAGE A3 Tools.WireTags.load + requireListed wire-tags.json; an unlisted inductive REFUSES
STAGE A4 Eff/Emit.emit{Types,Wire,Json,Subterm,Native} + manifest
         out: ocaml/eff/eff_*.ml, eff_manifest.txt, program-structure.json
STAGE A5 Eff/Goldens + Metadata             Lean evaluates the corpus and the fixtures
         gates: hand tree == Canonical.encode; every ctor of every metadata family reached;
                every ctor of every program family reached by the corpus
         out: ocaml/eff/goldens/**  (.bin, .json, .ty, corpus.txt, metadata.tsv, coverage*.txt)
STAGE A6 scripts/generate-engine-structure.py   program-structure.json × regex(api_engine.ml)
         out: ocaml/engine/e4_program_layout.{ml,json}      ← reads a pipeline-B output

── pipeline B ────────────────────────────────────────────────────────────────────────────
STAGE B1 Conform.Lcnf.persistedMonoIndex     olean → Name ↦ Decl .pure
STAGE B2 Externs.parse                       ocaml/engine/externs.txt → the seam table
STAGE B3 translateClosureInferring           roots + cap + table → Closure (≤64 carg rounds)
           per decl: translateDecl → ≤16 join-point carrier-seed passes → Ml.Bind
STAGE B4 Types.generate                      closure.realTypes ∪ --types ∪ mentioned → one
                                             `type … and …` group (full | alias | placeholder)
STAGE B5 collision fixpoint (≤4 rounds)      re-run B3+B4 with TypeNames fixed
STAGE B6 emissionGroups (SCC) → emit         dependency-ordered `let rec … and …` groups
STAGE B7 gates                               missing=∅, todos=∅, collisions=∅, ledger not stale
STAGE B8 Ml.render                           Ml.Module → text
         out: ocaml/gen/{machine,fibers,api}_gen.ml, ocaml/engine/api_engine.ml
```

Note the cycle: **A6 reads B8's output, and the Makefile runs A before B**
(`Makefile:92-93` puts `ocaml/engine/api_engine.ml` in `EFF_SOURCES`; `Makefile:120` makes
`$(GEN)/lcnf` depend on `$(GEN)/readme` ← `ts` ← `cas` ← `wire` ← `eff`). So one `make gen` pass
leaves A6's output one generation behind B8's. §5.1.

---

## 2. What the compiler world does about "one source, many targets", and what each teaches us

`docs/core/lcnf-route.md` §7 already banked the LLVM steer (profile-as-data, legalization,
`MCInst` as a common currency, and "do not write a low-tier backend"). I will not repeat it; this
section is the part that note did not do — the **invariants, the type-preservation discipline, and
the verification story**, with a concrete statement of each for this tree.

### 2.1 Lean's own LCNF → C pipeline

Read at `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/Lean/Compiler/`:
`LCNF/Basic.lean` (the IR), `LCNF/Passes.lean` (the pass list, `saveMono` at `:66`),
`LCNF/Check.lean` (`check` at `:234`, `checkCases` at `:215`, `checkLetValue` at `:137`),
`LCNF/PhaseExt.lean` (`:103`, the opacity filter), `LCNF/MonoTypes.lean`, `LCNF/Irrelevant.lean`,
`IR/ToIR.lean`, `IR/ToIRType.lean`, `IR/Checker.lean`, `IR/EmitC.lean`.

Three things Lean does that we do not:

1. **The IR is phase-indexed at the type level.** `Code`, `LetValue`, `Alt` are parameterised by
   a purity index, and the impure constructors carry `h : pu = .impure`, so `Code .pure`
   *cannot* contain them. Our 26-construct surface is not a documentation claim, it is a Lean
   type. **Teaching:** we should lean on this harder — the accepted-fragment predicate (§4(i))
   should be a predicate over `Code .pure`, not over strings.
2. **There is a structural checker, and it is run between passes.** `LCNF/Check.lean` checks fvar
   scoping, join-point scoping (`checkJpInScope`, `:144`), `cases` alternative well-formedness,
   and argument arity. `IR/Checker.lean` does the same for the lower IR. **Teaching:** the estate
   already has the hook — `Conform.Lcnf.Validity.checkDecl` runs Lean's own `Decl.check` on the
   decl read back out of `monoExt` (`tools/Conform/Lcnf/Validity.lean:375`) — but it is only run
   in the `compiler` conform profile over four roots. It should run over the *whole emitted
   closure*, every generation.
3. **Layout is a separate erasure with its own small universe.** `IR/ToIRType.lean` maps every
   Lean type to `irrelevant | object | tobject | u8 | u16 | u32 | u64 | usize | float`. That is
   the "DataLayout" of Lean's backend, decided once, independent of the code. **Teaching:** our
   `OTy` (`Eff/World.lean:40-48`) and `Ml.Ty` are two *different* layout universes for one
   language and neither is the other's refinement; §4(ii) proposes one.

`EmitC.lean` itself teaches the negative lesson: it is a string printer with essentially no
invariants, and it is *safe* only because everything upstream of it is checked. Our `Ml/Render.lean`
is in the same position, and our upstream is checked less.

### 2.2 MLIR and progressive lowering

MLIR's doctrine: many dialects, each with a **verifier** for its ops and types; lowering is a
sequence of *small legal steps*, each a set of conversion patterns; `--verify-each` runs the
verifier after every pass; rewrite rules are declarative (DRR/PDL) rather than C++ where possible;
type conversion is a first-class object (`TypeConverter`) separate from op conversion.

**Teaching, three concrete items.**

* *Verify after each step.* We have exactly one step (mono LCNF → OCaml syntax) and we verify
  after zero of them. The cheapest MLIR-shaped improvement is: verify the *input* (the fragment
  predicate + Lean's own `Decl.check`) and verify the *output* (`Ml.checkModule` made fatal).
  Both exist; neither gates.
* *Type conversion as its own object.* `TypeConverter` is precisely what `monoTy` + `kernelTy` +
  `tyOfInd` + `OTy.render` are, spread over three modules with two different universes. §4(ii).
* *Declarative patterns.* `builtin?` (`Translate.lean:154-268`) is ~70 hand-written
  `Name → Nat × (List Ml.Expr → Ml.Expr)` rows compiled into the generator. Externs are already a
  *file*. The asymmetry is unjustified: the builtin table should be the same kind of object as the
  extern table, so that a target profile can override a row without recompiling the generator, and
  so that the fidelity class of each row (§2.5) lives beside it.

### 2.3 LLVM IR as a typed interface; Cranelift

LLVM's leverage comes from the IR being *typed* and the verifier being part of the pipeline, so a
pass that produces nonsense is caught locally rather than at the assembler. Alive2 then does
**translation validation**: for each optimization instance, an SMT query that the target refines
the source. Cranelift's ISLE takes it further — instruction selection is a declarative rule
language, and the rules are verified individually against SMT semantics (Crocus/VeriISLE) — plus
`cranelift-fuzzgen` differentially fuzzes the compiler against an interpreter of the same IR.

**Teaching.** Per-rule verification is achievable for us in exactly one place and it is the right
place: **the builtin table**. Each row is a claim "`OCaml form` denotes the same function as
`Lean constant` on domain `D`". The estate already *classifies* those claims — the `Fidelity`
inductive in `tools/Conform/Effect4/Lcnf.lean:33-44` has `exact | domain | approximate | unsound`
— but classification is a comment. For an `exact` row the obligation is a Lean theorem when the
OCaml side is modelled (`Ml/Profile.lean` already carries `LibVal` signatures and law names for
exactly this), and for a `domain` row it is a theorem plus a *checked* side condition. Cranelift's
answer to "there are too many rules to prove" is: prove them one at a time, and fuzz differentially
in the meantime. That is the shape to copy.

### 2.4 Coq extraction to OCaml — the closest analogue, and its pitfalls

This is our nearest relative and its failure modes are the ones to fear.

* **`Obj.magic`.** Coq's extraction erases dependent types and inserts `Obj.magic` where OCaml's
  type system cannot follow; the generated code then compiles but the type system is no longer
  evidence of anything. **We do not do this, and the reason is worth naming:** we do not extract
  from the *kernel* terms, we extract from **mono LCNF, where Lean's own compiler has already done
  the erasure** and reduced the type language to constants, `→`, `lcAny` and `lcErased`. There is
  no `Obj.magic` anywhere in `ocaml/gen/` or `ocaml/engine/api_engine.ml`, and `Ml/Profile.lean`
  bans the `Obj` module outright. This is the single biggest architectural advantage of the LCNF
  route over Coq-style extraction and it should be stated in the top-level docs.
* **`Extract Constant` as an unaudited trust hole.** Coq's realizations are unchecked axioms about
  OCaml. Our `Externs.lean` is the same object and the estate has three defences Coq lacks:
  the row *changes a type*, so a mis-firing rewrite is an `ocamlopt` error; the ledger is checked
  (a row nothing hits is fatal, `LcnfGen.lean:201-215`); and the functor body type-checks with no
  instance (`gen-check.sh:63-72`). What is missing is the fidelity obligation per row.
* **Erased `Prop` does not cross.** `decisions.md:63` (row 27) records this as a decision:
  "certificates do not cross (`Prop` erasure)". That is correct and it is *load-bearing* for §3(f):
  anything stated as a `Prop` — `TypedAt`, `HasTy`, the typed-state invariant — is invisible to the
  emitter by construction.
* **Axioms.** A Coq axiom extracts to `assert false`. Ours would be a `noncomputable` constant with
  no mono decl, which lands in `missing` and is **fatal**. Better than Coq's default.

### 2.5 CompCert, CakeML, WebAssembly, Rust MIR

* **CompCert / CakeML** give the theorem's shape: a per-pass forward simulation between two
  formal semantics, composed. The precondition is that both semantics are formal objects.
  Ours are: `Conform.Lcnf.Semantics` (561 lines, an evaluator for LCNF) and
  `Conform.Lcnf.SemanticsTarget` (606 lines, an evaluator for the emitted OCaml syntax, `evalT` at
  `:424`). Both are Lean functions. **Neither file contains a single theorem**
  (`grep -c '^theorem\|^lemma'` = 0 for `Semantics.lean`, `SemanticsTarget.lean` and `Rules.lean`).
  So today the estate has the two halves of a simulation statement and none of the statement.
* **WebAssembly** teaches target selection: prefer a target whose semantics is pinned and
  mechanized. OCaml's is not mechanized; this is a cost of the current choice, paid by
  `SemanticsTarget` being *our* model of OCaml rather than OCaml's.
* **Rust MIR** teaches two habits we can adopt cheaply: (a) an **interpreter for your own IR is
  the oracle** (Miri) — we have one and do not run it; (b) **golden IR dumps as regression tests**
  (`mir-opt`) — `Conform.Lcnf.Validity`'s per-declaration `declHash` and construct census
  (visible in the stored receipt `.lake/conform/artifacts/995ec3…/closure.json`) are already a
  golden IR dump; committing them per root set would turn "the compiler changed the shape of our
  machine's LCNF" from an invisible event into a diff.

### 2.6 The verification story, stated three ways

The honest statement of where we are: **there is no theorem that the OCaml runtime agrees with the
Lean machine, and the mechanical evidence is a differential that is mostly not run.** Three tiers,
each with what exists, what it would take, and the cost.

**Tier 1 — golden traces (stamped).** `ocaml/eff/goldens/**` are Lean-cut bytes, JSON and typing
verdicts; `ocaml/goldens/eff/*.hex` are cut by Lean's own `Program.Wire`; `dune test eff` compares
them. This proves the *codec* agrees. It says nothing about the machine. It is cheap, it is in
`make check-ocaml`, and it works — the metadata coverage gate (§1.6) is why step 1 could not
silently skip a face.

**Tier 2 — differential testing (tested, but thin and partly ungated).** What exists:

| harness | subjects | corpus | gated? |
| --- | --- | --- | --- |
| `ocaml/gen/api_check.ml` | `api_gen` alone | **3** programs + 9 atom checks | yes, `dune test gen` |
| `ocaml/engine/test/test_diff.ml` | 3 OCaml engines (`Gen` / `Ref` / `Fast`) × 13 projections × many tapes | 37 byte goldens + truth corpus + **400** Lean-generated programs | yes, `make check-ocaml` |
| `test_diff.ml`'s `cross_face` (`:302-355`) | **Lean vs OCaml** | only the ~10 truth-corpus programs; only 3 projections (outcome, fibre count, exit *kind*) | **no** — "reported, not gated" (`:305-308`, `:352-355`) |
| `check-conform.py compiler` | LCNF evaluator vs emitted-OCaml evaluator vs native Lean vs `ocamlopt`-compiled OCaml, plus a **mutation that must fail** | 13 `Ty` vectors × 4 roots (`Ty.key`, `Ty.normalize`, `canonicalRaw`, `mergeColumns`) | yes, CI OCaml job only (`.github/workflows/lean_action_ci.yml:164`) |
| `Conform.Effect4.LcnfSemantics` / `LcnfMl` — the **20,387-vector** rung-2/rung-3 differential | LCNF evaluator, emitted OCaml read back, native Lean | 1,330 unary + 3,249 pair `Ty` vectors, 8 cases per unary and 3 per pair (`LcnfSemantics.lean:258-261`) | **no target and no CI job runs them** |

The last row is the finding. `tools/Conform/Cli/LcnfMl.lean` and `Cli/LcnfSemantics.lean` are
thin `main` drivers; `grep -rn 'Cli/LcnfMl\|Cli/LcnfSemantics'` over `Makefile`, `scripts/`,
`.github/workflows/` and `lakefile.toml` returns nothing. `docs/core/lcnf-route.md:58-59` cites the
20,387 vectors as the estate's evidence for "verified semantics". It is evidence that was
*produced once*, not evidence that is *maintained*.

**Tier 3 — a proved translation for a fragment.** This is statable and I recommend it be scoped
rather than dropped. The obstacle is precise: `OCaml5.Lcnf.Translate.code` is a `ReaderT TCtx
(StateM St)` action over `Lean.Compiler.LCNF.Code .pure`, it consults `Lean.Environment`, and
`Code .pure`'s semantics is not an object in Lean. You cannot prove anything about it directly.
The design that gets around it, in four pieces:

1. **A reference fragment.** An inductive `Frag` in our own namespace — exactly the 26-construct
   surface, but with `cases` carrying its own constructor table so that exhaustiveness is
   structural. This is a small inductive, perhaps 8 constructors.
2. **A checked reader** `ofCode : Code .pure → Except Refusal Frag`. This is *not* proved; it is
   the trusted door, and it is trusted the way `monoDecl?` is. Its obligation is discharged the
   way §4(i) says: the fragment predicate is decidable, every emitted declaration passes it, and
   Lean's own `Decl.check` passes on every one too.
3. **A pure lowering** `lower : Frag → Ml.Expr`, and `Translate.code` refactored to factor
   through it: `code = lower ∘ ofCode` on the accepted fragment, with the carrier/extern rewrites
   as a *separate* pass on `Frag` (which is where they belong — they are legalization, §2.2).
4. **The theorem.** `Conform.Lcnf.Semantics.eval` on `Frag` and
   `Conform.Lcnf.SemanticsTarget.evalT` on `Ml.Expr`, related by a value relation `R`, with
   `eval f v = some a → evalT (lower f) (Rv v) = some (Ra a)` — a forward simulation in CompCert's
   shape, by structural induction on `Frag`.

**Cost, honestly.** Piece 3 is the expensive one: `Translate.code` is 100 lines of monadic code
today but it carries five orthogonal concerns (naming, carriers, list literals, join-point
carrier seeding, wrapper folding), and factoring them apart is a real refactor of the one file the
whole OCaml estate depends on. Piece 4 is then mostly mechanical but the value relation has to
cover `Nat`-as-`int`, and *there the theorem is false* — it holds only under `n < 2^62`, so the
statement carries a side condition that has to be threaded, or the `Nat` carrier has to change
first. Piece 1 and 2 are cheap and they are worth doing *on their own*, because they turn the
fragment from prose into a gate (§4(i)) whether or not the theorem ever lands. **Recommendation:
do 1 and 2 now, defer 3 and 4 past this push, and in the meantime make Tier 2 gated and wide —
that is where the ratio of assurance to effort is best by an order of magnitude.**

---

## 3. Robustness to the language push, item by item

Verdict key: **automatic** = the generator handles it with no edit; **needs a rule** = one table
row, policy row or fixture must be added, and something fails loudly if it is not;
**breaks** = something is wrong and nothing fails, or a hand file must be edited.

### (a) New `Ty` constructors (`unknown`, L5) — mostly automatic, one rule, **two breaks**

**Automatic.** Pipeline A's types come off the environment: `ocaml/eff/eff_types.ml` already
carries `Ty_unknown` (`:7`), `Ty_refOf`, `Ty_deferredOf` and `Ty_var` (`:23-25`) with their wire
tags at `:45-47`, and the wire and JSON codecs followed — `Ty.unknown` landing mid-seat is itself
the cleanest demonstration that pipeline A is automatic: four faces regenerated with no edit to
`World.lean`. Pipeline B's types likewise (`Lcnf/Types.lean:266-305` iterates `info.ctors`).

**Needs a rule, three of them, and all three refuse loudly:**
1. `tools/Effect4Gen/wire-tags.json` must list the constructor —
   `WireTags.requireListed` refuses an unlisted inductive family (`Eff/World.lean:156-158`).
2. `OCaml5.Eff.Emit.tyO` (`src/OCaml5/Eff/Emit.lean:366-386`) is a **hand match on `Ty`**; a new
   constructor is a Lean non-exhaustive-match error in the generator itself. That is a good gate
   (the compiler is the gate), but note that the alphabet emitter is *the* place where `Ty` is
   hand-transcribed to OCaml text, so every `Ty` change touches it.
3. `OCaml5.Eff.Metadata.types` (`:52-60`) must gain a sample, or `EffGen` throws
   "metadata reaches no …" (`Tools/EffGen.lean:140`). Step 1 added `refOf`/`deferredOf`/`var` and
   the mid-seat `Ty.unknown` landing added `("unknown", .unknown)` at `Metadata.lean:53`. That
   gate has now fired correctly twice in one day; it is the best-working gate in the estate.

**Break 1 — `ocaml/engine/e4_program.ml:120-139`, now half-repaired in front of me.** A
hand-written `of_ty : Eff_types.ty -> A.ty` with **16 arms**, against an `Eff_types.ty` that had 19
constructors when I started reading and has 20 now. It is the only translation from the wire type
to the engine type (`of_ty` is reached from `Eff_iterate`'s cursor annotation; there is no reverse
`to_ty`). When I first read it there was **no default arm**, so the failure mode was either an
`ocamlopt` warning-8 build failure (`ocaml/engine/dune` sets `-w +a-4-9-40-41-42-44-45-70`, which
does **not** exclude 8) or a `Match_failure` raised inside the engine; which of the two I could not
settle without running `dune`, and the command that settles it is
`cd ocaml && opam exec --switch=effect4 -- dune build engine`. As of this writing the file carries
`| _ -> failwith "e4_program: Ty constructor beyond the frozen engine's alphabet"` (`:139`) — which
is precisely the interim repair recommended below, arrived at independently. So the failure is now
*named*: a program whose type annotation mentions `unknown`, `refOf`, `deferredOf` or `var` refuses
loudly in the engine instead of corrupting or crashing. Good. The remaining gap is that the four
arms are still missing, so those programs cannot be *run* by the engine at all — the engine is four
constructors behind the language, loudly.
*Fix:* this file is what `2026-09-17-runner-schema-codegen-plan.md` §3 already sentences to death —
"`engine/e4_program.ml` (the hand translation between two OCaml copies of one type, 430 lines),
`e4_program_layout.ml`, `scripts/generate-engine-structure.py`, the ordinal pin and the manifest
check. There is one copy of the program type, the engine's, and bytes are how a program reaches
it. This is the drift source, removed rather than generated." Do that. Until then, the interim fix
is one line: give `of_ty` a `| _ -> failwith "e4_program: Ty constructor beyond the frozen engine"`
so the failure is named rather than a `Match_failure` (**done**, `:139`), and add the four
missing arms so the engine can actually carry them.

**Break 2 — `ocaml/engine/e4_program_layout.json`.** The file says
`{"family": "Effect4.Program.Ty", "reason": "source-append-unavailable-in-frozen-engine",
"engine": 16, "source": 19}`. That row was **added by `7db30c8a` itself** (the commit's diffstat
shows `+6` lines on that file); `Ty` is now at 20, and the file still says 19, because the layout
step (stage A6) has not re-run since `Ty.unknown` landed — so the mirror not only records the
divergence, it *under-records* it. `make check` is green with it, because
`scripts/lib/program_structure.py:162-164` *records* an append shortage as a boundary instead of
raising, while a *changed or reordered* existing constructor does raise (`:160-161`). So the
design deliberately admits "the engine is behind" as a recorded state. See §5.1 for why that is
the wrong default and what to do.

**Break 2b — the case-site policy.** `tools/Conform/Effect4/cases-policy.json` has 32 decided
`Effect4.Program.Ty` sites, each with a `cover` list of the 15–16 constructors its default arm may
absorb, and `unlisted: "refuse"`. The check refuses when `absorbed ≠ cover` exactly, naming both
directions (`tools/Conform/Lcnf/Cases.lean:621-633`). The file has **zero** occurrences of
`refOf`, `deferredOf` or `unknown`; its last commit is `3f7bda29`, before the `Ty` growth; and `.lake/check/cases` is
stamped `Sep 17 23:56`, before `7db30c8a`. Since step 1's rule was "every catch-all alternative a
wildcard", every one of those default arms now absorbs three more constructors than its cover
names. **Assumed:** `make check-cases` is red. Command that settles it:
`make -B check-cases`. *Fix:* this is working as designed — the gate is telling you a decision has
gone stale. Re-seed the covers with `Cases.seed` (`Cases.lean:704-713` builds a policy from a
measured scan) and **sign the diff**, which is what the module's own docstring asks for
("Constructor covers come from a measured scan … and every later edit to it is a diff a human
signed"). Do this once for L5 (`Ty.unknown`) too, in the same slice.

### (b) New `NativeAtom` constructors and `eval` with `Option` results — automatic, one rule

**Automatic, already demonstrated.** `NativeAtom.eval` is reified at
`ocaml/gen/api_gen.ml:2589` as a flat `match` on the enum with nested `match` on the argument list
and `Val` shape; `Option` is OCaml's `option` natively, and the Lean `Option`-monad `do` blocks
have been compiled away by mono, so the output is plain `match … with None | Some x`
(`:2918-2923`). `NativeAtom.all` comes out as a module-level **value**, built once
(`:1382-1400`). Adding L3's 17 atoms adds arms and nothing else. `stringsAtom`'s variadic shape
already works.

**Needs a rule: the name lookup, and it is a real cost.** `Term.app` carries the atom as a
`String` (`src/Effect4/Machine/Term.lean:103`), and `nativeAtom` resolves it with
`NativeAtom.ofName? = all.find? (·.name == value)` (`:185`, `:258-259`). The emitted form is a
linear scan that calls `program_native_atom_name` per element
(`ocaml/gen/api_gen.ml:1477-1484`, `:1491-1493`). So **every term application in the OCaml engine
costs up to 20 constructor-match + string-compare pairs today, and up to 37 after L3.** It is
correct and it is quadratic in the wrong place: L4 makes `refUpdate` evaluate a term inside
*every* store step, so this scan moves onto the machine's hot path. *Fix:* see §4(v) — make
`ofName?` a generated `match` on the string, which OCaml compiles to a decision tree rather than a
scan, and keep `eval` a match on the enum.

### (c) `SyncOp.refUpdate cell (f : Term) (env : List Val)` with `refStep` calling `evalTerm` — automatic, one rule, one bootstrapping hazard

**Automatic, for the interesting part.** The worry in the brief is mutual recursion over
`Term`/`Terms` inside a store step. Both halves are already translated as one mutual group —
`let rec program_eval_term … and program_eval_terms …` (`ocaml/gen/api_gen.ml:2912`, `:2925`) —
because `emissionGroups` runs `Lean.SCC.scc` on the translated-name graph and emits one binding
group per component (`Translate.lean:1100-1121`). `refStep` (`src/Effect4/Machine/Stores.lean:880`)
gaining a call edge to `evalTerm` adds an edge to a node already in the closure; the SCC pass
reorders as needed. `SyncOp` gaining `Term` and `List Val` fields is one more variant arm in
pipeline A and pipeline B both. Nothing to write.

**Needs a rule: `Term` must be in the layer below the stores, and it is.** L1 already did it —
`src/Effect4/Machine/Term.lean` (untracked) holds `Lit`, `Term`, `Terms`, `NativeAtom`, `eval`,
`evalTerm` in namespace `Effect4.Program`, below `Stores.lean`, and the module's own docstring
gives the reason ("so that a store step can evaluate a term … and stay one atomic step"). The
namespace was kept deliberately so the wire tags, the generator's `Effect4.Program.Term` selection
(`tools/Tools/ProgramStructure.lean:21`) and every consumer are unchanged. That is the right call
and it is why (c) is nearly free.

**Bootstrapping hazard — retiring `FnName` breaks the regeneration command.** The root set of
`ocaml/engine/api_engine.ml` is stored **inside the generated file's own header**
(`:1-2`) and names `Effect4.Machine.FnName.total`, `.partialUpdate`, `.modify`, `.modifySome`;
`scripts/generate.py:110-114` reads the command back out of that file and runs it. Deleting
`FnName` makes those four roots resolve to nothing, `mono.findIn? env n` returns `none`, they land
in `Closure.missing`, and `LcnfGen` throws (`LcnfGen.lean:166-167`). So to regenerate after the
deletion you must first hand-edit a file whose second line says "Do not edit". *Fix, and it is
small:* move the four root sets into one tracked input — `ocaml/gen/roots.json` or four Makefile
variables — have `generate.py` read *that*, and render the header line *from* it. Then a root's
retirement is an ordinary diff on a tracked file. Do this **before** L4, because L4 is the slice
that retires `FnName`.

Second, minor: `Effect4.Machine.FnName` is a selected family
(`ProgramStructure.lean:27`) and is in `wire-tags.json`. Removing it from the Lean side leaves
`api_engine.ml`'s `fn_name` type declared and unreferenced — `program_structure.py` iterates over
*source* families (`:124`), so an engine declaration with no source family is silently ignored.
A dead type in the engine is harmless but it means the layout mirror cannot tell you the engine is
*ahead* either. Symmetric refusal (§5.1's fix) covers this.

### (d) `Ty.instantiate` / `matchTemplate` / `rowTy` — the checker is **not** in the closure, but `NativeOp.row` **is**

**Decided from the root, with evidence.** `Api.run` and `Api.replay` are documented raw — "it
checks neither the program nor the table" (`src/Effect4/Api.lean:321-323`) — and
`grep -c "typeOf\|type_of" ocaml/gen/api_gen.ml` is **0** over 659 declarations. The checked face
(`Api.HostSession.start`, `Api.Runner.load`) is not a root of any of the four outputs. So
`Ty.instantiate`, `Ty.matchTemplate` and the checker's `perform` rule do **not** enter the OCaml
closure, and L4 does not change that **provided the machine never instantiates a row**.

**But `NativeOp.row` is in the closure**, and it is the one thing that drags `Row` and therefore
`Ty` into the runtime: `ocaml/gen/api_gen.ml:3401-3403` translates
`Effect4.Program.NativeOp.row : NativeOp → Row`, and the two call sites are
`:3763` and `:4178`. At both, the machine reads **exactly one field**:
`match (_x : row) with | { kind = kind; _ } -> …` (`:3765`, `:4180`). Everything else in the
12-field record — `request`, `answer`, `error` (three `ty` values), `spelling`, `cite`,
`typeArgs`, `requires`, `trailing`, `shape`, `registration` — is built and discarded on **every
`perform`** (the arms at `:3415`, `:3427`, `:3440`, … are the per-operation record literals).

So the design answer for (d) has two parts:

1. **Keep the checker out.** Do not add `HostSession`/`Runner` to the `api_engine` roots for their
   *checking*; add them (per the runner plan §4) for the *session transitions*, and keep `start`'s
   certificate on the Lean side or behind a bytes boundary. If `HostSession.start` ever becomes a
   root, `Ty.instantiate`, `matchTemplate`, `rowTy`, `sub`, `normalize`, `join` and `diffTag` all
   enter the engine at once, and the engine acquires a second type checker whose agreement with
   Lean's nothing checks. That is the outcome to avoid, and today's root set avoids it.
2. **Split `kind` off `row` before L4.** Add `NativeOp.kind : NativeOp → RowKind` (a match, no
   record), have the two machine sites call it, and `Row` leaves the runtime closure entirely —
   along with `Ty`, `ServiceKey`, and the per-`perform` record allocation. This is a small,
   self-contained improvement that (i) removes ~150 lines of generated record literals, (ii) makes
   the L4 template change provably invisible to the engine (the engine's closure stops mentioning
   `Ty` at all, so `var 0` in a row cannot reach it), and (iii) is exactly the altitude move the
   estate's own rule asks for. **Cost/risk:** `NativeOp.row` and `NativeOp.kind` must agree —
   `kind = (row op).kind` is a one-line `rfl`-or-`cases` lemma per operation, or one `aesop` over
   the enum. The risk is a *third* place stating an operation's kind; mitigate by defining
   `NativeOp.kind` first and `row`'s `kind` field as `kind op`, so there is one source.

### (e) `Val.hasTyWith (oracle : HandleKind → Nat → Ty → Bool)` — LCNF lowers it; the machine should not *use* the parameterised version

**LCNF lowers higher-order parameters, four independent witnesses in the current output:**
`memo_world_update_entry … (f : memo_entry -> memo_entry)` (`ocaml/gen/api_gen.ml:5725`);
`list_nodup_decidable (inst_1 : _ -> _ -> bool)` (`:2130`);
`store_image_equiv (i : _ image) (f : _ -> _) (g : _ -> _)` (`:1851`); and — closest to the case
at hand — `program_val__has_ty__lam_0` (`:9689`), a lifted lambda from inside `hasTy` itself,
passed as a *value* to `program_reason_admits` at `:9786-9787`. The mechanics are
`monoTy`'s `forallE → .arrow` (`Translate.lean:78`), `letValueExpr`'s `.fvar f args → .app`
(`:697-702`), and `Lcnf/Types.kernelTy`'s non-dependent-arrow case (`Types.lean:169-175`). So
`hasTyWith` translates with no new rule.

**The machine should nevertheless not run the parameterised version, and the reason is
measured, not stylistic.** `Val.hasTy` is on the engine's external-answer admission path:
`program_external_value` (`:9745`, calling `hasTy` at `:9750`) and `program_err_admits` (`:9786`) call it per admitted value,
and `hasTy` recurses structurally over the whole value. Replacing the concrete `match` on
`Ty.handle` with an indirect call through an oracle parameter costs one closure call per handle
node, unless Lean's mono phase specialises `hasTyWith coarse` into a `._at_.hasTy.spec_0` twin —
which it does for `List.all` inside `hasTy` today (`:9505-9506`) but which I cannot promise for a
function-valued argument. *Design:* define `hasTyWith` for the proofs, define the runtime
`hasTy` concretely, and connect them with a lemma `hasTy v t a = hasTyWith coarse v t a` rather
than a definitional abbreviation. Then the laws generalise once (which is what L2 wants) **and**
the engine keeps its direct match. If you prefer one definition, mark `hasTyWith` `@[specialize]`
and then *check* the outcome mechanically: the closure report must show
`Val.hasTyWith._at_.Val.hasTy.spec_0` and not a bare `hasTyWith` with an arrow parameter.

One caveat worth recording: `kernelTy` only spells a **non-dependent** arrow
(`Types.lean:170`, `if b.hasLooseBVars then return (none, #[])`). An oracle whose type mentions a
bound variable — e.g. a dependent `(k : HandleKind) → Fits k → Bool` — becomes `lcnf_unknown` in
any *field* it sits in. Keep the oracle a plain first-order arrow.

### (f) A `List Ty` world column in the typed-state invariant — proof-only, and here is how to *check* that mechanically

**It cannot enter the closure, by construction.** `TypedAt` and `HeapFits Ρ` are `Prop`s; the
mono phase erases `Prop` before `saveMono` runs, and the estate depends on this in two places:
`Lcnf/Types.isIrrelevantFieldType` is literally `isProp <||> isTypeFormerType`
(`Types.lean:102-103`), the same predicate `Irrelevant.getRelevantCtorFields?` uses, and a field
satisfying it is **not emitted** (`:281`); and `docs/core/decisions.md:63` (row 27) records
"certificates do not cross (`Prop` erasure)" as a ratified fact.

**But "by construction" is not a check, and the push is exactly when it stops being true by
accident.** The hazard is not `Ρ` in a `Prop`; it is `Ρ` in a *structure a `Prop` mentions*. If a
future `TypedState` is a `structure` with a computational `Ρ : List Ty` field that some runtime
function reads, it crosses silently. The mechanical check is one line of the fix in §4(i): commit
the closure manifest. `LcnfGen` already prints `translated ({n})` with every Lean name
(`LcnfGen.lean:151-153`); write it to `ocaml/gen/closure-<output>.tsv`, commit it, and
`check-gen`'s `git diff` turns "a new Lean declaration entered the runtime" into a reviewable
diff. Today there is no artefact that says what the runtime closure is, so a new entrant is
invisible.

---

## 4. Improvements to the core pattern

### (i) An emitter self-check gate: the accepted fragment as a decidable predicate over the closure

**Most of it exists and none of it gates.** Four checks, in increasing cost:

| check | what it decides | where it is | status |
| --- | --- | --- | --- |
| the construct census | which of the 26 pure-fragment constructors each decl uses | `Conform.Lcnf.Validity.constructs` (`tools/Conform/Lcnf/Validity.lean:53-59`) | run only in the `compiler` conform profile, over 4 roots |
| Lean's own structural checker | fvar and join-point scoping, `cases` well-formedness, call arity | `Validity.checkDecl`, wrapping `Decl.check` under `runCompilerWithoutModifyingState` (`:375-380`) | same |
| the target well-formedness check | 12 syntactic properties + 4 profile properties of the emitted module | `OCaml5.Ml.Check.checkModule` / `Check.profile` (`src/OCaml5/Ml/Check.lean:13-35`) | **runs on every generation and is printed as "informational"** (`Tools/LcnfGen.lean:172-176`) |
| the case-site policy | every default arm in the compiled code, against a signed decision | `Conform.Lcnf.Cases` + `cases-policy.json` | **gated, in `make check`** (`Makefile:279`) — the one that works |

**Design.** A `Conform.Lcnf.Fragment` module with one decidable function
`accepts : Decl .pure → Except Refusal Unit`, written as the *exact complement* of
`Translate`'s six `todo` sites plus the builtin/extern coverage question, i.e.:

```
accepts d :=
  d.value is .code                                  -- not an extern without a row
  ∧ every `cases` on Bool has both arms or a default
  ∧ every `proj` is on a structure or on Prod
  ∧ every `Alt.alt` names a constructor of the scrutinee's inductive
  ∧ every called global is: in the closure, a builtin row, an extern row, or a constructor
  ∧ every carrier-valued position is a carrier position or has a `to_list` row
```

and then three wirings:

1. `LcnfGen` runs `accepts` over `closure.decls` and makes a failure **fatal**, beside the existing
   `missing`/`todos`/`collisions` refusals. This is strictly redundant with the `todo` mechanism
   *today* — and that is the point: it turns "the translator happened to have a rule" into "the
   fragment is stated, and the translator is checked against the statement". The moment a rule is
   added without a fragment clause, or a clause without a rule, one of them is red.
2. `Ml.checkModule` becomes fatal. **The honest obstacle:** it is informational today because the
   `--prelude` splice is an `Expr.raw` whose symbols the checker cannot see ("`Expr.raw` is
   opaque", `Ml/Check.lean:43-45`), so the seamed output reports `unbound-value` for every prelude
   symbol. The fix is small and is already half-built: `Ml.Check` counts `rawSites`, so add a
   declared symbol list to the prelude file (a `(* EXPORTS: … *)` line, or better, the prelude
   becomes `Ml.Decl`s rather than raw text) and make the check fatal for the unseamed outputs —
   `machine_gen`, `fibers_gen`, `api_gen` — **today**, since those have no prelude, and for
   `api_engine.ml` after the prelude declares its exports.
3. A **committed closure manifest** per output: `ocaml/gen/closure-api_gen.tsv` etc., holding one
   row per translated declaration (Lean name, OCaml name, recursive, the 26 construct counts, and
   Lean's own `declHash`). `LcnfGen` already computes all of it (`LcnfGen.lean:151-165` prints
   `translated`, `missing`, `frontier`, `wrapperRefs`, `todos`, `full`, `aliases`, `placeholders`,
   `notInductive`, `unknown`, `collisions`, and the `declHash` is in `Validity`). Add it to
   `GENERATED_PATHS` and `check-gen`'s `git diff` makes three invisible events visible: a new
   declaration entering the runtime closure (§3(f)), the cap starting to bite (`frontier`
   non-empty), and a Lean-toolchain upgrade changing the shape of the machine's LCNF.

**Cost/risk.** (1) is one module of maybe 150 lines and a day of matching it against
`Translate.lean` clause by clause; its risk is a *false* refusal that blocks generation, so land it
first as a warning-with-a-count, confirm the count is 0 on all four outputs, then make it fatal in
a second commit. (2)'s risk is the prelude work, which is real but bounded (one file,
`ocaml/engine/tools/api_engine_prelude.ml`). (3) is nearly free and I would do it first: it is the
only one of the four that would have *caught the two breaks in §3(a)* at review time, because the
manifest diff on `Ty`'s constructor count would have appeared in `7db30c8a`'s own diff.
**Red control for each:** for (1), a scratch Lean file with `| _ => ` on a policy-refused site must
be refused; for (2), a hand-inserted unbound name in a scratch copy of `api_gen.ml` must fail;
for (3), the `git diff` over a manifest with one row deleted must fail `check-gen`.

### (ii) Generating the OCaml *types* from Lean's inductives, with variance and mutability metadata

**The current state is two universes for one language.** Pipeline A has `OTy`
(`src/OCaml5/Eff/World.lean:40-48`: `int bool string unit option list prod named requirements`) and
pipeline B has `Ml.Ty` (`con arrow tuple var anon` plus the builtins of
`Lcnf/Types.builtinTy?:49-63`). They disagree about three things that matter:

* `OTy.requirements` is a **semantic** carrier — "strictly ascending `ServiceKey` list: proof-free
  bytes, checked at the boundary" (`World.lean:46`) — with the canonicality check compiled into the
  emitter (`Emit.lean:129`, `:140`). Pipeline B has no such notion; it would emit a plain list.
* `OTy` has no arrow, so pipeline A cannot carry a function-typed field at all; pipeline B can
  (`Types.lean:169-175`), non-dependently.
* `Array` is `list` in B (`Types.lean:59`) and does not exist in A.

**Design: one `Target.Layout` object, both pipelines project it.**

```
structure ParamInfo where
  name      : String          -- the OCaml type variable
  phantom   : Bool            -- appears in no relevant field of any constructor
  variance  : Variance        -- Co | Contra | Inv | Bi, computed from field positions
structure FieldInfo where
  leanName  : Name
  ocamlName : String
  relevant  : Bool            -- the compiler's own predicate, isProp ∨ isTypeFormerType
  ty        : Ml.Ty
  carrier   : Option Chain    -- an Externs `field` row, or A's `requirements`
inductive Layout
  | builtin  (ty : Ml.Ty)
  | alias    (ty : Ml.Ty)     -- a trivial structure, hasTrivialStructure?
  | record   (fields : List FieldInfo)
  | variant  (ctors  : List (String × List FieldInfo))
  | carrier  (chain : Chain)  -- an Externs `type` row
  | placeholder
def layoutOf : Name → MetaM (ParamInfo × Layout)   -- ONE reader of the environment
```

What this buys, concretely:

* **`Ty.unknown` and every later constructor is one place.** Today `Ty` is transcribed to OCaml
  text by hand in `Emit.tyO` (`Emit.lean:366-386`) *and* read from the environment in
  `Types.typeInfo?`. With `layoutOf`, `tyO` becomes a fold of `Layout` and the hand match goes.
* **`phantom` and `variance` remove the `undetermined-param` diagnostics** (`Ml/Check.lean:18`) —
  today they are part of the "informational" noise that keeps `checkModule` from being fatal, so
  (ii) unblocks (i)(2).
* **Mutability has exactly one home.** Lean has no mutable fields, so every generated record is
  immutable and every mutable thing is a *carrier* — which is already true and already stated by
  the `Externs` `field`/`type`/`elem` rows. Making `carrier` a field of `FieldInfo` says it in the
  type rather than in a side table consulted at three call sites
  (`Types.lean:292-297`, `Translate.lean:544-549`, `Translate.lean:800-803`).
* **It is the object a TypeScript target needs** (4(iv)), because the TS emitter needs exactly
  this — field names, relevance, tag spellings, phantom parameters — and nothing else about Lean.

**Cost/risk.** This is a refactor of two working generators whose outputs are byte-pinned by
`check-gen`. That is the *good* case: do it as a strict refactor, derive both old outputs from the
new object, and the receipt is `make check-gen` showing no diff on 14 generated files. The risk is
scope creep — `layoutOf` wants to absorb the wire tags, the schema bridge and the TS profile, and
it should not. Keep it to "what shape does this Lean type have in a target", one reader, two
projections. **Not in this push**; it is the natural first slice after L6, when the faces have
settled.

### (iii) A differential harness between the Lean machine and the OCaml engine on the corpus

**Three exist; the Lean-versus-OCaml one is the thin and ungated one.** From §2.6's table: the
`Gen`/`Ref`/`Fast` triple differential over 37 goldens + the truth corpus + the 400 Lean-generated
programs with 13 projections per replay position (`ocaml/engine/test/test_diff.ml`) is real,
gated, and wide — but it compares **three OCaml engines with each other**. The only place Lean's
own answer enters is `cross_face` (`:302-355`), which covers ~10 truth-corpus programs, compares
three projections (outcome, fibre count, exit *kind* — not the exit *value*), and is explicitly
"reported, not gated" (`:305-308`, `:352-355`). The 400 programs carry Lean's **typing** verdict
only: `tools/Tools/Corpus.lean:80` writes `name, wellTyped, readable, chars, reason, path, codes`
and nothing about running them.

**Design, in three steps, each independently useful.**

1. **Record Lean's run answer in the corpus index.** In `tools/Tools/Corpus.lean:80`, add three
   columns from `Api.run p fuel`: the outcome tag, the fibre count, and the root exit as
   **canonical bytes in hex** — bytes, not a rendering, because `Canonical` already gives exactness
   and the OCaml side already has the decoder. The index is installed as
   `generated/corpus-index.tsv` (`Makefile:198-201`) which `check-gen` holds, so **Lean's own
   answers become a committed pin** and a change in the machine's behaviour shows up as a diff on
   that file, per program, by name. That alone is worth the slice: it is DI-60's mechanism
   extended from "which programs type" to "what the machine answers".
2. **Gate `cross_face` on it.** `Corpora.lean_corpus ()` already parses `index.tsv`
   (`ocaml/engine/corpora.ml:366-376`; the description is at `:22-27`), so the new columns arrive for free. Replace the
   `note "reported, not gated"` with a `check`, and turn the two known name collisions (a `.hex`
   and a `.bin` golden sharing a name, `test_diff.ml:305-308`) into **two named exceptions** rather
   than a blanket exemption. Compare the exit *bytes*, not the exit kind.
3. **Wire the 20,387-vector lane.** `Conform.Effect4.LcnfSemantics` and `LcnfMl` already emit
   Conform reports; they need a `PROFILES` entry in `scripts/check-conform.py:33-40` and a
   `$(CHK)/lcnf-vectors` rule in the Makefile, in `check-host` (or the CI OCaml job, where the
   `ocamlopt` the `compiler` profile needs already lives).

**The red control, which the brief is right to insist on.** The estate already has the pattern and
it is the best thing in `check-conform.py`: the UTF-8 mutation at `:69-79` — mutate the emitted
`Char.code (String.get s i)` to `0`, require that it still *compiles* and that the selected
observation *fails*, and refuse if "the mutation did not fail the selected observation". Copy it
verbatim for the corpus differential: one scratch-copy mutation of `ocaml/gen/api_gen.ml` (e.g. one
`Nat.sub` clamp removed, or one `RowKind_sync` arm swapped) must be caught by at least one of the
400+ programs, and the number of programs that catch it is the harness's *sensitivity*, worth
printing.

**Cost, honestly, and the mitigation.** Step 1 makes `make corpus` run the machine 400 times where
today it only prints and types. I cannot measure it from this seat; the two mitigations are (a) the
Makefile already keys the corpus on `Tools.Corpus`'s Lake trace so it re-cuts only when the
generator, the printer, the wire or the tool moves (`Makefile:195-201`), and (b) if it is too slow,
record the run answer for a pinned subset — the wire corpus plus every fourth generated program,
100 of the 400 — and *say in the file's header which subset it is*, so the coverage is a stated
number rather than an impression. Step 3's cost is a few minutes of `ocamlopt` per run and belongs
in `check-host`, not `check`.

### (iv) Could `ts/eff` also be reified from LCNF?

**Measured first: `ts/eff` is already 8 generated files and 3 hand files**, and only one of the
three is substantial — `read.ts` (1,609 lines), beside `check.ts` (87) and `check-styles.ts` (49).
The generated column is `eff.gen.ts`, `json.gen.ts`, `profile.gen.ts`, `taxonomy.gen.ts`,
`forms.gen.ts`, `templates.gen.ts`, `wire.gen.ts`, `packages.gen.ts`. So the question is
*entirely* about the reader.

**The seam is already exact, and both sides say so.** `read.ts`'s own header (`:1-14`) draws its
pipeline: `parseSync` (oxc) → `programModuleOf` → `exprOf` (ESTree → "the fragment the Lean printer
emits") → `readEff(0, ·)` ("one matcher over the table Lean prints from") → `readModule` →
`decodeEff`; and it states the division: "Everything else in this package is generated from Lean …
This file holds what is logic and not data". Meanwhile the Lean reader
`Effect4.Program.readT` consumes a `TypeScript.Expr`/`Stmt` AST, never text
(`src/Effect4/Codegen/Read.lean:44`, `open TypeScript (Expr Stmt)`), and its generic step and
completeness are proved over the table (`Laws/Codegen/{Read,ReadPrint,PrintReadable,ModuleReadable}`).

So: **yes for §3 of `read.ts`, no for §2, and the boundary is `TypeScript.Expr`.**

* §2 (`programModuleOf`, `exprOf`) has **no Lean counterpart to lower** — Lean never parses
  TypeScript text, by design — so it stays hand-written. It is the host-parser adapter and it is
  the right place to admit a host dependency (oxc).
* §3 (`readEff`, the leaf readers, the row reader) **is** the LCNF image of `readT` and its leaf
  readers. Reifying it would move roughly two-thirds of `read.ts` into the generated column and buy
  the real prize: the TypeScript reader's completeness stops being a port's promise and becomes the
  Lean completeness theorem.

**What it needs, beyond the emitter.** `docs/core/lcnf-route.md` §4 lists eight items; three bite
here and one of them the note under-weighs:

1. the emitter into `TypeScript.Expr`/`Stmt` rather than strings (item 1) — which is also what makes
   rung 3's reader for the TS target possible;
2. sums as a `switch` on `_tag` with the **same** spellings `eff.gen.ts`'s `Schema.TaggedUnion` uses
   (item 2) — one encoding for the value and for the code that destructs it;
3. `Nat` as `bigint` or `number` (item 5) — a profile row, exactly as `powClamped` is for OCaml;
4. **tail calls (item 4), which is the one with a semantic bite.** `readT` recurses on the size of
   the tree; OCaml and Lean handle a deep program, and JavaScript overflows the stack. A stack
   overflow is *not a refusal* — it is an outcome outside the Lean function's range — so either the
   emitter trampolines self-tail-calls into `while (true)` with reassignment, or the TypeScript
   reader's contract gains a depth bound and the printed corpus gains a program that hits it.
   This must be decided before, not after, the emitter is written.

**Recommendation and cost.** This is a second backend and it is the largest item in this note.
**Not in this push.** But land the *seam* now, cheaply: split `read.ts` into `read-parse.ts` (§2,
ESTree → `TypeScript.Expr`-shaped JSON) and `read-table.ts` (§3, the generic step and the leaf
readers), with the boundary being exactly the printer's AST. Two benefits immediately: the hand
column drops to ~500 lines and is *named* as the host adapter, and when the emitter exists the
cutover is a file swap with `make check-ts-reader` (which already reads the 400 printed programs
and compares bytes against Lean's) as the differential.

### (v) How the atom table should be shaped so LCNF lowering of `eval` stays trivial

**The count first.** An atom's knowledge is in **twelve** places today: the `NativeAtom`
constructor (`src/Effect4/Machine/Term.lean:146-160`), `all` (`:165`), `name` (`:172`),
`names` (`:182`), `ofName?` (`:185`), `arity` (`:214`), `eval` (`:226`), then
`constGeneric` (`src/Effect4/Program/NativeAtom.lean:29`), `mono` (`:37`), `typeOf` (`:72`), the TS
prelude entry, and `eff_native.ml`'s `atom_names`/`const_atoms`
(`src/OCaml5/Eff/Emit.lean:484-486`). L3 adds seventeen atoms across all twelve.

**The tempting shape is wrong, and specifically wrong for LCNF.**

```lean
structure AtomRow where
  name  : String
  arity : Option Nat
  eval  : List Val → Option Val    -- ← do not do this
def all : List AtomRow := [ … ]
```

Three things break. (1) `eval` as a closure field lowers to a list of lifted top-level functions
referenced as values, and dispatch becomes *scan the list, then call through a pointer* — `eval`
stops being one `match` that OCaml compiles to a jump table. (2) The compiler's exhaustiveness
check, which is the single mechanism that has caught every omission in this tree, **stops firing**:
forgetting a row in a list literal is not a non-exhaustive match. (3) `Lcnf/Types.kernelTy` spells
an arrow field only when it is non-dependent (`Types.lean:169-175`), so the shape is one refactor
away from `lcnf_unknown`.

**The shape that keeps the lowering trivial and still gets the declarative object:**

1. **The enum stays the carrier and `eval` stays a `match` on it** — one arm per atom, as today.
   That is what gives the jump table in OCaml and the exhaustiveness error in Lean.
2. **Everything that is *data* moves into one row, and every per-atom function becomes a
   projection.** `structure AtomRow where name : String; arity : Option Nat; constGeneric : Bool;
   prelude : String` with `def row : NativeAtom → AtomRow` — still a `match`, still exhaustive,
   but **one** match instead of four. `name`, `names`, `arity`, `constGeneric` and the TS prelude
   entry become `(row a).field`; `eff_native.ml`'s two lists become
   `all.map (·.row.name)` / `all.filter (·.row.constGeneric)`, which is what `Emit.lean:484-486`
   already does structurally.
3. **`typeOf` stays separate and stays a match**, because it is not data: it is a function of the
   argument types with `sub` checks (`Program/NativeAtom.lean:72-90`). Keeping `Ty` out of
   `AtomRow` also keeps `Ty` from riding into the runtime closure the way `NativeOp.row` does
   (§3(d)); if `mono : Option (List Ty × Ty)` is wanted in the row, split `AtomRow` into a runtime
   half and a typing half.
4. **`ofName?` becomes a `match` on the string, not `all.find?`.** Two options.
   *(a) Cheap, no wire change:* `def ofName? : String → Option NativeAtom | "succ" => some .succ |
   … | _ => none`. OCaml compiles a string match to a decision tree, so the per-node cost drops
   from up to 37 name computations and compares to one; `ofName?_name`, `ofName?_sound` and
   `name_injective` (`Machine/Term.lean:187-199`) stay one `cases` each. The risk is a *second*
   spelling of the name table, which `row_name_injective` plus `ofName? (row a).name = some a`
   (both one `cases`) pin.
   *(b) Better, and it is a ruling for the owner:* stop carrying the name in the *machine*.
   `Term.app (atom : String)` is a string because "atoms are spelled by name on the wire, so
   appending it moves no ordinal and no byte" (`Machine/Term.lean:155-156`) — a real property,
   worth keeping for the **wire**, which does not require the **machine** to hold a string.
   `Term.app (atom : NativeAtom)` with the name ⇄ constructor map at the codec boundary removes the
   lookup from every step and keeps the append-only wire. It changes `Term`'s shape, hence `Term`'s
   wire tags, hence the goldens and the TS reader — so it is a ruling, not a slip-in.
5. **Keep `all_complete`** (`Machine/Term.lean:169-170`): it is what forces an appended constructor
   into the inventory, and the universal statement is worth more than the list.

**Why this matters more after L4 than before.** L4 makes `refStep` evaluate a term inside **every**
store step. Today the atom lookup is on the `Term.app` path only; after L4 it is on the machine's
hot path, once per `refUpdate`/`refModify`/`refUpdateSome`/… That is the reason to do step 4(a) in
the same slice as L3, not later.

---

## 5. Risks in the current implementation

Ordered by how badly each one damages the "one source of truth" claim. Each has the evidence, the
failure mode, and a fix sized to fit.

### 5.1 The engine mirror **records** a divergence instead of refusing it — and the fixpoint needs two passes

**Evidence.** `scripts/lib/program_structure.py:162-164`: when the engine declares fewer
constructors than the source, the producer appends
`{'reason':'source-append-unavailable-in-frozen-engine','engine':n,'source':m}` to `boundaries`
and continues; only a *changed or reordered* existing constructor raises (`:160-161`). The
committed result, today, in `ocaml/engine/e4_program_layout.json`:
`{"family": "Effect4.Program.Ty", "reason": "source-append-unavailable-in-frozen-engine",
"engine": 16, "source": 19}` — added by `7db30c8a` itself, and **already one behind again**: `Ty`
reached 20 constructors mid-seat and the row still reads 19, because stage A6 has not re-run.
`ocaml/engine/api_engine.ml:829` ends `Ty` at `Ty_lit of string`;
`ocaml/engine/e4_program_layout.ml` has 16 `Ty_` constructors; `ocaml/eff/eff_types.ml` has 20.

**Failure mode.** `make check` is green with the engine four constructors behind the language.
`check-gen` regenerates the *hermetic* groups (`Makefile:154,250`), which includes `eff` and
therefore `generate-engine-structure.py`, which re-derives the row and — because the shortage is
a boundary, not a refusal — writes whatever the new numbers are and still exits 0. The LCNF group is not in `HERMETIC_GROUPS`
(`Makefile:154`) so `api_engine.ml` is never re-cut in `check`; `git diff` catches a *hand edit* of
it but not *staleness*.

**Second defect, in the same place: the fixpoint needs two `make gen` passes.** `EFF_SOURCES`
includes `ocaml/engine/api_engine.ml` (`Makefile:93`) and `$(GEN)/lcnf` depends transitively on
`$(GEN)/eff` (`Makefile:120` ← `readme` ← `ts` ← `cas` ← `wire` ← `eff`), so within one `make gen`
the mirror is computed from the *old* `api_engine.ml` and then `api_engine.ml` is rewritten. A
single `make -B gen` therefore leaves `e4_program_layout.{ml,json}` one generation behind, and
`check-gen-full` reaches a fixed point only by being run twice.

**Fix.** The right fix is the one the tree has already designed:
`docs/research/2026-09-17-runner-schema-codegen-plan.md` §3 sentences `e4_program.ml`,
`e4_program_layout.ml` and `generate-engine-structure.py` to deletion — "There is one copy of the
program type, the engine's, and bytes are how a program reaches it. This is the drift source,
removed rather than generated" — and reports that the probe already ran: adding `Api.ofBytes` and
`Api.bytesOf` to the engine roots "translates the whole closure with no missing declaration and
nothing beyond the cap", needing three builtin rows (`Char.ofNatAux`,
`ByteArray.emptyWithCapacity`, `ByteArray.push`). **Do that.** Until it lands, two one-line
interim fixes: make `source-append-unavailable-in-frozen-engine` **raise** unless the family is
listed in an explicit, committed allowance file (so the divergence is a signed decision, not a
side effect), and move `$(GEN)/lcnf` *before* `$(GEN)/eff` in the Makefile order so one pass
reaches the fixpoint.

### 5.2 Three hand-written OCaml files sit in the load path, against the standing rule

The rule is "anything on the OCaml side not made directly from LCNF is ditched; keep only the
pipeline's import closure". Three files are in the path and are not from LCNF:

| file | size | what it is | how it fails |
| --- | --- | --- | --- |
| `ocaml/engine/e4_program.ml:120-139` | ~600 lines, `of_ty` is 20 | hand translation `Eff_types.*` → the engine's copy of the same types | `of_ty` has 16 arms against 20 constructors; as of this writing a named `failwith` catch-all (`:139`) has been added, so the four missing constructors refuse loudly instead of raising `Match_failure` (§3(a) Break 1). |
| `ocaml/engine/api_engine_inst.ml`, `api_engine_ref.ml` | 7.4 KB + 6.0 KB | hand transcriptions of `E4_program.PROGRAM_TYPES` and `E4_engine.INSTANCE` | defended: `ocamlopt` compares them against the generated file, and `test_diff.ml:53-57` says so explicitly ("a constructor that drifted … is a compile error here"). Acceptable as is. |
| `ocaml/engine/cas/e4_shape.ml` | 601 lines per the runner plan §2 | a per-kind schema table transcribed by hand | no gate at all: nothing compares it with Lean's `Store.Shape`. The runner plan §3 replaces it with a walk of the value by its `ShapeDoc`. |

**Fix.** `e4_program.ml` and `e4_shape.ml` both die with the runner plan's step 1. Interim: give
`of_ty` the four missing arms — the named `failwith` catch-all has landed at `:139` — and a one-line generated assertion
that `List.length Eff_types.ctor_names_ty = <n>` where `<n>` comes from Lean — a pin that goes red
on the next append instead of on the next `Match_failure`.

### 5.3 Root sets live inside files marked "Do not edit"

**Evidence.** `ocaml/gen/api_gen.ml:1-2` and `ocaml/engine/api_engine.ml:1-2` carry the full
regeneration command including every root; `scripts/generate.py:110-114` reads the command back out
of the generated file (`text.split('Regenerate with:\n', 1)[1].split('*)', 1)[0]`) and runs it.

**Failure mode.** Retiring a root — which L4 does, four times, when `FnName` goes — makes the
stored command name a constant that no longer exists; `LcnfGen` throws on `missing`
(`LcnfGen.lean:166-167`); and the only way to regenerate is to hand-edit a generated file. There is
a second, quieter mode: the root list is not reviewable as a tracked input, so "what is in the
runtime" is a fact you have to read out of a 1.1 MB artefact.

**Fix.** One tracked input — `ocaml/gen/roots.json` with four entries (out, import, cap, externs,
prelude, roots) — read by `generate.py`, with the header line *rendered from* it so the artefact
stays self-documenting. Do this **before L4**; it is half an hour and it unblocks the `FnName`
retirement.

### 5.4 `Ml.checkModule` runs on every generation and gates nothing

**Evidence.** `src/OCaml5/Tools/LcnfGen.lean:172-176`: the diagnostics are printed with the label
"informational; prelude symbols in rawD opaque". The check decides 12 syntactic properties and 4
profile properties (`src/OCaml5/Ml/Check.lean:13-35`), including `unbound-value`, `ctor-arity`,
`duplicate-field`, `profile-banned` (`Obj`, `Marshal`, `Domain`) and `bad-name`.

**Failure mode.** The one check that would catch a malformed *emitted* module is advisory, so the
first line of defence is `ocamlopt`, i.e. a separate tool in a separate lane (`make check-ocaml`,
not `make check`). A generated file can be committed that no one has compiled.

**Fix.** Make it fatal for the three unseamed outputs today (`machine_gen`, `fibers_gen`,
`api_gen` — they have no `--prelude`, so the `rawD` excuse does not apply to them), and for
`api_engine.ml` after the prelude declares its exported symbols. Two commits, the first of which is
a three-line change.

### 5.5 The estate's headline evidence is unwired, and two documents overstate what is checked

**Evidence.** `Conform.Effect4.LcnfSemantics` and `Conform.Effect4.LcnfMl` implement the
20,387-case differential (`LcnfSemantics.lean:258-261`: "The 20,387 cases: eight per unary vector,
three per pair", over 1,330 unary and 3,249 pair `Ty` vectors). Their drivers
(`tools/Conform/Cli/LcnfSemantics.lean`, `Cli/LcnfMl.lean`) are three-line `main`s.
`grep -rn 'Cli/LcnfMl\|Cli/LcnfSemantics'` over `Makefile`, `scripts/`, `.github/workflows/` and
`lakefile.toml` returns **nothing**. `tools/Conform/Effect4/Lcnf.lean` (the validity + fidelity
driver) is likewise unwired. And there are **no theorems** in the LCNF lane:
`grep -c '^theorem\|^lemma'` is 0 for `Conform/Lcnf/Semantics.lean`, `SemanticsTarget.lean` and
`Rules.lean`.

Two overstatements to correct while fixing it: `docs/core/lcnf-route.md:58-59` and `:111` present
the 20,387-vector differential as the estate's current evidence ("So 'verified semantics' today
means: a differential on 20,387 vectors…"), when it is evidence produced once; and
`docs/GENERATED.md:48` lists `make check-gen` as a check of the lcnf group, which is true only for
hand edits, not for staleness (§5.1).

**Fix.** §4(iii) step 3 — one `PROFILES` entry and one `$(CHK)` rule. Then amend both documents to
say which lane runs where.

### 5.6 `check-gen-full` is nightly-only, so the LCNF outputs are not regenerated on any change

**Evidence.** `.github/workflows/lean_action_ci.yml:169-170` gates `nightly-gen-full` on
`github.event_name == 'schedule'`; the push/PR jobs are `build`, `check` (→ `make check` →
`check-gen` → hermetic only), `check-tools`, `check-host` (a named subset, `:135`) and
`check-ocaml`. So a commit that changes the machine's Lean source and does not re-cut
`api_gen.ml`/`api_engine.ml` is green until the next nightly.

**Failure mode.** Exactly what §5.1 shows: the engine drifts behind the language for as long as
nobody runs `make gen-lcnf`, and the staleness has a window of up to a day plus however long the
nightly stays red.

**Fix.** Two options, and I prefer the first. (a) Add `make gen-lcnf` to the `check-ocaml` job,
which already has the `opam` switch and already spends minutes on `dune`; the LCNF cut is a Lean
run, not a proof, so the marginal cost is small and the job that would notice the breakage is the
job that builds the OCaml. (b) Keep it nightly and add a cheap *staleness* check to `make check`:
compare a committed closure manifest's `declHash` column (§4(i)(3)) against a fresh
`persistedMonoIndex` lookup — no translation, no emission, just 659 hash comparisons.

### 5.7 Fragile matching on constant names — mostly loud, two silent spots

**Evidence and the honest grading.** `Translate.builtin?` is 70 rows of literal `Name` patterns and
the module says so: "Names are unchecked literals: several are specialisations that only exist in
the target's environment" (`Translate.lean:152-153`), e.g.
`` `List.foldl._at_.Array.appendList.spec_0 `` at `:237`. `carrierRewrite?` matches by string
suffix: `s.endsWith "List.get?Internal"`, `"List.get?"`, `"List.getElem?"`, `"List.take"`,
`"List.takeTR"`, `"List.takeTR.go"` (`:624-645`).

*Mostly loud, and this is to the design's credit.* A `builtin?` row that stops matching means the
callee is translated from its own mono decl instead — either correct (a Lean-level body) or an
`extern` with no row, which is a `todo` and therefore fatal. A `carrierRewrite?` that stops firing
means `useAsList` inserts a `to_list` — correct, slower, and **reported** (`LcnfGen.lean:199-200`
prints every site) — or, for a carrier with no `to_list` row, a fatal `todo` (`:505`).

*Two silent spots.* (1) **The fidelity claims are comments.** `Nat.sub` truncating, `Nat.pow`
saturating, `Nat.shiftRight` clamping at 63, `UInt8.ofNat` masking, `Array.uget` → `List.nth`: each
is a claim about equality of two functions on a domain, and the estate *classifies* them
(`Fidelity` = `exact | domain | approximate | unsound`, `tools/Conform/Effect4/Lcnf.lean:33-44`)
without checking any of them, in a driver nothing runs (§5.5). A row silently reclassified from
`exact` to `domain` by a Lean stdlib change is invisible. (2) **The engine mirror parses OCaml with
a regular expression.** `scripts/lib/program_structure.py:33` is
`re.finditer(r'(?m)^[ ]*(type|and)\s+([^=\n]+?)\s*=', source)` over the *generated*
`api_engine.ml`; it does handle nested comments (`:17-31`) and raises on an ambiguous declaration
(`:49`), but a formatting change in `Ml/Render.lean` would silently change what the mirror believes
the engine declares.

**Fix.** For (1): move the builtin table into a *file*, as the externs table already is, with the
fidelity class and the domain as columns; then the `compiler` conform profile's mutation pattern
(§4(iii)) can be pointed at one row at a time, and an unclassified row is a refusal. For (2): it
disappears with §5.1's fix; until then, pin `Ml.Render`'s type-declaration format with one golden.

### 5.8 The `Metadata` gate covers the families a fixture *mentions* — a new family gets no coverage and no refusal

**Evidence.** `src/OCaml5/Tools/EffGen.lean:136-141`:
`for f in families do if ! (Metadata.all.any (·.family == f.spec.leanName)) then continue` — the
per-constructor coverage requirement (`:140`, "metadata reaches no {c.name}") applies **only** to
families some fixture already names. Meanwhile the corpus coverage loop excludes nine families by
name (`:185-187`) precisely because the corpus cannot reach them.

**Failure mode.** Add a family to `Tools.ProgramStructure.blocks` with no `Metadata` fixture and it
lands in `eff_types.ml`, `eff_wire.ml` and `eff_json.ml` with **zero** codec coverage and nothing
refuses. The `Ty` change did not hit this (the family was already covered, which is why `refOf`
*had* to be added to `Metadata.types:59-60`), but L7 (user service carriers) and row 2 (records and
variants) both add families.

**Fix.** Invert the condition: every family in the nine-name corpus exclusion list
(`EffGen.lean:185-187`) **must** be named by at least one fixture, or refuse. That is a five-line
change and it makes the two lists — what the corpus cannot reach, and what `Metadata` must
therefore cover — each other's complement by construction rather than by attention.

### 5.9 `frontier` is reported; `missing` is fatal

**Evidence.** `LcnfGen.lean:155` prints `frontier (beyond --cap {n})`; the fatal list at `:166-171`
is `missing`, `todos` and `collisions` only.

**Failure mode.** If the closure grows past the cap, generation *succeeds* and emits calls to
untranslated names. That is loud at `ocamlopt` (an unbound value is an error, not a warning), so the
practical risk is low — but the asymmetry is unjustified and the current headroom is unstated
(`--cap 2000`, 659 declarations today; `grep -c "LCNF mono:"` is the measurement).

**Fix.** One line: make a non-empty `frontier` fatal, and record the cap headroom in the closure
manifest (§4(i)(3)) so the number is visible.

---

## Recommendations for the push

Ordered, with the slice each belongs beside. "Now" means inside this push; "after" means the next
plan. Nothing here asks for a decision the owner has not already made except where marked
**ruling**.

### Now, before L3/L4 — three small things that unblock the push

**N1. Move the four root sets out of the generated files.** `ocaml/gen/roots.json` (out, import,
cap, externs, prelude, roots), read by `scripts/generate.py`, with each artefact's header line
*rendered from* it. Half an hour. **This is a blocker for L4**: L4 retires `FnName`, four of
`api_engine.ml`'s roots are `FnName.*`, and the stored command cannot be updated without editing a
file marked "Do not edit" (§5.3).

**N2. Re-seed the case-site policy and sign the diff.** `tools/Conform/Effect4/cases-policy.json`
has 32 decided `Ty` sites whose covers are four constructors behind, and `make check-cases` is
almost certainly red (§3(a) Break 2b — **assumed**; `make -B check-cases` settles it). Re-seed with
`Cases.seed` (`tools/Conform/Lcnf/Cases.lean:704-713`) and review the diff, which is what the
module asks for. Do it once now and once again with L5's `Ty.unknown`, in L5's own commit.

**N3. Finish `e4_program.ml`'s `of_ty` and pin the constructor count.** The named `failwith`
catch-all landed mid-seat (`:139`); what remains is the four missing arms
(`unknown`, `refOf`, `deferredOf`, `var`) and one generated assertion that the engine's `ty` arity
equals Lean's, so the next append goes red at build time rather than at run time (§5.2). This is a
stopgap for a file the runner plan deletes; write it as five lines with a comment saying so.

### Now, beside L3 — the atom table

**N4. One `AtomRow`, `eval` stays a match, `ofName?` becomes a match.** §4(v) steps 1–3 and step
4(a). The reason it belongs in L3 rather than after: L3 adds seventeen atoms across twelve places,
and L4 puts the name lookup on the machine's hot path (a term is evaluated inside every
`refUpdate` store step). Doing it with L3 costs one refactor; doing it after costs the refactor
plus seventeen×twelve edits made twice.

### Now, beside L4 — keep the runtime closure free of `Ty`

**N5. Split `NativeOp.kind : NativeOp → RowKind` off `NativeOp.row`.** The machine reads exactly
one field of a 12-field record it builds per `perform` (`ocaml/gen/api_gen.ml:3765`, `:4180`), and
that one field is why `Row`, `Ty` and `ServiceKey` are in the runtime closure at all. Define
`kind` first and `row`'s `kind` field as `kind op`, so there is one source and the agreement is
`rfl`. Payoff: after L4 the engine's closure does not mention `Ty`, so making rows templates
(`var 0` in `request`) is *provably* invisible to the engine (§3(d)).

### Now, cheap and high-leverage — make the invisible visible

**N6. Commit a closure manifest per LCNF output.** One TSV per output: Lean name, OCaml name,
recursive, the 26 construct counts, Lean's `declHash`; added to `GENERATED_PATHS`. Everything is
already computed (`LcnfGen.lean:151-165`, `Validity`'s `declHash`). This is the single change that
would have surfaced §5.1 and §5.2 inside `7db30c8a`'s own diff, and it is the mechanical check that
§3(f)'s `Prop`-erasure claim needs (§4(i)(3)).

**N7. Record Lean's run answer in `generated/corpus-index.tsv` and gate `cross_face` on it.**
§4(iii) steps 1–2, with the mutation-must-fail red control copied from
`scripts/check-conform.py:69-79`. This turns the estate's widest corpus (400+ programs) from an
OCaml-versus-OCaml differential into a Lean-versus-OCaml one, and makes the machine's answers a
committed pin. If the Lean run cost is too high, pin a stated subset and say which.

**N8. Wire the 20,387-vector lane, and make `Ml.checkModule` fatal for the three unseamed
outputs.** One `PROFILES` entry plus one `$(CHK)` rule (§4(iii) step 3); three lines in
`LcnfGen.lean` (§5.4). Then amend `docs/core/lcnf-route.md:58-59` and `docs/GENERATED.md:48`, both
of which currently claim more than the checks deliver (§5.5).

**N9. Make `frontier` fatal and `source-append-unavailable-in-frozen-engine` raise** unless the
family is in a committed allowance file; and move `$(GEN)/lcnf` before `$(GEN)/eff` so one
`make gen` reaches the fixpoint (§5.1, §5.9). Four lines, three files.

**N10. Add `make gen-lcnf` to the `check-ocaml` CI job.** It already has the `opam` switch and
already spends minutes on `dune`; the LCNF cut is a Lean run. Today the LCNF outputs are
regenerated only by the nightly (`lean_action_ci.yml:169-170`), so the engine can drift behind the
language for a day (§5.6).

### After the push — the three big ones, in this order

**A1. The runner plan's step 1: `Api.ofBytes`/`Api.bytesOf` as engine roots.** This deletes
`ocaml/engine/e4_program.ml`, `e4_program_layout.{ml,json}`,
`scripts/generate-engine-structure.py`, the ordinal pin and the manifest check, and replaces
`e4_shape.ml`'s hand table with a walk of the value by its `ShapeDoc`. The probe is recorded as
already run (`2026-09-17-runner-schema-codegen-plan.md` §3: whole closure, no missing declaration,
nothing beyond the cap, three builtin rows owed). **This is the structural fix to §5.1 and §5.2
and it is the highest-value item in this note.** Its one stated cost is `Bytes = List UInt8`, so
the compiled decoder walks a list — correctness first, a `Bytes` carrier row when a benchmark asks.

**A2. One `Target.Layout` object, both pipelines project it.** §4(ii). Do it as a strict refactor
whose receipt is `make check-gen` showing no diff on fourteen generated files. It is also the
object a TypeScript target needs, so it precedes A3.

**A3. The TypeScript reader from LCNF.** §4(iv). Land the *seam* now (split `read.ts` at the
`TypeScript.Expr` boundary into `read-parse.ts` and `read-table.ts`, ~500 hand lines and ~1,100
reifiable), and the emitter after A2. Decide the tail-call policy (trampoline vs a depth bound in
the reader's contract) **before** writing the emitter — a JavaScript stack overflow is an outcome
outside the Lean function's range, so it is a semantic question, not an optimisation.

**A4 (ruling, not now). Should `Term.app` carry `NativeAtom` instead of `String`?** §4(v) step
4(b). It removes the atom lookup from every machine step and keeps the append-only wire property by
mapping name ⇄ constructor at the codec boundary. It changes `Term`'s shape, hence `Term`'s wire
tags, the goldens and the TS reader. Recommendation: **yes, after the push**, as its own slice with
the wire-tag retirement done the way `whileLoop`/`callback` were.

**A5 (defer, and say so). The proved translation.** §2.6 Tier 3. Do pieces 1 and 2 (the reference
fragment `Frag` and the checked reader `ofCode`) as part of N-series work, because they are what
turns the accepted fragment from prose into a gate whether or not the theorem lands. Defer pieces
3 and 4: factoring `Translate.code`'s five concerns apart is a real refactor of the one file the
whole OCaml estate depends on, and the simulation theorem is **false** without a side condition,
because `Nat` is `int` — so it either carries `n < 2^62` through every case or waits for a `Nat`
carrier. Being honest about that is better than a theorem with a hole in it.

### What I would not do

* **Do not put the checker in the OCaml closure.** Today `grep -c typeOf ocaml/gen/api_gen.ml` is
  0 and that is worth defending. Adding `HostSession.start` as a root for its *certificate* would
  pull `instantiate`, `matchTemplate`, `rowTy`, `sub`, `normalize`, `join` and `diffTag` into the
  engine at once and give the estate a second type checker whose agreement with Lean's nothing
  checks (§3(d)).
* **Do not make `eval` a record field.** §4(v): it costs the jump table, the exhaustiveness error,
  and (one refactor later) the arrow spelling in `kernelTy`.
* **Do not widen the `Metadata` fixtures by hand each time.** Invert the condition instead
  (§5.8): every family the corpus cannot reach must be named by a fixture, or refuse.

---

## References

### This tree

Generator (Lean half):
`src/OCaml5/Lcnf/Dump.lean`, `Naming.lean`, `Native.lean`, `Types.lean`, `Externs.lean`,
`Translate.lean`; `src/OCaml5/Ml/Syntax.lean`, `Render.lean`, `Check.lean`, `Profile.lean`,
`Identifier.lean`; `src/OCaml5/Eff/World.lean`, `Emit.lean`, `Goldens.lean`, `Metadata.lean`;
`src/OCaml5/Tools/LcnfGen.lean`, `EffGen.lean`, `EffWire.lean`, `CasGoldens.lean`, `LcnfDump.lean`;
`tools/Tools/ProgramStructure.lean`, `WireTags.lean`, `Corpus.lean`;
`tools/Conform/Lcnf/{Index,Validity,Cases,Rules,Semantics,SemanticsTarget}.lean`,
`tools/Conform/Effect4/{Lcnf,LcnfSemantics,LcnfMl,Normalization,TargetLeanNative}.lean`.

Generated artefacts and their checks:
`ocaml/gen/{machine_gen,fibers_gen,api_gen}.ml`, `api_check.ml`, `NOTES.md`, `dune`;
`ocaml/engine/api_engine.ml`, `api_engine_inst.ml`, `e4_program.ml`, `e4_program_layout.{ml,json}`,
`externs.txt`, `tools/api_engine_prelude.ml`, `tools/gen-check.sh`, `corpora.ml`,
`test/test_diff.ml`, `dune`; `ocaml/eff/eff_*.ml`, `goldens/**`; `ocaml/README.md`,
`ocaml/STANDARDS.md`.

Orchestration: `Makefile` (the `gen-*`/`check-*` graph), `scripts/generate.py`,
`scripts/generate-engine-structure.py`, `scripts/lib/program_structure.py`,
`scripts/check-conform.py`, `scripts/lib/conform_report.py`,
`.github/workflows/lean_action_ci.yml`, `docs/GENERATED.md`.

Language and plans: `src/Effect4/Program/Ty.lean`, `NativeAtom.lean`, `src/Effect4/Machine/Term.lean`,
`Stores.lean`, `src/Effect4/Api.lean`, `Api/Runner.lean`, `Api/RunnerBytes.lean`,
`src/Effect4/Codegen/Read.lean`, `ts/eff/read.ts`;
`docs/core/lcnf-route.md`, `docs/core/decisions.md` (rows 26, 27, 29, 30, 44),
`docs/core/language-cut.md`;
`docs/research/2026-09-18-rows-42-43-plan.md` (§2c, the L1–L7 table),
`docs/research/2026-09-17-runner-schema-codegen-plan.md` (§2, §3, §4),
`docs/research/2026-09-16-ocaml-engine-base-abstractions.md`,
`docs/research/2026-09-10-lcnf-generator-hardening.md` (the ten generator defects and their fixes).

### Lean's own compiler, consulted at `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/`

`Lean/Compiler/LCNF/Basic.lean` (the IR; the purity index and the `h : pu = .impure` fields that
make the pure fragment 26 constructors), `LCNF/Passes.lean:66-72` (`saveMono`, and the mono pass
list at `:122-140`), `LCNF/PhaseExt.lean:103` (the opacity filter that replaces a
public-but-not-transparent body with `.extern [.opaque]` — a *visibility* fact a consumer must not
read as a *language* fact), `LCNF/Check.lean` (`check` at `:234`, `checkCases` at `:215`,
`checkJpInScope` at `:144`, `checkLetValue` at `:137`), `LCNF/Irrelevant.lean` and
`LCNF/MonoTypes.lean` (relevance and the trivial-structure verdict), `LCNF/LambdaLifting.lean`,
`LCNF/StructProjCases.lean`, `LCNF/ReduceArity.lean` (the `_redArg` split the translator folds),
`LCNF/PrettyPrinter.lean:218` (`ppDecl'`), `LCNF/DeclHash.lean`;
`Lean/Compiler/IR/ToIR.lean`, `IR/ToIRType.lean` (the low IR's nine-element type universe — the
"DataLayout" of Lean's own backend), `IR/Checker.lean`, `IR/EmitC.lean`, `IR/EmitLLVM.lean`.

### Outside literature, for §2

* **Lean's backend.** Ullrich and de Moura, *Counting Immutable Beans: Reference Counting
  Optimized for Purely Functional Programming* (IFL 2019); Reinking, Xie, de Moura and Leijen,
  *Perceus: Garbage Free Reference Counting with Reuse* (PLDI 2021). Why the low tier is already
  written and should not be rewritten.
* **MLIR.** Lattner et al., *MLIR: Scaling Compiler Infrastructure for Domain Specific
  Computation* (CGO 2021); the MLIR docs on dialect conversion, `TypeConverter`, op verifiers,
  `--verify-each`, and declarative rewrite rules (DRR/PDL). The source of "verify after every
  step" and "type conversion is its own object".
* **LLVM.** the LLVM Code Generator and Language Reference documents (the steer already banked in
  `lcnf-route.md` §7); Lopes, Lee, Hur, Chen and Regehr, *Alive2: Bounded Translation Validation
  for LLVM* (PLDI 2021); Zhao, Nagarakatte, Martin and Zdancewic, *Formalizing the LLVM
  Intermediate Representation for Verified Program Transformations* (Vellvm, POPL 2012).
* **Cranelift.** the ISLE instruction-selector DSL and its SMT-based rule verification
  (Crocus / "Lightweight, Modular Verification for WebAssembly-to-Native Instruction Selection",
  ASPLOS 2024), plus `cranelift-fuzzgen`'s differential fuzzing against an interpreter of the same
  IR. The model for "prove the rewrite rules one at a time, fuzz differentially meanwhile".
* **Coq extraction.** Letouzey, *A New Extraction for Coq* (TYPES 2002) and the Coq reference
  manual's extraction chapter — the origin of the `Obj.magic` and `Extract Constant` hazards that
  the mono-LCNF route structurally avoids (§2.4).
* **Verified compilation.** Leroy, *Formal Verification of a Realistic Compiler* (CACM 2009) and
  the CompCert per-pass forward-simulation architecture; Kumar, Myreen, Norrish and Owens,
  *CakeML: A Verified Implementation of ML* (POPL 2014). The shape of the Tier-3 theorem.
* **A pinned target semantics.** Haas et al., *Bringing the Web up to Speed with WebAssembly*
  (PLDI 2017) and the mechanized Wasm semantics (WasmCert). Why a target whose semantics is
  mechanized is worth more than one whose is not — the cost OCaml imposes on us, paid by
  `Conform.Lcnf.SemanticsTarget` being our model of OCaml rather than OCaml's.
* **An interpreter as the oracle.** Rust's MIR, Miri, and the `mir-opt` golden-dump tests. The
  model for §4(i)(3)'s committed closure manifest and for running our own LCNF evaluator as the
  differential oracle rather than leaving it unwired.
