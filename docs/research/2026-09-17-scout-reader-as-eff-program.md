# Scout A: the reader as an authored `Eff` program

2026-09-17, at `b9c75004`. Research only; no tracked file changed, no gate run. Everything
below marked **compiled** was checked with `lake env lean` on scratch files under
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/aa7ebaa0-7350-4784-b70e-322956de92e8/scratchpad/scoutA/`
(`probe1.lean` … `probe8.lean`); their text and output are in §8. Everything marked **read**
is a claim about a file in the tree with its path. Everything marked **inferred** is an
argument from those two, not an executed fact.

**The short answer.** The owner is right that the authoring layer already has the capability.
A Lean function over a table authors one layer of the reader as an ordinary `Eff` program; it
lies in `Straight`, the machine runs it, the meaning agrees with a Lean specification of the
same layer, and it prints as Effect TypeScript using only prelude names that already exist
(`caseTag`, `fst`, `snd`, `eq`, `pair`). That is compiled, not argued. The coordinator's first
assessment was wrong on two of its three points: list atoms are **not** needed (a list encoded
as tagged pairs is taken apart by `select … (.tag "cons")` alone), and a `TypeScript.Expr`
**does** have a mechanical route to a value (the existing `Canonical` generator already handles
a `List`-nested recursive inductive — `Json` — although its `Val.ctor` image is invisible to
every atom and every decision the language has, so the encoding must change or an eliminator
must be added). It was right about the recursion: `Eff` has no procedure form, and unrolling it
costs a factor of the table's total arity per level, measured.

---

## 1. What the authoring layer can do today

Read, from the source.

**The carrier.** `src/Effect4/Program/Authoring.lean:78`

```
abbrev Src (Op : Type) := Env → List Nat → Except Refusal (Eff Op)
```

with `TermSrc`, `CauseSrc`, `ActionSrc`, `LayerSrc` beside it (`:75`–`:87`). `Env`
(`:70`) is the names in scope and the declared layer names. A `Src Op` is a Lean function, so
**a Lean function over a table is already a program builder**: the fold happens in Lean, at
authoring time, and what lands in the tree is one first-order `Eff`.

**The one name-resolving operation** is `var` (`:133`), nearest binder first. `lit`, `nat`,
`str`, `bool`, `unit` (`:138`–`:143`) and `app atom args` (`:147`) are the rest of the term
surface. `elaborate` (`:175`) evaluates a `Src` at the empty scope; `Module` and
`elaborateModule` (`:178`, `:224`) place shared layers by name.

**The lifts.** `src/Effect4/Program/Authoring/Lifts.lean` — **50** generated operations, one
per constructor an author may write, emitted by `tools/Effect4Gen/Authoring.lean` over
`tools/Effect4Gen/binders.json` (53 lines; the binding signature: which argument of which
constructor abstracts which binders). (`docs/STATE.md` still says 48; counted at
`b9c75004`, the file has 50 `def`s and 50 matching `#print axioms` receipts. I did not check
which two landings moved the count; the STATE line is stale, nothing else about it is.) The
ones this note uses:

| declaration | line | shape |
| --- | --- | --- |
| `bind (answer : String) (first rest : Src Op)` | `:51` | `rest` sees `answer` |
| `perform (op : Op) (request : TermSrc)` | `:45` | a row call |
| `selectBool (scrutinee : TermSrc) (arm0 arm1 : Src Op)` | `:153` | neither arm binds |
| `selectOption (bound : String) …` | `:161` | `arm1` sees `bound` |
| `selectTag (payload rest : String) (scrutinee : TermSrc) (tag : String) …` | `:169` | `arm0` sees `payload`, `arm1` sees `rest` |
| `iterate (cursor answer : String) (cursorTy : Ty) (initial test step result : TermSrc) (body : Src Op)` | `:177` | four terms over the cursor, one body |

**The sugar.** `src/Effect4/Program/Authoring/Sugar.lean` is five conveniences:
`bindWith first (fun r => rest)` (`:25`, a binder over a fresh name minted from the scope's
length), `flatMap` (`:30`), `andThen` (`:33`), `map` (`:36`), `ifElse` (`:40`, which is
`selectBool`).

**The rows.** `src/Effect4/Program/Authoring/Rows.lean`, generated from `NativeOp.all`: one
wrapper per native row (`Ref.make`, `Ref.get`, …), each a `perform` of that row with its
request spelled by `pair`.

**The forms.** `src/Effect4/Program/Authoring/Forms.lean`, 19 combinators generated from
`Codegen.Forms.all`, each guarded against the printer's own `Template.expand`
(`src/Effect4/Codegen/Forms.lean:61`) so the reading and the expansion cannot drift. Note that
`Forms.Template` is a template calculus over the **`Eff`** signature (`Forms.lean:31`), not
over the syntax signature; the R4 table is the target-side twin. The design note already
records this as two tables with one calculus
(`docs/research/2026-09-16-printer-reader-positions-design.md` §14, first bullet).

**Scope safety.** `Src.Scoped` (`src/Effect4/Laws/Program/Authoring.lean:41`), the
`authoring_scoped` dispatcher tactic (`src/Effect4/Laws/Program/Authoring/Tactic.lean:49`) and
`elaborate_scoped` (`src/Effect4/Laws/Program/Authoring/Sugar.lean:46`), which closes any
elaborated program at level 0.

**So "authoring a reader" means** a Lean function `Table → TermSrc → Src NativeOp`: it takes
the table and the term that names the node, and returns a program. `elaborate` (or applying the
`Src` at a one-name scope) turns it into one `Eff`. This is exactly dogfood 6's shape — a Lean
`Model` plus a sixty-line `compileP : Model → List Event → Eff`
(`docs/research/2026-09-16-dogfood-6-effect-machine-receipt.md` §3) — with the table in place of
the statechart.

---

## 2. Encoding the input

### 2.1 What `Val` is, and what the language can see of it

`src/Effect4/Store/Val.lean:149`–`:167`: `unit`, `bool`, `nat`, `str`, `bytes`, `list`, `pair`,
`none`, `some`, `ctor index args`, `ref`, `handle`.

The language's eliminators are far narrower than that alphabet. Read:

- `src/Effect4/Program/Decision.lean:31` — `Val.tagPayload? tag` matches **exactly**
  `.list [.str t, payload]`. Nothing else.
- `:50` — `Decision.decide`: `.bool` needs `.bool b`; `.option` needs `Val.none`/`Val.some`;
  `.tag t` is total (a hit gives the payload, everything else gives the whole value).
- `src/Effect4/Program/NativeAtom.lean:127` — `eval`: `fst` needs `.list (a :: _)`, `snd` needs
  `.list (_ :: b :: _)`, `tagIs` is `tagHit` (`:123`, again `.list [.str t, _]`), `isSome` and
  `getOrElse` need `Val.none`/`Val.some`, `eq` takes two naturals or two strings.
- The **only** constructors of structured values are `pair` (`.list [a, b]`) and `strings`
  (a flat `.list` of strings, `:21`). There is no atom that builds `Val.ctor`, `Val.some`,
  `Val.none` or a general `Val.list`. This one is **read**, off the twenty arms of
  `NativeAtom.eval` (`:127`–`:154`) and the twenty names of `NativeAtom.all` (`:43`); I did
  not find a way to check it by execution, and the `#guard` in probe 3 that looks like such a
  check is a tautology and proves nothing.
- `Lit` (`src/Effect4/Program/Eff.lean:235`) is `unit | nat | bool | str`. A program cannot
  write a structured constant; it must build one with `pair`.

### 2.2 `Val.ctor` is invisible to the language — compiled

Probe 3 runs the same authored layer on two encodings of one node:

```
#guard answerOf (.list [.str "call", .list [.str "head", .str "args"]]) = .ok (.str "head")
#guard answerOf (.ctor 7 [.str "head", .str "args"])                   = .error "failure"
#guard NativeAtom.eval .fst [.ctor 7 [.str "a", .str "b"]] = none
#guard NativeAtom.eval .snd [.ctor 7 [.str "a", .str "b"]] = none
#guard NativeAtom.eval .tagIs [.str "call", .ctor 7 [.str "a"]] = some (.bool false)
#guard Decision.decide (.tag "call") (.ctor 7 [.str "a"]) = some (false, some (.ctor 7 [.str "a"]))
```

All pass. So the generated `Canonical`/`Image` image of a family — which is `.ctor index args`
(`src/Effect4/Store/Derived/Json.lean:99`–`:113`) — **cannot be taken apart by any atom or any
decision the language has**. The only way a program could reach inside one is a row, which
means host code doing the work, not the program. This is the single hardest fact in this note.

### 2.3 But the generator does handle a tree like `Expr`

Read. `Effect4.Json` (`src/Effect4/Data/Json.lean:288`) has `| arr (elements : List Json)` and
`| obj (entries : List (String × Json))`, and the generator emits a complete `Canonical`
instance for it with the nested-`List` helpers `toValL0`, `toValP1`, `toValL2` and the matching
readers (`src/Effect4/Store/Derived/Json.lean:98`–`:160`). Mutual blocks are handled too: the
`Program` group emits `Effect4.Program.Eff@Effect4.Program.NativeOp`, a seven-type mutual family
(`tools/Effect4Gen/manifest.json`).

`TypeScript.Expr`/`Stmt` (`.lake/packages/typescript/TypeScript/Syntax.lean:35`–`:118`) is a
two-type mutual inductive with `List Expr`, `List (String × Expr)`, `List Stmt`,
`List Parameter`, `List TypeRef` and `List (Nat × List Stmt)`. The first five are shapes the
generator demonstrably emits. `List (Nat × List Stmt)` is a list of pairs whose second component
is itself a list; whether the helper-naming scheme handles that nesting I did **not** check
(§9). So: **an `Image` for `TypeScript.Expr` is a manifest entry, not new machinery** —
inferred, with one open risk.

That does not help by itself, because of §2.2. It helps only if a `ctor` eliminator lands
(§6, item 3).

### 2.4 The encoding that works today: tagged pairs

`pair` builds `.list [a, b]`, and `select … (.tag t)` reads exactly that. So encode

```
ident s        ↦  pair "ident" s
call f args    ↦  pair "call" (pair f args)
[]             ↦  pair "nil" unit
x :: xs        ↦  pair "cons" (pair x xs)
```

and every destructuring the reader needs is `selectTag` plus `fst`/`snd`. **No list atom is
required** — compiled, probe 3 (a):

```
def takeTwo (lst : TermSrc) : Src NativeOp :=
  selectTag "c1" "nil1" lst "cons"
    (selectTag "c2" "nil2" (app "snd" [var "c1"]) "cons"
      (succeed (app "pair" [app "fst" [var "c1"], app "fst" [var "c2"]]))
      (Authoring.fail (str "arity")))
    (Authoring.fail (str "arity"))
```

runs on the encoded list `["X","Y","Z"]` and answers `Val.list [.str "X", .str "Y"]`. The
packet's §5b sentence "argument lists need list atoms, which the language lacks" is therefore
**too strong**: it is true for `Val.list` and false for the encoding the language already reads.
The variadic rows (`raceAll`, `mergeAll`) are exactly the same cons walk, but they need the
recursion (§3), because their length is not fixed per row.

**Output.** Built the same way, by `pair`. A template's substitution is a fixed tuple per row,
so nested `pair`s suffice; a variadic row's substitution is a cons list, again `pair`. No
constructor atom and no row is needed to build the answer — compiled (probes 1, 2, 4 all answer
`pair ctor args`).

### 2.5 Typing: `Ty` has no recursive type, and that decides the shape

Read: `src/Effect4/Program/Ty.lean:23`–`:43`. `Ty` is `never, unit, nat, int, string, bool,
handle, option, list, prod, except, exitOf, causeOf, fiberOf, union, lit`. There is no `mu`, no
type variable, no named recursion. **No `Ty` denotes the set of `Expr` trees.** That is not an
opinion; there is no constructor that could.

`Ty.handle target` (`:30`) is the opaque escape, but it does not help: `taggedColumn`
(`Ty.lean:599`) admits only members that are `prod (lit _) _` or one of
`unit|nat|int|string|bool|lit`, so `select … (.tag _)` refuses a `handle` scrutinee.

Compiled, probe 8, `effTy sig [nodeTy] layer` for one layer that dispatches on `call`, reads
the head's name and compares it:

| node type | result |
| --- | --- |
| `handle "TypeScript.Expr"` | **refused** |
| `union (prod (lit "call") (prod (handle "TypeScript.Expr") (handle "ExprList"))) (prod (lit "ident") string)` | **refused** — the decision itself accepts it (`Decision.arms` gives arm 0 the type `readonly [TypeScript.Expr, ExprList]`), but the inner `selectTag` on the head gets a `handle` and refuses |
| `union (prod (lit "call") (prod (prod (lit "ident") string) string)) (prod (lit "ident") string)` | **typed**, answer `readonly ["bind", string]` |

The rule this establishes: **a layer types exactly as deep as it inspects, and only if the input
type is spelled out to that depth.** Children that are handed on to the next layer must carry
the full recursive type, which cannot be written. So the reader-as-a-program is a **raw**
program in the general case. That is not fatal — `Straight`, `run_eq_meaning`, `Looped` and
`loopAgreement` require no typing premise (`src/Effect4/Program/Fragment.lean:20`,
`src/Effect4/Laws/Program/Agreement/Machine.lean:1896`,
`src/Effect4/Laws/Program/DenoteB.lean:123`,
`src/Effect4/Laws/Program/Agreement/Loop.lean:839`) — but it costs two concrete things:

- `Api.printModule` (`src/Effect4/Api.lean:185`) goes through `emitModule`, which needs a
  typing certificate; an untyped reader has no exported module with an `Effect.Effect<A, E>`
  annotation. `Api.print` (the bare expression) still succeeds. Compiled: probe 4 prints the
  38-row open reader (`(Api.print big).isOk = true`), probe 6 gets a whole module only because
  its input is a literal.
- `Typed.*`, `Api.author` and the facade's certificate-first half do not apply to it.

---

## 3. The recursion: three shapes, measured

### (i) Authoring-time unrolling to a bounded depth — measured, and it does not scale

`Eff` has no procedure form and no program-valued variable, so a reader that reads its children
must **contain a copy of itself** at every child position. Probe 7 builds exactly that over a
three-row table whose arities sum to 4, and measures the wire bytes (`Api.bytesOf`):

| depth | bytes | factor |
| --- | --- | --- |
| 1 | 3,531 | |
| 2 | 17,475 | 4.9 |
| 3 | 73,251 | 4.2 |
| 4 | 296,355 | 4.0 |

The factor is the table's total arity, as the structure predicts. For the real table probe 4
measures one layer at **46,295 bytes** (38 rows, argument destructuring and binder-name checks;
depth 46, 115 steps, 9,623 characters of printed TypeScript). Counting only the *program*
children of the printer's clauses gives a branching factor of about 33, so — **inferred** from
the measured layer and the measured factor — depth 2 is roughly 1.6 MB, depth 3 roughly 50 MB,
depth 4 roughly 1.7 GB. The brief names depth-4 corpus programs; I did not measure the corpus's
own depths (§9). **Shape (i) is dead** at any depth the corpus actually reaches.

This is dogfood 6's F21 ("about 17 KB per event … a procedure form would divide it by the
number of states", `2026-09-16-dogfood-6-effect-machine-receipt.md` §5) measured again on a
different workload, and the same conclusion.

### (ii) One layer as an `Eff` program, recursion supplied outside — works today

This is the shape probes 1, 2, 4, 6 all exercise. One layer is 46 KB; the recursion is the
generic fold (`cata_eff`, `src/Effect4/Program/Fold.lean:1006`) on the Lean side, or a plain
recursive walk on the host side. The design note's warning applies and is not a problem here:
"the effectful compile is not a monadic fold … `Eff.bind` takes a program, not a function, so
there is no `Monad (Eff CompileOp)` and `foldM_eff` does not apply"
(`2026-09-16-printer-reader-positions-design.md` §14). It does not apply because the *layer* is
the `Eff` program and the *fold* is not: the fold is Lean's (or the host's), and it calls the
layer once per node.

The honest cost is that the recursion is then **not** on any face. The Lean side already has
`cata_eff`; the TypeScript side would need its own recursive driver (about ten lines); the
OCaml engine would need one too. "One definition on every face" becomes "one *dispatch table*
on every face, with three trivial drivers".

### (iii) A worklist with `iterate` — runs today, untyped

Compiled, probe 5: a loop whose cursor is `pair worklist count`, with the worklist a
cons-encoded list, popping one item per round.

```
#guard Straight p5 = false
#guard Looped   p5 = true
(Api.run p5 200).exit       answers Val.nat 3
(meaningB 10 p5 [] empty).1 answers Val.nat 3
(Api.typeOf p5).isSome = false, Api.explain p5 refuses at []
```

So the machine runs it, the budgeted meaning agrees with it, and it is inside `Looped` — the
fragment where `Agreement.loopAgreement` relates the two
(`src/Effect4/Laws/Program/Agreement/Loop.lean:839`). No list atom is needed, again.

It does not type, and the reason is structural, not my annotation: `effTy`'s `iterate` arm
(`src/Effect4/Program/Typing.lean:353`–`:361`) types `step` at the **whole** cursor annotation,
not at the type refined by the test, and requires `Ty.sub c1.normalize cursor.normalize`. So the
annotation must be a single type that every round's cursor inhabits **and** on which every
projection the step performs succeeds. For an unbounded worklist that is a recursive type.

The other cost of (iii): the output. A worklist reader has to build the answer bottom-up, so it
carries an explicit result stack in the cursor and a "pop k, apply constructor" discipline in
the step. That is expressible with `pair` alone, but it is the most code of the three shapes and
the furthest from "as mechanical and AST-to-AST as possible".

### Recommendation

**(ii).** It is the only shape that is small (one 46 KB layer, linear in the table), the only
shape whose program is a direct image of the table with no control machinery of its own, and the
only shape where the specification and the program have the same shape (one layer versus one
layer), which is what makes §4's theorem cheap. (iii) is the fallback if the owner later wants
the recursion itself to be one artefact on every face; it should not be the first cut.

---

## 4. The proof route

### 4.1 What is landed, exactly

- `Straight` (`src/Effect4/Program/Fragment.lean:20`) admits `succeed`, `fail`, `failCause`,
  `sync`, `suspend`, a `sync` row, `bind`, `select` (all three decisions), `exit`, `catchCause`,
  `matchCause`, `onExit`. **Every construct an authored layer reader uses is in it** —
  compiled, probes 1, 2, 4 all guard `Straight … = true`.
- `denote` and `meaning` (`src/Effect4/Laws/Program/Denote.lean:66`, `:130`) take an
  environment: `meaning (e : NativeEff) (env : List Val) (s : Stores)`.
- `run_eq_meaning` (`src/Effect4/Laws/Program/Agreement/Machine.lean:1896`) is stated at
  `env = []` and `Stores.empty`, with the budget `max (depth e) (2 * steps e + 6)`.
- `LoopAgreement` (`src/Effect4/Laws/Program/LoopAgreement.lean:27`) is likewise at `[]`.

### 4.2 The statement the brief proposes, and what it needs

`meaning (authorLayer table) [encode node] Stores.empty = (Exit.success (encode (matchLayer table node)), Stores.empty)`

is a statement about `denote`, and it is **provable with what is landed**, by induction on the
table: the program is a right-nested chain of `select`s and `ifElse`s, `denote`'s `select` arm
(`Denote.lean:96`–`:100`) is exactly `Decision.decide` followed by the chosen arm, and
`denote`'s `succeed`/`fail` arms are `evalTerm`. Each row contributes one step of the chain and
one `NativeAtom.eval` equation. No new lemma family is needed; what is needed is the set of
evaluation equations for `pair`/`fst`/`snd`/`eq` on the encoding, which is the same list dogfood
6's open `compile_correct` needs (`2026-09-16-dogfood-6-effect-machine-receipt.md` §2, "its
proof needs exactly the primitive equations and safety lemmas the consolidated plan's S8a
schedules").

**What it does *not* give you is the machine**, and this is the gap the brief did not name.
`run_eq_meaning` and `loopAgreement` are both at the empty environment. A reader program has a
free variable (the node), so neither theorem applies to it as stated. Three ways out, in order
of cost:

- **(a) Close the program.** Feed the node in as a literal built by `pair`, and the program is
  closed; `run_eq_meaning` applies unchanged. Compiled, probe 2:
  `(Api.run p2 (budgetOf p2)).exit = some (meaning p2 [] Stores.empty).1`, and the machine's own
  exit is the expected `["bind","ARGS"]`. This is fine for a *test* — one program per node —
  and useless for a reader whose input varies.
- **(b) Generalise the agreement to a non-empty initial environment.** `Api.run`
  (`src/Effect4/Api.lean:305`) starts the root fiber at the empty environment, so this is a
  change to the machine's entry, not only to a proof. Not priced here.
- **(c) Do not need the machine.** For R6 the reader runs on the **host**, as printed Effect
  TypeScript, not on the Lean machine. What has to be true there is the `denote` theorem above
  plus the executed agreement the truth harness already provides: the printed program run on
  rc.112 answering what the Lean side answers, resting on the prelude's per-atom self-test
  (`harness/truth/prelude.ts`, `selfTestCases`). There is no semantic model of TypeScript in
  this tree, so that half is tested, never proved, and the note should not pretend otherwise.
  This is the cheapest route and the one I recommend.

### 4.3 Keep `matchT` as the specification

Yes. The packet's §2 calculus and `match_inst` (`docs/research/2026-09-17-template-probe.lean:104`,
proved at `[propext, Quot.sound]` over templates by one mutual induction) should stay exactly as
it is. The compile theorem of §4.2 then relates the authored program to `matchLayer`, and
`matchLayer` is where `match_inst` lives. Nothing in the laws moves onto `denote`. This is the
packet's own recommendation ("the cheap way to keep both is a compile theorem … so the laws stay
on `matchT`") and it survives everything measured here.

### 4.4 The one thing that is circular today

`Api.readable` is `false` on every authored layer reader — compiled, probes 2 and 4. The reason
is not the approach: `readable`'s arms at `src/Effect4/Codegen/Read.lean:794`–`:798` return
`false` for `select … .option`, `select … (.tag _)` and `iterate`, "read back by the generic
reader from the template table (R5)". So **the reader-as-a-program is built out of exactly the
constructs R5 is landing the reader for.** Consequences: the program prints (compiled) but does
not round-trip until R5.2 is done; R6 cannot precede R5; and the first time the reader program
reads its own printed image will be a genuinely good regression test.

---

## 5. What it buys and costs for R6

### 5.1 The printed image, verbatim — compiled

Probe 6 prints a one-row layer reader through this repository's own printer:

```
Effect.flatMap(
  Effect.sync(() => pair("call", pair(pair("ident", "Effect.flatMap"), "ARGS"))),
  (a0) => caseTag(a0, "call",
    (a1) => caseTag(fst(a1), "ident",
      (a2) => Effect.suspend(() => eq(a2, "Effect.flatMap")
        ? Effect.succeed(pair("bind", snd(a1)))
        : Effect.fail("no rule")),
      (a2) => Effect.fail("no rule")),
    (a1) => Effect.fail("no rule")))
```

and as a module:

```
export const layerReader: Effect.Effect<readonly ["bind", "ARGS"], string> = …
```

Every name outside `effect` is already in `harness/truth/prelude.ts`: `pair`, `fst`, `snd`,
`eq`, `caseTag`, `optionCase`. **No new prelude export is needed.**

### 5.2 What the TypeScript side still has to supply, either way

`ts/eff/read.ts` is 1,547 lines and its header names four stages:
`parseSync` (oxc text → ESTree), `exprOf` (ESTree → the printer's `Expr` fragment),
`readEff(0, ·)` (the clauses, a hand port of `Read.lean`), `decodeEff` (the schema check).

The reader-as-a-program replaces **only the third**. It leaves:

1. **the parse**, oxc → ESTree — unchanged, and correctly at the boundary
   (`2026-09-16-printer-reader-positions-design.md` §4: parsing is the host's);
2. **`exprOf`**, ESTree → the fragment — unchanged, and now it must *also* encode that fragment
   as the prelude's tagged-pair values, which is a new function of about the same size as
   `exprOf` itself (one arm per `Expr` constructor, mechanical, generatable from the same
   syntax table R2 imports);
3. **the recursive driver** — ten lines under shape (ii);
4. **the decode of the answer** — the reader program answers nested `pair`s, so a second small
   adapter turns that into the `Eff` node shape `eff.gen.ts` expects, before `decodeEff`.

So R6 by this route deletes `readEff`'s clauses and adds two encoders. The packet's own plan
(export the table as `ts/eff/templates.gen.ts` and write one matcher over it) deletes the same
clauses and adds **one** matcher over a table, with no encoding of the AST into values, no
change to the value language, and no answer-decoding step.

### 5.3 The honest comparison

| | the packet's plan | the reader as an `Eff` program |
| --- | --- | --- |
| what is shared across faces | the table, as a document | the table **and** the matching logic, as a program |
| new Lean code | `Template.lean`, `Templates.lean`, `readT` | the same, **plus** the authored program and its compile theorem |
| new TypeScript | one matcher (hand-written, ~150 lines) | an AST-to-value encoder, an answer decoder, a driver |
| new value-language work | none | §6's list |
| proof | `match_inst` + `read_exact`'s converse | the same, plus one compile theorem |
| what the OCaml engine gets | nothing new | it can run the reader, once the encoders exist there too |

**Inferred:** the reader-as-a-program is *more* total work for R6, not less, and its payoff is
not R6 — it is that the repository gains a worked example of "a compiler written in the language
itself", which is the S9a agent unlock's own subject matter. That is a real payoff, and it is
not R6's.

---

## 6. Authoring and language additions, smallest first

An atom is far cheaper than a constructor. Read, from the two-atom commit `6762ccb0` ("prove
pure option inspection and default selection", `isSome` + `getOrElse`): 56 files, +757/−100, but
the **hand-written** owners are few — `src/Effect4/Program/NativeAtom.lean` (+28: the
constructor, `all`, `name`, `arity`, `constGeneric`, `mono`, `eval`, `typeOf`),
`src/Effect4/Laws/Program/Typed.lean` (+57), `src/Effect4/Laws/Program/Progress.lean` (+19),
`harness/truth/prelude.ts` (+13), `tools/Conform/Effect4/cases-policy.json` (+46), the test
batteries. Everything else is regeneration or re-pinning: `ts/eff/profile.gen.ts`, the OCaml
files (`ocaml/gen/api_gen.ml` and `ocaml/engine/api_engine.ml` both carry the
"GENERATED by OCaml5.Lcnf … Do not edit" header), the corpus and result pins. Compare a
constructor, which `docs/STATE.md` item 5 prices as "one row in `binders.json` plus the
hand-written owners (`effTy`, `compileEff`, `denote`, `print`, `read`, `Straight`, and on the
OCaml face the translation arm)" — and whose retirement cost was measured at 209 declarations
for `branch` and 62 for `yieldError`.

With that scale, smallest first:

1. **Nothing.** Shape (ii) with the tagged-pair encoding needs **no** language addition. The
   whole of §§1–4 is compiled against `b9c75004` unchanged. This is the finding that matters
   most. What it needs is *authoring* work only: a Lean module that folds the R4 table into a
   `Src NativeOp`, which is ordinary code in the shape of `tools/Effect4Gen/Forms.lean`.

2. **An authoring helper for cons lists** (`Authoring/Sugar.lean` or a new
   `Authoring/Data.lean`): `consT`, `nilT`, `listOf`, `takeN` (probes 3, 4, 7 all wrote these by
   hand). Cost: a few `Src`-level definitions with `unfold` + `authoring_scoped` scope lemmas,
   the pattern `Authoring/Forms.lean`'s lemmas already use. No constructor, no atom, no wire
   change, no OCaml change. Unlocks nothing new; it makes (ii) and (iii) readable.

3. **Atoms `ctorIndex` and `ctorArg`, or a `Decision.ctor`**, so a program can take apart the
   `Canonical` image directly instead of a bespoke tagged-pair encoding. Two atoms cost what
   `isSome`/`getOrElse` cost (above): about 120 hand-written lines across five owners, one
   prelude export each, everything else regenerated. A `Decision` constructor is dearer: it is a
   constructor of `Decision` (`Program/Decision.lean:36`), so `decide`, `arms`, `binds`,
   `arms_length`, `decide_typed`, the wire tag, the printer's clause, the reader's clause and
   the OCaml regeneration all move — the constructor cascade, not the atom one. **The typing is
   the blocker either way**: `typeOf` for `ctorArg` would have to answer the type of a
   positional field of a `ctor`, and `Ty` has no constructor-indexed product. So these atoms
   would be usable only in raw programs. Recommend the two atoms **only** if the owner wants the
   reader to consume the generated image; otherwise skip, because the tagged-pair encoding needs
   nothing (item 1).

4. **`Image`/`Canonical` for `TypeScript.Expr`** — a `tools/Effect4Gen/manifest.json` group with
   `Imports: TypeScript.Syntax`. Cost: one manifest entry plus whatever the generator's helper
   naming needs for `List (Nat × List Stmt)` (§9). Only useful together with item 3.

5. **Generalise `run_eq_meaning` (and `loopAgreement`) to a non-empty initial environment.** A
   real proof task and a change to `Api.run`'s entry. Needed only if the owner wants the *Lean
   machine* to be one of the faces the open reader runs on. Not needed for R6 (§4.2(c)).

6. **A procedure form, or a proof that a `gen` loop's meaning is the fold of its body.** This is
   dogfood 6's item 1 (`§6, "what the core is missing"`) and the only thing that would make
   shape (i) viable. It is a language design question of its own size; it is out of scope for R4
   to R6 and should stay out.

7. **A recursive type in `Ty`.** What typing the reader would actually need. Enormous (the type
   algebra, `sub`, `join`, `normalize`, `ofTy`, the printer's type spelling, the OCaml mirror).
   Do not.

---

## 7. Verdict

**Later, and not as the way to do R6.** Specifically:

- R6 should be done as the packet says: export the table as a document, write one matcher over
  it in TypeScript. That is the smaller total change (§5.3), it adds one artefact on the
  TypeScript side rather than three, and it does not depend on an encoding decision for `Val`.
- The reader-as-an-`Eff`-program should be taken up **after R5.2**, as a worked demonstration
  rather than as R6's mechanism — because until R5 lands, a program built from
  `select … (.tag _)` cannot be read back at all (§4.4), and because its value is the
  demonstration, not the deletion.
- It is **not** a research item in the sense of "we do not know if it is possible". It is
  possible today; probes 1, 2, 3, 4, 6 are the receipt. What is open is only whether it is worth
  the two encoders on the host side.

**The first slice that would prove it out end to end**, in order, each small:

1. `Test/Codegen/LayerReaderProbe.lean` (unrooted first): the R4 table folded into a
   `Src NativeOp` by a Lean function, with `#guard`s that `Straight` holds and that the meaning
   equals `matchLayer` on one node per row of the table. This is probe 1 scaled to the real
   table; probe 4 already shows it is 46 KB and runs.
2. The compile theorem of §4.2 for that layer, one `rfl`-sized case per row, stated against
   `matchLayer` so the laws stay on `matchT`.
3. Print and run it on the host, one closed program per test node (the node as a `pair`
   literal, §4.2(a)), because that variant types and therefore emits a module with its
   annotation — compiled, probe 6. If the printed reader agrees with `matchLayer` on every row,
   the claim "the host reader is this repository's own program" is established, and the owner
   can then decide whether to pay for the two encoders in `ts/eff/` that the open variant
   needs.

Steps 1 to 5 of the packet's §4 do not depend on any of this, and should not wait for it.

---

## 8. The probes

Eight scratch files, all compiled with `cd /Users/pooks/Dev/lean4-effect4 && lake env lean <file>`
(probes 4, 5, 7, 8 with `-M 8192` or `-M 16384`), one at a time, no rebuild triggered. Location:
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/aa7ebaa0-7350-4784-b70e-322956de92e8/scratchpad/scoutA/`.

### probe1.lean — one layer authored from a table, meaning versus specification

The whole program, as authored:

```lean
structure TRow where
  head : String
  ctor : String

def table : List TRow :=
  [ ⟨"Effect.flatMap", "bind"⟩, ⟨"Effect.succeed", "succeed"⟩ ]

def refuseP : Src NativeOp := Authoring.fail (str "no rule")

def rowArm (r : TRow) (headName argsV : TermSrc) (rest : Src NativeOp) : Src NativeOp :=
  ifElse (app "eq" [headName, str r.head])
    (succeed (app "pair" [str r.ctor, argsV]))
    rest

def layerReader (rows : List TRow) (node : TermSrc) : Src NativeOp :=
  selectTag "p" "notCall" node "call"
    (selectTag "h" "notIdent" (app "fst" [var "p"]) "ident"
      (rows.foldr (fun r rest => rowArm r (var "h") (app "snd" [var "p"]) rest) refuseP)
      refuseP)
    refuseP

def readerAt (rows : List TRow) : Except Refusal NativeEff :=
  layerReader rows (var "node") { names := ["node"] } []
```

and the specification beside it:

```lean
def matchLayer (rows : List TRow) : Val → Option Val
  | .list [.str "call", .list [h, args]] =>
    match h with
    | .list [.str "ident", .str name] =>
      (rows.find? (·.head == name)).map fun r => tagged r.ctor args
    | _ => none
  | _ => none
```

Guards, all passing (the compile printed nothing):

```
#guard (readerAt table).isOk
#guard Straight readerTree = true
#guard answerOf (nCall "Effect.flatMap" argsA) = matchLayer table (nCall "Effect.flatMap" argsA)
#guard answerOf (nCall "Effect.flatMap" argsA) = some (tagged "bind" argsA)
#guard answerOf (nCall "Effect.succeed"  argsA) = matchLayer table (nCall "Effect.succeed" argsA)
#guard answerOf (nCall "Effect.zip"      argsA) = none
#guard matchLayer table (nCall "Effect.zip" argsA) = none
#guard answerOf (tagged "ident" (.str "a0")) = none
```

with `answerOf v = (meaning readerTree [v] Stores.empty).1` projected through `Exit.success`.

### probe2.lean — the closed variant, the machine, printing, reading, typing, size

```
#guard Straight p2 = true                     -- passed
#guard Straight p20 = true                    -- passed
#guard exitOf p2  = some (.list [.str "bind", .str "ARGS"])   -- passed
#guard exitOf p20 = some (.list [.str "c19",  .str "ARGS"])   -- passed
#guard (Api.run p2 (budgetOf p2)).exit = some (meaning p2 [] Stores.empty).1  -- passed
#guard (Api.print p2).isOk                    -- passed
#guard (Api.print p20).isOk                   -- passed
#guard Api.readable p2 = true                 -- FAILED (see §4.4)
#guard (Api.print p2 read back = p2)          -- FAILED (same reason)
#eval  (Api.typeOf p2).isSome                 -- true
#eval  Api.explain p2                         -- "typed"
#eval  (Api.bytesOf p2).length                -- 1895
#eval  (Api.bytesOf p20).length               -- 10138
#eval  depth p2, steps p2                     -- 6, 7
#eval  depth p20, steps p20                   -- 24, 25
```

`budgetOf e = max (depth e) (2 * steps e + 6)`, the budget `run_eq_meaning` names. The two
failures are the intended ones: `readable` is `false` on `select … (.tag _)` by construction
until R5.

### probe3.lean — cons lists without list atoms; `Val.ctor` blindness

All guards passed. Outputs: `(Api.typeOf p3).isSome = true`, `Api.explain p3 = "typed"`,
answer type `readonly ["X", "Y"]` — a *bounded* literal cons list types; an unbounded one does
not (§2.5).

### probe4.lean — a realistic 38-row layer, measured

```
meaning on an encoded Effect.flatMap(…, (a0) => …)
  → Val.list [Val.str "bind", Val.list [Val.list [Val.str "ident", Val.str "a0"],
                                        Val.list [Val.list [Val.str "ident", Val.str "Y"], Val.unit]]]
(Api.bytesOf big).length  = 46295
depth big = 46 ; steps big = 115
printed TypeScript length = 9623
(Api.print big).isOk = true
Api.readable big     = false
Straight big         = true   (#guard)
```

### probe5.lean — the `iterate` worklist

```
#guard Straight p5 = false ; #guard Looped p5 = true      -- both passed
(Api.run p5 200).exit                → Val.nat 3
(meaningB 10 p5 [] Stores.empty).1   → Val.nat 3
(Api.typeOf p5).isSome               → false
Api.explain p5                       → "refused at []"
```

### probe6.lean — the printed image (quoted in §5.1)

### probe7.lean — the unrolling cost (table in §3(i))

### probe8.lean — typing one layer at three candidate node types (table in §2.5)

---

## 9. What I did not check

- **Whether the `Canonical` generator actually emits for `TypeScript.Expr`.** I read that it
  handles `List`-nested recursion (`Json`) and mutual blocks (`Eff`), and I read `Expr`'s
  declaration. I did not add a manifest group and run the generator, and in particular I did not
  check `List (Nat × List Stmt)` (a list of pairs whose second component is a list) or the
  `Option TypeRef` fields, or whether the generator needs a `DecidableEq` instance that
  `TypeScript.Expr` does not have (it has only a hand-written `BEq`,
  `.lake/packages/typescript/TypeScript/Syntax.lean:210`).
- **The actual R4 table.** `src/Effect4/Codegen/Template.lean` and `Templates.lean` do not
  exist yet. My 38-row table in probe 4 is transcribed by eye from `Print.lean`'s clauses and
  `Print.heads` (56 heads, `Print.lean:133`–`:143`); the arities and binder counts are
  approximate. The 46 KB figure is therefore the right order of magnitude, not a measurement of
  the real table.
- **The branching factor of 33** used in §3(i)'s projection. I counted program children by hand
  off `Print.lean`'s clauses; I did not derive it from `binders.json`.
- **The corpus's own depths.** §3(i)'s "depth 4" is the brief's number, not a measurement. The
  400 generated programs are in `tools/Tools/Corpus.lean`'s stream; I did not run anything over
  them.
- **Whether `denote`'s equations actually close the §4.2 theorem in practice.** I argued it from
  the arms of `denote` (`Denote.lean:66`–`:118`) and the atom evaluations; I did not write the
  proof, not even for one row.
- **`raceAll` and `mergeAll` as variadic rows.** I showed a cons walk works for a *fixed* number
  of arguments and that the same walk is what a variadic row needs; I did not author a variadic
  row's arm, because it needs the recursion (shape ii or iii) to terminate the walk.
- **`gen`/`Stmts`.** The packet keeps the statement machine hand-written in the first cut; I did
  not look at what an authored statement reader would cost.
- **The host side.** No TypeScript was written or run. The claim that `exprOf` would need a twin
  encoder is read off `ts/eff/read.ts`'s header and structure, not measured.
- **D1 (`iterate`'s annotation).** Out of this scout's scope; nothing here changes the packet's
  §5 analysis, except to add that my probe 5 confirms `effTy`'s `iterate` arm types `step` at the
  whole annotation, which is one more reason (b), "a typed reader", is the larger route.
- **`make check` and every gate.** Not run; no tracked file was touched.
