# Scout B: reading types back, and `iterate`'s ergonomics

Read-only scout, 2026-09-17, on `refactor/phase1-phase3` at `b9c75004`. No compiler was run:
no `lake`, no `lean`, no `make`, no `bun`, no `tsc`. Every Lean snippet below is **not
compiled**.

Two questions from the owner: how the reader should obtain `iterate`'s cursor type (the
"bidirectional" question, taken in both of its senses), and how to make `iterate` ergonomic.

## 0. Evidence words

- **proved** — a theorem in the tree, cited by path and name.
- **tested** — a `#guard` or a harness lane in the tree that exercises it.
- **stamped** — a receipt in the record (a commit message, `docs/STATE.md`, a committed
  generated file) that says a gate passed.
- **reproduced** — I re-derived it by hand from definitions I read at the cited lines. No
  compiler confirmed it.
- **assumed** — taken on trust and named as such.

## 1. Corrections to the facts I was given

Four of the five facts in my brief hold exactly as stated. Here is what I found different.

1. **`Effect.iterate` and `Effect.loop` do not exist in rc.112.** My brief asks whether the
   printer should print "the idiomatic head, e.g. `Effect.iterate(initial, { while, body })`".
   There is no such export. `grep "export const iterate\|export const loop\b"` over
   `vendor/effect-4.0.0-rc.112/src` returns exactly two hits, neither of them an `Effect`
   combinator: `vendor/effect-4.0.0-rc.112/src/Stream.ts:1540` (`Stream.iterate`) and
   `vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4930` (`iterateEager`, `@internal`, an
   eager array walker for concurrent `forEach`). The only loop the public `Effect` surface
   has is `Effect.whileLoop` (`vendor/effect-4.0.0-rc.112/src/Effect.ts:1282-1286`), which
   answers `Effect<void, E, R>`. §5 works from that.

2. **The corpus number is 44 + 1.** Of the 400 generated programs, 44 hold a loop; `pLoop`
   from the wire corpus is the forty-fifth. Evidence: `git show 37ff9b21 --
   generated/corpus-index.tsv` removes 44 rows whose name starts with `g` and the row
   `pLoop`; a forty-sixth changed row, `pAwait`, is a `readable false → true` flip from the
   `callback` retirement, not a removal. `generated/corpus-index.tsv` now has 363 program
   rows. (tested by `Test/Codegen/ReadContract.lean:665-670`, which pins that the reader's
   refusals on the 400 are exactly the loop-bearing programs.)

3. **The collisions that matter are not the `int` ones.** `ofTy nat = ofTy int` is real
   (`src/Effect4/Codegen/Types.lean:271`, with `ofTy_nat`/`ofTy_int` as `rfl` theorems at
   `:322-324`), but `Ty.int` is uninhabited and admission-refused, so it is the least
   interesting collision. The dangerous ones are `handle "number"` against `nat` and
   `handle "void"` against `unit`, which are inhabited. §2.

4. **The annotation is younger than the printed shape, and the unannotated shape used to
   read.** Before `37ff9b21` the loop printed `let a1 = 0` with no annotation and no
   `Effect.map` wrapper, and both readers read it. `git show 37ff9b21 --
   harness/truth/generated/pLoop.ts` is the whole diff:

   ```diff
   -  let a1 = 0
   -  return Effect.whileLoop({
   +  let a1: number = 0
   +  return Effect.map(Effect.whileLoop({
        while: () => isZero(a1),
        body: () => Ref.update(a0, incr),
        step: (a2) => { a1 = succ(a1) },
   -  })
   +  }), () => undefined)
   ```

   This is the single most useful fact in the note, and §4 turns on it.

## 2. Question 1(A): bidirectional printing, and why the quotient law is unsound here

### 2.1 Where a `Ty` meets source, and why `iterate` is different

There are three places a core type meets target syntax, and `iterate` is the odd one.

- The module declaration: `declarationType` (`src/Effect4/Codegen/Print.lean:608`) projects
  the **certificate's** type, and `envelopeCheck` (`src/Effect4/Codegen/Admit.lean:66`)
  compares the declared `TypeRef` with `declarationType` of the type the checker computed
  from the program. The core type is recomputed, never read back.
- A service key: `printKey` (`Print.lean:312`) projects `sig.serviceTy key`, and
  `keyReadable` (`src/Effect4/Codegen/Read.lean:740`) asks only that the projection succeeds.
  The core type comes from the **signature**, which the reader already holds.
- `iterate`'s cursor: `Eff.iterate (cursorTy : Ty) …` (`src/Effect4/Program/Eff.lean:372`).

In the first two the type is recoverable from something the reader has. In the third it is
not. **`iterate`'s cursor annotation is the only `Ty` stored inside the program alphabet**
(checked: `grep ": Ty)" src/Effect4/Program/Eff.lean` returns only `:372` among the
constructors). That is the whole of D1: B19's "never a section" was written when no type was
program data, and `iterate` made one.

### 2.2 The kernel of `ofTy`, measured

The only equivalence that makes `ofTy` injective on classes is, by definition, its own
kernel: `t ≈ u` iff `ofTy t = ofTy u = some r`. Its relation to the two orders already in
the tree:

- **It is strictly coarser than normalization.** `ofTy t = ofNormalized t.normalize`
  (`Types.lean:311`), so `normalize t = normalize u → t ≈ u`; that inclusion is proper, and
  `Types.lean:315` (`ofTy_normalize`) is the proved half.
- **It is unrelated to `Ty.sub`.** `sub nat int = false` and `sub int nat = false`
  (reproduced from `src/Effect4/Program/Ty.lean:373-387`: neither `nat, int` nor `int, nat`
  matches an arm, so both fall to `| _, _ => false`), yet `nat ≈ int`. In the other
  direction `sub (lit "a") string = true` (proved, `Ty.sub_lit_string`, `Ty.lean:640`) while
  `ofTy (lit "a") = .literal "a" ≠ .name ["string"] []`. So the two relations cross.

The classes with more than one **canonical** member, read off `ofNormalized`
(`Types.lean:268-304`):

| target `TypeRef` | canonical `Ty`s that project to it |
| --- | --- |
| `number` | `nat`, `int`, `union nat int`, `handle "number"`, and any union of these |
| `void` | `unit`, `handle "void"` |
| `string` | `string`, `handle "string"` |
| `boolean` | `bool`, `handle "boolean"` |
| `never` | `never`, `handle "never"` |
| `Option.Option<number>` | `option nat`, `option int`, `handle "Option.Option<number>"` |
| any `r` at all | `r`'s own head, and `handle (the text that parses to r)` |

The handle row is the general case and the one to keep in mind: `ofNormalized (.handle
target) = parseLegacy target` (`Types.lean:274`), and `parseLegacy` accepts the whole
non-reserved qualified-identifier grammar (`Types.lean:263`, header at `:14-21`). So **every
type in `ofTy`'s image has at least two canonical preimages**, one structural and one a
handle whose text spells it. Reproduced, not compiled.

### 2.3 `effTy` does not respect the kernel

This is the fact that decides the question. Two witnesses, both reproduced from the
definitions:

**Witness 1, no `int` involved.** Take the loop `iterate c (lit (nat 0)) (app "lt" [var 0,
lit (nat 3)]) (app "succ" [var 0]) (var 0) (succeed (lit .unit))`, the shape of
`pIterateCount` (`Test/Program/CompileContract.lean:609`).

- With `c = .nat` it types: `NativeAtom.typeOf .lt [nat, nat]` is `some .bool`
  (`src/Effect4/Program/NativeAtom.lean:186`), and `Ty.sub nat nat = true` by `sub_refl`
  (`Ty.lean:621`). Tested at `CompileContract.lean:644`.
- With `c = .handle "number"` — the same class, since `parseLegacy "number" = .name
  ["number"] []` — it refuses: `typeOf .lt [handle "number", nat]` asks `Ty.sub (handle
  "number") .nat`, which has no arm and is `false`, so `termTy` of the test is `none` and
  `effTy` is `none` (`src/Effect4/Program/Typing.lean:353-361`).

**Witness 2, with `int`.** `c = .union .nat .int` is canonical (`normalizeRow` keeps both:
neither `sub nat int` nor `sub int nat` holds, so the antichain drops neither), and
`ofTy (union nat int) = number` because `unionOf` erases duplicates (`Types.lean:172-175`).
The initial check passes (`sub nat (union nat int) = sub nat nat || sub nat int = true`, by
`sub_union_right`, `Ty.lean:625`), but the test fails: `sub (union nat int) nat = sub nat nat
&& sub int nat = false` (`sub_union_left`, `Ty.lean:635`).

**The direct question my brief asks — "does replacing `nat` by `int` in a cursor annotation
preserve typing?" — has a blunter answer than either witness: it does not even reach the
body.** `iterate .int (lit (nat 0)) …` fails the first conjunct, `Ty.sub c0.normalize
cursor.normalize`, because `sub nat int = false`. So `int` cannot replace `nat` at a cursor
whose initial value is a literal at all. The reason is the arithmetic atoms, every one of
which is `nat`-only (`src/Effect4/Program/NativeAtom.lean:180-204`, read):

```
succ, pred : [a] → nat        when a.sub .nat          (:181-182)
isZero     : [a] → bool       when a.sub .nat          (:183)
add        : [a,b] → nat      when both a.sub .nat     (:185)
lt         : [a,b] → bool     when both a.sub .nat     (:186)
eq         : [a,b] → bool     when both nat or both string (:187-188)
```

Nothing in the term language ever produces or accepts an `int`. `int` is a type with no
introducer, no eliminator and no inhabitant.

So the checker distinguishes types that `ofTy` identifies. The meaning distinguishes them
too: `Val.hasTy (Val.nat 0) (.handle "number") = false` (`src/Effect4/Program/Typed.lean:45-53`
— a `.nat` value never matches a `.handle` type), while `Val.hasTy (Val.nat 0) .nat = true`
(`:37`).

**Consequence.** A quotient lens whose canonizer picks a representative
(Foster, Pilkiewicz and Pierce, *Quotient Lenses*, ICFP 2008; the same canonizer idea drives
Boomerang, Bohannon, Foster, Pierce, Pilkiewicz and Schmitt, *Boomerang: Resourceful Lenses
for String Data*, POPL 2008) is **sound as a syntactic law and unsound as a typing law**.
The syntactic law would be

```lean
-- not compiled
theorem read_print_quotient (hr : readable sig spell n e) (hp : print sig n e = .ok x) :
    readEff sig spell n x = .ok (canonCursors e)
```

with `canonCursors` replacing each `iterate` annotation by its class representative. That is
provable in principle, and `print (canonCursors e) = print e` holds because `ofTy` is
constant on a class. But the object it returns is a **different program** whose type may
differ, so `Api.admitModule` (`Codegen/Admit.lean:111`) would stop meaning "what I read types
as what I printed". I would not take it.

Note also what "up to an equivalence" costs the rest of the estate: `roundTrip_eq`, the
corpus `.json` oracles (`tools/Tools/Corpus.lean`, whose whole design is "read the `.ts`, compare
bytes with the `.json`"), and the OCaml and TypeScript differentials all compare programs for
equality. A law modulo an equivalence needs every one of those comparisons to change.

### 2.4 `int`, quantified, and a hole in its ban

`Ty.int` is a **reserved uninhabited constructor**. Measured:

- `Val.hasTy v .int allocated = false` for every value (`src/Effect4/Program/Typed.lean:83`,
  the single arm `| .int => false`). proved by construction.
- `rawSupportedErrTy .int = false` (`src/Effect4/Program/Eff.lean:57`), so it cannot be an
  error column.
- `admitProgram` refuses it: `findIntInTable` over the supplied rows and `findIntInEffTy`
  over the certificate's answer and error columns, both to `AdmitRefusal.uninhabited`
  (`src/Effect4/Program/Admission.lean:29-51`, `:83-103`). tested at
  `Test/Api/ApiContract.lean:366-396`.
- **No atom, literal, row or generator ever produces one.** `Lit` is `unit | nat | bool | str`
  and `Lit.ty` never answers `.int` (`Eff.lean:235-246`); no arm of `NativeAtom.typeOf`
  answers `.int` (`NativeAtom.lean:180-204`); `grep "Ty.int\|\.int\b"` finds no occurrence in
  `src/Effect4/Program/Native.lean`, `src/Effect4/Program/Wire.lean` or
  `Test/Program/Gen.lean`.

The grep counts, so the owner can weigh "retire or confine" against the alternative:

- `grep -rn "Ty\.int\b\|| \.int\b" --include="*.lean" src/Effect4` gives **29 lines in 12
  files**. Ten are in the two generated modules (`Program/Fold.lean` 9,
  `Program/Derived.lean` 1). Five are `TypeScript.Expr.int`, a different constructor
  (`Codegen/Read.lean` 3, `Codegen/SourceBindings.lean` 1, `Codegen/Schema.lean` 1). That
  leaves **14 hand-written lines in seven files**, one of them a comment: seven arms in
  `Program/Ty.lean` (`renderRaw:66`, `members:86`, `key:107`, `isNever:145`, `isMember:344`,
  `normalize:447`, `taggedColumn:603`), and one each in `Codegen/Types.lean:271`,
  `Program/Typed.lean:83`, `Program/Admission.lean:31`, `Program/Eff.lean:59`,
  `Schema/Codec.lean:46` and `Schema/Bridge.lean:42` (plus the comment at
  `Schema/Bridge.lean:17`).
- **5 lines in `Test/`** construct a `Ty.int`, all of them the admission red controls in
  `Test/Api/ApiContract.lean` (`:366-368`, `:383`). Every other `.int` in `Test/` (79 lines)
  is `TypeScript.Expr.int`, an integer literal, a different constructor entirely.

So the honest quantification: **`int` costs thirteen hand-written arms and buys nothing.**
Retiring it would be a clean deletion of the last uninhabited type. But it is
**not** the repair for D1: the collisions that matter are the handle ones, and those do not
go away with `int`. Retiring it is worth doing for its own sake, in the `Ty` series (M2),
alongside the `Schema` arms that would go with it.

**A hole worth raising.** `findInt` scans the row table and the inferred `EffTy`. It does not
walk the program tree, and since `37ff9b21` the program tree contains a `Ty`. Reproduced
counterexample (not compiled):

```lean
-- an admitted program carrying `Ty.int` inside a cursor annotation
.catchIf (.lit (.bool true)) (.succeed (.lit (.nat 0)))
  (.iterate .int (.var 0) (.lit (.bool false)) (.var 0) (.lit .unit) (.succeed (.lit .unit)))
```

The `catchIf` handler binds the body's error column, which is `never`
(`Typing.lean:320-325`); `termTy` of `var 0` is then `never`, and `Ty.sub never .int = true`
(`Ty.lean:376`, `| .never, _ => true`), so the annotation check passes. The test is a
literal, the step is the same `never`-typed variable, the result is `unit`. The program's own
type is `⟨unit, never, ∅⟩`, so `findIntInEffTy` sees nothing, the table is empty, and
`admitProgram` accepts. **Finding S-B1**, below.

### 2.5 What a section can and cannot be

`readTy : TypeRef → Option Ty` with the law in the printing direction is definable:

```lean
-- not compiled
theorem ofTy_readTy {r : TypeRef} {t : Ty} (h : readTy r = some t) : ofTy t = some r
```

by structural induction on the fifteen arms of `ofNormalized`, choosing `nat` for `number`,
`unit` for `void`, and **no `handle` arm at all** (so every handle-spelled preimage refuses).
The order question — `ofTy` sorts union members by `Ty.key` (`Ty.lean:103-119`) while
`readTy` would rebuild a union by `Ty.join` — resolves because `readTy` is the identity on
constructor tags, so it preserves the key order of the members `ofNormalized` walked.
Reproduced; the one arm that needs care is `union`, and `Ty.normalize`'s `antichain sub`
could drop a member only if `ofTy` had produced two comparable members, which it cannot after
`unionOf`'s dedup.

What cannot exist is the other law, `readTy (ofTy t) = some t` for all `t` (that is exactly
non-injectivity). The packet already withdrew it and is right to have done so.

## 3. Question 1(B): bidirectional type checking, and the annotation as a mode switch

### 3.1 The reading

In the bidirectional discipline (Pierce and Turner, *Local Type Inference*, POPL 1998 and
TOPLAS 2000; Dunfield and Krishnaswami, *Bidirectional Typing*, ACM Computing Surveys 2021)
an annotation is a switch from checking to synthesis, written exactly where synthesis cannot
reach. A loop's cursor type is the canonical such place: it is the loop invariant, and loop
invariants are not synthesizable in general (the observation is as old as Hoare, *An
Axiomatic Basis for Computer Programming*, CACM 1969; algebraically it is the parameter of
the iteration operator — Elgot, *Monadic Computation and Iterative Algebraic Theories*, 1975;
Bloom and Ésik, *Iteration Theories*, 1993).

So: the annotation should exist, and it should be **optional**. That is the whole answer to
1(B), and it is what §4 recommends.

### 3.2 The rule, with the annotation optional

Today (`src/Effect4/Program/Typing.lean:353-361`, read):

```lean
| .iterate cursor initial test step result body => do
  let c0 ← termTy sig env initial
  let t  ← termTy sig (env ++ [cursor]) test
  let b  ← effTy  sig (env ++ [cursor]) body
  let c1 ← termTy sig (env ++ [cursor, b.answer]) step
  let d  ← termTy sig (env ++ [cursor]) result
  if t = .bool ∧ Ty.sub c0.normalize cursor.normalize = true
      ∧ Ty.sub c1.normalize cursor.normalize = true
    then some ⟨d, b.error, b.requires⟩ else none
```

With `cursorTy : Option Ty` the arm becomes one line longer (not compiled):

```lean
| .iterate cursorTy initial test step result body => do
  let c0 ← termTy sig env initial
  let cursor := cursorTy.getD c0          -- synthesis when absent, checking when present
  let t  ← termTy sig (env ++ [cursor]) test
  …                                        -- unchanged from here
```

Every program typed today with `cursorTy = t` is typed identically with `some t`, because the
arm is the same text. `none` is new, and it means "the cursor is exactly the initial value's
type"; the first `sub` check is then `sub_refl` and cannot fail. **This is a conservative
extension of the checker.** Reproduced.

`HasTy.iterate` (`src/Effect4/Laws/Program/Typing/HasTy.lean:179-188`) and `inv_iterate`
(`src/Effect4/Laws/Program/Typing/Inversion.lean:150-163`) take the same shape change: keep
the rule's seven premises and add `cursorTy.getD c0 = cursor` as an eighth, so the rule reads
as it does today with `cursor` a derived name. `effTy_sound`'s arm
(`Laws/Program/Typing/Sound.lean:113-117`) and the blame arm
(`src/Effect4/Program/Typing/Blame.lean:179-200`) each change by that one binding;
`initialNotCursor` becomes unreachable under `none`, which is correct and not a loss.

### 3.3 What the host infers when the annotation is absent

The printed statement is `let`, not `const` (`Print.lean:404`, `Stmt.letInit`; rendered as
`let a1: number = 0` in `harness/truth/generated/pLoop.ts`). TypeScript widens a literal
initialiser at a `let`, so:

| initial | `Lit.ty` | `let aN = <printed>` infers | agrees with `ofTy`? | evidence |
| --- | --- | --- | --- | --- |
| `lit (nat 0)` | `nat` | `number` | yes | **stamped** |
| `lit (str "x")` | `string` | `string` | yes | reproduced |
| `lit (bool true)` | `bool` | `boolean` | yes | reproduced |
| `lit .unit` | `unit` | `undefined` | **no — `ofTy .unit` is `void`** | reproduced |

The `nat` row is stamped, not inferred: `pLoop.ts` printed `let a1 = 0` before `37ff9b21`
and `check-truth` was green at that commit's parent. The other three are reproduced and I did
not run `tsc` on any of them (`let` widens a literal initialiser, `const` does not; the
harness sets `"strict": true` in `harness/truth/tsconfig.json`).

The fourth row is the one control to run before taking §4: `ofTy .unit = .name ["void"] []`
(`Types.lean:270`, proved as `ofTy_unit` at `:320`), and the printer spells the unit literal
`undefined` (`harness/truth/generated/pLoop.ts`, the `() => undefined` result). It cannot
break the module's declared type, which Lean computes and `envelopeCheck` compares, but it
could move a `check-tsdiag` row. If it does, the repair is small: keep the annotation for a
unit cursor, which under (d′) is the author writing `some .unit` and losing only the round
trip on unit-cursor loops — or, better, take template row A of §5.6, which prints a
unit-*result* loop as the bare `Effect.whileLoop`; a unit *cursor* is a different thing and
would still want the control.

**The widened case is exactly where the host cannot infer**, and the brief's example is right:
`Option.none` is `<A = never>(): Option<A>`
(`vendor/effect-4.0.0-rc.112/src/Option.ts:256`), so `let a = Option.none()` infers
`Option.Option<never>` and a later `a = Option.some(3)` is an error. An annotation is the only
repair on the host side too. (Today this case is unreachable from our term language anyway —
§5.2, no atom constructs an option.)

## 4. The options, the recommendation, and the ruling owed

`readable` on `iterate` is `false` today (`src/Effect4/Codegen/Read.lean:798`); `ts/eff/read.ts:1235`
refuses the head the same way. The five options in my brief, plus the two the tree suggested,
against what each makes `readable` mean.

| | option | `readable (iterate c …)` | `read_print` | `read_exact` | what is lost | cost |
| --- | --- | --- | --- | --- | --- | --- |
| (a) | chosen representative `readTy` | `readTy (ofTy c) = some c` and the children | exact, on that domain | unchanged (no premise) | loops whose cursor is a handle-spelled or `int`-bearing type never read back | one function (~15 arms), two theorems, one `readable` arm, one template hole sort; amends B19 for one clause |
| (b) | typed reader carrying a `TyEnv` | children only | exact | needs the environment threaded through the statement | the reader becomes an elaborator; ties reading to the checker | every arm of `readEff` and every numbered case of `read_exact_all` (`Read.lean`, 3,504 lines) |
| (c) | `TypeRef` stored in `Eff` | children only | exact | unchanged | the core alphabet depends on the target's syntax; `effTy` must read a `TypeRef`, i.e. `readTy` again but inside the checker | alphabet, wire, OCaml and TypeScript mirrors, `Ty` ordering in the derived group |
| (d) | annotation optional, printed from the certificate, never read | children only | exact on `none` | unchanged | needs `print sig (env : TyEnv)` in place of `print sig (n : Nat)` | the §5 change of the typed-surface analysis: `Print.lean` and every round-trip lemma |
| **(d′)** | **annotation `Option Ty`; `none` prints unannotated and reads back; `some t` prints the annotation and does not read back** | **`cursorTy = none` and the children** | **exact on `none`** | **unchanged** | **loops with a widened cursor stay out of the round-trip lanes** | **one alphabet field, ~8 hand-edited declarations, the rest regenerated** |
| (e) | quotient round trip, reader canonizes | children only | only up to `canonCursors` | unchanged | `read ∘ print` no longer returns the program; every equality comparison in the corpus and the two differentials changes | moderate code, worse guarantee (§2.3) |
| (f) | store a subtype `{t : Ty // Readable t}` | `true` unconditionally | exact, no premise | unchanged | `Eff` stops being plain first-order data | `DecidableEq`/`Repr` deriving, the wire codec, JSON, the OCaml and TypeScript mirrors, every construction site |

### 4.1 Recommendation: take (d′) now, keep (a) additively in reserve

Five reasons, in order of weight.

1. **It restores the pre-`37ff9b21` image exactly.** Under (d′), plus one classifier for the
   unit-result loop (§5.6), `pLoop` prints byte-for-byte what it printed before the
   retirement: `let a1 = 0`, bare `Effect.whileLoop`, no `Effect.map`. That image was read by
   both readers and was green on the host lanes. The whole of D1 disappears, and with it R4's
   `type` hole sort (the R4 packet §2's `Subst` sum loses its `type` case) and R5.3's
   dependence on an owner ruling.
2. **It recovers the whole corpus.** `Test/Program/Gen.lean:261-265` writes `cursor := match
   initial with | .lit value => value.ty | _ => .nat`, which is `termTy env initial` for every
   literal initial and `nat` where the initial is a variable the generator draws at type
   `nat`. So **every one of the 44 generated loops, and `pLoop`, is a `none` under the new
   rule**, and all 45 rows return to `generated/corpus-index.tsv`, the tsdiag lane and the
   OCaml differential. (a) recovers the same 45 and no more, because the same annotations are
   their own class representatives.
3. **It keeps B19 literally whole.** Nothing reads a `TypeRef` back. The reader does not see
   an annotation because there is none to see. (a) needs a section and a written amendment.
4. **It is the cheapest moment in the alphabet's life.** `iterate` landed on 2026-09-17 at
   wire tag 28. `Option Term` is already a field shape the wire codec handles
   (`src/Effect4/Program/Wire.lean:18`, `ActionTerm.interruptAll`'s optional interruptor at
   `Eff.lean:400`), so `Option Ty` needs no new codec machinery. The annotation has **no
   runtime meaning**: every machine and meaning site binds it as `_` (`Compile.lean:608`,
   `:1254`, `:1276`, `:1301`, `:1307`; `NodeLenses.lean:45`, `:102`;
   `Laws/Program/DenoteR.lean:879`), so nothing about the compile, the reference, the
   budgeted meaning or the loop-agreement proofs moves.
5. **It is the same direction as (d), one step short.** (d) is the principled end state and it
   needs `print` to carry a `TyEnv`, which the typed-surface analysis already schedules for
   binder annotations (`docs/research/2026-09-16-typed-surface-integration-analysis.md` §5).
   Doing that inside `Print.lean` and `Read.lean` *before* R4/R5 replace them is work thrown
   away. (d′) is (d) with the printer left alone.

**What (d′) gives up**, stated plainly: a loop whose cursor must be wider than its initial
value prints and does not read back — the same status `select … .option` and `select … .tag`
have today. If and when such a program appears in a corpus, (a) is additive on top: keep
`Option Ty`, and let `readable (iterate (some c) …)` ask `readTy (ofTy c) = some c` instead of
being `false`. The two compose; (a) alone does not give reasons 1, 3 or 4.

### 4.2 The declarations (d′) touches

Hand-edited (reproduced by reading each site, not compiled): `Eff.lean:372` (the field),
`Typing.lean:353` (one `let`), `Typing/Blame.lean:179` (the same `let`),
`Laws/Program/Typing/HasTy.lean:179`, `Inversion.lean:150`, `Sound.lean:113` (one premise
each), `Print.lean:397-412` (the annotation becomes a `match` on the option),
`Read.lean:798` (`readable`'s arm), plus the `iterate` row of the R4/R5 template table when
it lands. On the OCaml face, the `iterate` arm of `ocaml/eff/e4_program.ml`.

Regenerated: `Program/Derived.lean:1310`/`:1422`/`:1581`, `Program/Fold.lean:1033`/`:1131`,
`Program/Wire.lean`, `Program/Binders.lean` (unchanged — the binder row is by argument index,
`tools/Effect4Gen/binders.json:31`), `Program/Scoped.lean`, `Program/NodeLenses.lean`,
`Program/Authoring/Lifts.lean:177`, `Laws/Program/Authoring/Lifts.lean:279`,
`src/OCaml5/Eff/Goldens.lean`, `ts/eff/{eff,json,wire}.gen.ts`.

Gates that must move with it: `make check`, `check-gen`, `check-compat` (the `iterate` field
shape changes, so tag 28's byte layout changes — `iterate` has no retained byte vector, being
one day old, but the policy should name the change), `check-ocaml`, and then the **promotion**
of `generated/corpus-index.tsv` and `generated/tsdiag-agreement.tsv` with the 45 rows back,
which the `Eff` series was already holding for its end (`docs/STATE.md`, item 5).

### 4.3 What the owner must rule here

**D1′.** Take (d′) — `Eff.iterate (cursorTy : Option Ty)`, `none` synthesized from the
initial value and printed unannotated, `some t` printed and not readable — in place of the
packet's (a)? If yes, R4's `type` hole sort and R5.3's blocker both go away, and the
owner also decides whether (a) is scheduled behind it or dropped.

## 5. Question 2: making `iterate` ergonomic

### 5.1 What rc.112 gives an author, and what each one is

Every row read at the cited line.

| rc.112 | where | signature, shortened | what it is |
| --- | --- | --- | --- |
| `Effect.whileLoop` | `Effect.ts:1282-1286`, impl `internal/effect.ts:4624-4645` | `<A,E,R>(options: { while: LazyArg<boolean>, body: LazyArg<Effect<A,E,R>>, step: (a: A) => void }) => Effect<void,E,R>` | the one loop primitive; a `makePrimitive` with op `"While"` |
| `Effect.reduce` | `Effect.ts:638`, impl `internal/effect.ts:4449-4484` | `(elements: Iterable<A>, zero: LazyArg<Z>, f: (z,a,i) => Effect<Z,E,R>) => Effect<Z,E,R>` | **derived**: `suspend(() => { let index = 0; let state = zero(); return map(whileLoop({…}), () => state) })` — literally the shape we print |
| `Effect.forEach` | `Effect.ts:1088`, impl `internal/effect.ts:4648-4696` | `(self: Iterable<A>, f: (a,i) => Effect<B,E,R>, options?: { concurrency, discard }) => Effect<B[]|void,E,R>` | **derived at concurrency 1** (`forEachSequential`, `:4706-4729`, a `whileLoop` over an iterator); concurrent path is `iterateEagerImpl` |
| `Effect.forever` | `Effect.ts:14480`, impl `internal/effect.ts:2444-2468` | `(self) => Effect<never,E,R>` | **derived**: `whileLoop({ while: constTrue, body: …, step: constVoid })` |
| `Effect.repeat` | `Effect.ts:14574` | `(self, schedule: Schedule<…>) => …` | schedule-driven; `Schedule` is a stepped state machine (`Schedule.ts:1-10`, `InputMetadata` at `:58-68`) |
| `Effect.iterate` | — | — | **does not exist in rc.112** |
| `Effect.loop` | — | — | **does not exist in rc.112** |

So: of the six, three (`reduce`, sequential `forEach`, `forever`) are derived forms over
`whileLoop` **in rc.112 itself**, which means they are derived forms over our `iterate` if we
can spell their arguments. `repeat` needs `Schedule`, a separate algebra. Two do not exist.

### 5.2 Which of them our language can express today, and what each lacks

Written as `Eff` data, against the alphabet **as it is today** (the annotation is a bare `Ty`;
under (d′) every `.unit`/`.nat` annotation below becomes `none`). All reproduced from the
definitions; none compiled.

**`forever body` — expressible now, one line.**

```lean
-- not compiled; the cursor is unit and the test is the literal `true`
def forever (body : Eff Op) : Eff Op :=
  .iterate .unit (.lit .unit) (.lit (.bool true)) (.lit .unit) (.lit .unit) body
```

Types: `termTy` of the test is `bool`, `sub unit unit` twice, answer `unit`
(`Typing.lean:353-361`). Difference from rc.112 worth naming: `Effect.forever` answers
`never` (`Effect.ts:14491`); ours answers `unit`, at a result term the machine never reaches.
That is a **typing** difference, not a behavioural one, and it is a candidate for the `Ty`
series in M2 rather than something to fix here.

**`whileLoop` (the unit loop) — expressible now.** `iterate c initial test step (lit .unit)
body`. This is exactly the retired constructor, and the retirement's own record says so
(`effTy_iterate_of_whileLoop`, commit `438b93f2`, cited in the select/iterate packet §1.9).

**`repeatN n body` and `countTo n body` — expressible now.** Cursor `nat`, initial `lit (nat
0)`, test `app "lt" [var 0, lit (nat n)]`, step `app "succ" [var 0]`. Every atom exists
(`NativeAtom.lean:44`).

**`reduce` and `forEach` — not expressible.** They need a list value in a term and a way to
walk it. What is there: `Val.list` exists (`Store/Val`), `Ty.list` exists (`Ty.lean:32`), the
atom `strings` builds a list of strings (`NativeAtom.lean:139`), and `pair`/`fst`/`snd` build
and project pairs. What is missing, measured against `NativeAtom.all` (`:43-45`, twenty
atoms): **no `length`, no indexing, no `head`, no `tail`, no `cons`, no `append`.**

The minimal addition is **one atom**:

```lean
-- not compiled
| uncons                                            -- list a → option (prod a (list a))
-- eval:   | .uncons, [.list (x :: xs)] => some (Store.Val.some (Val.list [x, .list xs]))
--         | .uncons, [.list []]        => some Store.Val.none
-- typeOf: | .uncons, [a] => match a.normalize with
--                          | .list t => some (.option (.prod t (.list t)))
--                          | _ => none
```

With `uncons`, `select … .option` (landed) is the eliminator, `pair`/`fst`/`snd` carry the
`(rest, accumulator)` cursor, and both `reduce` and sequential `forEach` are derived forms
over `iterate`. A two-atom alternative (`length` and an indexing atom) needs a fallback value
at the index, which `getOrElse` can only supply if the caller has one; `uncons` needs none.
**Recommendation: one atom, `uncons`, and it belongs with the list work, not with this
slice.**

One more gap, found while writing the option example the brief asks for: **no term
constructs an `Option` value.** `NativeAtom.eval` has `isSome` and `getOrElse` as
eliminators (`NativeAtom.lean:147-150`) and no `some`/`none` introducer; the only
option-typed term in the language is `causeError c` (`NativeAtom.typeOf`, `:195`). The
`FnName` partial functions (`zeroWhenPositive`, `noChange`, `Machine/Stores.lean:113-115`)
produce options inside the store step, not as a typed answer — no row answers `Ty.option`
(checked: `grep option src/Effect4/Program/Native.lean` is empty). So **an `option`-cursor
search is not authorable today**, whatever the loop's ergonomics. §5.5 writes it anyway and
marks the hole.

### 5.3 The forms mechanism, and what it cannot yet hold

`Codegen.Forms` (`src/Effect4/Codegen/Forms.lean`) is the derived-form table: nineteen rows
(`all`, `:89-124`, tested at `:196-198`), a `Template` algebra with `expand`
(`:31-44`, `:61-73`), and `tools/Effect4Gen/Forms.lean` generating one authoring combinator
per row into `src/Effect4/Program/Authoring/Forms.lean`, each with a `#guard` that its
elaboration equals `Template.expand` on the row's own example arguments
(`Authoring/Forms.lean:92-147`). That mechanism is exactly what a new derived form should use
— Landin's point that a derived form is sugar and adds no power (*The Next 700 Programming
Languages*, CACM 1966; made precise by Felleisen, *On the Expressive Power of Programming
Languages*, 1991) is the estate's own "prefer derived forms over new constructors" rule.

**But `Template` has no loop former** (`Forms.lean:31-44`: `argument`, `succeed`, `die`,
`bind`, `onExit`, `matchCause`, `service`, `yieldNow`, `fork`, `forkIn`, `forkScoped`,
`acquireRelease`). So no loop form can be a `Forms.all` row until `Template` gains

```lean
-- not compiled
| iterate (cursorTy : Option Ty) (initial test step result : TermTemplate) (body : Template)
```

That is one constructor, one `expand` arm, and one arm in `forms.ts`'s interpreter
(`ts/eff/forms.ts`, which "interprets every template constructor", review-log B13). It also
lets `Template` express the existing `close`/`insert` machinery over a loop body, which needs
the binder count (1 at child 0, `Program/Binders.lean:28`).

**Recommendation on where the loop forms live.** Two tiers, and they are not the same thing:

- **Authoring-only sugar** (`whileLoop`, `forever`, `repeatN`, `countTo`, `iterateWith`):
  plain definitions in `Authoring/`, no `Forms.all` row, no printed head, no reader work. They
  cost one definition and one `#guard` each, exactly as the packet's §3c says of `matchTag`
  and `retry`.
- **`Forms.all` rows** (`Effect.forEach`, `Effect.reduce`, and `Effect.forever` if we want the
  head recognized on the reading side): these are *foreign spellings the reader admits*, so
  they need `Template.iterate`, the atoms of §5.2, and a row in the taxonomy. Not now.

`Effect.forever` is the one borderline case: it has a real rc.112 head and a one-line
expansion, so it is the cheapest first `Forms.all` loop row once `Template.iterate` exists.

### 5.4 The authoring shapes

Today the lift is generated from `tools/Effect4Gen/binders.json:31` into
`src/Effect4/Program/Authoring/Lifts.lean:177`:

```lean
def iterate {Op : Type} (cursor : String) (answer : String) (cursorTy : Effect4.Program.Ty)
    (initial : TermSrc) (test : TermSrc) (step : TermSrc) (result : TermSrc) (body : Src Op) : Src Op
```

Eight arguments, two of them binder names, one a mandatory `Ty`. The contract writes it as
`iterate "i" "a" .nat (nat 0) test step result body` (`Test/Program/AuthoringContract.lean:99`,
`:109`).

**The proposal, four definitions, none of them a constructor.** `bindWith`
(`Authoring/Sugar.lean:25`) is the precedent: mint a fresh name from the scope's length and
hand the author a `TermSrc` function. The loop binds two names at two depths — the cursor at
`env.names.length`, the body's answer at `env.names.length + 1` (`Lifts.lean:178-184`) — so
two fresh names are minted.

```lean
-- not compiled. Argument order follows rc.112's object, `{ while, body, step }`
-- (vendor/effect-4.0.0-rc.112/src/Effect.ts:1283-1285); the first key is spelled `test`,
-- the constructor's own field name (Eff.lean:372), because `while` is a Lean `do` keyword
-- and the estate already renames around that (`ifElse`, Authoring/Sugar.lean:39-41).
namespace Effect4.Program.Authoring

/-- The loop, with the cursor and the body's answer as Lean functions.
`result` defaults to the cursor, which is `Effect.reduce`'s own shape
(`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:4468-4482`). -/
def iterateWith {Op : Type} (initial : TermSrc)
    (test : TermSrc → TermSrc)
    (body : TermSrc → Src Op)
    (step : TermSrc → TermSrc → TermSrc)
    (result : TermSrc → TermSrc := id)
    (cursorTy : Option Ty := none) : Src Op := fun env p =>
  let c := "_" ++ toString env.names.length
  let a := "_" ++ toString (env.names.length + 1)
  iterate c a cursorTy initial (test (var c)) (step (var c) (var a)) (result (var c))
    (body (var c)) env p

/-- `Effect.whileLoop` (`vendor/effect-4.0.0-rc.112/src/Effect.ts:1282`): the loop that
answers nothing. The retired constructor, as sugar. -/
def whileLoop {Op : Type} (initial : TermSrc) (test : TermSrc → TermSrc)
    (body : TermSrc → Src Op) (step : TermSrc → TermSrc → TermSrc) : Src Op :=
  iterateWith initial test body step (result := fun _ => unit)

/-- `Effect.forever` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:2464-2468`). -/
def forever {Op : Type} (body : Src Op) : Src Op :=
  iterateWith unit (fun _ => bool true) (fun _ => body) (fun _ _ => unit) (fun _ => unit)

/-- Run the body `n` times, the index in scope. `Schedule.recurs n` as a form. -/
def countTo {Op : Type} (n : Nat) (body : TermSrc → Src Op) : Src Op :=
  whileLoop (nat 0) (fun i => app "lt" [i, nat n]) body (fun i _ => app "succ" [i])

end Effect4.Program.Authoring
```

Four properties of that shape, each deliberate:

- **No type argument in the common case.** `cursorTy := none` is the default, and under (d′)
  the checker synthesizes. An author who wants a wider cursor writes `(cursorTy := some
  (.union .nat .string))` and reads the refusal at the path if it is wrong
  (`Api.author` → `Api.check` → `blame`, `src/Effect4/Api.lean:436-443`, `:491-496`).
- **No binder-name arguments.** The two names are minted, as `bindWith` mints one. An author
  who wants readable names writes the underlying `iterate` lift, which stays.
- **The result defaults to the cursor**, which is the shape of `Effect.reduce` and of every
  counting loop; `whileLoop` overrides it to unit.
- **Named arguments make it read like the host.** `iterateWith (nat 0) (test := …) (body :=
  …) (step := …)` is `Effect.whileLoop({ while, body, step })` with the initial value in
  front, which is where `Effect.reduce` puts its `zero`. The one spelling that cannot match
  is `while`, a Lean `do` keyword; `test` is the constructor's own field name and is the
  honest substitute. (`«while»` would parse, at the cost of a noisy call site.)

**Should authoring offer `whileLoop` again?** Yes. It costs one definition and one `#guard`,
it is the name the host uses, and the alphabet is unchanged — which is exactly the trade the
retirement was made to get.

### 5.5 Before and after, three loops

All `Src NativeOp`. Not compiled; the "before" column is the spelling the tree has today.

**(1) Count to three, answering the count.** Before (the shape of
`AuthoringContract.lean:108-112`):

```lean
iterate "i" "a" .nat (nat 0) (app "lt" [var "i", nat 3]) (app "succ" [var "i"])
  (var "i") (succeed unit)
```

After:

```lean
iterateWith (nat 0) (test := fun i => app "lt" [i, nat 3])
  (body := fun _ => succeed unit) (step := fun i _ => app "succ" [i])
```

**(2) Accumulate into a `Ref` — the `pLoop`/`pWhileLoop` fixture.**
`Test/Program/CompileContract.lean:563-570` writes the positional tree; by name today it is

```lean
bind "r" (Ref.make (nat 0)) <|
  bind "_" (iterate "i" "a" .nat (nat 0)
              (app "lt" [var "i", nat 3]) (app "succ" [var "i"]) (var "i")
              (Ref.update .incr (var "r")))
           (Ref.get (var "r"))
```

After:

```lean
bindWith (Ref.make (nat 0)) fun r =>
  andThen (countTo 3 fun _ => Ref.update .incr r) (Ref.get r)
```

That is the whole point of the exercise: the second reads as the Effect program it is
(`Effect.flatMap(Ref.make(0), (r) => Effect.andThen(…, Ref.get(r)))`), and no level, no
binder name and no type appears.

**(3) Search with an `option` cursor — not authorable today.** The intended spelling:

```lean
-- not compiled, and NOT typeable today: no term constructs an Option value (§5.2).
-- Read a Ref until it holds something interesting; the cursor is the answer found so far.
bindWith (Ref.make (nat 0)) fun r =>
  iterateWith (cursorTy := some (.option .nat))
    (initial := optionNone)                                -- does not exist
    (test    := fun found => app "not" [app "isSome" [found]])
    (body    := fun _ => Ref.get r)
    (step    := fun _ a => optionSome a)                   -- does not exist
```

Two things are missing and they are independent: the term-level `Option` introducers
(`some`, `none` as atoms, or an `Option`-answering row), and — only if the initial value is
`none` — the widened annotation, which is why `cursorTy := some (.option .nat)` appears. The
second is precisely the case (d′) leaves unreadable and (a) would recover. **This is the
concrete program that decides whether (a) is ever needed**, and it cannot be written until
the option introducers land. That ordering is useful: take (d′) now, and revisit (a) when the
option atoms make the widened cursor reachable.

### 5.6 Should the printer print an idiomatic head?

**Not a new one — there is none to print** (§1, correction 1). But there is a template row
worth adding immediately, and it is free:

- **Row A, classifier `result = .lit .unit` (and, under (d′), `cursorTy = none`):**
  `Effect.suspend(() => { let aN = initial; return Effect.whileLoop({ while, body, step }) })`.
  That is the **pre-`37ff9b21` image**, it is shorter, it drops the `Effect.map` head, and
  `Effect.whileLoop` already answers `void` (`Effect.ts:1286`) so the types line up with no
  wrapper. The row prints no `result` hole and the reader supplies `.lit .unit` from the row
  itself, which is what keeps `read_exact` exact: the classifier determines the field the
  image does not carry, exactly as `select`'s `.bool` decision does today.
- **Row B, otherwise, `cursorTy = none`:** today's image without the annotation.
- **Row C, `cursorTy = some t`:** today's image, `let aN: ofTy t = initial`, not readable
  (or readable under (a)).

The three rows are pairwise disjoint in the image and decidable by inspection: A and B differ
by the head inside the block (`Effect.whileLoop` against `Effect.map`), B and C by whether the
`letInit` carries a type — and the reader **already** refuses an annotated `letInit`
(`Read.lean:93`, `.annotation "local const"`), so C needs no new refusal. This is exactly
R4's "one constructor may own several templates selected by a classifier", and it is the
first real instance of it.

One consequence to weigh, reproduced not tested: the `Effect.map` wrapper is a host frame our
machine does not model (`compileEff` enters `Prim.whileLoop` directly, `Compile.lean:608` and
`:1276`). The truth lane compares schedules and frame counts (`harness/truth/corpus.json`,
each entry's `"frames"` and `"schedule"`), and it is stamped green today *with* the wrapper
(`docs/STATE.md`, "check-truth (36 programs agree with rc.112)"), so the wrapper is not
observed. Row A removes the question rather than answering it.

## 6. Findings raised

- **S-B1, `findInt` does not walk the program tree.** Since `37ff9b21` a `Ty` lives inside
  `Eff` (`Eff.lean:372`), and `admitProgram`'s int scan covers only the supplied row table
  and the certificate's answer and error columns (`Program/Admission.lean:83-103`). §2.4 has
  a reproduced program that carries `Ty.int` in a cursor annotation and is admitted. The fix
  is one more disjunct in `admitProgram`, over the annotations the tree holds — which is a
  `foldMap_eff`, the shape `holdsLoop` already uses (`Test/Codegen/ReadContract.lean:658`).
  Under (d′) the scan runs on `Option Ty`; the hole is the same either way.
- **S-B2, `Effect.forever`'s answer type.** rc.112 answers `never` (`Effect.ts:14491`); our
  `forever` would answer `unit`, at a result term the machine never reaches. The core has no
  way to say "this loop does not finish". Belongs with the `Ty` series (M2), not here.
- **S-B3, no `Option` introducer in the term language.** `isSome` and `getOrElse` are
  eliminators (`NativeAtom.lean:147-150`); nothing constructs an option; no row answers one.
  So `select … .option` has, today, almost no scrutinee to eliminate. Worth pairing with the
  option atoms already recorded as a gap.
- **S-B4, `readable`'s Boolean guard has to be re-pinned.** R5.2 says `readable` "is guarded
  by a Boolean equality against today's definition on the corpus before it is redefined". Any
  option above changes `iterate`'s arm from `false`, so the guard must be restated as
  "equal on every corpus program that holds no loop" (`holdsLoop` is already the predicate).
  Both (a) and (d′) preserve `readable`'s two structural properties for free, because the new
  condition mentions neither the level nor the path: `readable_weaken`
  (`src/Effect4/Codegen/Read.lean:3256`, its `iterate` arm at `:3261`) and
  `readable_hoistAll` (`src/Effect4/Laws/Codegen/HoistingReadable.lean:292`) go through by
  the argument entry 18 of the review log makes for the `service` arm.

## 7. What I did not check

- **Nothing was compiled.** Every Lean snippet is a proposal; every claim marked *reproduced*
  is my own reading of the definitions at the cited lines.
- **I ran no `tsc`.** Only the `nat` row of §3.3's table is stamped, from the pre-`37ff9b21`
  truth lane; the `string`, `bool` and `unit` rows are reproduced. I did not check whether
  the 44 generated loops that left `check-tsdiag` at that commit covered a `str` or `bool`
  initial, which would have stamped two more rows.
- I did not read `ts/eff/read.ts` beyond its two `iterate` mentions (`:1235`, `:1431`), so I
  cannot say what R6's host reader costs under either option beyond "one template row".
- I did not read `ocaml/eff/e4_program.ml`, so the OCaml cost of the `Option Ty` field is
  stated from the packet's own note that the arm is hand-written, not from the file.
- I did not check `Ty.key` ordering against `readTy`'s union arm with a machine; §2.5's order
  argument is reproduced.
- I did not measure how many of the 44 generated loops would still be readable if the
  generator were changed to draw a widened cursor sometimes; the generator draws none today.
- I did not look at `Schedule.ts` beyond its header and `InputMetadata` (`:1-10`, `:58-68`),
  so §5.1's `repeat` row is the shallowest in the table.
- I did not evaluate the packet's §5b question (the reader as an `Eff` program) against
  either option; both are compatible with it as far as I can see, and neither depends on it.

## 8. What the owner must rule

1. **D1′ (replaces D1).** Take (d′): `Eff.iterate (cursorTy : Option Ty)`, `none` synthesized
   from the initial value and printed unannotated, `some t` printed and not readable. If yes,
   R4's `type` hole sort and R5.3's blocker disappear, `Print.lean` is not touched beyond one
   clause, and the 45 corpus rows come back. If no, the packet's (a) is the next best and
   needs a written amendment to B19 confined to `iterate`'s reader clause.
2. **Whether (a) is scheduled or dropped.** It becomes reachable only when a widened cursor
   is authorable, which needs the `Option` introducers of S-B3. Recommendation: record it as
   deferred with that dependency, not as owed.
3. **Template row A** (§5.6): print a unit-result loop as the bare `Effect.whileLoop`, which
   restores the pre-`37ff9b21` bytes. This is a golden-moving change and wants the owner's
   word even though it is a strict simplification.
4. **The loop sugar's home.** Authoring-only definitions now (`iterateWith`, `whileLoop`,
   `forever`, `countTo`), with `Forms.all` rows for `Effect.forEach`/`Effect.reduce` deferred
   behind `Template.iterate` and the `uncons` atom. Recommendation: yes to the first, defer
   the second.
5. **S-B1**, the `findInt` hole: fix with the alphabet change, or file it.
