# Loop sugar over `iterate`, and list elimination from the algebra

2026-09-17. The owner's asks of the day: float sugar for loops and folds built on `iterate`
("just because Effect does not have it does not mean we cannot"); do not refurbish what was just
retired (no `whileLoop` constructor, no second printed loop shape); evaluate `uncons` from the
algebra, not as an ad hoc atom. Probe: `docs/research/2026-09-17-loop-sugar-probe.lean`, compiled
with `lake env lean` against the tree with DI-91 applied; every result below marked compiled comes
from it.

## 1. What `iterate` is

One cursor `c`, a pure test, an effectful body, a pure step over the cursor and the body's answer,
a pure result. It is the iteration of the map `c ↦ if test c then (body c, then step) else result
c`, which lands in "another cursor, or an answer". That is an Elgot iteration, and
`src/Effect4/Laws/Program/Iter.lean` already has its laws (`iter`, `iter_succ`, `iter_uniform`,
`iter_congr`). It is the language's only recursion. Everything below is a Lean function that
authors one `iterate`; none adds a constructor, an atom, a wire tag or a printed shape.

## 2. The sugar, compiled

All of these elaborate, type-check (`Api.typeOf`), and give the stated answer on the machine
(`Api.run`), except where noted.

| form | what the author writes | what it is | probe |
| --- | --- | --- | --- |
| `iterateWith init { while_, body, step, result := id, cursorTy := none }` | binders are Lean functions; keys in rc.112's `{ while, body, step }` order; the result defaults to the cursor; no annotation by default (DI-91) | the generated `iterate` lift with names minted from the scope's length, as `bindWith` does | counts to 3: typed, answers 3 |
| `forRange lo hi (fun i => body)` | the loop most authors mean | `iterateWith lo` with test `lt i hi`, step `succ i` | bumps a `Ref` five times: typed, answers 5 |
| `foldRange lo hi zero (fun i acc => effect)` | an accumulator beside the counter | a pair cursor `(i, acc)`, taken apart with `fst`/`snd` for the author; answers `acc` | sums 0..4: typed, answers 10 |
| `whileEff cond body` | a loop whose CONDITION is an effect (read a `Ref`, poll a queue) | `iterate`'s test is a pure term, so the cursor is the condition's last answer: run `cond` once before the loop and again at the end of each round | bumps a `Ref` while it is below 3: typed, answers 3 |
| `reduceT xs zero (fun acc x => effect)` | a fold over a list, today | cursor `(acc, rest)` over a cons list encoded as tagged pairs; `out` is the `.tag "cons"` decision, the test is `tagIs("cons", rest)` | sums `[1, 2, 3]`: answers 6; NOT typed (§3) |

The counting loop prints, through the repository's printer, as the one loop shape, with no
annotation:

```ts
Effect.suspend(() => {
  let a0 = 0
  return Effect.map(Effect.whileLoop({
    while: () => lt(a0, 3),
    body: () => Effect.succeed(undefined),
    step: (a1) => {
      a0 = succ(a0)
    },
  }), () => a0)
})
```

`Effect.whileLoop` in that text is rc.112's function, the host primitive our one loop prints
through. No constructor of ours carries that name any more and none returns.

Names are open. `whileEff` could be `repeatWhile`; `forRange`/`foldRange` could sit under a
`Loop.` namespace. Home: `src/Effect4/Program/Authoring/Loops.lean`, hand-written like
`Sugar.lean`, each definition with its scope lemma through `authoring_scoped` (the pattern
`Authoring/Forms.lean` uses). Not yet written into the tree.

## 3. Lists: what the algebra says is missing

`reduceT` runs and does not type, because a tagged cons list has a recursive type and `Ty` has
none. `Ty` does have `list`, `option` and `prod`. So the typed fold is one step away: the list's
own destructor on the native `Val.list`.

Read the type formers of `Ty` as data types and ask, for each, whether the term language has its
introduction (the algebra, `in`) and its elimination (the coalgebra, `out`):

| type former | introduction | elimination | gap |
| --- | --- | --- | --- |
| `bool` | literal | `select … .bool`; `not`, `and`, `or` | none |
| `nat` | literal, `succ` | `isZero`, `pred` (that pair is `out : Nat → 1 + Nat`) | none |
| `string` | literal, `strings` | `eq` | none |
| `prod` | `pair` | `fst`, `snd` | none |
| tagged pairs | `pair` with a string tag | `select … (.tag t)`, `tagIs` | none |
| `option` | **none**: no term builds `some x` or `none` | `select … .option`, `isSome`, `getOrElse` | **introduction** |
| `list` | **none**: no term builds a list | **none**: nothing takes one apart | **both** |
| `exitOf`, `causeOf`, `fiberOf`, `handle` | by effects and rows | `matchCause`, the `cause*` atoms, `awaitFiber` | none at term level, by design |

So the evaluation of `uncons` from the algebra is: it is not an ad hoc atom, it is the list
functor's `out`, `list a → option (prod a (list a))` (Lambek's isomorphism read right to left),
and it is one of five missing pieces of two type formers the language already has:

- `none`, `some`: the introduction of `option`. Today `select … .option` can only scrutinize a
  row's answer, because no term produces an option (scout B's finding S-B3).
- `nil`, `cons`: the introduction of `list`.
- `uncons`: the elimination of `list`, landing in `option` of a `prod`, so the existing
  `.option` decision and `fst`/`snd` finish the job. No new `Decision`: a decision is a
  program-level case analysis, and `iterate`'s test is a term, so a term-level test is needed
  either way (`isSome (uncons rest)`); the atom alone serves both.

With that kit, everything else on lists is derived, by the one engine, and nothing else needs an
atom: `head`, `tail`, `length`, `append`, `reverse`, `range`, and the two Effect forms an author
reaches for, which rc.112 itself defines by a loop (`vendor/effect-4.0.0-rc.112/src/Effect.ts:638`
`reduce`, `:1088` `forEach`):

```
reduce xs zero f  :=  iterateWith (pair zero xs)
  { while_ := fun c => isSome (uncons (snd c))
    body   := fun c => selectOption (uncons (snd c)) (succeed c)          -- unreachable under the test
                         (fun cell => bindWith (f (fst c) (fst cell)) fun acc => succeed (pair acc (snd cell)))
    step   := fun _ next => next
    result := fun c => fst c }

forEach xs f      :=  reduce xs nil (fun acc x => map (fun y => cons y acc) (f x)), then reverse
```

`forEach` is where DI-91's stated annotation earns its place: the accumulator starts as
`nil : list never`, and `Ty.sub` is covariant under `list` with `never` under everything
(`src/Effect4/Program/Ty.lean`, `sub`), so the cursor is stated once as `some (prod (list b)
(list a))` and the empty start fits under it. That is the docstring's "a cursor whose members grow
(an accumulator that starts empty)", made concrete.

What the algebra then gives as THEOREMS, once, over the derived forms (the catamorphism recovered,
not assumed):

- `reduce` is the fold: at budget `length xs + 1`, `meaningB (reduce xs z f)` is `List.foldlM` of
  `f`'s meaning. The engine is `iter_uniform`; the budgeted meaning and its monotonicity are
  landed (`Laws/Program/DenoteB.lean`), and the loop agreement carries it to the machine
  (`Laws/Program/Agreement/Loop.lean`).
- fold fusion for `reduce` as an instance of `iter_uniform`.
- `forEach` answers the list of answers in order; on an empty list it runs nothing.

The alternatives, priced in the project's measured cascades:

| route | cost | verdict |
| --- | --- | --- |
| five atoms (`none`, `some`, `nil`, `cons`, `uncons`) | the atom cascade, measured on `isSome`/`getOrElse` (commit `6762ccb0`): about 60 hand-written lines per atom across `NativeAtom.lean`, `Laws/Program/Typed.lean`, `Progress.lean`, `harness/truth/prelude.ts`, the conformance policy; the rest regenerated | recommended; closes both gaps in the table, not one |
| `uncons` alone | one atom | works for folds over lists that rows return; leaves lists and options unbuildable, so `forEach` cannot collect |
| a `Decision.list` | a constructor of `Decision`: `decide`, `arms`, `binds`, the typing arm, a wire tag, a printer and a reader clause, the OCaml face | dearer, and still needs a term-level emptiness test for `iterate` |
| a primitive fold constructor | the constructor cascade (`docs/STATE.md`, item 5), a second recursion engine, a second set of loop laws | no: one engine, folds as theorems |

Typing the kit needs the atoms to be generic in the element type (`fst` and `getOrElse` already
are; `none` and `nil` answer `option never` and `list never`). Two details to settle when it is
built: whether nullary atoms are allowed (`strings` is variadic, so arity is already not fixed at
one or two), or whether `none`/`nil` are literals; and the prelude's spellings on the host
(`Option.none()`, `Option.some(x)`, `[]`, `[x, ...xs]`, and an `uncons` export).

Scout C (dispatched the same day) is asked to check this evaluation and price it against the
generators.

## 3b. The owner's question: proper tree types

"What about proper tree types? Those are quite accessible in Lean." They are, and the store
already has them. `src/Effect4/Store/Shape.lean`: `Shape.sum name cases` (named cases with a wire
tag and fields), `Shape.named name` (a reference into `ShapeDoc`'s table, which is how recursion is
written), and `acceptsAt defs : Val → Shape → Bool`. The generators emit a `Shape` and an `Image`
(value form `Val.ctor index args`) for every Lean inductive in the manifest, nested lists and
mutual families included. What has no recursion is `Ty`, the language's own type syntax, and
scout A found the matching hole on the value side: no atom or decision can see a `Val.ctor`.

So the affordable route is not structural recursive types inside `Ty` (what scout A priced as
"enormous": coinductive subtyping, `normalize`, `join`, `ofTy`), but ONE nominal constructor, as
`Ty.handle` already is nominal: `Ty.data name`, resolved against a `ShapeDoc` in the signature,
with membership by `acceptsAt`, introduction typed from a case's field shapes, and elimination as
one case analysis that is the shape functor's `out`. Then `.option`, `.tag` and the list
eliminator of §3 are three instances of one eliminator, a tagged cons list or a tree folds TYPED,
a Lean inductive an author declares becomes language data, and the authored reader layer over
`TypeScript.Expr` (scout A) stops being a raw program. Whether the five atoms of §3 are then
subsumed or sit beside it is scout C's to price (asked the same day).

## 4. What to rule

1. The sugar of §2 as authoring-only definitions in `Authoring/Loops.lean`, and its names.
2. The list and option kit of §3 as one slice (five atoms), with `reduce` and `forEach` as derived
   forms and the fold theorem as its law. It is language surface, so it belongs after the reader
   line (R4 to R6) unless the owner wants folds sooner.
