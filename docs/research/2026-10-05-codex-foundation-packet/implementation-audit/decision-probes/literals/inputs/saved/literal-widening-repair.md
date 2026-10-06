# Seat T5 scratch: the tested repair of number and boolean literals at `pair` and `tuple`

Not landed (coordinator's addendum 6, item 4). Kept for the owner's ruling.

## The repair

Two lines of `harness/truth/prelude-atoms.gen.ts`, which the atom table generates
(`src/Effect4/Machine/Term.lean`, `NativeAtom.row`, the `prelude` strings of `.pair` and `.tuple`).

Before:

    export const pair = <const A, const B>(a: A, b: B): readonly [A, B] => [a, b]
    export const tuple = <const A extends readonly unknown[]>(...items: A): A => items

After:

    type Wide<T> = T extends number ? number : T extends boolean ? boolean : T
    export const pair = <const A, const B>(a: A, b: B): readonly [Wide<A>, Wide<B>] => [a, b] as unknown as readonly [Wide<A>, Wide<B>]
    export const tuple = <const A extends readonly unknown[]>(...items: A): { readonly [I in keyof A]: Wide<A[I]> } => items as unknown as { readonly [I in keyof A]: Wide<A[I]> }

A string literal keeps its literal type, as DI-55 asks. A number or boolean literal widens, as
Lean's literal rule types it.

## What was tested (tsgo 7.0.0-dev.20260629.1, effect 4.0.0-rc.112, bun 1.4.2)

- `truth-scratch.py truth-corpus.json` with the three `--patch` arguments (the new `cons`, and the
  two lines above): `run-truth` passes on 42 programs, the rate limiter's request among them.
  tsgo reports three errors, all in `harness/truth/tuples.typecheck.ts`, lines 5 to 7: the pins
  `readonly [7]`, `readonly [7, "x"]` and `readonly [7, "x", true]`.
- The eight printed Queue steps and the request, each compiled alone at the cell's printed type:
  all accepted. Without the repair, the probe's first take attempt, the real take step and the
  request are refused.

## How to repeat

`truth-scratch.py` (this folder) copies the lane into a temporary directory beside the harness,
patches the copied atom prelude, runs the modules on the pin and type-checks them. The step
texts are `skOffer.txt`, `skTryTake.txt`, `skRetryTake.txt`, `skWithdraw.txt`, `takeStep.txt`,
`offerStep.txt`, `withdrawTake.txt`, `withdrawOffer.txt` and `text-request.txt` in this folder.
