# The codec generator's proofs for large recursive sums (second look)

Status: logged for a second look (owner, 2026-10-18: "log it for a second look later, it's likely
unoptimized"). History, not authority. Found while generating the Tool codec group in seams S3b.

## The one thing to know first

The generator's recursive template did not scale to `Program.EffName`: its round-trip proof timed
out in `whnf` even at four times the default budget. A budget raise treated the symptom and was
reverted. One `rfl` equation per reader arm fixes it (below); making that the default is open.

## What was observed

- `Live.View` reaches `EffName` through one field, `WaitView.registration : Option EffName`
  (`src/Effect4/Run/View.lean`).
- `EffName` has 57 constructors and refers to itself (`withWaiter (base : EffName)`). `Machine.Name`
  also refers to itself. So the generator emits the recursive template: one structural reader
  `raw…` over `Val`, with one `.ctor n [v0, …]` arm per constructor.
- Each arm of the generated `ofVal_toVal` runs `simp only [toVal…, raw…, Canonical.ofVal_toVal]`.
- The one-field arm `cont` times out at 800,000 heartbeats, in `whnf`, inside `simp`.
- The plain (non-recursive) template handles `Machine.SyncOp` (31 constructors) at 400,000. Its
  rule raises the budget only past 32 constructors (`emitPlain`, `tools/Effect4Gen/Main.lean`).
- The recursive template handles `Program.Eff` (29 constructors) at the default budget.

## The likely cause

`simp only [raw…]` needs the reader's equation lemmas. Lean builds them on first use, by splitting
a 57-arm match whose patterns are natural-number literals and list lengths, inside a structural
recursion over the nested inductive `Val`. That construction grows faster than linearly in the arm
count. The budget is not the constraint.

## Candidate fixes, to measure

1. Decode in two stages: `.ctor tag fields => arm tag fields`, with `arm` a match on the tag alone
   and each arm a small match on its field list. The equation lemmas then stay small.
2. Prove each arm without the equation lemmas: rewrite the inner `Canonical.ofVal_toVal` facts,
   then close by definitional unfolding (`show` and `rfl`), which needs no splitter.
3. Emit the equation lemmas once, eagerly, at the reader's definition, and measure whether that
   alone fixes the cost.

Each candidate must keep today's bytes for every existing group: `generate.py --only derived`
refuses a diff.

## What landed (owner's choice, 2026-10-18: fix the generator now)

Measurements first. On the cut file, `rfl` unfolds the reader at one constructor cheaply, and
`toVal`'s equation lemma builds cheaply. `simp only [raw…]` is what times out. So the cost is
the reader's equation lemmas, which Lean builds by splitting the whole match.

The generator gains an opt-in flag, `--arm-lemmas` (`tools/Effect4Gen/Main.lean`):

- `emitArmLemma` states each reader arm as its own equation, proved by `rfl`. The round-trip
  proof rewrites with these instead of the reader's equation lemmas.
- A zero-argument arm closes by `rfl`.
- A plain sum takes the recursive item's exactness: `guarded toVal ofVal` with `guarded_exact`,
  so no proof splits the whole match.

Result: the Tool group through `Live.View` (6,697 lines, `EffName` and `SyncOp` included)
compiles in 6.3 seconds at the default budget, with no `maxHeartbeats` option.

## The second look that remains

- Whether `--arm-lemmas` becomes the default for every group. That changes the bytes of every
  existing group and rebuilds their dependents, so it waits for a measured comparison.
- The plain template's budget rule (past 32 arms) may then go: `TypeReason` (34 arms) is its
  one known user.

## What this does not establish

- The cause is measured on the cut file; the general claim for other groups is not.
- It says nothing about the store, the native codecs or the TypeScript printer.
