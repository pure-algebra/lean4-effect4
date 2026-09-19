# Seat T2 receipt — typing part 2: the relational view and the fold condition

Branch `seat/T2-typing-view`, worktree `.claude/worktrees/agent-aa4416f10d8eb45b1`, based at
`4b4e6aa3`. Items 0.6, 1.4a, 1.4, 1.5 of the tooling-first plan.

**Evidence key.** *Proved* = a Lean theorem that built. *Tested* = a `#guard`, a probe or a
mutation run that I executed and read. *Reproduced* = a number I re-measured from the tree.
*Stamped* = a generator emitted it and the drift check holds it. *Assumed* = nothing here is
assumed unless it says so.

## 0. The worktree was branched from the wrong commit

Read first because it affects the merge. The worktree arrived at `9187b9b6` (the tip of
`origin/main`, two README commits), not at `4b4e6aa3` as the brief says. Nothing of mine was at
risk — `9187b9b6` is reachable from `origin/main` and from the sibling worktree
`agent-a7b1392df4968558a` — so I created a **new** branch `seat/T2-typing-view` at `4b4e6aa3`
and left `worktree-agent-aa4416f10d8eb45b1` where it was. No history was rewritten and nothing
was reset.

I also copied `.lake/packages` and `.lake/build` from the main checkout, which sits at exactly
`4b4e6aa3`, instead of paying a cold build: the first narrow build replayed in 0.6 s. That is a
read of the main checkout, not a write to it.

## 1. The commits

| commit | what landed |
| --- | --- |
| `b7790888` | **0.6** `Ty.join_unknown`, `Ty.join_unknown_left`, `CTy.le_unknown`, `CTy.join_unknown`; the carrier rule in `Ty.lean`'s header; eleven guards in `Test/Program/TypeAlgebraContract.lean` |
| `1b46e5b8` | **1.4a** `tools/Tools/Variances.lean`, the hermetic family `variances` before `derived`, `tools/Effect4Gen/variances.json` |
| `f2a6aa71` | **1.4** `tools/Effect4Gen/View.lean`, manifest group `TyView`, the generated `src/Effect4/Laws/Program/TyView.lean`, `tools/Effect4Gen/guards/tyview.lean`, `Test/Program/TyViewContract.lean` |

(The table is completed as the remaining commits land; see §7 for what is not done.)

## 2. The two decisions I took, and why

### D1 — `join_unknown` by antisymmetry, not by `mem_normalizeRow`

The plan's route for 0.6 is "`join_unknown` via `mem_normalizeRow` + `sub_unknown`". I did not
take it. That route has to show that the normalised row of `(normalize t).members ++ [unknown]`
is exactly `[unknown]`, which needs `sub unknown x = true → x = unknown` at a member — and that
is a `cases x` over the whole alphabet, i.e. exactly the per-constructor enumeration this wave
exists to remove.

What landed instead is an antisymmetry between two normal types, and it names no constructor:

```lean
theorem join_unknown (t : Ty) : join t unknown = unknown :=
  OrderProof.sub_antisymm_normal sub_trans (join t unknown) unknown
    (normal_normalize (.union t unknown)) Normal.unknown
    (sub_unknown (join t unknown))
    (OrderProof.sub_normalize_union_right sub_trans t unknown)
```

`unknown` is above the join by `sub_unknown`, and below it because the join covers its right
operand. Both laws already existed. **Proved**, at `[propext, Quot.sound]`.

Consequence for placement: `join_unknown` needs `OrderProof`, which ends at
`TypeAlgebra.lean:806`, so it sits in the last `Effect4.Program.Ty` block beside `sub_join_left`
and `join_least` rather than beside `join_never` in the earlier block. `CTy.le_unknown` and
`CTy.join_unknown` are beside `CTy.never_le`, which is where the plan puts them.

### D2 — the generated view lives under the Laws, not under `Program`

The brief says `src/Effect4/Program/TyView.lean`. It is
`src/Effect4/Laws/Program/TyView.lean`, and the coordinator has accepted the change. The reason
is a hard constraint the brief did not state: **nothing under the core root `Effect4` imports
aesop**, which is what keeps the core's import closure — and the LCNF/OCaml pipeline cut from
it — free of proof search (`lakefile.toml`, the aesop require: "nothing under the core root
`Effect4` imports it, so the core's import closure … is unchanged"). Three of the view's laws
close with `aesop` and would not close without it inside the budget I had.

The view is proof-only: no runtime reader, no face, no emitter and no codec reads `Ty.args`, so
nothing in the core needs it. Two further benefits the coordinator named: `Ty.args` stays out of
the case-site policy, and out of the core's exhaustiveness inventory.

**Proposed decisions row** (I did not edit `docs/core/decisions.md`):

> **A generated view whose only consumers are proofs is emitted under `Laws`.** The core root's
> import closure is what the LCNF/OCaml pipeline is cut from, and nothing in it may import
> aesop; a generated file whose laws need proof search therefore lands under
> `src/Effect4/Laws/`, not beside the type it views. The test is consumers, not subject matter:
> `Ty.args`/`Ty.sameHead` are data about `Ty`, but no runtime reader, face, emitter or codec
> reads them, so they are Laws. A generated file under `Laws` is audited exactly like hand
> source — same axiom ceiling, same proof-shape rules — and stays out of the case-site policy
> and the core exhaustiveness inventory, which is the second reason to prefer the placement
> when it is available. (Seat T2, tooling plan 1.4.)

**Proposed decisions row** (the one the brief asked me to draft, on the wildcard/classifier
rule):

> **Wildcards in proofs, explicit negatives in classifiers.** A proof may close its case list
> with `| _ =>`: a constructor added later is absorbed, and absorption is what "a new
> constructor must never touch a proof" means. A *classifier* — a function whose answer decides
> whether a value is supported, encodable, printable, admitted or refused — may not: its
> default must be the **negative** class, with the positive arms listed explicitly, so a
> constructor added later defaults into refusal rather than into silent acceptance. DI-95 is
> the instance that named the rule (`Schema.Codec.isSupported` carried `| _ => true` and
> accepted four constructors nobody had implemented). The case-site policy
> (`tools/Conform/Lcnf/Cases.lean`, `make check-cases`) is the gate: every default is recorded
> with the class it absorbs, and a default that absorbs the positive class of a classifier is a
> policy row that must be signed. (Tooling plan 0.1/P2; drafted by seat T2.)

## 3. A1, and which branch I took

**Branch: the fallback — one lemma per congruence arm plus a dispatcher.** Not because the
single proof fails to close, but because it fails the axiom ceiling.

*Tested, both halves.*

1. The single generated proof **does** close over the whole square:
   ```lean
   fun_cases Ty.sub a b
   case case1 => rw [sameHead_refl _ ha, argsBelow_refl]; rfl
   all_goals aesop (add norm simp [isMember, litRule, topRule, sameHead, args, argsBelow,
     Variance.holds, Bool.and_assoc])
   ```
   builds, with `maxHeartbeats 4000000` and `maxRecDepth 100000`. The reason it is cheap is the
   splitter: `Ty.sub.induct` has **sixteen** cases, not 400, and the catch-all is one case
   carrying negative hypotheses (`#check Effect4.Program.Ty.sub.induct` — A2 confirmed; both
   `.induct` and `.induct_unfolding` derive).
2. That proof reaches **`Classical.choice`**, and the file is audited source under
   `src/Effect4/Laws` whose ceiling is `[propext, Quot.sound]` (`Test/Audit/AxiomGate.lean:68`).
   Bisected: `fun_cases` alone is clean (`[propext, Quot.sound]`), plain `aesop` is clean
   (`[propext]`), and the choice enters in the **catch-all case only** — where aesop must
   instantiate a negative hypothesis of the form `∀ a1 a2 b1 b2, a = a1.prod a2 → b = b1.prod b2
   → False` and falls back on classical reasoning to do it.

What landed instead, and why it is better than the plan's sketch of the fallback: **split on
`sameHead` first**. That makes the catch-all — the one case a square-of-constructors proof
cannot discharge without search — into `rfl`.

```lean
theorem sub_eq_false_of_not_sameHead … (hh : sameHead a b = false) : sub a b = false := by
  fun_cases Ty.sub a b
  case case1 => rw [sameHead_refl _ ha] at hh; exact Bool.noConfusion hh
  case case2 … case6 => exact Bool.noConfusion ha / hb / htop / hlit
  case case16 => rfl                      -- the arm IS `false`
  all_goals simp only [sameHead, Bool.true_eq_false] at hh

theorem sub_eq_argsBelow_of_sameHead … (hh : sameHead a b = true) : sub a b = argsBelow sub a b := by
  revert hh
  fun_cases Ty.sameHead a b               -- one case per ARM, not per pair
  …  case i => intro _; exact sub_args_<ctor> _ _ …
```

and `sub_eq_args` is the two of them under `cases hh : sameHead a b`. Nine generated arm lemmas
(`sub_args_option` … `sub_args_deferredOf`), each the idiom of `Ty.lean`'s `sub_*_of_ne` with
the reflexive case folded in so no caller has to carry an inequality.

**Every generated declaration is at `[propext, Quot.sound]`** (measured; `sameHead_refl`,
`sameHead_symm`, `sameHead_trans`, `args_congr`, `eq_of_sameHead`, `Variance.holds_trans`,
`Variance.holds_antisymm` are at `[propext]` alone).

Two corrections to the research note's statements, found by building them:

* `sameHead_refl (t : Ty) : sameHead t t = true` as the note states it is **false**: `union` is
  the head `sameHead` refuses, so `sameHead (union a b) (union a b) = false`. The law needs
  `isMember t = true`, which is what every caller has.
* `sameHead` must compare payloads with `decide (s = t)`, **not** `s == t`. At `String` and at
  `Nat` the `LawfulBEq` instance reaches `Classical.choice` (`beq_self_eq_true` at `String` is
  `[propext, Classical.choice, Quot.sound]`); `decide` through the derived `DecidableEq` reaches
  no axiom at all. This is what took the head lemmas from `Classical.choice` to `[propext]`.

## 4. The red controls, and how each was exercised

### 1.4a — the variance reader

Eleven controls, checked on **every run** of the driver and printed:
`Ref` inv, `Fiber` [co, co], `Layer` [contra, co, co], `Context` contra, `Deferred` [inv, inv],
`Cause` [co], `Effect` [co, co, co], `Queue` [inv, inv], `PubSub` [inv], and the two **inferred**
aliases `Exit` [co, co] and `Option` [co] — so a broken inference fails there and not silently.

Exercised in the failing direction by six in-memory mutations of the vendored text (the driver
reads through a `readModule` function, so the vendored tree is never touched — confirmed with
`git status -- vendor/`). Each was refused with its own message:

```
Ref loses `in`:            Ref.Ref reads [co] but rc.112 declares [inv]
Layer's ROut flips:        Layer.Layer reads [co, co, co] but rc.112 declares [contra, co, co]
Fiber's E flips:           Fiber.Fiber reads [co, contra] but rc.112 declares [co, co]
Context loses `in`:        Context.Context reads [none] but rc.112 declares [contra]
Success (Exit's) flips:    Exit's parameter A is passed at two positions of different variance: inv and co
Some (Option's) flips:     Option's parameter A is passed at two positions of different variance: co and inv
```

Thirteen hermetic `#guard`s in the module check the scanner on planted declaration lines. One of
them found a real bug: `=>` inside a parameter default (rc.112 spells its variance markers
`Covariant<A> = (_: never) => A`) naively closes the angle bracket, so the reader lost the rest
of the list. Fixed in `balancedAngle`/`splitTop`; the guard is `X<out A = (_: never) => void, in
out B>` reading `[co, inv]`.

Cross-check of the count, computed without sharing a line of code: the driver says 22 of 61
top-level declarations in the twelve modules carry `in`/`out`; an independent grep over the same
files says **22**. That is `decls-ck.ts:21-28`'s notion (`hasVariance`: some type parameter of
this declaration carries an `in` or an `out` modifier), which is the cross-check the plan asks
for.

### 1.4 — the generator

Three **shape refusals**, each exercised against a mutated copy of `variances.json` and each
naming the row (the driver takes `--variances <path>` so the real table is never touched):

```
A head with a recursive field and no row:
  View: `Ty.refOf` has 1 recursive field(s) and no row in tools/Effect4Gen/variances.json's
  `heads`; declare its variance from rc.112 (tools/Tools/Variances.lean) before generating the view
A variance list of the wrong length:
  View: `Ty.prod` has 2 recursive field(s) but tools/Effect4Gen/variances.json declares 3 variance(s) for it
A row naming no constructor:
  View: tools/Effect4Gen/variances.json declares a variance for `queueOf`, which is no constructor of `Ty`
```

The **semantic** check is emitted rather than performed in the generator, and is stronger for
it. The file carries one probe pair per position per head and one crossing probe per head of
arity two or more. Exercised by declaring `refOf` covariant: the emitted file fails twice, at
the probe and at the arm lemma's own proof —

```
error: Expression (lit "a").refOf.sub string.refOf did not evaluate to `true`
error: unsolved goals … ⊢ (x0.sub y0 && y0.sub x0) = x0.sub y0
```

— and since `scripts/generate.py --only derived` builds each emitted module after installing it,
a wrong table fails regeneration.

The brief's out-of-order fixture is `Test/Program/TyViewContract.lean` (imported by
`Test/All.lean`): two relations over one fixture carrier, `positional` and `crossed`. They
**agree** on every probe that uses the same atom at both positions — which is why the variance
probe alone is not enough — and the **crossing probe** (distinct atoms at every position) tells
them apart. That is the argument for emitting one per binary head, and the module restates the
five real crossing probes so they cannot be weakened silently.

## 5. Measured before/after

(Completed as the proof rewrites land; see §7.)

## 6. Facts worth carrying forward

* `Ty.sub.induct` and `Ty.sub.induct_unfolding` both derive (A2 **confirmed**), with sixteen
  cases and the catch-all as one case carrying negative hypotheses. `fun_cases Ty.sub a b` and
  `fun_cases Ty.sameHead a b` both work and are the two splits the view's proofs use. Nothing
  in `src/` used `fun_induction`/`fun_cases` over `Ty` before this branch.
* `Val.hasTy.alg`'s carrier is **`Ty × (Val → List String → Bool)`**, not
  `Val → List String → Bool`: `fold_of` builds a *paramorphism*, so `Val.hasTy.eq_cata` reads
  `Val.hasTy v ty allocated = (cata_ty Val.hasTy.alg ty).snd v allocated`. A5's "exact carrier
  read at the first build" — this is it, and `AdmitsSub`'s fields are stated over the `.2`
  component accordingly.
* `String.Pos` is indexed by its string in v4.33.1 and the raw byte offset moved to
  `String.Pos.Raw`; `String.trim` is deprecated and `String.trimAscii` answers a `String.Slice`.
  A text reader in this toolchain should scan `List Char`.
* `simp` at `(x == x) = true` for `String` or `Nat` pulls in `Classical.choice`; `decide (x = x)`
  through the derived `DecidableEq` pulls in nothing.
* `/-- doc -/ set_option … in theorem` does not parse; the `set_option … in` must come first.

## 7. What is not done

(Completed at the end of the run.)
