# Proof engineering and metaprogramming: making the language widen for free (2026-09-18)

A research seat's note, written against the working tree at `refactor/phase1-phase3` on the
evening of 2026-09-18. Rows 42/43 steps 1 and 2 are committed (`7db30c8a`, `02e7d4f0`); L1 of the
language push is committed (`61afe78f`); and while I was writing, the main session began L5 —
`Ty.unknown`, a twentieth constructor — which is uncommitted in the working tree as I finish. That
diff turned out to be the best evidence in the note, so §0.2 reads it.

## 0. What this note is, and what its evidence is worth

The question: **why does adding a constructor still cost hand proof edits, and what instrument
removes each cost?** The owner's rule is "build the instrument the second time a chore appears";
the chore has now appeared three times in one night, named in the plan itself, and a fourth time
in the diff sitting in the working tree while I write (§0.2):

> The three `TypeAlgebra` proofs that enumerate handle arms (`sub_trans_core`,
> `sub_antisymm_normal`, `sub_normalize_of_sub`) each gained the invariant alternatives — the
> same chore three times, so a `sub` induction principle that hides the arm shapes is owed to
> the bank.
> — `docs/research/2026-09-18-rows-42-43-plan.md` §2b, correction 3

**Evidence key.** Every claim about this tree or about the toolchain is *read* from the file and
line I cite; I opened each one. Nothing in this note is **proved**, **tested**, **reproduced** or
**stamped** — this seat may not run `lake`, and one Lean compiler at a time is a project rule the
main session holds. Every design claim (that a sketch compiles, that a proof closes, that a
generated script works) is **assumed** until a narrow build tests it. Where I think a sketch is
likely to need repair I say so in its own words rather than hiding it in a risk list. Where a
received belief in the notes is wrong, I say that too (§6 corrects one).

Read for this note: the three briefed research notes; `src/Effect4/Laws/Auto/{Positions,
PositionGate,TypedStateGen,TypedSources,Census,Inversion,Traversals}.lean`;
`src/Effect4/Program/{Ty,Typed,NativeAtom,FoldOf,Fold}.lean`; `src/Effect4/Machine/{Term,
Stores}.lean`; `src/Effect4/Laws/Program/{TypeAlgebra,Template,Progress,MeaningSound}.lean`;
`src/Effect4/Laws/Program/Typed/{Vocabulary,Sources,State}.lean`;
`src/Effect4/Laws/Program/Authoring/Tactic.lean`; `src/Effect4/Laws/Codegen/Read.lean`;
`Test/Audit/{AxiomGate,PositionCensus,TraversalCensus}.lean`; the aesop frontend
(`.lake/packages/aesop/Aesop/Frontend/*`, `Aesop/RuleSet/Name.lean`, `Aesop/Options/Public.lean`);
`.lake/packages/batteries/Batteries/Util/ProofWanted.lean`; and in the pinned toolchain
`~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/` the files cited inline.

### 0.1 The bill, measured

| chore | where | size today |
| --- | --- | --- |
| `sub`'s congruence arms, three times | `Laws/Program/TypeAlgebra.lean:32-40`, `:514-526`, and `sub_normalize_of_sub` (`:749`, `:825`) | four `first` alternatives each, one per *shape* of constructor (one covariant child, two covariant, one invariant, two invariant) |
| `hasTy_sub` | `src/Effect4/Program/Typed.lean:144-399` | 256 lines; 18 copies of a six-line `union` block and 16 copies of a four-line `first` mismatch block (§0.2 measures the sixteen arriving tonight) |
| the `_of_ne` inversions of `sub` | `src/Effect4/Program/Ty.lean:779-808` | seven lemmas, each the same two-line script; `refOf`/`deferredOf` never got theirs, which is why step 1 inlined their shapes into the three proofs |
| `step_typed` | `Laws/Program/Progress.lean:176-403` | 228 lines, 24 arms; ten of them byte-identical but for one `exact` |
| `syncOpOf_validIn` | `Laws/Program/Progress.lean:434-489` | constructor **lists** in the patterns (`| refGet \| refUpdate _ \| …`), which a new row must edit |
| the non-straight case of `sound` | `Laws/Program/MeaningSound.lean:642-647` | a 12-constructor list that a new non-straight constructor must edit |
| `Ty.closed`, `Ty.isNever`, `Ty.isMember`, `NativeAtom.typeOf`'s fallback, `NativeAtom.constGeneric`, `mono` | `Ty.lean:186-191`, `:176-180`, `:389-394`, `NativeAtom.lean:93-96`, `:29-32`, `:37-47` | grouped alternation lists; a new constructor edits each — and tonight's diff edited all three `Ty` ones |

Against that, the instruments that already work and should be the model:

| instrument | where | what it buys |
| --- | --- | --- |
| `fold_of` | `src/Effect4/Program/FoldOf.lean` (876 lines) | a hand traversal becomes an algebra + `eq_cata`, at `[propext]`, no hand proof |
| decided table facts | `Laws/Codegen/Read.lean:78-89` — `theorem table_linear : table.all rowLinear = true := by decide` and `table_fact` to instantiate at a row | the reader's exactness proof "has no case per constructor" (`Read.lean:8`) |
| the twelve template laws | `Laws/Program/Template.lean:25-105` | one `aesop` call each |
| the position census + totality gate | `Laws/Auto/Positions.lean`, `PositionGate.lean` | a new state field fails the build until it is sourced |
| the goal-directed dispatcher | `Laws/Program/Authoring/Tactic.lean:19-49` | `authoring_scoped`: read the goal head, apply the lemma named after it, `repeat'` |

The gap between the two tables is the subject of this note. In one sentence: **the tree has
learned to generate *functions* from a signature and to decide *table facts*, and has not yet
learned to generate the *relational* vocabulary — the children of a node with their variance,
and the arm lemmas of a relation over them.** That, plus one unused compiler feature (§1.1),
is most of the bill.

### 0.2 The chore, measured live while this note was being written

Between my first read of the tree and my last, the main session appended a twentieth constructor
to `Ty` — `Ty.unknown`, decisions row 46, L5 of the language push — and it is in the working tree,
uncommitted, as I write. So the bill in §0.1 is not an estimate from an old commit; it is a diff I
can read. The snapshot below is `git diff --numstat -- src/` taken at the end of my reading — the
main session is still editing, so the totals moved by a line or two between my two measurements;
the **distribution** is the point and it did not move:

| file | +/− | what changed |
| --- | --- | --- |
| `src/Effect4/Program/Typed.lean` | **+61 / −15** | `hasTy_sub` gained **16 new `first` blocks**, each the same three lines: `first \| exact absurd rfl hbu \| (revert hsub; unfold Ty.sub; …)` — one per mismatch arm |
| `src/Effect4/Laws/Program/TypeAlgebra.lean` | **+5 / −1** | `sub_trans_core` gained *two lines* (`by_cases hcu : c = .unknown`); `sub_normalize_of_sub` two more; `hasTy_normalize` one case name in a grouped `induction … with` |
| `src/Effect4/Program/Ty.lean` | +25 / −3 | the constructor and its nine readers, each one line |
| `src/Effect4/Program/Fold.lean` | +22 / −0 | generated: the `TyAlgebra` field, the `cata_ty` arm, the `TyHom` equation |
| `src/Effect4/Laws/Program/Typing/HasTy.lean` | +14 / −10 | the checker's typing rules |
| `src/Effect4/Program/Checker.lean` | +10 / −5 | the checker |
| thirteen more | +31 / −13 | faces, goldens, the schema bridge, the blame printer, the OCaml alphabet |
| **total** | **+168 / −47** over 19 files | one constructor |

Read those first two rows together, because they are the whole argument of this note:

- **`sub_trans_core` paid two lines.** Its structure dispatches on `isMember` *before* it looks at
  constructors, so a new *exceptional rule* (`sub t .unknown = true`) slots in once at the top:
  `by_cases hcu : c = .unknown; · subst hcu; exact sub_unknown a`.
- **`hasTy_sub` paid sixty-one.** Its structure is `cases a` and then `cases b` inside every arm, so
  the new rule has to be re-excluded in **every one of the sixteen mismatch arms**, and because the
  arm cannot tell "b is the top" from "b is a genuine mismatch" it now tries both with a `first`.

The tree's own rule is that new proofs use no `first`. This diff adds sixteen. Not through
carelessness — through the *shape* of the proof, which decides the cost of a constructor before
anyone writes the constructor. That is the sentence the rest of this note tries to act on.

And it **builds**: the session's own build log for this slice reports zero errors and
`Build completed successfully`. So nothing here is a claim about correctness; it is a claim about
**cost**, which is the only thing at issue. Sixty-one lines that a `rfl` would have covered, plus
the secondary churn the linter then reports (`linter.unusedSimpArgs` on the grouped `simp only`
lists whose arguments the new arm made redundant) — paid once per constructor, in four proofs,
forever.

For the record, `sub` now has **five** exceptional rules and nine congruence arms
(`src/Effect4/Program/Ty.lean`, `def sub`):

```lean
  if a = b then true
  else match a, b with
  | .never, _ => true
  | .union a1 a2, b => sub a1 b && sub a2 b
  | a, .union b1 b2 => sub a b1 || sub a b2
  -- the top (decisions row 46): every type is below `unknown`
  | _, .unknown => true
  | .lit _, .string => true
  | …nine congruence arms…
  | _, _ => false
```

so the view of §1.2 needs a fourth guard — `topRule a b`, alongside `litRule a b` — and the
exceptional rules it leaves hand-stated become five. Five design rules, nine mechanical ones: that
ratio is the case for the split, and it got *better* tonight, not worse, because the new rule is a
design rule.

Two proof-shape counts for the ratchet of §3.1, taken now: bare `first` lines in `src/` are **32**
(15 under `src/Effect4/Laws/`, 16 of the other 17 added by tonight's diff), inline `first |`
occurrences **94**, `simp_all` **118** in `src/` and **94** under Laws, `try` **282** in `src/` and
**250** under Laws.

---

## 1. Proofs that never see constructors

The question asks which of three routes is best for stating reflexivity, transitivity,
antisymmetry, monotonicity and preservation **once** for a relation given by a case table over
`Ty`: a custom induction principle, a generic structural-relation framework, or generated
per-constructor lemmas fed to aesop. The honest answer is that these are three *layers*, not
three options, and that the tree is missing the cheapest one entirely.

### 1.1 Layer 0 — the compiler already derives the induction principle, and nothing uses it

`Ty.sub` is defined by well-founded recursion (`src/Effect4/Program/Ty.lean:423-444`, with
`termination_by sizeOf a + sizeOf b` at `:444`). For any such definition Lean 4.33.1 derives a
**functional induction principle** whose cases are the definition's *own* arms with the induction
hypotheses for exactly its recursive calls:

```
The `fun_induction` tactic is a convenience wrapper around the `induction` tactic to use the
functional induction principle. … `fun_induction f x₁ ... xₙ y₁ ... yₘ` … is equivalent to
`induction y₁, ... yₘ using f.induct_unfolding x₁ ... xₙ`
```
— `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/Init/Tactics.lean:1049-1079`
(implementation: `Lean/Meta/Tactic/FunInd.lean:795` `deriveUnaryInduction`, `:1101`
`deriveInductionStructural`; `fun_cases` at `Init/Tactics.lean:1081-1110`).

Three properties of this make it the right first move, and all three are read from the source:

1. **The case list is the definition's, so it is regenerated with the definition.** Adding
   `Ty.refOf` adds one arm to `sub` and therefore one case to `Ty.sub.induct_unfolding`. No hand
   artefact records the arm list.
2. **The catch-all stays one case.** The match compiler builds a *splitter* for overlapping
   patterns, giving the fall-through alternative negative hypotheses rather than enumerating the
   complement: `mkNotAlt` and `mkSplitterHyps` in `Lean/Meta/Match/Match.lean:151-180`, with the
   overlap map in `Lean/Meta/Match/MatcherInfo.lean:22-35` (`Overlaps`). So `sub`'s final
   `| _, _ => false` does not explode into 19×19 − 13 cases; it is one case carrying "not any
   earlier pattern". This is the single fact that makes the approach practical, and it is the
   fact I would want tested first.
3. **`if a = b then true else …` becomes a hypothesis, not a case split I write.** `sub`'s
   leading guard is part of its case tree, so each case arrives with `a = b` or `a ≠ b` in hand —
   which is exactly the `by_cases heq : a = b` that opens all three `TypeAlgebra` proofs
   (`:11-12`, `:503-504`) and `hasTy_sub` (`Typed.lean:150`) — and it is where tonight's top rule
   landed in `sub_trans_core` (`:14-15`), for free, because the case tree already had the split.

So the shape of a relational law becomes:

```lean
private theorem sub_trans_core (a b c : Ty) (hab : sub a b = true) (hbc : sub b c = true) :
    sub a c = true := by
  fun_induction Ty.sub a b generalizing c <;>
    aesop (rule_sets := [Effect4.TyOrder])
```

I do not claim that closes today — the bank does not exist yet, and `generalizing c` with a
three-way recursion is the part I expect to need work (see 1.4). What I do claim, from the
source, is that **the arm enumeration disappears from the proof text**, and that is the property
the owner asked for.

`fun_induction` is available for `Val.hasTy` (`src/Effect4/Program/Typed.lean:34-104`,
structural in `ty`), for `Ty.normalize` (`Ty.lean:549-573`), for `Ty.instantiate`
(`:458-482`), for `Ty.infer` (`:484-499`) and for `Ty.sub`. **Nothing in `src/` uses it**: a
grep for `fun_induction` and `fun_cases` over `src/` finds nothing. That is the cheapest
unexploited lever in the tree.

Cost and risk, stated plainly. Deriving `Ty.sub.induct_unfolding` for a 14-arm well-founded
definition is real work for the elaborator, done once and then cached in the `.olean` of the
module that first asked for it (realization results are added to the environment and replayed —
`Lean/Environment.lean:2709` `realizeConst`, `Lean/Meta/Basic.lean:2694`). If the derivation is
slow, the fix is to ask for it in one small module early in the Laws import order rather than in
a hot one. If the splitter's negative hypotheses turn out to be unwieldy (they are stated as
`∀ …, a = pattern → … → False`), the `aesop` bank needs `Ty.noConfusion`-style normalisation to
discharge them, and that is exactly what `norm simp` rules on constructor disequality already do
(`Laws/Auto/Inversion.lean:63-73`). Second risk: `tactic.fun_induction.unfolding` defaults to
`true` (`Init/Tactics.lean:1074`), which unfolds the call in the goal — usually what you want for
`sub`, and wrong when the goal must keep `sub a b` folded; the option is per-proof.

### 1.2 Layer 1 — the generated relational view: children with variance

`fun_induction` gives *the same* case list as the definition, which is right for a law about
`sub` alone. It does not help a law that relates **two** functions — `hasTy` respecting `sub`,
`normalize` respecting `sub` — because the two case trees do not align. For those, the missing
vocabulary is the node's children *with the variance the relation reads them at*. This is the
relator of the datatype's signature functor, and in the literature it is exactly what makes such
proofs generic (§5.3).

A new generated group (`tools/Effect4Gen/`, group `TyView`, out `src/Effect4/Program/TyView.lean`,
in `HERMETIC_GROUPS` with `check-gen` drift) emits:

```lean
-- GENERATED by tools/Effect4Gen/View.lean; do not edit

/-- How a relation reads a recursive argument: as rc.112 declares the parameter
(`Fiber<out A, out E>` covariant, `Ref<in out A>` invariant; decisions row 55). -/
inductive Variance | co | contra | inv
  deriving DecidableEq, Repr

/-- A Boolean relation lifted through a variance. -/
def Variance.holds (r : Ty → Ty → Bool) : Variance → Ty → Ty → Bool
  | .co,     x, y => r x y
  | .contra, x, y => r y x
  | .inv,    x, y => r x y && r y x

/-- The immediate `Ty` children of a type, each with the variance the order reads it at. -/
def Ty.args : Ty → List (Variance × Ty)
  | .never | .unknown | .unit | .nat | .int | .string | .bool
  | .handle _ | .lit _ | .var _                     => []
  | .option t | .list t | .causeOf t                => [(.co, t)]
  | .refOf t                                        => [(.inv, t)]
  | .prod a b | .except a b | .exitOf a b
  | .fiberOf a b | .union a b                       => [(.co, a), (.co, b)]
  | .deferredOf a b                                 => [(.inv, a), (.inv, b)]

/-- Same constructor and equal non-recursive payload. `union` answers `false`: the order
treats it by distribution and choice, not by congruence (an exception declared in the
generator's input, beside the variances). -/
def Ty.sameHead : Ty → Ty → Bool
  | .never, .never | .unknown, .unknown
  | .unit, .unit | .nat, .nat | .int, .int
  | .string, .string | .bool, .bool                        => true
  | .handle s, .handle t                                    => s == t
  | .lit s, .lit t                                          => s == t
  | .var i, .var j                                          => i == j
  | .option _, .option _ | .list _, .list _
  | .causeOf _, .causeOf _ | .refOf _, .refOf _             => true
  | .prod _ _, .prod _ _ | .except _ _, .except _ _
  | .exitOf _ _, .exitOf _ _ | .fiberOf _ _, .fiberOf _ _
  | .deferredOf _ _, .deferredOf _ _                        => true
  | _, _                                                    => false

/-- The two rules between union members that are not congruences (`Ty.lean`, `def sub`):
the literal rule, and the top added tonight for decisions row 46. -/
def Ty.litRule : Ty → Ty → Bool
  | .lit _, .string => true
  | _, _            => false

def Ty.topRule : Ty → Ty → Bool
  | _, .unknown => true
  | _, _        => false
```

and, in the same generated file, the five laws the proofs need. The first is the whole point:

```lean
/-- **`sub` between union members is the variance-wise comparison of corresponding arguments.**
Everything a relational proof needs to know about `Ty`'s constructors, in one statement. -/
theorem Ty.sub_eq_args (a b : Ty) (ha : isMember a = true) (hb : isMember b = true)
    (hlit : litRule a b = false) (htop : topRule a b = false) :
    sub a b =
      (sameHead a b &&
        (a.args.zip b.args).all fun p => p.1.1.holds sub p.1.2 p.2.2) := by
  cases a <;> cases b <;>
    simp only [isMember, litRule, topRule, sameHead, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, Bool.false_and,
      Bool.and_false] at ha hb hlit ⊢ <;>
    ⋯   -- the generated residue: `sub`'s own unfold plus `sub_refl` on the equal cases

theorem Ty.sameHead_refl (t : Ty) : sameHead t t = true
theorem Ty.sameHead_trans {a b c : Ty} : sameHead a b = true → sameHead b c = true → sameHead a c = true
theorem Ty.sameHead_symm {a b : Ty} : sameHead a b = true → sameHead b a = true
/-- Corresponding arguments correspond: same length, same variances. -/
theorem Ty.args_congr {a b : Ty} (h : sameHead a b = true) :
    a.args.length = b.args.length ∧ a.args.map Prod.fst = b.args.map Prod.fst
/-- A child is smaller: the termination measure of every relational law. -/
theorem Ty.sizeOf_args {t : Ty} {v : Variance} {x : Ty} (h : (v, x) ∈ t.args) : sizeOf x < sizeOf t
/-- A node is its head and its children. -/
theorem Ty.eq_of_sameHead {a b : Ty} (h : sameHead a b = true)
    (hx : a.args.map Prod.snd = b.args.map Prod.snd) : a = b
```

I checked `sub_eq_args` against every pair of `Ty`'s 20 constructors by hand while reading
`Ty.lean:414-432`. The cases that could have broken it and do not:

- **equal types.** `sub t t = true` by the leading guard; the right side is `true` too, because
  `sameHead t t = true` and `Variance.holds sub v x x = true` for each variance by
  `sub_refl` (`Ty.lean:733`). So the law needs **no `a ≠ b` hypothesis** — a simplification over
  every existing `_of_ne` inversion, which all carry one.
- **`.handle s` vs `.handle t`, `s ≠ t`; `.lit s` vs `.lit t`; `.var i` vs `.var j`.**
  `sameHead` compares the payload, so the right side is `false`; `sub` reaches
  `| _, _ => false`. Agreed.
- **`.deferredOf`'s bracketing.** `sub`'s arm is
  `sub a1 a2 && sub a2 a1 && sub e1 e2 && sub e2 e1` (left-nested); the view gives
  `(sub a1 a2 && sub a2 a1) && ((sub e1 e2 && sub e2 e1) && true)`. `&&` associates, so the
  generated proof needs `Bool.and_assoc` in its `simp only` list. Named because it is the kind of
  detail that makes a first build red.
- **`.except (error value)` vs `.exitOf (value error)`.** The view is positional and `sub`'s arms
  are positional in the same order (`Ty.lean:424-425`), so the two agree without a per-constructor
  permutation. If a future constructor's `sub` arm compared arguments out of order the generator
  would have to carry a permutation; today none does, and the generator should *refuse* rather
  than guess (see the red control below).
- **`.never`, `.union` on either side, `.lit` vs `.string`, anything vs `.unknown`.** Excluded by
  `ha`, `hb`, `hlit`, `htop`. Those five rules stay hand-stated, in the four lemmas that already exist: `sub_never_core`
  (`TypeAlgebra.lean:5-7`), `sub_union_left` and `sub_union_right` (`Ty.lean:737-756`),
  `sub_lit_string`, and the top rule `sub_unknown` added tonight. Five exceptional rules, nine
  congruence arms: the view removes the
  nine and leaves the four, which is the right split because the four are *design*, not boilerplate.

The generator's input is the inductive plus one hand line per relation — the variance of each
recursive argument and the exceptional constructor pairs. That is the same shape as
`Positions.defaultCarriers`/`stops`/`defaultWrappers` (`Laws/Auto/Positions.lean:32-41`): a small,
declared design list, not a transcription of the type.

### 1.3 `sub_trans_core` under the recommendation

Today (`Laws/Program/TypeAlgebra.lean:10-72`): 63 lines, five nested `by_cases`, a
`cases a <;> cases b` with `try contradiction`, a nested `cases c`, and a `first` with four
alternatives whose shapes are the constructor shapes. Under the recommendation:

```lean
/-- Absorption and the canonical order use the same structural transitivity proof. -/
private theorem sub_trans_core (a b c : Ty) (hab : sub a b = true) (hbc : sub b c = true) :
    sub a c = true := by
  -- the four exceptional rules first, each by its own hand lemma; unchanged from today
  by_cases hna : isMember a = true
  case neg => -- a is `never` or a union
    exact sub_of_not_member_left hna hab hbc            -- one hand lemma, today's `:64-70`
  by_cases hnb : isMember b = true
  case neg => exact sub_of_not_member_mid hna hnb hab hbc   -- today's `:51-63`
  by_cases hnc : isMember c = true
  case neg => exact sub_of_not_member_right hnb hnc hab hbc -- today's `:39-50`
  by_cases hl : litRule a b = true ∨ litRule b c = true
  case pos => exact sub_of_litRule hl hab hbc          -- `.lit s ≤ .string`, both ways
  -- the congruence case: one arm, no constructor named
  rw [Ty.sub_eq_args a b hna hnb (by simpa using hl.imp_left ..)] at hab
  rw [Ty.sub_eq_args b c hnb hnc (by simpa using hl.imp_right ..)] at hbc
  rw [Ty.sub_eq_args a c hna hnc (litRule_trans_false hl ..)]
  exact args_trans (fun x y z hx hz hxy hyz =>
      sub_trans_core x y z hxy hyz) hab hbc
termination_by sizeOf a + sizeOf b + sizeOf c
decreasing_by exact Nat.add_lt_add_three (Ty.sizeOf_args ..) (Ty.sizeOf_args ..) (Ty.sizeOf_args ..)
```

with `args_trans` a *generic* lemma in the hand bank, proved once from `sameHead_trans`,
`args_congr` and `Variance.holds_trans`:

```lean
/-- The variance-wise comparison composes, given composition below it. -/
theorem Ty.args_trans {r : Ty → Ty → Bool}
    (htrans : ∀ x y z, sizeOf x + sizeOf y + sizeOf z < n → r x y = true → r y z = true → r x z = true)
    {a b c : Ty}
    (hab : (sameHead a b && (a.args.zip b.args).all fun p => p.1.1.holds r p.1.2 p.2.2) = true)
    (hbc : (sameHead b c && (b.args.zip c.args).all fun p => p.1.1.holds r p.1.2 p.2.2) = true) :
    (sameHead a c && (a.args.zip c.args).all fun p => p.1.1.holds r p.1.2 p.2.2) = true

/-- Three lines, once: composition at each variance. -/
theorem Variance.holds_trans {r : Ty → Ty → Bool} (v : Variance)
    (htrans : ∀ x y z, r x y = true → r y z = true → r x z = true) {x y z : Ty} :
    v.holds r x y = true → v.holds r y z = true → v.holds r x z = true := by
  cases v <;> aesop
```

**Adding a constructor.** `Ty.args` and `Ty.sameHead` gain an arm; the generator regenerates the
file including `sub_eq_args`'s proof; `make gen-hermetic` + `check-gen` stamps it. The three hand
proofs — `sub_trans_core`, `sub_antisymm_normal`, `sub_normalize_of_sub` — and
`Variance.holds_trans` and `args_trans` are **not touched**. That is "zero proof edits", and the
place the edits moved to is generated code, which is the tree's established answer (the fold is
"the drift killer", `docs/research/2026-09-10-program-as-schema.md` per the memory index).

The catch, stated: the generator must be *told* the new constructor's variance. It cannot read it
off rc.112. So the true cost of a new parametrised constructor is **one line of declared
variance**, and if you get it wrong the variance is wrong everywhere at once — which is better
than today (step 1 got it wrong in `sub` alone and step 2 had to correct it in three proofs;
`rows-42-43-plan.md` §2b correction 3).

### 1.4 What the view does *not* fix, and the second framework it needs

`hasTy_sub` (`src/Effect4/Program/Typed.lean:143-357`) is not a law about `sub` alone: it says
`Val.hasTy` is monotone along `sub`. The view removes the boilerplate — 17 copies of the
`union` block and 15 mismatch blocks, about 150 of its 214 lines — because the case analysis
becomes `a = b` / `a` not a member / `b` not a member / literal rule / congruence. It does not
remove the congruence case, which must say what `hasTy` does at each constructor.

The right instrument for that is **a condition on the algebra**, and it is available because
`Val.hasTy` is *already a fold*: `fold_of Effect4.Program.Val.hasTy` is in
`src/Effect4/Program/Folds/Ty.lean:34`, so `Val.hasTy.alg : TyAlgebra (fun _ => Val → List String → Bool)`
and `Val.hasTy.eq_cata` exist, at `[propext]` with no hand proof. So:

```lean
/-- Pointwise order on an admission carrier. -/
def Adm := Val → List String → Bool
def Adm.le (p q : Adm) : Prop := ∀ v al, p v al = true → q v al = true

/-- GENERATED (one field per constructor, from the same variance input as `Ty.args`):
what an admission algebra must satisfy for its fold to respect `sub`. -/
structure AdmitsSub (alg : TyAlgebra (fun _ => Adm)) : Prop where
  /-- the empty union admits nothing -/
  never       : ∀ v al, alg.ty_never v al = false
  /-- a union is the disjunction of its members -/
  union       : ∀ p q v al, alg.ty_union p q v al = (p v al || q v al)
  /-- the literal rule -/
  lit_string  : ∀ s, Adm.le (alg.ty_lit s) alg.ty_string
  -- covariant arms: monotone
  option      : ∀ p q, Adm.le p q → Adm.le (alg.ty_option p) (alg.ty_option q)
  list        : ∀ p q, Adm.le p q → Adm.le (alg.ty_list p) (alg.ty_list q)
  causeOf     : ∀ p q, Adm.le p q → Adm.le (alg.ty_causeOf p) (alg.ty_causeOf q)
  prod        : ∀ p q p' q', Adm.le p q → Adm.le p' q' → Adm.le (alg.ty_prod p p') (alg.ty_prod q q')
  except      : ∀ p q p' q', Adm.le p q → Adm.le p' q' → Adm.le (alg.ty_except p p') (alg.ty_except q q')
  exitOf      : ∀ p q p' q', Adm.le p q → Adm.le p' q' → Adm.le (alg.ty_exitOf p p') (alg.ty_exitOf q q')
  fiberOf     : ∀ p q p' q', Adm.le p q → Adm.le p' q' → Adm.le (alg.ty_fiberOf p p') (alg.ty_fiberOf q q')
  -- invariant arms: the arm IGNORES its argument. This is DI-17 / decisions row 44
  -- ("a handle is coarse by kind; the world's tables type what it holds") stated as a law.
  refOf       : ∀ p q, alg.ty_refOf p = alg.ty_refOf q
  deferredOf  : ∀ p q p' q', alg.ty_deferredOf p p' = alg.ty_deferredOf q q'
  -- leaves: nothing to say
  var         : ∀ v al, alg.ty_var 0 v al = false   -- a template parameter has no inhabitant
  -- the top, added tonight with `Ty.unknown` (decisions row 46): one field, not sixteen arms
  top         : ∀ v al, alg.ty_unknown v al = true

/-- **Proved once, in the bank:** the fold of an admission algebra respects `sub`. -/
theorem cata_admits_sub {alg : TyAlgebra (fun _ => Adm)} (h : AdmitsSub alg)
    {a b : Ty} (hsub : sub a b = true) : Adm.le (cata_ty alg a) (cata_ty alg b)

/-- And `hasTy_sub` is an application. -/
theorem hasTy_sub (a b : Ty) (v : Val) (allocated : List String := [])
    (hsub : Ty.sub a b = true) (hv : Val.hasTy v a allocated = true) :
    Val.hasTy v b allocated = true := by
  simpa only [Val.hasTy.eq_cata] using
    cata_admits_sub Val.hasTy_admitsSub hsub v allocated (by simpa [Val.hasTy.eq_cata] using hv)
```

`Val.hasTy_admitsSub` is a 14-field instance, each field one to four lines (`option` is
`fun p q h v al => by cases v <;> simp_all` and so on; the two handle fields are `rfl`, because
the arms really do ignore their arguments — `Typed.lean:59-68` — and `top` is `rfl`, because
`Val.hasTy v .unknown = true` by definition, `Typed.lean:95`). Tonight's sixteen `first` blocks
are that one `rfl`. **Adding a constructor** adds one
generated field to `AdmitsSub` and one hand line to the instance, at a place the compiler names
("structure instance missing field `queueOf`"). That is the honest cost: not zero, but one line
in one place instead of twelve lines in each of four proofs, and the compiler is the checklist.

The same `AdmitsSub`-shaped condition serves `hasTy_normalize` (`TypeAlgebra.lean:183`),
`hasTy_mono` (`Laws/Program/Typed.lean:278`), `causeAdmits_congr_at` (`TypeAlgebra.lean:157`), and — this is
the point for the push — `Val.hasTyWith (oracle)` of L2 (`rows-42-43-plan.md` §2b, "Step 4"),
where `hasTy := hasTyWith coarse` and `hasTyIn W := hasTyWith W.oracle` must be **monotone in the
oracle**. Under the algebra formulation that is one more generic theorem
(`cata_admits_sub` is monotone in `alg` pointwise), not a re-proof of the three laws. The plan
already says "the existing laws generalise once and the current ones are instances"; this is the
mechanism that makes that true.

### 1.5 Layer 2 — generated per-constructor arm lemmas, for aesop

The seven `_of_ne` inversions at `Ty.lean:758-787` are seven copies of

```lean
theorem sub_option_of_ne (a b : Ty) (hne : option a ≠ option b) :
    sub (option a) (option b) = sub a b := by
  conv => lhs; unfold sub
  simp only [hne, ↓reduceIte]
```

`refOf` and `deferredOf` never got theirs, which is *why* step 1 inlined their shapes into three
proofs. A command `#relation_arms Ty.sub` in `Laws/Auto/` generates one per congruence arm, by
reading the matcher of `sub` (§3.1 has the mechanism) and emitting the same two-line script; the
bank registers them as `norm simp` in `Effect4.TyOrder`. This is the cheapest of the three layers
to build and the least valuable of the three, because `sub_eq_args` subsumes it. **Recommendation:
skip it** unless `sub_eq_args` turns out not to close. It is listed because it is the fallback if
the view's law fights the elaborator.

### 1.6 Custom eliminators: what I would and would not register

`@[induction_eliminator]` and `@[cases_eliminator]` exist in this toolchain
(`Lean/Meta/Tactic/ElimInfo.lean:216-222` and `:253-261`), and — the useful part — the eliminator
is keyed on the **array** of targets:

```lean
def getCustomEliminator? (targets : Array Expr) (induction : Bool) : MetaM (Option Name) := do
  let mut key := #[]
  for target in targets do … key := key.push declName
  return customEliminatorExt.getState (← getEnv) |>.map.find? (induction, key)
```
— `Lean/Meta/Tactic/ElimInfo.lean:270-278`

so a **binary** eliminator for `(Ty, Ty)` can be registered and `induction a, b` will pick it up
(`Lean/Elab/Tactic/Induction.lean:829-832`). And registering it is *safe against existing proofs*,
which I checked: the custom eliminator is consulted only when no `using` clause is given, and
without one a two-target `induction` currently **fails** —

```lean
  if optElimId.isNone then
    if tactic.customEliminators.get (← getOptions) then
      if let some elimName ← getCustomEliminator? targets induction then …
    unless targets.size == 1 do
      throwMissingEliminator
```
— `Lean/Elab/Tactic/Induction.lean:827-833`

— so registering a `(Ty, Ty)` eliminator can only turn an error into a success. No existing proof
changes behaviour.

Despite that, **I recommend not registering one.** `Ty.sub.induct_unfolding` (§1.1) is the same
thing, derived by the compiler, regenerated with the definition, and named after the function it
follows; a hand-written `Ty.subInduct` would be a second artefact recording the arm list — the
chore this note exists to remove. Register a custom eliminator only where the compiler cannot
derive one: `Ty.Normal` (`Ty.lean:565-585`), whose `normal_children` (`TypeAlgebra.lean:455-475`)
is a per-constructor `match` in the *statement* and a constructor-list `induction … with` in the
proof. Under the view that becomes one statement —

```lean
theorem normal_args (t : Ty) (h : Normal t) : ∀ p ∈ t.args, Normal p.2
```

— and the `Normal` inductive itself should gain a generated `args`-shaped constructor set or, more
cheaply, a generated `Normal.args` lemma per constructor in the `Effect4.TyOrder` bank. I did not
work this one through; it is the one place in §1 where I am guessing rather than reading.

### 1.7 Cost and risk for §1

Build order and sizes, assumed: (a) `fun_induction` probe on one existing proof — an afternoon,
and it either works or tells you the splitter is the problem; (b) the `TyView` generator —
about 250 lines of emitter beside `tools/Effect4Gen/Fold.lean`'s 1385, reusing `ctorFields`
(`tools/Effect4Gen/Main.lean:174-190`) and the group mechanism; (c) `AdmitsSub` and
`cata_admits_sub` — one hand module of perhaps 150 lines, of which `cata_admits_sub` is the only
real proof; (d) rewriting the four laws against it.

What could go wrong, in the order I think it will:

1. **`sub_eq_args`'s generated proof does not close.** 400 pairs, a `List.zip`/`List.all`
   normalisation on each. The mitigation is that the generator can emit **one lemma per
   congruence arm plus a dispatcher** instead of one 400-case script, trading elegance for
   robustness; the arm lemmas are §1.5, so the fallback is already designed.
2. **`args_trans` needs the size bound threaded.** Transitivity's measure is a triple while the
   view's `sizeOf_args` is unary; the plumbing is `Nat` arithmetic and `omega`, and today's proof
   already carries exactly this (`TypeAlgebra.lean:568-575`, `decreasing_by`). Expect an hour of
   fighting, not a design change.
3. **`hasTy_sub`'s statement changes shape.** It currently takes `allocated : List String := []`
   with a default value; `cata_admits_sub` returns `Adm.le`, so callers get the arguments in a
   different order. There are eleven call sites (`grep hasTy_sub src/`), all in Laws. Cheap, but
   it is a real edit to eleven places — and it is a *one-time* edit, which is the trade.
4. **The variance input becomes a second source of truth about rc.112.** It must cite
   `vendor/effect-4.0.0-rc.112/src/Ref.ts:59` and `Deferred.ts:58` as decisions row 55 does, and
   the citation gate (`make check-citations`) should cover it.

**Red control** for the view: a fixture inductive with a constructor whose `sub` arm compares its
arguments out of order (say `| .swapped a b, .swapped c d => sub b c && sub a d`) must make the
generator **refuse**, not emit a wrong `args`. The generator must verify its own output — read the
relation's arm for each constructor and check it is the variance-wise comparison of corresponding
positions — and `throwError` otherwise. Without that check the view is a lie that type-checks.

---

## 2. Aesop banks

### 2.1 Where the tree is now: one unnamed global bank

There is **no** `declare_aesop_rule_sets` anywhere in `src/`, `Test/` or `tools/`. Every
registration in the tree goes into aesop's **`default`** rule set, which is enabled for every
`aesop` call in the tree and in anything that imports it:

| registration | where | what it puts in `default` |
| --- | --- | --- |
| generic `Except`/`Option`/`Bool`/`ite` inversions | `Laws/Auto/Inversion.lean:125-132` | 23 `norm simp` rules |
| the reader's leaf exactness | `Laws/Codegen/Read.lean:287-288` | 5 `safe forward` rules |
| the **checker's own definitions** | `Laws/Program/Typing/CheckInversion.lean:39-42` | `check`, `checkStmt`, `checkStmts`, `checkEffs`, `checkAction`, `checkLayer`, `checkLayers`, `StmtTy.fold`, `GenTy.mergeT`, `GenTy.joinAnswerT`, `EffTy.joinAnswer_eq`, `GenTy.merge_eq` as `norm simp` |
| the generated typed-state skeleton | `Laws/Program/Typed/State.lean:142-170` | 16 `safe constructors`, ~40 `safe forward` accessors, 6 `norm unfold` |

That is roughly 90 global rules, of which the third row is the dangerous one: putting the
*checker's recursive definitions* in the default `norm simp` set means every one of the tree's
**~210 `aesop` tactic invocations** (a grep for tactic-position occurrences in `src/`; 461 lines
mention the word, most of them docstrings and attribute lines) tries to
unfold `check` during normalisation. `Laws/Auto/Inversion.lean:15` states the intent for its own
rules — "so they act inside Aesop and leave every existing `simp` call alone" — which is right for
23 generic `Except` lemmas and wrong for a mutually recursive checker.

This is the answer to "where would the 400-case `infer_closed` not work": it works
(`Laws/Program/Template.lean:50-51`) because `Template.lean` is imported early and the default
bank it sees is small. The same call placed after `CheckInversion` would carry the checker's
unfolding rules into all 400 branches. **The bank is not a cost you pay once; it is a cost every
later call pays.** Naming the banks is what makes that cost local.

### 2.2 The banks to declare, and the exact syntax for this aesop

Pinned aesop is `3448c0bcc5ce01b2d1546e483ec3620e32df3d0e` ("chore: bump toolchain to v4.33.0",
2026-08-10), per `lake-manifest.json` and `.lake/packages/aesop/.git`. Its frontend:

```lean
-- .lake/packages/aesop/Aesop/Frontend/Command.lean:21-23
syntax (name := declareRuleSets)
  "declare_aesop_rule_sets " "[" ident,+,? "]"
  (" (" &"default" " := " Aesop.bool_lit ")")? : command
```

so the declarations are, verbatim:

```lean
/-- Banks that must stay on for every call, because existing proofs depend on them. -/
declare_aesop_rule_sets [Effect4.Inversion] (default := true)

/-- Banks a proof asks for by name. -/
declare_aesop_rule_sets [Effect4.TyOrder, Effect4.TypedState, Effect4.Rows, Effect4.Atoms,
  Effect4.Reader, Effect4.Checker]
```

and the registrations (`Aesop/Frontend/Attribute.lean:20-25` for the attribute;
`Aesop/Frontend/RuleExpr.lean:259` for `ruleSetsFeature`; `:78-107` for the phases `safe`/`norm`/
`unsafe` and the builders `apply`/`simp`/`unfold`/`tactic`/`constructors`/`forward`/`destruct`/
`cases`/`default`):

```lean
attribute [aesop norm simp (rule_sets := [Effect4.Inversion])] bind_eq_ok map_eq_ok …
attribute [aesop safe constructors (rule_sets := [Effect4.TypedState])] RSavedOk
attribute [aesop safe forward (rule_sets := [Effect4.TypedState])] RSavedOk.c0 RSavedOk.c1 RSavedOk.c2
attribute [aesop norm unfold (rule_sets := [Effect4.TypedState])] TaskOk
@[aesop safe apply (rule_sets := [Effect4.TyOrder])] theorem foo … := …
add_aesop_rules safe forward (rule_sets := [Effect4.TyOrder]) [Ty.sub_eq_args, Ty.args_congr]
erase_aesop_rules [Effect4.TyOrder (safe) Ty.sub_eq_args]
```

and the call sites (`Aesop/Frontend/Tactic.lean:24-32`, where `ruleSetSpec := "-"? ident` lets a
call *drop* a set):

```lean
theorem … := by aesop (rule_sets := [Effect4.TyOrder])
theorem … := by aesop (rule_sets := [Effect4.Rows, -default])   -- only this bank + builtin
theorem … := by aesop (config := { terminal := true, maxRuleApplications := 400 })
```

The reserved names are `default`, `builtin` and `local`
(`.lake/packages/aesop/Aesop/RuleSet/Name.lean:17-27`); `default` and `builtin` are both enabled
by default (`Aesop/Frontend/Extension.lean:56-57`), so `-default` still leaves `builtin`.

### 2.3 What goes in each bank

| bank | contents | default? | why separate |
| --- | --- | --- | --- |
| `Effect4.Inversion` | today's 23 generic `Except`/`Option`/`Bool`/`ite` `norm simp` rules (`Laws/Auto/Inversion.lean:125-132`) | **yes** | every existing `aesop` call relies on them; naming them costs nothing and lets a hot proof drop them |
| `Effect4.TyOrder` | the generated view (`Ty.args`, `sameHead`, `litRule`) as `norm simp`; `sub_eq_args`, `args_congr`, `sameHead_*`, `sizeOf_args` as `safe forward`; `Variance.holds` as `norm unfold`; `AdmitsSub` accessors as `safe forward` | no | the `Ty` laws are one module family; nothing else wants `sub` unfolded |
| `Effect4.TypedState` | the generated `Ok` structures: `safe constructors`, accessors `safe forward`, sum-typed `Ok`s `norm unfold` — moved out of `default` (`Typed/State.lean:142-170`) | no | R4 of the metaprogramming review already asks for this; ~56 rules that nothing outside the invariant wants |
| `Effect4.Rows` | `syncOpStep_*` arm equations, `refStep*`, `refPeek`/`refPoke` lemmas, the decided row facts (§4) | no | only `Progress` and the store laws |
| `Effect4.Atoms` | per-atom `eval`/`typeOf` equations, `Val` frame inversions, `Lit.toVal_*` | no | only the term-typing laws |
| `Effect4.Reader` | the five `readLeaf_exact` forward rules (`Laws/Codegen/Read.lean:287`) and the table facts | no | only the codegen laws |
| `Effect4.Checker` | the checker's definitions as `norm unfold` (**not** `norm simp`), from `CheckInversion.lean:39-42` | no | the one registration that must come out of `default` first |

### 2.4 Keeping a bank from exploding

Four failure modes, each with a rule the tree can state. The numbers are aesop's own defaults,
read from `.lake/packages/aesop/Aesop/Options/Public.lean:41-145`: `maxRuleApplicationDepth := 30`,
`maxRuleApplications := 200`, `maxGoals := 0` (unlimited), `maxNormIterations := 100`,
`useSimpAll := true`, `useDefaultSimpSet := true`, `terminal := false`,
`warnOnNonterminal := true`.

1. **A rule that creates metavariables.** `sub_trans` as `safe apply` would ask aesop to guess the
   middle type; `hasTy_sub` would ask it to guess two. Aesop's README asks for these per call, and
   `Laws/Auto/Inversion.lean:8-14` already records the policy ("a rule that creates
   metavariables, such as a transitivity, per call only, as it advises"). **Rule: a bank contains
   no lemma with a hypothesis-only variable in its conclusion.** This is mechanically checkable —
   `forallMetaTelescope` the type, and refuse if the conclusion leaves any metavariable
   unassigned — and belongs in a `#bank_check <RuleSet>` command.
2. **`norm unfold` on a recursive definition.** `maxNormIterations := 100` is per goal; a mutual
   checker unfolding into itself burns it and **fails the whole call** rather than backing off.
   **Rule: a recursive definition enters a bank as `norm unfold` only with its own equation
   lemmas beside it, and never as `norm simp`.**
3. **`safe forward` rules that fire on every hypothesis.** The typed-state bank's ~40 accessors are
   forward rules; with a goal carrying eight `Ok` hypotheses that is 320 saturation attempts per
   goal before any search. Aesop's forward index keys on the hypothesis type so most are cheap,
   but the invariant's accessors all have the shape `P.<pred> w e x.<field>`, which indexes
   poorly. **Rule: the frame lemmas are proof *terms*, generated, not aesop goals** (§3.3) — which
   removes the largest consumer of that bank and is a better answer than tuning it.
4. **`useDefaultSimpSet := true`** means every `aesop` also carries Lean's global `@[simp]` set.
   That is usually wanted and is the reason a bank looks cheaper than it is. For a measured proof,
   `aesop (simp_config := { … })` and `(rule_sets := [X, -default])` isolate it.

### 2.5 Measuring, and pinning the measurement

Aesop has the instrument built in (`Aesop/Options/Public.lean:198-209`):

```lean
set_option aesop.collectStats true
#aesop_stats                       -- per-rule elapsed and success/failure counts, sorted
set_option aesop.stats.file "generated/aesop-stats.jsonl"   -- one JSON record per invocation
```

with the report at `Aesop/Stats/Report.lean:36-124` (total time, successful vs failed, per-rule
`elapsedSuccessful`/`elapsedFailed` at `Aesop/Stats/Basic.lean:125-165`). Two uses:

- **A per-module time pin that may only go down.** `make check-aesop` builds the Laws modules with
  `aesop.stats.file` set, reads the JSONL, and compares total elapsed per module against a pinned
  number in `generated/aesop-budget.tsv`; over budget fails, under budget prints "re-pin". This is
  the tree's existing count-pin idiom applied to time, and it satisfies the incrementality rule
  (memory: "gates must be incremental") because the numbers come from a build that had to happen.
- **Coverage, not time: `#auto_census`.** `Laws/Auto/Census.lean:70-103` already re-proves every
  theorem of a module from its statement under a heartbeat cap, in a rolled-back environment
  (`attempt`, `:52-68`), and reports the ones the tactic closes with their source line count and
  the axioms of the found proof. So `#auto_census Effect4.Laws.Program.TypeAlgebra using aesop
  (rule_sets := [Effect4.TyOrder])` answers "what does the new bank buy" **before** any proof is
  rewritten. That is the right first use of the bank: measure, then delete.

The one flaw in `#auto_census` for this purpose: it runs the tactic on the statement with the
whole module's environment available, guarded only by `usesWhatFollows` (`Census.lean:44-51`),
which checks declaration *lines* within the module. A rule set defined in a later module is
therefore visible to it, and a "closed" verdict can be optimistic about import order. Worth a
line in its docstring.

### 2.6 Cost and risk for §2

Declaring the sets is an hour. Moving the four existing registrations is mechanical but **is a
behaviour change for every `aesop` invocation in the Laws tree (~210)**, so it must be one commit
per bank with a narrow build,
and — per the seat rule already in memory ("announce aesop rule-set changes to in-flight seats")
— announced. The order that minimises risk: declare all seven sets first (no behaviour change);
move `Effect4.Checker` out of `default` and fix the fallout (the largest single win, and the
proofs that break tell you exactly which ones depended on a global unfold); then `Effect4.Reader`;
then `Effect4.TypedState` (its consumers are not written yet, so it is free today and expensive in
a month — do it now); leave `Effect4.Inversion` as `(default := true)` indefinitely.

One gate consequence I checked and could not fully settle. `declare_aesop_rule_sets` expands to

```lean
    elabCommand $ ← `(meta initialize ($(quote rsNames).forM $ declareRuleSetUnchecked (isDefault := $(quote dflt))))
```
— `.lake/packages/aesop/Aesop/Frontend/Command.lean:31`

and the binder-free `initialize` elaborates to `@[no_expose, init] private meta def initFn :
IO Unit := do …` (`Lean/Elab/Declaration.lean:366`), which is a safe `def` with a body, not a
bodiless `opaque`, so the trust gate's declaration pass does **not** refuse it
(`Test/Audit/AxiomGate.lean:614-625`), and `initialize` is not in `forbiddenTrustTokens`
(`:242-244`). What it will do is reach `Classical.choice` through `registerSimpAttr`
(`Aesop/Frontend/Extension.lean:27-31`), so the module that declares the sets needs one entry in
`auditImplementationModules` (`AxiomGate.lean:91-108`) — and the gate's staleness check
(`:658-666`) refuses an entry that does *not* reach `Classical.choice`, so the entry cannot be
added speculatively. **Assumed**, not tested: put the declarations in one new module
`src/Effect4/Laws/Auto/RuleSets.lean`, build, and let the gate say which of the two it is.

**Red control** for a bank: for each bank, one theorem in the Laws tree that closes *only* with
it, and a fixture that runs the same statement with `(rule_sets := [-<Bank>])` and must fail.
Without that, a bank that has quietly stopped mattering keeps being paid for.

---

## 3. The instruments owed now

All four live beside the three that exist, in `src/Effect4/Laws/Auto/`, and all four obey the
three standing constraints: **fuel-bounded recursion** (as `Positions.walkType` does at
`Laws/Auto/Positions.lean:89-93`, with a loud `REFUSED` on exhaustion, and `writeSites` at
`:228-231`), **tables read by `whnf` and `Expr` decoding, never evaluated** (as
`TypedSources.decodeRows` does at `:64-80`), and **no `initialize`** (§6).

### 3.1 `#exhaustive_gate` — which matches break when a constructor is added

The brief asks for a command listing every definition and theorem whose match becomes
non-exhaustive after a constructor is added. A command cannot know what you are about to add, but
it can decide the equivalent and more useful question: **which matches on `T` have no catch-all
alternative, and so will break?** That question is exactly decidable from the matcher's own type,
because the match compiler builds each alternative's type as `∀ fields, motive <patterns>`:

```lean
  mkMinorType (xs : Array Expr) (lhs : AltLHS) (notAltHs : Array Expr): MetaM Expr :=
    withExistingLocalDecls lhs.fvarDecls do
      let args ← lhs.patterns.toArray.mapM (Pattern.toExpr · (annotate := true))
      let minorType := mkAppN motive args
      …
      mkForallFVars xs minorType
```
— `Lean/Meta/Match/Match.lean:165-172`

so the pattern of alternative `i` at discriminant `d` is literally the `d`-th argument of `motive`
in that alternative's body, and the alternative is a **catch-all at `d`** exactly when that
argument is a bound variable rather than a constructor application. A field-less alternative
carries an artificial `Unit` binder (`mkSimpleThunkType`, `Lean/Expr.lean:684`), which
`MatcherInfo.altNumParams` already counts (`Lean/Meta/Match/MatcherInfo.lean:104-107`), so the
telescope length is given, not guessed.

```lean
open Lean Meta Elab Command
namespace Effect4.Laws.Auto.Exhaustive

/-- Is alternative `i` of `matcher` a catch-all at discriminant `d`? Read from the matcher's
own type: the alternative's body is `motive p₁ … pₙ`, and a `pᵈ` that is a bound variable
catches every constructor, present and future. -/
def altIsCatchAll (matcher : Name) (info : Match.MatcherInfo) (i d : Nat) : MetaM Bool := do
  let cinfo ← getConstInfo matcher
  forallBoundedTelescope cinfo.type (info.getFirstAltPos + i + 1) fun xs _ => do
    let altTy ← inferType xs.back!
    forallBoundedTelescope altTy info.altNumParams[i]! fun _ body => do
      let pats := (← whnf body).getAppArgs
      let some p := pats[d]? | return false
      return p.consumeMData.isFVar

structure Row where
  holder : Name
  mod : Name
  matcher : Name
  discr : Nat
  alts : Nat
  catchAll : Bool

/-- Every matcher application in `e` whose discriminant `d` has type headed by `target`,
with whether it has a catch-all there. Fuel-bounded, as the position census's walks are. -/
def matchesOn (target : Name) (holder mod : Name) :
    Nat → Expr → Array Row → MetaM (Array Row)
  | 0, _, acc => do
    logWarning m!"REFUSED {holder}: the term walk ran out of depth"
    return acc
  | fuel + 1, e, acc => do
    let mut acc := acc
    if let some app ← matchMatcherApp? e (alsoCasesOn := true) then
      for h : d in [:app.discrs.size] do
        let dty ← whnf (← inferType app.discrs[d])
        if dty.getAppFn.constName? == some target then
          let info := app.toMatcherInfo
          let mut catchAll := false
          for i in [:info.numAlts] do
            if ← altIsCatchAll app.matcherName info i d then catchAll := true
          acc := acc.push { holder, mod, matcher := app.matcherName, discr := d,
                            alts := info.numAlts, catchAll }
    match e with
    | .app f a => matchesOn target holder mod fuel a (← matchesOn target holder mod fuel f acc)
    | .lam _ t b _ | .forallE _ t b _ =>
      matchesOn target holder mod fuel b (← matchesOn target holder mod fuel t acc)
    | .letE _ t v b _ =>
      matchesOn target holder mod fuel b
        (← matchesOn target holder mod fuel v (← matchesOn target holder mod fuel t acc))
    | .mdata _ b | .proj _ _ b => matchesOn target holder mod fuel b acc
    | _ => return acc

syntax (name := exhaustiveGate) "#exhaustive_gate " ident (" under " ident)? : command
```

The elaborator scans `Traversals.definitionsUnder env scope` (`Laws/Auto/Traversals.lean:151-167`,
which already filters matchers, recursors and compiler helpers) plus the theorems, and reports
`tsv` rows sorted by module, then fails on a **definition** row with `catchAll = false`.

**It must not fail on a theorem row**, and this is the limit I want stated rather than papered
over. `cases t <;> …` in a proof compiles to `Ty.casesOn`, which has one alternative per
constructor and no catch-all by construction; the *tactic* that was written may well be
`<;> aesop`, which handles a new constructor fine, but the proof **term** cannot tell you that:
the tactic script leaves no residue in it. Likewise a `first | … | …` alternative list — the
thing this note is about — is invisible in the term. So:

- for **definitions**, `#exhaustive_gate` is exact and should be a hard gate. It flags today, from
  what I read: `Ty.closed` (`Ty.lean:177-182`), `Ty.isMember` (`:380-385`),
  `NativeAtom.constGeneric` (`NativeAtom.lean:29-32`), `NativeAtom.mono` (`:37-47`),
  `NativeAtom.typeOf`'s fallback group (`:93-96`), and `Val.hasTy`'s type dispatch
  (`Typed.lean:34-103`) — and for every one of those, **flagging is the desired behaviour**: a new
  constructor *should* make them fail to compile, because each needs a decision. The gate's value
  for definitions is not the refusal, it is the **inventory**: a `make`-readable list of exactly
  what a constructor addition costs, printed before you start.
- for **proofs**, the exact instrument is at the syntax level, and the tree already owns the
  machinery: `Test/Audit/AxiomGate.lean:392-465` tokenizes every audited source with Lean's own
  tokenizer, skipping comments, doc comments and string literals. Extending it with a second,
  *counted* list — `first`, `simp_all`, `try` — gives a **monotone budget** rather than a refusal:
  the count per module is pinned in `generated/proof-shape.tsv` and may only decrease. Today's
  numbers over `src/Effect4/Laws/`: 94 `simp_all`, 15 bare `first`, 250 `try`. A hard refusal
  would be a lie (the estate has 94 of them); a ratchet is honest and moves.

**Fuel, and the gate's own axioms.** The walk is explicitly fuel-bounded rather than using core's
`forEachExpr` (`Lean/Meta/ForEachExpr.lean:75-80`), which is a `partial def` — not refused (the
token gate reads *our* source, the declaration pass reads *our* declarations), but the in-house
pattern is what the other three censuses use and there is no reason to differ. The module joins
`auditImplementationModules` (`AxiomGate.lean:91-108`) like the four before it.

**Red control.** `test/fixtures/exhaustive-gate/no-catch-all.lean.txt`: a definition matching all
20 `Ty` constructors with no wildcard must appear in the report with `catchAll = false`; the same
definition with a final `| _ => …` must not. And one negative control: a definition matching on
`Term`, not `Ty`, must not appear at all.

### 3.2 `theorem_wanted` as the obligation ledger

R2 of the metaprogramming review plans the ledger as Batteries' `theorem_wanted`, matched to
witnesses by `isDefEq` under `forallMetaTelescope`. Both halves check out, with two corrections.

**What `theorem_wanted` actually is.** In pinned Batteries (`4488d40d…` = `v4.33.0`),
`theorem_wanted name binders : T` elaborates to a *private placeholder* `def` carrying a wrapper
type:

```
Each elaborates to a private placeholder `def name binders : ProofWanted T := ⟨⟩` (resp.
`DefWanted T`), so the wanted result is visible to downstream files and tools by type rather than
by side-channel.
```
— `.lake/packages/batteries/Batteries/Util/ProofWanted.lean:17-21`, with
`public structure ProofWanted (α : Sort u) : Type where mk ::` at `:62-65` and the command's
config `{ cmdName := "theorem_wanted", wrapper := ``ProofWanted, requireProp := true }` at `:149`

so it is a real `def` with a real body: no `axiom`, no `sorry`, nothing the trust gate refuses,
and `collectAxioms` on it sees only the axioms of `T`'s own constants. Good.

**Correction 1: build the placeholder as a declaration, not through the command.** The census
computes the obligation as an `Expr`; `theorem_wanted` takes syntax. Round-tripping through the
delaborator is where a generator like this goes to die (the string emitter it replaces had to set
`pp.fullNames` and undo line wrapping — `TypedStateGen.oneLine`, `:42-47`). Since the command's
whole output is one `def`, emit it directly:

```lean
/-- Record `stmt` as an open obligation. Exactly what `theorem_wanted` produces, from an `Expr`. -/
def addWanted (name : Name) (stmt : Expr) : MetaM Unit := do
  let u ← getLevel stmt                      -- `stmt : Prop`, so `u = 0`
  let ty  := mkApp  (mkConst ``ProofWanted [u]) stmt
  let val := mkApp  (mkConst ``ProofWanted.mk [u]) stmt
  addDecl <| .defnDecl { name, levelParams := [], type := ty, value := val,
                         hints := .abbrev, safety := .safe }
```

**Correction 2: `isDefEq` is the wrong join, and `#auto_census` is the right one.** A witness
proved with *weaker* hypotheses — the normal case for a good lemma — is not definitionally equal
to the template. `isDefEq` under `withNewMCtxDepth` (`Lean/Meta/Basic.lean:1752` for
`forallMetaTelescope`, `:1999` for `withNewMCtxDepth`) answers "same statement", not "this
witnesses that". The join the tree wants is "the template follows from the witness", and
`Laws/Auto/Census.lean:52-68` already implements it, rolled back, heartbeat-capped, with the
axioms of the found proof reported:

```lean
def attempt (type : Expr) (tac : Syntax) (cap : Nat) (modIdx : ModuleIdx) (first : Nat) :
    TermElabM (Option (Array Name)) :=
  withoutModifyingState do
    tryCatchRuntimeEx (withOptions (fun o => maxHeartbeats.set o cap) <| withCurrHeartbeats do
      let goal ← mkFreshExprMVar type
      let rest ← Tactic.run goal.mvarId! (Tactic.evalTactic tac)
      unless rest.isEmpty do return none
      …)
```

So the ledger's join is: for each obligation, `attempt template (← `(tactic| intros; exact?%
$(witness) <;> assumption)) …`. Cheap, honest, already tested machinery, and it reports the
axioms — so a witness that sneaks past the ceiling is caught at the join rather than at the gate.

**The ledger as a whole.**

```lean
syntax (name := obligations) "#typed_state_obligations " ident+ : command
```

for each `(definition, matcher arm, owner, written typed fields)` from the write census with arm
attribution (`matchMatcherApp?` gives the arms; `Positions.writeSites` gives the sites —
`Laws/Auto/Positions.lean:228-262` — and the two are joined by asking, per site, which
alternative's body contains it): build the template from the definition's type by
`forallMetaTelescope`, look for a witness by `attempt`, and if there is none, `addWanted`. Then
print `wanted / proved / total` and fail on:

- an obligation with no witness **and** no `ProofWanted` placeholder (someone deleted the
  placeholder without proving it);
- a `ProofWanted` placeholder that is no longer an obligation (staleness — the same check
  `PositionGate` already makes for source rows, `Laws/Auto/PositionGate.lean:54,70-71`);
- the wanted count above its pin.

Finding the placeholders needs no environment extension and no naming convention: they are
**the constants whose type's head is `ProofWanted`**, which one pass over `env.constants` finds
(they are `private`, so mangled, and `privateToUserName?` recovers the name — the gate already
does exactly this at `AxiomGate.lean:279-296`). This is the answer to §6 in miniature: *the type
is the tag*.

**Cost and risk.** The arm attribution is the new work: `Positions.writeSites` walks the whole body
and does not record which `match` alternative a site sits in. The fix is one extra parameter — when
the walk descends into `app.alts[i]`, push `(matcher, i)` onto a path — and it is about 30 lines.
Risk: structural recursion compiles bodies into auxiliaries (`popR` writes nothing, `popR._f`
writes 17 sites — `2026-09-18-position-census-design.md` appendix), so an arm of the *source* is
an arm of the *auxiliary*, and the obligation's name must be built from the auxiliary. That is
already how the design names things ("its unit is the *definition*, not the arm" — §2C of that
note), and R3 of the review moves to arms; the two must be reconciled before the emitter is
written, or the ledger's row names will churn. I would keep the definition as the unit and record
the arm as *data on the row* rather than in the name.

**Red control.** A fixture with (i) a `ProofWanted` whose statement nothing proves — must count as
open; (ii) a theorem that proves something *else* of the same shape — must **not** be accepted as
the witness; (iii) a `ProofWanted` for a definition that no longer exists — must fail as stale.

### 3.3 Frame lemmas: generate the proof term, not an aesop goal

R4 plans one `theorem frame_<Owner>_<fields>` per (owner, written-field set), "proved by `aesop
(rule_sets := [TypedState])`". The proof does not need a search. For a structure owner, the
generated `Ok` is a `structure … : Prop` with one field per clause
(`Laws/Program/Typed/State.lean:42-46` for `RSavedOk`, `:55-61` for `RunFiberOk`), and a structure
update `{x with frame := f}` elaborates to `RunFiber.mk x.id f x.pending …`, whose projections
reduce: `({x with frame := f}).pending` is `x.pending` by `rfl`. So the frame lemma is an
anonymous constructor whose components are the old accessors and the new hypotheses, and the
generator knows every one of them:

```lean
/-- GENERATED: `RunFiberOk` survives a write to `frame` and `pending`. -/
theorem frame_RunFiber_frame_pending {W : Type} (P : Preds W) (w : W) (e : Expect)
    (x : RunFiber …) (h : RunFiberOk P w e x)
    (f : RSaved) (hf : RSavedOk P w (.fiber x.id) f)
    (p : List (Pending …)) (hp : P.PendingOk w e p) :
    RunFiberOk P w e { x with frame := f, pending := p } :=
  ⟨hf, hp, h.c2, h.c3, h.c4, h.c5⟩
```

Deterministic, instant, no bank, no `maxRuleApplications`. **Recommendation: amend R4** — the
aesop rule set stays for the *witness* proofs (R5), where the search is doing real work; the frame
lemmas are terms.

Two subtleties the generator must handle, and the second is a genuine trap:

1. **A sum-typed owner** (`TaskOk`, `FinNameOk`, `CmdOk` — `State.lean:48-52`, `:68-78`) is a `def`
   by `match`, not a structure, so there is no accessor to reuse; its frame lemma is
   `by cases x <;> exact …`, or simply omitted (a sum is rebuilt, not updated).
2. **A clause that mentions another field.** `RunFiberOk.c0` is
   `RSavedOk P w (.fiber (x.id)) x.frame` (`State.lean:56`): the *expectation* reads `x.id`. A
   write to `id` therefore invalidates `c0` even though `c0` is about `frame`. So the generator
   must compute, per clause, the set of `x.<field>` it mentions, and promote any clause whose set
   meets the written set from "framed" to "obligation". This is read off the clause `Expr` with
   `Positions.readSites` (`Laws/Auto/Positions.lean:265-290`), which already finds projections in
   both spellings. If the generator skips this, it emits **false** frame lemmas that do not
   type-check — so the failure is loud, which is the one comfort.

**Red control.** A fixture owner with two fields where field 1's clause reads field 2: the
generator must emit an obligation for field 1 when field 2 is written, and a frame when it is not.

### 3.4 `#atom_table_check` — what `decide` can and cannot do

The tree's proven instrument for a table is the decided fact plus the row projection:

```lean
theorem table_linear : table.all rowLinear = true := by decide
theorem table_fact {check : Templates.Row → Bool} (h : table.all check = true)
    {row : Templates.Row} (hrow : row ∈ table) : check row = true :=
  List.all_eq_true.mp h row hrow
```
— `Laws/Codegen/Read.lean:78-89`

and `NativeAtom` is ready for it: `all` is the inventory, `all_complete` forces an appended
constructor into it (`src/Effect4/Machine/Term.lean:163-171`), and `covers_iff` already turns a
Boolean coverage check into the universal fact (`:203-213`). So:

```lean
/-- Every structural obligation on one atom, as a Boolean. -/
def atomWellFormed (a : NativeAtom) : Bool :=
  -- the name is the inventory's, exactly once
  (names.count a.name == 1) &&
  -- arity agrees with the monomorphic signature
  (match a.mono, a.arity with
   | some (args, _), some n => args.length == n
   | some (args, _), none   => false
   | none, _                => true) &&
  -- `typeOf` at the declared signature answers the declared answer
  (match a.mono with
   | some (args, ans) => a.typeOf args == some ans
   | none             => true) &&
  -- a const-generic atom is polymorphic (DI-55): it has no monomorphic signature
  (!a.constGeneric || a.mono.isNone)

theorem atom_table_wf : NativeAtom.all.all atomWellFormed = true := by decide +kernel
```

`decide +kernel` exists in this toolchain (`Init/Tactics.lean:1472` `decide optConfig`;
`Lean/Elab/Tactic/Decide.lean:78-83` rejects `+kernel` with `+native` and otherwise hands the
reduction to the kernel), and it is the right choice here because `atomWellFormed` compares
`String`s, whose `DecidableEq` goes through `List Char` and is slow in the elaborator. The memory
index already records `decide +kernel` as this tree's tool for typing certificates.

**What `decide` cannot do, said plainly.** The obligation that matters — "if the arguments have the
declared types then the value `eval` produces has the declared answer type" — quantifies over
`Val` and `Ty`, both infinite. It is not decidable and no amount of `+kernel` changes that. What
the instrument should do instead:

- **decide** the structural obligations above (arity, names, coverage, signature agreement,
  const-genericity), one theorem, no per-atom proof — and `typeOf_mono`
  (`NativeAtom.lean:98-113`) already reduces the *polymorphic-free* part of typing to
  argument-wise subsumption, so for the 7 monomorphic atoms the semantic obligation follows from
  one generic lemma;
- **generate one `ProofWanted` per atom** for the semantic obligation, and let the hand proof be
  three lines each, closed by `aesop (rule_sets := [Effect4.Atoms])` after `cases` on the
  argument frames;
- **refuse the fallback group.** `typeOf`'s final alternation
  (`NativeAtom.lean:93-96`) lists 18 constructors so that an appended atom cannot inherit `none`
  — deliberate, and documented (`NativeAtom.lean:8-11`). It is a *definition*, so
  `#exhaustive_gate` flagging it is the point (§3.1). Leave it.

So the honest shape of §3.4 is: **`#atom_table_check` decides the table's well-formedness and
*declares* the semantic obligations; it does not discharge them.** L3 of the language push adds 17
atoms (`rows-42-43-plan.md` §2c), so the payoff is 17 × (no hand structural proof) and 17 × (one
three-line semantic proof the command names for you).

**Red control.** A fixture atom whose `arity` and `mono` disagree must make `decide +kernel` fail;
an atom missing from `all` must make `all_complete` fail (it already does); an atom with a
`ProofWanted` and no witness must keep the ledger's open count above zero.

---

## 4. "The same lemma at every row": `Progress.step_typed`

### 4.1 What the duplication actually is

`step_typed` (`Laws/Program/Progress.lean:176-403`) is 228 lines over 24 `NativeOp` rows. Ten of
its arms are the *same nine lines* —

```lean
    obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv
    cases ho
    simp only [syncOpStep] at hstep
    obtain ⟨heap', hr, rfl⟩ := refStep_of_syncOpStep hstep
    simp only [refStep] at hr
    obtain ⟨c, hpeek, hc⟩ := Option.map_eq_some_iff.mp hr
    simp only [Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    have hcn : Val.hasTy c .nat = true := hheap c (mem_of_refPeek_eq_some hpeek)
```

— followed by one `exact`. The nine lines are not the proof; they are the **re-derivation, at each
row, of a fact about `refStep`'s shape**. And `refStep` does have one shape:
`src/Effect4/Machine/Stores.lean:880-916` is thirteen heap rows of which twelve are
`(refPeek heap cell).map (fun a => (⟨answer⟩, refPoke heap cell ⟨content⟩))` and one
(`refUpdateSomeAndGet`, `:908-912`) is the same with a second peek.

So the instrument is not a tactic. **A tactic that replays nine lines twelve times is the chore
automated rather than removed.** The instrument is to say the shape once.

### 4.2 The recommendation: a step schema, one lemma, kernels as data

```lean
/-- Every heap row reads the cell, computes an answer and an optional new content from what the
cell holds, and writes back. The twelve `ref.*` rows are this with twelve kernels. -/
def refStepOf (cell : RefKey) (k : Val → Option (Val × Option Val)) (heap : RefHeap) :
    Option (Val × RefHeap) :=
  (refPeek heap cell).bind fun a =>
    (k a).map fun r =>
      (r.1, match r.2 with | some next => refPoke heap cell next | none => heap)

/-- The kernel of each row: what it answers and what it leaves in the cell. -/
def SyncOp.refKernel : SyncOp → Option (RefKey × (Val → Option (Val × Option Val)))
  | .refGet cell            => some (cell, fun a => some (a, none))
  | .refSet cell v          => some (cell, fun _ => some (Val.cell cell, some v))
  | .refGetAndSet cell v    => some (cell, fun a => some (a, some v))
  | .refSetAndGet cell v    => some (cell, fun _ => some (v, some v))
  | .refUpdate cell f       => some (cell, fun a => some (Val.unit, some (f.total a)))
  | .refGetAndUpdate cell f => some (cell, fun a => some (a, some (f.total a)))
  | .refUpdateAndGet cell f => some (cell, fun a => some (f.total a, some (f.total a)))
  | .refUpdateSome cell pf  => some (cell, fun a => some (Val.unit, pf.partialUpdate a))
  | .refGetAndUpdateSome cell pf => some (cell, fun a => some (a, pf.partialUpdate a))
  | .refUpdateSomeAndGet cell pf =>
      some (cell, fun a => match pf.partialUpdate a with
                           | some a' => some (a', some a') | none => some (a, none))
  | .refModify cell f       => some (cell, fun a => some ((f.modify a).1, some (f.modify a).2))
  | .refModifySome cell pf  => some (cell, fun a => some ((pf.modifySome a).1,
                                                          some ((pf.modifySome a).2.getD a)))
  | _                       => none

/-- One theorem, proved once, replacing the nine repeated lines and ten `exact`s. -/
theorem refStepOf_typed {cell : RefKey} {k} {heap heap' : RefHeap} {a : Val} {ansTy : Ty}
    (hheap : ∀ c ∈ heap, Val.hasTy c .nat = true)
    (hk : ∀ c ans next?, Val.hasTy c .nat = true → k c = some (ans, next?) →
            Val.hasTy ans ansTy = true ∧ ∀ n, next? = some n → Val.hasTy n .nat = true)
    (hstep : refStepOf cell k heap = some (a, heap')) :
    Val.hasTy a ansTy = true ∧ ∀ c ∈ heap', Val.hasTy c .nat = true
```

and then two connector lemmas — `refStep_eq_refStepOf : o.refKernel = some (cell, k) → refStep o
heap = refStepOf cell k heap` (by `cases o <;> rfl`, which is where the twelve rows are read
*once*), and `kernel_typed o : … ` as a table of twelve one-line facts registered in
`Effect4.Rows` — and `step_typed`'s twelve heap arms collapse to one:

```lean
  | refGet | refSet | refGetAndSet | … =>   -- or, better, no arm list at all
    exact refStepOf_typed hheap (kernel_typed _ _) (refStep_eq_refStepOf .. ▸ hstep)
```

Three properties I want to claim for this, and one I cannot:

- **It is what the owner's steer asks for.** "One deep module": the schema is the module, the rows
  are data. It is the same move `Laws/Codegen/Read.lean` already made for the printer, where the
  result was a proof with "no case per constructor" (`:8`).
- **It survives L4's function-taking rows.** When `SyncOp.refUpdate cell (f : Term) (env : List Val)`
  carries a term and `refStep` evaluates it (`rows-42-43-plan.md` §2c, L4), only the *kernel*
  changes: `fun a => (evalTerm (env ++ [a]) f).bind decode`. `refStepOf` and `refStepOf_typed`
  are untouched, and the new per-row obligation is discharged by `evalTerm_hasTy` — which is
  already proved and is already the plan's replacement for the four `FnName.*_hasTy_nat` theorems
  (`Progress.lean:85-121`, retired per §2b's step-3 findings). A term that fails to evaluate, or
  decodes to the wrong shape, is the kernel's `none`, and `refStepOf` propagates it: the frontier
  stays in one place instead of thirteen.
- **It survives the rows becoming templates.** `ansTy` is a *parameter* of `refStepOf_typed`, so
  when the answer becomes `Ty.instantiate σ row.answer` the schema does not notice. Only
  `kernel_typed` gains a `σ` and a `matchTemplate` hypothesis, and `rowTy_closed_some`
  (`Laws/Program/Template.lean:78-84`) is the bridge that already exists for the closed case.
- **What I cannot claim**: that `refStep` can be *redefined* through `refStepOf` without cost.
  Redefining it changes its unfold equations, and `refStep` has thirteen census theorems stated
  against them (`Stores.lean:919` onward, `refStep_make` and kin, each a `census:` receipt). The
  safe path is to **add** `refStepOf` and prove `refStep_eq_refStepOf` (`cases o <;> rfl`), leaving
  `refStep` and its receipts alone. The cost is one extra definition and one `rfl` proof; the
  benefit is that no census receipt moves. **Recommended.**

### 4.3 The tactic, for the arms that do not fit

Twelve of 24 rows are heap rows. The rest — `refMake` (allocation), `deferredMake`,
`deferredIsDone`, `deferredPoll`, `deferredSucceed`, `deferredFail`, `scopeMake`, `clockNow`,
`external`, `deferredAwait`, `sleep` — each have their own `syncOpStep_*` arm equation
(`Progress.lean:341-403`) and a short script. Those want a dispatcher, and the tree has the
pattern: `authoring_scoped_step` reads the goal's head and applies the lemma *named after it*
(`Laws/Program/Authoring/Tactic.lean:23-45`), wrapped in `repeat'` (`:49`). The same shape:

```lean
open Lean Elab Tactic Meta in
/-- One step of a row proof. Reads the row from the hypothesis `hstep : syncOpStep o s = some …`
and rewrites by the arm equation named after `o`'s head (`syncOpStep_<ctor>`), then inverts the
request by the inversion named after the row's request type. Never tries an alternative against
a goal it cannot close. -/
elab "row_step" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let some h := (← goal.getDecl).lctx.findDecl? fun d => … -- the `syncOpStep` hypothesis
      | throwError "row_step: no `syncOpStep` hypothesis"
    let .const ctor _ := (← whnfR (← inferType h)).getAppArgs[0]!.getAppFn
      | throwError "row_step: the operation is not a constructor application"
    let armEq := `Effect4.Machine ++ Name.mkSimple ("syncOpStep_" ++ ctor.getString!)
    if (← getEnv).contains armEq then
      evalTactic (← `(tactic| simp only [$(mkIdent armEq):ident] at $(mkIdent h.userName):ident))
    else
      throwError "row_step: no arm equation {armEq}; add one beside the row"

macro "row_steps" : tactic => `(tactic| repeat' row_step)
```

The important design choice, copied from `authoring_scoped`: **the tactic fails loudly when a row
has no arm equation**, rather than falling through to a search. That turns "add a row" into "add a
row and its one-line arm equation, which the tactic then finds by name" — the naming convention is
the registry (§6).

I rate this second in value to the schema. A dispatcher tactic is the right answer when the arms
are *genuinely different* (as `authoring_scoped`'s lifts are); it is the wrong answer when they are
the same arm twelve times, and twelve of 24 rows here are the same arm.

### 4.4 The constructor lists that must go regardless

Two proofs in the same family will break on the *next* constructor no matter what happens to
`step_typed`, and both fixes are one line:

- `syncOpOf_validIn` (`Progress.lean:434-489`) groups rows by pattern alternation:
  `| refGet | refUpdate _ | refGetAndUpdate _ | …`. The owner's rule is wildcard catch-alls. Here
  the wildcard is available because the groups are exhaustive by request shape: reorder so the
  cell-request group is `| _ => (obtain ⟨k, rfl⟩ := Val.hasTy_refTy_inv hv; cases ho; exact hval)`
  last. A new row then lands in the wildcard, and if its request is not a cell the *inversion*
  fails to type-check — loud, immediate, and at the right place.
- `sound`'s non-straight case (`MeaningSound.lean:642-647`) lists twelve constructors and answers
  `absurd hs Bool.false_ne_true`. Moving that arm **last** and making it `| _, _, _, _, _, hs, _, _`
  is safe for exactly the reason the list exists: a new *straight* constructor makes `Straight e`
  reduce to `true`, so `hs : true = true`, and `absurd hs Bool.false_ne_true` fails to elaborate.
  The build breaks with a type error at the arm instead of a missing-case error — same signal, no
  list to maintain. I checked `Straight`'s use here reads `hs : Straight e = true` and the arm is
  positioned *before* `.perform`, so the reorder is the whole change.

### 4.5 Cost and risk for §4

`refStepOf` + `refKernel` + `refStep_eq_refStepOf` + `refStepOf_typed` is perhaps 120 lines, of
which one is a real proof. It deletes roughly 130 lines of `step_typed` and — the point — makes
L4's rewrite of thirteen rows a rewrite of thirteen *kernel lines* rather than thirteen proof arms.

Risks. (1) `refStepOf`'s `bind`/`map` nesting must reduce the same way `refStep`'s does or
`cases o <;> rfl` fails; the partial rows are where I expect trouble, because `refStep` writes
`match pf.partialUpdate a with | some a' => refPoke … | none => heap` inside the `map`'s lambda
while the schema writes the `match` in the kernel. If `rfl` does not close, `simp only [refStep,
refStepOf, refKernel]` will, and the cost is a longer but still single proof. (2)
`refUpdateSomeAndGet` peeks twice and needs `refPeek_poke_self` (which exists — it is used at
`Progress.lean:320`) to fit the schema; its kernel as written above assumes that lemma. (3) The
schema must not be *the* definition (see 4.2) or thirteen census receipts move.

**Red control.** A fixture row whose `refKernel` line disagrees with its `refStep` arm (say
`refGetAndSet`'s kernel answering the new value instead of the old) must make
`refStep_eq_refStepOf` fail. That single `rfl` proof is what makes the kernel table trustworthy;
without the fixture, a wrong kernel would be a wrong theorem about a right machine.

---

## 5. Lessons from the literature and from other projects

Read in the pinned toolchain for this section, so the first four rows are facts about what is
already on disk here; the rest is knowledge, marked as such, and in every case I say whether the
*mechanism* transfers or only the *idea*.

### 5.1 Lean 4 core: a deriving handler that proves a law per constructor already exists

`Lean/Elab/Deriving/LawfulBEq.lean` is 55 lines that, for any non-mutual non-nested inductive,
generate an `instance … : LawfulBEq T := LawfulBEq.mk (by deriving_LawfulEq_tactic)` and register
the handler:

```lean
def mkLawfulBEqInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do mkLawfulBEqInstance declName
    return true
  else return false

builtin_initialize
  registerDerivingHandler ``LawfulBEq mkLawfulBEqInstanceHandler
```
— `Lean/Elab/Deriving/LawfulBEq.lean:47-56`

and `deriving_LawfulEq_tactic` is **not** a search: it is a macro that applies a small bank of
hand-proved helpers (`deriving_lawful_beq_helper_dep`, `deriving_lawful_beq_helper_nd`,
`and_true_curry`) driven by the constructor structure — `Init/LawfulBEqTactics.lean:19-60`.

That is the architecture of §1 in miniature, from the toolchain itself:
**a hand bank of generic lemmas + one dispatcher tactic + a generated instance.** It is the
strongest evidence I have that the recommendation is the idiomatic Lean 4 answer and not an
invention. The shared helpers — `mkInductArgNames`, `mkImplicitBinders`, `mkInstImplicitBinders`,
`mkInductiveApp`, `mkContext`, `mkLocalInstanceLetDecls`, `mkHeader`, `mkDiscrs`, `mkLet` in
`Lean/Elab/Deriving/Util.lean:24-200` — are the ones a `TyView`/`AdmitsSub` generator should use
rather than re-deriving; the handlers build **syntax** and `elabCommand` it, which is also what R1
of the metaprogramming review prescribes for the typed-state skeleton.

**Transfers, with one caveat.** `registerDerivingHandler : Name → DerivingHandler → IO Unit`
(`Lean/Elab/Deriving/Basic.lean:286-291`) must be called during initialization, but from the
*binder-free* `initialize`, which — §6 — the trust gate does **not** refuse. So `deriving
AdmitsSub` is available to this tree. Whether it is *wanted* is a separate question: a `deriving`
clause attaches to the inductive's declaration site, and `Ty` lives in `src/Effect4/Program/Ty.lean`
below the Laws root, so an `AdmitsSub` handler would drag the Laws vocabulary into the core root.
**Recommendation: a command (`#admits_sub Val.hasTy`) in `Laws/Auto/`, not a `deriving` clause.**
Same generator, right side of the boundary.

Two more core mechanisms worth knowing:

- **`ext` theorems are realized on demand, keyed to the structure.** `realizeExtTheorem`
  (`Lean/Elab/Tactic/Ext.lean:101-133`) builds `Struct.ext` by elaborating
  `by intro params* {..} {..}; intros; subst_eqs; rfl` and `addDecl`s it the first time anyone
  asks. It is in **core**, not Mathlib, at this pin — so every generated `Ok` structure has
  `<Owner>Ok.ext` for free, which matters for the frame lemmas (§3.3) whenever the goal is an
  equality of updated records rather than a predicate.
- **`getUnfoldEqnFor?` and `getEquationsFor`** (`Lean/Meta/Eqns.lean:312`,
  `Lean/Meta/Match/MatchEqs.lean:143`) are how `fold_of` reads a definition's arms
  (`src/Effect4/Program/FoldOf.lean:208-215`, `armOf`). Any new reader of a definition's case tree
  should go through them rather than `delta?`.

### 5.2 Mathlib's instruments — the ideas, since the code is unavailable

Mathlib is deliberately not a dependency (`lake-manifest.json` lists aesop, batteries, hash,
typescript, effects). From knowledge, not read here:

- **`@[simps]`** generates projection lemmas for a structure and tags them `@[simp]`. The tree's
  analogue exists: the generator emits `NodeLenses` and the `Ok` accessors, and the accessors are
  registered as aesop forward rules (`Typed/State.lean:143`). Nothing to borrow beyond the
  reminder that *the generated lemma should carry its own registration*, which
  `TypedStateGen.lean:310-324` already does.
- **`@[gcongr]`** is the closest match to §1.4 in the whole ecosystem: a tagged database of
  *congruence-monotonicity* lemmas (`a ≤ b → f a ≤ f b` shapes) plus a tactic that decomposes a
  monotonicity goal by looking up the head symbol. That is exactly "`hasTy` respects `sub` by
  cases on the constructor", solved by a tagged database and a dispatcher rather than by one big
  proof. The *design* transfers directly and is what `Effect4.TyOrder` plus a `mono_step`
  dispatcher would be; the code does not, and building the database by hand is the thing to avoid
  — generate it from the variance table.
- **`to_additive`** transports a whole theorem along a name-and-term dictionary held in an
  environment extension. The idea — one theorem, mechanically transported along a signature map —
  is exactly what a generated view buys. The mechanism does **not** transfer: it needs a
  persistent environment extension, which §6 shows this tree cannot have.
- **`@[ext]`** is in core at this pin (5.1), so nothing is owed.

### 5.3 Isabelle/HOL's BNF package: the relator is the missing vocabulary

Isabelle's `datatype` command (the bounded-natural-functor package, Blanchette/Hölzl/Lochbihler/
Panny/Popescu/Traytel, ITP 2014) generates, for every datatype, not only `map_F` and `set_F` but
the **relator** `rel_F` — the lifting of a relation on the parameters to a relation on the
datatype — together with its laws: `rel_F_mono`, `rel_F_OO` (the relator of a composition is the
composition of relators), `rel_F_conversep`, `rel_F_eq`. Transitivity of a structural order is then
`rel_F_OO` plus transitivity below; antisymmetry is `rel_F_conversep` plus antisymmetry below;
reflexivity is `rel_F_eq`.

`Ty.args` + `Variance.holds` **is** `rel_Ty` for a variance-annotated signature, `args_trans` is
`rel_OO`, and `eq_of_sameHead` is `rel_eq`. Naming that is worth a paragraph in the eventual
`docs/core` page, because it tells a reader where the design comes from and what laws to expect
next (the two I did not need but would generate anyway: `args_mono`, i.e. the comparison is
monotone in the relation, and `args_conversep`, i.e. reversing the relation reverses the
comparison with `contra`/`co` swapped — that second one is what would let `sub_antisymm_normal`
and `sub_trans_core` share even more).

Also transferable from the Isabelle world: `case_names` and `consumes`/`induct` attributes make a
generated induction rule's cases *nameable*, so a proof script survives a change in case order.
Lean's equivalent is that `fun_induction … with | caseName => …` uses the definition's own arm
names, which change when the definition does — so the discipline is: **do not name cases in a
proof that must survive a constructor addition; close them with `<;> aesop (rule_sets := …)`.**
That is a concrete style rule the tree can adopt today.

### 5.4 Coq: `Equations`, `Program`, and proof repair

- **`Equations`** (Sozeau & Mangin) derives, for a definition by dependent pattern matching, its
  equations *and* a functional elimination principle (`funelim`). Lean 4.33.1 already has both:
  `getUnfoldEqnFor?`/`getEquationsFor` and `fun_induction`/`fun_cases`
  (`Init/Tactics.lean:1049-1110`). **Nothing to import; something to start using** (§1.1).
- **`Program`/`Obligation Tactic`** defers side conditions to an obligation queue closed later by a
  named tactic. The sound analogue here is Batteries' `theorem_wanted` (§3.2) — it leaves a
  *placeholder with a type*, not an admitted goal — and the "obligation tactic" is
  `#auto_census … using aesop (rule_sets := […])`, which reports which obligations the bank already
  closes. The pairing of the two is, I think, the single most useful thing in this note after
  §1.1: **generate the obligation, then measure what the bank closes, then hand-prove the residue.**
- **Proof repair** (Ringer's PUMPKIN PATCH and PUMPKIN Pi, and the survey below) transforms existing
  proofs along a *type equivalence* when a datatype's representation changes. Its lesson for us is
  negative and worth stating: a new constructor is **not** an equivalence — it adds content, and no
  repair tool can invent the new arm. So the strategy cannot be "repair the proofs afterwards"; it
  must be "state the proofs over the signature so the new arm lands in generated code or in one
  named hole". That is what §1.2 and §1.4 do, and it is why I do not recommend building anything
  repair-shaped.
- **CompCert's tactic discipline** (Leroy): small, named, deterministic per-module tactics —
  `Inv`, `monadInv`, `TrivialExists` — rather than one large automation. This tree already follows
  it (`authoring_scoped`, `Laws/Program/Authoring/Tactic.lean`), and `row_step` (§4.3) is the next
  one. The discipline that matters is the one `authoring_scoped_step` states in its docstring:
  *"no alternative is ever tried against a goal it cannot close"* — the opposite of `first`.

### 5.5 Iris, and the boilerplate-reduction line

- **Iris/Coq** makes `Proper`/`NonExpansive` instances the registry: `f_equiv` and `solve_proper`
  close congruence goals by instance resolution, so no proof enumerates a connective's arguments.
  The transferable rule: **congruence is registered once per constructor and dispatched, never
  enumerated per proof.** `causeAdmits_congr_at` (`TypeAlgebra.lean:155`) and
  `reasonAdmits_congr`/`causeAdmits_congr` (`Laws/Program/Typed.lean:204-226`) are this tree's
  hand-written instances of exactly that; they should be bank members in `Effect4.TyOrder`.
- **Autosubst / Autosubst 2** (Schäfer–Tebbi–Smolka; Stark–Schäfer–Kaiser) generate de Bruijn
  substitution *and its lemmas* from a **binding signature**. The tree already does this — the
  authoring lifts are generated over `tools/Effect4Gen/binders.json` — so the lesson is the one
  the estate has already learned once and should apply again: when a chore is indexed by a
  signature, extend the signature file, not the lemmas. `binders.json` is the precedent for the
  variance file §1.2 needs.
- **Ott / Lem** (Sewell et al.) compile one declarative language definition to several provers.
  `manifest.json` + `wire-tags.json` + `tools/Effect4Gen` is this tree's Ott, and the hermetic
  group mechanism is its `check-gen`. Nothing to borrow; a name for what exists.
- **"Scrap Your Boilerplate"** (Lämmel & Peyton Jones) and datatype-generic programming (Gibbons,
  *Datatype-Generic Programming*) give the `cata`/algebra vocabulary the tree already uses. Their
  limit is the one this note keeps hitting: generic traversal of **one** value is solved (that is
  `fold_of`); a relation between **two** values needs the relator, which is §5.3.
- **"QED at Large: A Survey of Engineering of Formally Verified Software"** (Ringer, Palmskog,
  Sergey, Gligoric, Tatlock; *Foundations and Trends in Programming Languages* 5(2–3), 2019) is the
  proof-engineering survey the brief names. Its finding that matters here: in long-lived
  developments, **proof maintenance under specification change dominates initial proof cost**, and
  the interventions that pay are (i) proof engineering *for* change — abstraction boundaries that
  absorb it — and (ii) machine-checked *inventories* of what a change touches. This note's §1–§4 is
  (i); §3.1's `#exhaustive_gate` and §3.2's ledger are (ii). The survey's third intervention,
  proof repair, is the one I argue against above.

### 5.6 What does not transfer, and why

| wanted | blocked by | what to do instead |
| --- | --- | --- |
| a persistent registry keyed by attribute (`to_additive`'s dictionary, a simp-set-like extension) | `initialize x : T ← …` is a bodiless `opaque` (§6) | the type is the tag (§3.2), or the name is the tag (§6.3) |
| `native_decide`-backed table checks | `native_decide` in `forbiddenTrustTokens` (`AxiomGate.lean:242-244`) and `Lean.ofReduceBool` in `forbiddenAxioms` (`:205`) | `decide +kernel` (§3.4) |
| Mathlib-scale `simp`/`simp_all` automation | the estate's explicit-tactic rule (no `simp_all`, `first`, `try` in new proofs) | `simp only` + named aesop banks (§2) |
| `Program`-style admitted obligations | `sorry` refused in source *and* by `sorryAx` (`:205`, `:242`) | `theorem_wanted` (§3.2) |
| Mathlib's `@[gcongr]` database | Mathlib absent | generate the same database from the variance table (§1.2, §1.4) |

---

## 6. Persisting a meta-level table without `initialize`

### 6.1 What the gate actually refuses, precisely

`rows-42-43-plan.md` §2a records the finding as "the trust gate refuses `partial`, `unsafe`,
`implemented_by` and `initialize` throughout `src`". Reading both sides, that is **half right, and
the half that is wrong is the half that matters**:

- `initialize` is **not** a forbidden token. `forbiddenTrustTokens` is
  `["unsafe", "partial", "sorry", "axiom", "native_decide", "extern", "implemented_by"]`
  (`Test/Audit/AxiomGate.lean:242-244`) and `forbiddenTrustKeywords` is `["admit"]` (`:260`).
- The **binder form** `initialize x : T ← e` elaborates to a **bodiless `opaque`**:

```lean
      let defStx ← `($[$doc?:docComment]? @[$attrId:ident initFn, $(attrs?.getD ∅),*] $(vis?)? $[meta%$meta?]? opaque $id : $type)
```
  — `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/Lean/Elab/Declaration.lean:349`

  and a bodiless `opaque` is refused by the declaration pass, by exactly the reasoning the gate
  documents ("it denotes an arbitrary inhabitant rather than the value it advertises",
  `AxiomGate.lean:620-625`, with the synthesised bodies `Inhabited.default`/`Classical.ofNonempty`
  at `:260-262`). **So an environment extension is genuinely unavailable**, because
  `registerSimplePersistentEnvExtension` and `registerSimpleScopedEnvExtension`
  (`Lean/ScopedEnvExtension.lean:265`) return a value that must be bound — the binder form.
- The **binder-free form** `initialize do …` elaborates to a plain safe `def`:

```lean
      elabCommand (← `($[$doc?:docComment]? @[no_expose, $[$attrs],*] private $[meta%$meta?]? $[unsafe%$unsafe?]? def initFn : IO Unit := do $doSeq))
```
  — `Lean/Elab/Declaration.lean:366`

  which is **not** refused: not unsafe, not partial, has a body. (`meta` sets `ComputeKind.meta`,
  `Lean/Elab/DeclModifiers.lean:120-122` and `Lean/Elab/DefView.lean:219-223` — not `isUnsafe`.)

Two consequences the notes do not yet record:

1. **`registerDerivingHandler` is available** (`Lean/Elab/Deriving/Basic.lean:286`, type `IO Unit`),
   so a custom `deriving` handler is possible under `src/` through the binder-free `initialize`.
   Whether to use one is §5.1's question; the point is it is not blocked.
2. **`registerBuiltinAttribute` is not**, and not because of the gate: it throws unless
   `initializing`, and its own docstring is the reason —

```lean
def registerBuiltinAttribute (attr : AttributeImpl) : IO Unit := do
  …
  unless (← initializing) do
    throw (IO.userError "Failed to register attribute: Attributes can only be registered during initialization")
```
   — `Lean/Attributes.lean:69-74`

   It *could* be called from a binder-free `initialize`, but a custom attribute with no environment
   extension behind it has nowhere to put what it records — the attribute's `add` runs in `AttrM`
   and must persist its entry somewhere. So **a custom attribute is not the answer**, and the
   question in the brief ("check whether that needs `initialize`") resolves to: yes for the
   registry the attribute would need, even if not for the registration call itself.

### 6.2 What `whnf` decoding costs, and it is not a workaround

`TypedSources.readRows` decodes `Effect4.Program.Typed.sources` a constructor at a time
(`Laws/Auto/TypedSources.lean:64-86`), fuel-bounded, with a loud error on an unrecognised row. Its
own header calls this a consequence of the gate, and R1 of the metaprogramming review plans to
replace it with a `typed_position` command writing an environment extension — a plan
`Typed/Vocabulary.lean:5-7` already documents as if it had landed ("Rows are declared with
`typed_position` … and read from its environment extension"), which it has not. That plan **cannot
land**, per 6.1.

That is not a loss, and I want to say why rather than treating the present code as a stopgap. The
table-as-data design has three properties an extension does not:

1. **It is data in the source, readable by a person**, `Typed/Sources.lean:22-60`, with comments
   grouping the rows. An extension's contents are invisible except through a command.
2. **It is checked by the elaborator at its declaration site.** `Expected.fiber "x.id"` is a
   `String` today, which is the design's one weakness (§6.4); the moment a row's expectation is a
   *term*, `def sources : List Row := […]` type-checks every one of them where it is written.
   An extension populated by a command gets the same checking only if the command elaborates the
   term, which is more machinery for the same result.
3. **It is ordered, and diffs.** The gate prints counts per kind (`PositionGate.lean:63-67`); a
   review can read the table's diff. An extension's insertion order is an implementation detail.

The cost of decoding is one `whnf` per cell with a fuel bound — for 90 rows, nothing. **So: keep
reading the table; drop R1's `typed_position` command from the plan.**

### 6.3 The three gate-compatible registries, ranked

When a *command* needs to find things scattered across modules, there are exactly three
mechanisms available here, and all three are already used somewhere in the tree:

1. **The type is the tag.** Scan `env.constants` for declarations whose type's head is a marker
   constant. This is how the obligation ledger finds its placeholders (`ProofWanted α`, §3.2), and
   the gate already scans constants and resolves private names
   (`AxiomGate.lean:279-296`, `:612-627`). Cost: one pass over the constant map, which
   `Traversals.definitionsUnder` (`:151-167`) and `Census.elabAutoCensus` (`:80-88`) both already
   pay. **Best for obligations and for anything with a natural wrapper type.**
2. **The name is the tag.** A derived declaration lives at a computed name beside its parent:
   `f.alg`, `f.hom`, `g.eq_cata` (`FoldOf.lean:1-30`), `<Owner>Ok`, `syncOpStep_<ctor>`,
   `<f>_scoped`. A command then asks `env.contains (n ++ `eq_cata)` — which the traversal census
   already does to report "converted" rows (`Traversals.lean:234`) — and a *tactic* resolves the
   lemma by name from the goal's head, which `authoring_scoped_step` does
   (`Authoring/Tactic.lean:43`). Cost: nothing; a missing name is a loud error at the use site.
   **Best for generated lemmas and for dispatcher tactics.** This is the mechanism §4.3's
   `row_step` uses, and the reason it must fail loudly when the name is absent.
3. **An aesop rule set.** Aesop's rule sets *are* scoped environment extensions
   (`Aesop/Frontend/Extension.lean:18-39`), declared once inside aesop's own `initialize` and
   populated by an attribute — so a bank of facts registered with
   `@[aesop … (rule_sets := [Effect4.X])]` is a persistent, import-aware, per-module-scoped registry
   that this tree may use **without writing an `initialize` of its own**. Reading it back
   programmatically is possible (`#aesop_rules Effect4.X`, `Aesop/Frontend/Command.lean:62-78`,
   via `getGlobalRuleSet`). **Best when the registry's purpose is proof search**, which is most of
   them; it is a poor general-purpose key-value store and should not be abused as one.

What is *not* available, and the honest consequence: there is **no way to record a fact at
declaration `A` in module `M₁` and read it at a command in module `M₂` unless the fact is a
declaration**. Every registry in this tree must therefore be spelled as declarations — a list, a
placeholder, a lemma at a computed name, or an aesop rule. Stated positively, that is a *good*
constraint: it makes every registry auditable by `grep` and by the axiom gate, which is the reason
the gate refuses the alternative.

### 6.4 One defect in the present table, worth fixing while it is small

`Typed/Vocabulary.lean:20-35` carries expectations as `String`: `Expected.fiber (id : String)`,
with rows like `.nested (.fiber "x.id")` (`Sources.lean:24`). The emitter then *interpolates* the
string into generated text (`TypedStateGen.expectText`, `:29-37`), so `"x.id"` is checked for the
first time in the generated file, at a line nobody wrote. The metaprogramming review's syntax row
names this exactly ("rows carry the expected type as a **string** … interpolated into emitted
text") and proposes a `typed_position` command with a `term` antiquotation — which is the right
diagnosis and, per 6.1, the wrong mechanism.

The gate-compatible version: keep `sources : List Row` as data, and change `Expected`'s payload
from `String` to a **first-order term of the owner's fields** — an index into a generated
projection table, or a tiny inductive `Proj | id | frame | current` per owner. Then a misspelled
field is a type error in `Sources.lean` where the row is written. That is a small change now (90
rows, one file) and a large one after layer 1 instantiates the bundle. I raise it as a decision for
the owner rather than acting on it: **D-1, does the source table's expectation carry a string or a
typed projection?** My recommendation is the typed projection, and the cost is one generated
`Proj` enumeration per owner from the position census, which the census already computes.

---

## Recommendations for the push

The ordering principle: **an instrument that removes a cost the push is about to pay must land
before the slice that pays it.** The language push's slices are L1–L7 of
`rows-42-43-plan.md` §2c; four of them pay a cost this note removes.

### Now — the next constructors are L6/L7, records and variants (row 2), and `int`/`float`

| # | do | why now | size, assumed |
| --- | --- | --- | --- |
| 1 | **Probe `fun_induction`.** One proof, one afternoon: `fun_induction Ty.sub a b` inside `sub_trans_core`, and read what the splitter gives. | It is free, already derived by the compiler, and it decides whether §1 has a spine or needs the heavier view. Nothing else should be built before this answer. | half a day |
| 2 | **`#exhaustive_gate Ty` + the report.** The inventory of every match on `Ty` with no catch-all, printed by `make`. | L5's `Ty.unknown` touched nine `Ty` readers tonight and each was found by the compiler one at a time. This says, before you start, exactly which definitions will fail — six that I found by reading, and the gate will find the ones I missed. | ~150 lines of meta + a fixture |
| 3 | **Declare the seven aesop rule sets**, move nothing. | Zero behaviour change; it makes every later move a one-line diff and lets a hot proof say `-default` today. | an hour + one gate entry |
| 4 | **The `TyView` generator** (`Ty.args`, `sameHead`, `litRule`, `topRule`, `sub_eq_args` and four friends), and rewrite the three `TypeAlgebra` proofs and `hasTy_sub` against it. | This is the chore the plan itself flagged three times, and §0.2 measures it live: `Ty.unknown` cost 16 `first` blocks and +61 lines in `hasTy_sub` tonight. L6/L7, records and variants (row 2) and `int`/`float` are the next constructors; each pays the same bill until this lands. | ~250 lines emitter, ~80 lines of proof rewrite |
| 5 | **`AdmitsSub` + `cata_admits_sub`**, and `hasTy_sub`/`hasTy_normalize`/`hasTy_mono` as applications. | **L2 turns `hasTy` into `hasTyWith oracle` and needs all three laws monotone in the oracle.** Under the algebra formulation that is one more generic theorem; done the present way it is three re-proofs of 200, 40 and 50 lines. This is the single highest-leverage item in the note. | ~150 lines, of which one real proof |
| 6 | **`refStepOf` + the kernel table + `refStepOf_typed`**, collapsing `step_typed`'s twelve heap arms. | **L4 rewrites all thirteen heap rows to carry a `Term`.** With the schema that is thirteen kernel lines; without it, thirteen nine-line proof arms rewritten twice (once for the term, once for the template). | ~120 lines added, ~130 deleted |
| 7 | **`#atom_table_check`** (the decided part) **+ a `ProofWanted` per atom.** | **L3 adds seventeen atoms.** Seventeen structural proofs become one `decide +kernel`; the seventeen semantic ones get named for you. | ~80 lines |
| 8 | **The two constructor lists.** `syncOpOf_validIn`'s pattern groups → a trailing wildcard; `sound`'s non-straight arm → moved last and made `_`. | Twenty minutes each, and both are on the path of every future row and every future `Eff` constructor. | half a day with the builds |

Items 4–7 are independent of each other and of the push's own slices, so they can be seats in
parallel if the owner wants them parallel; 1 gates 4.

### After the push

| # | do | note |
| --- | --- | --- |
| 9 | Move the four existing registrations into their banks, one commit each, red control each. Order: `Effect4.Checker` (the biggest win and the loudest failures), `Effect4.Reader`, `Effect4.TypedState`, leave `Effect4.Inversion` as `(default := true)`. | ~210 aesop invocations see the change; announce it to in-flight seats, per the standing rule |
| 10 | The frame-lemma generator, emitting **proof terms** (§3.3). | **Amends R4** of the metaprogramming review |
| 11 | The obligation ledger: `ProofWanted` placeholders added from `Expr`, joined by `Census.attempt`. | **Amends R3**: `isDefEq` is the wrong join |
| 12 | `make check-aesop`: `aesop.stats.file` → a per-module time pin that may only fall. | The measurement half of §2 |
| 13 | Drop R1's `typed_position` command from the plan and the claim from `Typed/Vocabulary.lean:5-7`; decide **D-1**. | The plan asks for a mechanism the gate forbids (§6.1) |

### Decisions for the owner

- **D-1.** Does `Expected`'s payload stay a `String` or become a typed projection per owner
  (§6.4)? *Recommend: typed projection, now, while the table is 90 rows.*
- **D-2.** Ratify the two amendments to the metaprogramming review: **R4** frame lemmas are
  generated proof terms, not `aesop` goals; **R3** the witness join is an `#auto_census`-style
  rolled-back `attempt`, not `isDefEq`. *Recommend: both.*
- **D-3.** Where does the variance table live — a declared `tools/Effect4Gen/variances.json` beside
  `binders.json`, or inline in the emitter? *Recommend: the JSON file, so the rc.112 citation sits
  beside the datum and `make check-citations` can see it.*
- **D-4.** Register a `(Ty, Ty)` custom `@[induction_eliminator]`? *Recommend: no* — it is safe
  (§1.6) but it is a second hand artefact recording the arm list, which is the chore.
- **D-5.** Is the proof-shape ratchet (`first`/`simp_all`/`try` counts per module, may only fall) a
  gate or a report? *Recommend: a gate with today's numbers as the pin — 94 / 15 / 250 over
  `src/Effect4/Laws/` — because a ratchet nobody enforces is a report.*

### What I would not build

- **A bespoke `Ty.subInduct` eliminator** — `Ty.sub.induct_unfolding` is the same thing, derived.
- **The seven-plus-two `sub_<ctor>_of_ne` arm lemmas** — `sub_eq_args` subsumes them; keep them as
  the fallback if §1.2's law fights the elaborator.
- **Anything proof-repair shaped.** A new constructor is not an equivalence; no tool invents the
  arm (§5.4). Abstraction over the signature is the only thing that pays.
- **An environment extension, a custom attribute, or a `typed_position` command.** Not available,
  and the alternative is better (§6.2, §6.3).
- **A `row_step` tactic as the primary answer to §4.** Twelve of 24 arms are the same arm; a tactic
  that replays them is the chore automated rather than removed. Build the schema; keep the tactic
  for the dozen genuinely different rows.

### The honest summary

Three of the six questions have answers that are *already in the toolchain and unused*:
`fun_induction`/`fun_cases` for the case tree of a definition (§1.1), core's `ext` realization and
`LawfulBEq` deriving as the template for generating a law per constructor (§5.1), and aesop's own
rule sets and statistics as the bank and the measurement (§2). Two more have answers that exist in
this tree and need one more instance: the decided table fact (`table_fact`) and the generated fold
(`fold_of`). Only one thing genuinely has to be invented, and it is small: **the relational view of
a signature — the children of a node with the variance the order reads them at, and the four laws
about it.** That is the missing vocabulary, it has a name in the literature (the relator of a
bounded natural functor, §5.3), and it is about 250 lines of generator.

The thing I am least sure of, and would test first: whether `sub_eq_args`'s single generated proof
closes over 400 constructor pairs, or whether the generator has to emit one lemma per arm. That is
the difference between an elegant instrument and a workable one, and either way the hand proofs
stop seeing constructors — which is the requirement.

---

## References

Paths are absolute where they leave the repository. Everything under `src/`, `Test/`, `tools/`,
`test/` and `docs/` is relative to `/Users/pooks/Dev/lean4-effect4`. The toolchain root is
`/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/`, abbreviated `LEAN/` below.

### The briefs and the plan this note serves

- `docs/research/2026-09-18-metaprogramming-review.md` — R1–R8. §1's table of "what the code does
  by hand that the API does" is the frame this note extends; R3 and R4 are the two I amend (§3.2,
  §3.3), R1 is the one I argue cannot land (§6.1).
- `docs/research/2026-09-18-position-census-design.md` — the four censuses, the source table, the
  totality gate, §3a's landed list and §3b's re-plan. §2C's "unit is the definition, not the arm"
  is the tension with R3 I flag in §3.2.
- `docs/research/2026-09-18-rows-42-43-plan.md` §2b, §2c — the correction that names the chore
  ("the same chore three times, so a `sub` induction principle … is owed to the bank") and the
  L1–L7 slice list that fixes the ordering in *Recommendations*.

### The live measurement (§0.2)

- The working tree at the time of writing: `git status --porcelain` over 30 modified files,
  `git diff --numstat -- src/` = 168 insertions / 47 deletions across 19 files for the single
  constructor `Ty.unknown` (169/47 at my first measurement, ten minutes earlier — the session is
  live); `git diff -- src/Effect4/Program/Typed.lean` shows the sixteen new
  `first` blocks and `git diff -- src/Effect4/Laws/Program/TypeAlgebra.lean` the two-line
  alternative. HEAD is `61afe78f` ("machine: language push L1 — the alphabet once, below the
  stores"). The diff is uncommitted, so these numbers are reproducible only until the main session
  commits; the commit that lands `Ty.unknown` is the durable citation.

### The chores, read

- `src/Effect4/Laws/Program/TypeAlgebra.lean:10-77` (`sub_trans_core`, the top rule handled once at
  `:14-15`, the four `first` alternatives at `:32-40`), `:183-225` (`hasTy_normalize`), `:457-477`
  (`normal_children`, a per-constructor `match` in the statement), `:499-571`
  (`sub_antisymm_normal`, its `first` list at `:514-526`), `:749`/`:825` (`sub_normalize_of_sub`),
  `:854-881` (the `Std` order instances the laws feed).
- `src/Effect4/Program/Typed.lean:34-104` (`Val.hasTy`, the type dispatch, `unknown` at `:95`),
  `:144-399` (`hasTy_sub`, 256 lines, 18 `union` blocks, 16 `first` mismatch blocks).
- `src/Effect4/Program/Ty.lean:23-61` (the 20 constructors, `unknown` appended tonight), `:176-180`
  (`isNever`), `:186-191` (`closed`), `:389-394` (`isMember`), `:423-444` (`sub`, five exceptional
  rules and nine congruence arms, with `termination_by`), `:458-514` (`instantiate`, `infer`,
  `matchTemplate`), `:549-573` (`normalize`), `:573-600` (`Normal`), `:709-712` (`sub_unknown`,
  the top rule added tonight), `:754-808` (`sub_refl`, the union rules, `sub_lit_string`, the seven
  `_of_ne` inversions — and the absence of `refOf`/`deferredOf` ones, which is the immediate cause
  of the chore).
- `src/Effect4/Laws/Program/Progress.lean:159-166` (`refStep_of_syncOpStep`), `:176-403`
  (`step_typed`, 24 arms), `:434-489` (`syncOpOf_validIn`, constructor lists in patterns),
  `:85-121` (the four `FnName.*_hasTy_nat` L4 retires).
- `src/Effect4/Laws/Program/MeaningSound.lean:642-647` (the twelve-constructor `absurd` arm),
  `:648-690` (the `perform` case: `rowTy_closed_some`, `progress`, `hasTy_sub` in use).
- `src/Effect4/Machine/Stores.lean:847-916` (`refPeek`, `refPoke`, `refStep`'s thirteen heap rows),
  `:1938` (`syncOpStep`).
- `src/Effect4/Program/NativeAtom.lean:19-22` (`causeInputError?`), `:29-47`
  (`constGeneric`, `mono` — grouped lists), `:72-96` (`typeOf` and its deliberate fallback group),
  `:98-113` (`typeOf_mono`, the table-driven half already done).
- `src/Effect4/Machine/Term.lean:145-171` (`NativeAtom`, `all`, `all_complete`), `:203-213`
  (`covers_iff`: a Boolean coverage check becoming a universal fact).

### The instruments that work, and are the model

- `src/Effect4/Program/FoldOf.lean` — `fold_of`: the header at `:1-49` says what it produces;
  `:180-206` `reduceCases`; `:208-215` `armOf` reading the unfold equation; `:869-876` the command.
  The precedent for adding declarations from a command.
- `src/Effect4/Laws/Codegen/Read.lean:8-23` (a proof with "no case per constructor"), `:40-89`
  (the decided table facts and `table_fact`), `:287-288` (forward rules in `default`).
- `src/Effect4/Laws/Program/Template.lean:25-105` — twelve laws by one `aesop` each; `:50-51` the
  400-case `infer_closed`; `:78-84` `rowTy_closed_some`.
- `src/Effect4/Laws/Auto/Positions.lean:32-41` (the declared carrier/wrapper/stop lists — the
  precedent for a declared variance list), `:89-151` (`walkType`, fuel-bounded with a loud
  refusal), `:228-262` (`writeSites`), `:265-290` (`readSites`, both projection spellings),
  `:294-307` (`closure`).
- `src/Effect4/Laws/Auto/PositionGate.lean:37-73` — the totality gate: missing, stale, duplicate.
- `src/Effect4/Laws/Auto/TypedSources.lean:9-13` (why the table is read, not run), `:22-86` (the
  decoder, fuel-bounded).
- `src/Effect4/Laws/Auto/TypedStateGen.lean:29-47` (`expectText`, `oneLine` — the string
  interpolation §6.4 is about), `:310-324` (the aesop registrations, into `default`), `:399`
  (`IO.FS.writeFile`).
- `src/Effect4/Laws/Auto/Census.lean:24-51` (`axiomsOf`, `declaredAt`, `usesWhatFollows`), `:52-68`
  (`attempt` — the rolled-back join §3.2 reuses), `:70-103` (`#auto_census`).
- `src/Effect4/Laws/Auto/Traversals.lean:59-73` (`familyOf`, `domainOf`), `:139-167`
  (`isCompilerHelper`, `moduleOf`, `definitionsUnder`), `:203-267` (`#traversal_census`).
- `src/Effect4/Laws/Auto/Inversion.lean:8-20` (the policy on metavariable-creating rules — already
  right), `:125-132` (23 rules into `default`).
- `src/Effect4/Laws/Program/Authoring/Tactic.lean:19-49` — `authoring_scoped`: the goal-directed
  dispatcher, and the rule "no alternative is ever tried against a goal it cannot close".
- `src/Effect4/Laws/Program/Typed/{Vocabulary.lean,Sources.lean,State.lean}` — the vocabulary
  (`Vocabulary.lean:20-66`, and `:5-7`'s stale claim), the 90-row table, the generated skeleton
  (`State.lean:31-42` the bundle, `:42-78` the `Ok` predicates, `:142-170` the registrations).
- `Test/Audit/AxiomGate.lean:91-108` (`auditImplementationModules` and its staleness check at
  `:658-666`), `:205` (`forbiddenAxioms`), `:242-262` (`forbiddenTrustTokens`,
  `forbiddenTrustKeywords`, `synthesizedOpaqueBodies`), `:279-296` (resolving private
  declarations — the pattern for finding `ProofWanted` placeholders), `:392-465` (the source
  tokenizer §3.1's ratchet extends), `:612-627` (the unsafe/partial/bodiless-`opaque` pass).
- `Test/Audit/PositionCensus.lean:16-34`, `Test/Audit/TraversalCensus.lean:14-18` — how a census
  becomes a build artefact.
- `test/fixtures/trust-gate/` (19 fixtures incl. `known-red.txt`) — the red-control pattern every
  instrument in §3 should copy.

### The toolchain, v4.33.1

- `LEAN/Init/Tactics.lean:1008` (`induction … elimTarget,+`), `:1046` (`cases`), `:1049-1079`
  (**`fun_induction`** and `f.induct_unfolding`), `:1081-1110` (`fun_cases`), `:1472`
  (`decide optConfig`).
- `LEAN/Lean/Elab/Tactic/Decide.lean:78-129` — `+kernel` vs `+native`, and why `+kernel` is the
  cheap one for a big table.
- `LEAN/Lean/Meta/Tactic/FunInd.lean:25-45` (what the functional induction principle is), `:795`
  (`deriveUnaryInduction`), `:1101` (`deriveInductionStructural`).
- `LEAN/Lean/Meta/Tactic/ElimInfo.lean:190-222` (`@[induction_eliminator]`), `:253-261`
  (`@[cases_eliminator]`), `:264-278` (`getCustomEliminator?`, keyed on the *array* of targets).
- `LEAN/Lean/Elab/Tactic/Induction.lean:23-28` (`tactic.customEliminators`), `:817-840`
  (`getElimNameInfo`: the custom eliminator is consulted only without `using`, and a multi-target
  `induction` otherwise fails — why registering a binary eliminator is safe).
- `LEAN/Lean/Meta/Match/MatcherApp/Basic.lean:15-71` — `MatcherApp` and `matchMatcherApp?`
  (`alsoCasesOn`).
- `LEAN/Lean/Meta/Match/MatcherInfo.lean:37-49` (`AltParamInfo`, `hasUnitThunk`), `:52-107`
  (`MatcherInfo`, `getFirstAltPos`, `altNumParams`), `:22-35` (`Overlaps`).
- `LEAN/Lean/Meta/Match/Match.lean:146-200` — `withAlts`, **`mkMinorType`** (the alternative's type
  is `∀ xs, motive <patterns>`: the fact §3.1's catch-all detector rests on), `mkNotAlt` and
  `mkSplitterHyps` (why a catch-all stays one case).
- `LEAN/Lean/Expr.lean:684` (`mkSimpleThunkType`), `:1076` (`consumeMData`).
- `LEAN/Lean/Meta/Basic.lean:1717-1762` (`forallMetaTelescope`, `forallMetaTelescopeReducing`,
  `forallMetaBoundedTelescope`), `:1974-1999` (`withNewMCtxDepth`), `:2113` (`whnfR`),
  `:2586-2720` (`realizeConst` and `enableRealizationsForConst`).
- `LEAN/Lean/Meta/Eqns.lean:312` (`getUnfoldEqnFor?`), `LEAN/Lean/Meta/Match/MatchEqs.lean:143`
  (`getEquationsForImpl`), `LEAN/Lean/Meta/ForEachExpr.lean:53-80` (`forEachExpr'`/`forEachExpr`,
  both `partial` — why §3.1 writes its own fuel-bounded walk).
- `LEAN/Lean/Elab/Declaration.lean:342-366` — **`elabInitialize`**: `:349` the binder form is a
  bodiless `opaque` (so no environment extensions), `:366` the binder-free form is a plain `def`
  (so a deriving handler is possible). The single most load-bearing citation in §6.
- `LEAN/Lean/Attributes.lean:60-74` — `registerBuiltinAttribute` throws unless `initializing`.
- `LEAN/Lean/Elab/Deriving/Basic.lean:278-305` (`derivingHandlersRef`, `registerDerivingHandler`),
  `LEAN/Lean/Elab/Deriving/Util.lean:24-200` (the shared syntax builders),
  `LEAN/Lean/Elab/Deriving/LawfulBEq.lean:19-56` (**a deriving handler that proves a law**),
  `LEAN/Init/LawfulBEqTactics.lean:19-60` (its hand bank plus one macro tactic — the architecture
  §1 recommends, from the toolchain itself).
- `LEAN/Lean/Elab/Tactic/Ext.lean:101-133` (`realizeExtTheorem`: `ext` is in core at this pin and
  is realized on demand), `:137-155` (`realizeExtIffTheorem`).
- `LEAN/Lean/ScopedEnvExtension.lean:265` (`registerSimpleScopedEnvExtension`),
  `LEAN/Lean/Environment.lean:862` (`enableRealizationsForConst`), `:2709` (`realizeConst`).
- `LEAN/Lean/Elab/DeclModifiers.lean:120-145` (`ComputeKind`, `Modifiers`, `isPartial`),
  `LEAN/Lean/Elab/DefView.lean:219-223` (how `meta` is applied).
- `LEAN/Lean/Structure.lean:157` (`getStructureFields`), `:239` (`getStructureFieldsFlattened`),
  `LEAN/Lean/Meta/AppBuilder.lean:364` (`mkAppM`), `LEAN/Lean/Meta/Tactic/Constructor.lean:19`
  (`MVarId.constructor`), `LEAN/Lean/Elab/Tactic/Basic.lean:572-590` (`liftMetaTactic`),
  `LEAN/Lean/Elab/Term/TermElabM.lean:1889` (`elabTermEnsuringType`),
  `LEAN/Lean/Elab/InfoTree/Main.lean:247` (`realizeGlobalConstNoOverloadWithInfo`).

### Aesop, pinned at `3448c0bcc5ce01b2d1546e483ec3620e32df3d0e` (2026-08-10)

Version read from `lake-manifest.json` and `.lake/packages/aesop/` git log; it declares
`batteries v4.33.0` in `.lake/packages/aesop/lakefile.toml`.

- `.lake/packages/aesop/Aesop/Frontend/Command.lean:21-33` (**`declare_aesop_rule_sets`**, with
  `(default := …)`, expanding to `meta initialize` — the §2.6 gate question), `:35-49`
  (`add_aesop_rules`), `:51-60` (`erase_aesop_rules`), `:62-78` (`#aesop_rules`), `:86-100`
  (`#aesop_stats`).
- `.lake/packages/aesop/Aesop/Frontend/Attribute.lean:20-25` — the `@[aesop …]` attribute syntax.
- `.lake/packages/aesop/Aesop/Frontend/RuleExpr.lean:78-107` (phases `safe`/`norm`/`unsafe`;
  builders `apply`/`simp`/`unfold`/`tactic`/`constructors`/`forward`/`destruct`/`cases`/`default`),
  `:157-207` (indexing modes, transparency, `immediate`, `pattern`), `:259-301`
  (`ruleSetsFeature`, the feature grammar).
- `.lake/packages/aesop/Aesop/Frontend/Tactic.lean:24-32` (tactic clauses: `add`, `erase`,
  `rule_sets` with `"-"? ident`, `config`, `simp_config`), `:61-64` (`aesop`, `aesop?`).
- `.lake/packages/aesop/Aesop/Frontend/Extension.lean:18-39` (`declareRuleSetUnchecked : IO Unit`,
  and that a rule set *is* a scoped environment extension), `:56-57` (the builtin sets declared by
  aesop's own `initialize`).
- `.lake/packages/aesop/Aesop/RuleSet/Name.lean:17-27` — `default`, `builtin`, `local`, reserved.
- `.lake/packages/aesop/Aesop/Options/Public.lean:36-145` (the search options and their defaults:
  `maxRuleApplicationDepth 30`, `maxRuleApplications 200`, `maxNormIterations 100`,
  `useSimpAll true`, `useDefaultSimpSet true`, `terminal false`), `:198-209`
  (`aesop.collectStats`, `aesop.stats.file`).
- `.lake/packages/aesop/Aesop/Stats/Basic.lean:91-183` and `Aesop/Stats/Report.lean:36-124` — what
  `#aesop_stats` measures, which is what §2.5's time pin reads.

### Batteries, pinned at `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d` (`v4.33.0`)

- `.lake/packages/batteries/Batteries/Util/ProofWanted.lean:14-58` (the doc: opaque holes vs
  transparent derived defs, and the soundness argument), `:62-95`
  (`ProofWanted`, `ProofWanted.Stmt`, `DefWanted`, `DerivedWanted`), `:128-152` (the command
  configurations; `theorem_wanted` → `ProofWanted`, `requireProp := true`). Note `:154-175`: the
  command's *own* file-local registries are `private initialize … ← registerSimplePersistentEnvExtension`,
  i.e. exactly the shape §6.1 shows this tree cannot write — which is fine, because Batteries is
  not inside the audited tree.
- `.lake/packages/batteries/Batteries/Tactic/` — `Lint/` (a linter framework, if the proof-shape
  ratchet ever wants to be a linter rather than a tokenizer pass), `Trans.lean`, `Case.lean`,
  `SeqFocus.lean`.

### Literature (knowledge, not read here; cited for the design, not for an API)

- J. C. Blanchette, J. Hölzl, A. Lochbihler, L. Panny, A. Popescu, D. Traytel, *Truly Modular
  (Co)datatypes for Isabelle/HOL*, ITP 2014 — the BNF package: `map`, `set` and the **relator**
  `rel_F` generated per datatype, with `rel_mono`, `rel_OO`, `rel_conversep`, `rel_eq`. This is
  §1.2's design under its proper name, and the source of the two extra laws I would generate
  (`args_mono`, `args_conversep`).
- T. Ringer, K. Palmskog, I. Sergey, M. Gligoric, Z. Tatlock, *QED at Large: A Survey of
  Engineering of Formally Verified Software*, Foundations and Trends in Programming Languages
  5(2–3), 2019 — the proof-engineering survey the brief names; the finding that maintenance under
  specification change dominates, and the taxonomy that separates *engineering for change* from
  *proof repair*. §5.4 argues the second does not apply to constructor addition.
- T. Ringer et al., PUMPKIN PATCH / PUMPKIN Pi — proof transformation along a type equivalence.
  Cited for why it is the wrong tool here.
- M. Sozeau, C. Mangin, *Equations Reloaded*, ICFP 2019 — derived equations plus functional
  elimination; Lean 4.33.1 already ships both (`fun_induction`, `getEquationsFor`).
- S. Schäfer, T. Tebbi, G. Smolka, *Autosubst*, ITP 2015, and K. Stark, S. Schäfer, J. Kaiser,
  *Autosubst 2*, CPP 2019 — substitution operations *and lemmas* generated from a binding
  signature. The precedent for `tools/Effect4Gen/binders.json`, and the argument for a
  `variances.json` beside it (D-3).
- P. Sewell et al., *Ott*, and *Lem* — one declarative language definition, several prover backends;
  the shape `manifest.json` + `tools/Effect4Gen` already has.
- R. Lämmel, S. Peyton Jones, *Scrap Your Boilerplate*, TLDI 2003; J. Gibbons,
  *Datatype-Generic Programming*, SSDGP 2006 — generic traversal of one value, which `fold_of`
  covers; their limit is relations between two values, hence the relator.
- X. Leroy, *Formal Verification of a Realistic Compiler*, CACM 2009, and the CompCert sources —
  the tactic discipline of small named deterministic tactics per module, which
  `authoring_scoped` follows and `row_step` should.
- The Iris development (Jung, Krebbers, et al.) — `Proper`/`NonExpansive` instances as the
  congruence registry with `f_equiv`/`solve_proper` dispatching; the rule "register congruence once
  per constructor, never enumerate it per proof".
- Mathlib4's `@[simps]`, `to_additive`, `@[ext]`, `@[gcongr]` — cited in §5.2 for their designs.
  Mathlib is not a dependency of this tree and nothing here can be imported; `@[gcongr]`'s
  design — a tagged monotonicity-congruence database plus a head-directed dispatcher — is the one
  worth copying, generated rather than hand-tagged.
