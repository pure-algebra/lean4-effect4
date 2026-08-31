# Retained algebra closure contract

Status: FROZEN / RED, breaker-authored 2026-08-31

Implementation fence: `Effect4/Algebra/**`

Battery: `Effect4Test/Algebra/RetainedClosureContract.lean`

This packet closes the generic declarations that remained inside the retained
Foldlab source spans after the first extraction packet. It adds no new carrier
beside `Signature`, `Program`, and `Handler`. The one admitted new structure,
`ModelMorphism`, bundles a polymorphic map with the already-owned
`IsMonadMorphism` predicate so model morphisms can be quantified and compared
by equality.

## Frozen source and scope

Foldlab commit: `feb29321fd50204aa338209d313e84a3f8b71c66`

| Source | Retained declarations | Whole-file SHA-256 |
| --- | --- | --- |
| `library/cas/Cas/Lang/Representation.lean:80-84` | `eq_of_forall_interpret` | `5ca0f4cfeeb396c0f084d547a72825ddbe8a6c6a37e0786dbed9e94d68b652a8` |
| `library/cas/Cas/Backend/Universal.lean:140-143` | `interpret_vis` | `cce4f2a50a7e2a2e8b57b4de1a82f90c86efcb9749683795fd2b9e96d2ad8010` |
| `library/cas/Cas/Backend/Universal.lean:187-190` | `interpret_op_of_rightUnit` | same digest |
| `library/cas/Cas/Backend/Universal.lean:316-320` | `interpret_isMonadMorphism_of_equations` | same digest |
| `library/cas/Cas/Backend/Universal.lean:541-585` | `IsMorphE`, conversions, equality-form initiality | same digest |
| `library/cas/Cas/Backend/Universal.lean:598-631` | interpreter pin and anti-vacuity companion | same digest |
| `library/cas/Cas/Backend/SumAlgebra.lean:400-467` | one-target equivalences and all-model injection uniqueness | `d6a67f6efa75d81662f79945ce84ce54e83392b786bd9ce5a4884c01c2f7070b` |

The source declarations are evidence inputs only. Effect4 must not import
Foldlab.

## CATEGORIES

- `contracts` — every retained declaration receives an exact native
  signature or an explicit downstream-adapter disposition;
- `inductive-data` — `interpret_vis` exposes the defining beta equation of
  the `Program.vis` constructor;
- `algebraic-laws` — every theorem requires only the monad equations its
  proof consumes;
- `abstraction-modules` — `ModelMorphism` bundles an existing map and
  predicate without introducing a second notion of morphism;
- `specification-design` — freeness, interpreter separation, and initiality
  in signature models retain their distinct quantifier orders;
- `proof-mechanics` — the initial program monad is the separating target for
  programs and the sole target needed by injection uniqueness.

## REQUIRES

1. The declarations and universes frozen by
   `test/contracts/algebra-extraction.contract.md`.
2. `interpret_identity`, the injection handlers, their interpretation laws,
   and their sum-to-identity theorem.
3. `LeftUnit`, `RightUnit`, `BindAssoc`, and `IsMonadMorphism` remain the only
   equation predicates used by this slice.
4. The target universe used by an all-interpretations theorem is the universe
   of the relevant syntactic `Program` target. Effect4 has no implicit
   universe lift; broader target-universe comparison remains a separate
   explicit-lift obligation.

## ENSURES

### RALG-1 — interpreter separation

`Program.eq_of_all_interpretations` states that agreement under every lawful
handler into the syntactic target universe implies program equality. Its proof
must instantiate the hypothesis with `Program S` and `identityHandler`; it is
not a new behavioral quotient.

### RALG-2 — named constructor and operation equations

`interpret_vis` is the named definitional beta equation and requires only a
`Monad`. `interpret_perform_of_rightUnit` is public and requires an explicit
`RightUnit`, not `LawfulMonad`. The existing lawful
`interpret_perform` remains the convenient corollary.

### RALG-3 — morphism construction at exact equations

`interpret_isMonadMorphism_of_equations` constructs the existing predicate
from `LeftUnit` and `BindAssoc`; it does not demand right unit, functor laws, or
applicative laws.

### RALG-4 — anti-vacuity at the pin boundary

`interpret_inhabits_the_pin` proves that `interpret` satisfies both hypotheses
of `interpret_pinned` whenever left unit, associativity, and right unit are
available. The theorem is deliberately stated at the same bare-`Monad`
boundary as the pin.

### RALG-5 — one first-class morphism API

`ModelMorphism S M` stores an explicit result-type-indexed map and evidence of
the existing `IsMonadMorphism` predicate. `ofIsMonadMorphism` and
`toIsMonadMorphism` are the two binder-form conversions; the map round trip
and structure round trip are public equations. `ModelMorphism.ext` makes
equality depend only on the map field. No `IsMorphE` clone is admitted.

`program_is_initial_in_models_eq` fixes a handler and produces a unique
`ModelMorphism` preserving that handler's operations. Uniqueness is structure
equality, not merely a family of pointwise equations. This is initiality in
the category of `S`-models; it is not initiality among bare monads.

### RALG-6 — injection strength is explicit in the name

For each injection, the core exposes:

- `*_one_target_iff`, the equivalence at the syntactic target and injection
  handlers;
- `*_unique_one_target`, the pointwise uniqueness theorem using only that
  target;
- `*_all_models_iff`, the corresponding equivalence under every lawful model
  in the syntactic target universe; and
- `*_unique_all_models`, the wide law as a corollary of the one-target result.

The previously extracted `Program.inl_unique` and `Program.inr_unique` have
the one-target hypothesis despite their unsuffixed names. They do not close
the retained wide Foldlab declarations. They may remain for compatibility
with the first frozen packet, but all new code uses the strength-qualified
names.

## DECREASES

No evaluator or new recursive carrier is introduced. Proof recursion is
structural only where an existing `Program` induction is needed. Separation,
initiality, and injection uniqueness otherwise decrease by instantiating a
universal hypothesis with the syntactic model and rewriting by already-owned
identity equations.

## FRAME

- Do not change `Signature`, `Program`, `Handler`, or `IsMonadMorphism`.
- Do not introduce `Behavior`, `HHandler`, `IsMorphE`, a second free-program
  carrier, or a universe-lifting coercion.
- Do not edit the original extraction contract or its battery.
- Do not add Foldlab compatibility spellings to the Effect4 core.
- Do not turn a fixed-fuel runner into the separating semantics.
- Preserve unrelated working-tree changes.

## FALSIFIER

Each row gives the complete refutation shape. The Lean battery freezes the
corresponding type, so a stronger premise or weaker conclusion is red.

| Law | Refutation equation or shape |
| --- | --- |
| RALG-1 | exhibit `left != right` while every stated interpretation gives equal results; the identity handler is the required separating witness |
| RALG-2a | exhibit a handler, operation, and continuation for which interpreting `vis` differs from handler action followed by the continuation |
| RALG-2b | require more than `RightUnit`, or exhibit a right-unital target where `interpret (perform op) != handle op` |
| RALG-3 | require right unit or `LawfulMonad`, or exhibit left unit plus associativity where interpretation fails either morphism equation |
| RALG-4 | at a target satisfying all three equations, show that `interpret` fails either hypothesis of `interpret_pinned` |
| RALG-5 | produce a model morphism whose conversion changes its map, or two operation-preserving `ModelMorphism` values not equal to the canonical one |
| RALG-6 | produce a candidate satisfying the syntactic-target square but differing from the appropriate injection; the all-model claim is then dead by instantiation |

Existing registered attacks already cover the load-bearing boundaries:
`E4-ALG-CE-002` and `E4-ALG-CE-003` require both halves of the interpreter
pin, while `E4-ALG-CE-004` prevents category/monoid conflation. The retained
injection witness is a strengthening theorem, not a new counterexample, so no
new register ID is minted by this packet.

## Frozen native signatures

Names, universes, argument roles, and propositions below are frozen. Binder
names may differ.

```lean
universe uS uT uAns v

variable {S : Signature.{uS, uAns}}
variable {M : Type uAns -> Type v}

theorem Program.eq_of_all_interpretations
    {S : Signature.{uS, uAns}} {A : Type uAns}
    {left right : Program S A}
    (equal :
      ∀ (M : Type uAns -> Type (max uS uAns))
          [Monad M] [LawfulMonad M] (handler : Handler S M),
        interpret handler left = interpret handler right) :
    left = right

theorem interpret_vis
    {M : Type uAns -> Type v} {S : Signature.{uS, uAns}}
    {A : Type uAns} [Monad M]
    (handler : Handler S M) (operation : S.Op)
    (next : S.Answer operation -> Program S A) :
    interpret handler (Program.vis operation next) =
      handler.handle operation >>= fun answer => interpret handler (next answer)

theorem interpret_perform_of_rightUnit
    {M : Type uAns -> Type v} {S : Signature.{uS, uAns}} [Monad M]
    (rightUnit : RightUnit M) (handler : Handler S M)
    (operation : S.Op) :
    interpret handler (Program.perform operation) = handler.handle operation

theorem interpret_isMonadMorphism_of_equations
    {M : Type uAns -> Type v} {S : Signature.{uS, uAns}} [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (handler : Handler S M) :
    IsMonadMorphism S (fun {_A} program => interpret handler program)

theorem interpret_inhabits_the_pin
    {M : Type uAns -> Type v} {S : Signature.{uS, uAns}} [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (rightUnit : RightUnit M) :
    (forall handler : Handler S M,
      IsMonadMorphism S (fun {_A} program => interpret handler program)) /\
    forall (handler : Handler S M) (operation : S.Op),
      interpret handler (Program.perform operation) = handler.handle operation

structure ModelMorphism
    (S : Signature.{uS, uAns}) (M : Type uAns -> Type v) [Monad M] where
  map : (A : Type uAns) -> Program S A -> M A
  laws : IsMonadMorphism S (fun {A} program => map A program)

def ModelMorphism.ofIsMonadMorphism [Monad M]
    (map : {A : Type uAns} -> Program S A -> M A)
    (laws : IsMonadMorphism S map) : ModelMorphism S M

theorem ModelMorphism.toIsMonadMorphism [Monad M]
    (morphism : ModelMorphism S M) :
    IsMonadMorphism S
      (fun {A} program => morphism.map A program)

theorem ModelMorphism.ext [Monad M]
    {left right : ModelMorphism S M}
    (equal : forall (A : Type uAns) (program : Program S A),
      left.map A program = right.map A program) :
    left = right

theorem ModelMorphism.ofIsMonadMorphism_map [Monad M]
    (map : {A : Type uAns} -> Program S A -> M A)
    (laws : IsMonadMorphism S map) {A : Type uAns}
    (program : Program S A) :
    (ModelMorphism.ofIsMonadMorphism map laws).map A program = map program

theorem ModelMorphism.ofIsMonadMorphism_toIsMonadMorphism [Monad M]
    (morphism : ModelMorphism S M) :
    ModelMorphism.ofIsMonadMorphism
        (fun {A} program => morphism.map A program)
        morphism.toIsMonadMorphism =
      morphism

theorem program_is_initial_in_models_eq [Monad M]
    (leftUnit : LeftUnit M) (assoc : BindAssoc M)
    (rightUnit : RightUnit M) (handler : Handler S M) :
    exists morphism : ModelMorphism S M,
      (forall operation : S.Op,
        morphism.map _ (Program.perform operation) = handler.handle operation) /\
      forall other : ModelMorphism S M,
        (forall operation : S.Op,
          other.map _ (Program.perform operation) = handler.handle operation) ->
        other = morphism

theorem Program.inl_one_target_iff ...
theorem Program.inr_one_target_iff ...
theorem Program.inl_unique_one_target ...
theorem Program.inr_unique_one_target ...
theorem Program.inl_all_models_iff ...
theorem Program.inr_all_models_iff ...
theorem Program.inl_unique_all_models ...
theorem Program.inr_unique_all_models ...
```

The executable battery is the exact source for the eight injection theorem
types abbreviated above.

## Downstream adapter obligations

These are Foldlab compatibility rows, not additional Effect4 declarations:

| Foldlab spelling | Adapter target |
| --- | --- |
| `eq_of_forall_interpret` | `Effect4.Program.eq_of_all_interpretations` |
| `interpret_op_of_rightUnit` | `Effect4.interpret_perform_of_rightUnit` |
| `IsMorphE` plus its two conversion theorems | `Effect4.ModelMorphism`, `ofIsMonadMorphism`, and `toIsMonadMorphism` |
| `prog_is_initial_in_S_models` | `Effect4.program_is_initial_in_models_eq`, projected to the legacy existential family if required |
| `syntactic_hyp_iff`, `syntactic_hyp_iff_inr` | the two `Program.*_one_target_iff` theorems |
| wide `Prog.inl_unique`, `Prog.inr_unique` | `Program.inl_unique_all_models`, `Program.inr_unique_all_models` |
| `existsUnique_handler` | `program_is_free` |
| `interpret_satisfies_the_property` | `interpret_inhabits_the_pin` |

Every alias must live in the Foldlab adapter, resolve to the native theorem,
and receive its own compatibility type check. No alias is a reason to carry a
second proof or carrier in Effect4.

## Expected red state and acceptance

Against the current implementation, the narrow command must fail because the
new native declarations above do not yet exist:

```text
lake env lean Effect4Test/Algebra/RetainedClosureContract.lean
```

The expected missing families are `Program.eq_of_all_interpretations`,
`interpret_vis`, `interpret_perform_of_rightUnit`,
`interpret_isMonadMorphism_of_equations`, `interpret_inhabits_the_pin`,
`ModelMorphism`, `program_is_initial_in_models_eq`, and all eight
strength-qualified injection laws. A builder closes the packet only when the
narrow battery and default build pass, the new theorems appear in the human
axiom receipt and exhaustive axiom gate, and the Foldlab aliases are checked
downstream.
