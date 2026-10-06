import Effect4.Laws.Program.Typing.Replace
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typing.Focus — the focus function answers the pair of the replacement law

`Program/Typing/Focus.lean` computes the focus at an address of a program: the sub-program, its
environment and its type (`focusAt`). The replacement law says that such a pair exists
(`hasTy_replace`, `Laws/Program/Typing/Replace.lean`). This module proves that the computed
pair is the law's, so the law holds at the function's answer with no existential.

| Statement | In words |
| --- | --- |
| `focusAt_typed` | the answer is the sub-program at the address, and it has the answered type in the answered environment; for every program, typed or not |
| `focusAt_nil` | at the root the answer is the checker's |
| `hasTy_focusAt`, `check_focusAt` | on a typed program the function answers at every address of a program |
| `hasTy_replace_focusAt`, `check_replace_focusAt` | a program of the answered type in the answered environment stands in the focus's place, under every extension of the signature, and the whole keeps its type |

## How it is proved

The work is in `Laws/Program/Typing/Replace.lean`. Its step lemma has one case for each case of
the step function, and each case says that the function answers the environment of the typing
rule (`NodeHasTy.child_step`). One induction on the path folds it
(`NodeHasTy.replace_envAt`). Here `focusAt_eq_some` unfolds the function into its three facts:
the node at the address, the environment at the address, and the checker's type there. The
typing judgment gives a program one type in one environment (`effTy_complete`), so the law's
pair is the function's.

## Placement

Concept `initial-algebras-folds`: the typing judgment follows the program's constructors, and
the step function is its inversion at one child. Requirement R14, the proposed claim
`focus-function` (role inversion; pointer `NodeHasTy.replace_envAt`), under decisions rows 288
and 292. Consumers: `Sketch.check_fill_focusAt` and `Sketch.check_omit_focusAt`
(`Laws/Program/Sketch.lean`), a reader of a term's type at a node, and a slice view that walks
down a program with its types.

Reach: the six judgments, at every signature of every operation alphabet; a program as the
focus, at every address; every extension of the signature. `focusAt_typed` holds for every
program.

These statements do not establish:

- an environment after a sibling that the checker refuses: the function answers `none` there;
- the environment of a term that reads an extension of its node's environment;
- a bound on the cost of a walk over every address;
- any behaviour, or a focus of a smaller type, or of a type that is equal only after
  normalization.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

/-- **The focus function, unfolded.** It answers `f` exactly when three facts hold: the node at
the address is the program `f.program`; the environment at the address is `f.env`; the checker
gives `f.program` the type `f.ty` there. A step of `focus-function`: each law below reads it. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem focusAt_eq_some {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {path : List Nat}
    {f : Focus Op} :
    focusAt s env0 p path = some f ↔
      (Node.eff p).at_ path = some (.eff f.program) ∧
        (Node.eff p).envAt s (.env env0) path = some (.env f.env) ∧
        effTy s f.env f.program = some f.ty := by
  obtain ⟨q, env, t⟩ := f
  unfold focusAt
  constructor
  · intro h
    split at h
    · rename_i q1 env1 hat henv
      obtain ⟨t1, ht, hf⟩ := Option.map_eq_some_iff.mp h
      cases hf
      exact ⟨hat, henv, ht⟩
    · cases h
  · rintro ⟨hat, henv, ht⟩
    simp only [hat, henv, ht, Option.map_some]

/-- **At the root the focus is the checker's answer.** The focus at the empty path is the
program itself, in the root's environment, at the type that `effTy` answers. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem focusAt_nil (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    focusAt s env0 p [] = (effTy s env0 p).map fun t => ⟨p, env0, t⟩ := rfl

/-- **The answer is typed.** Whatever the focus function answers is the sub-program at the
address, and that sub-program has the answered type in the answered environment. It holds for
every program: the program around the focus need not have a type. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal focusAt_typed {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {path : List Nat}
    {f : Focus Op} (hf : focusAt s env0 p path = some f) :
    (Node.eff p).at_ path = some (.eff f.program) ∧ HasTy s f.env f.program f.ty

/-- **On a typed program the focus function answers at every address of a program.** The
answered program is the one at the address. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal hasTy_focusAt {s : Signature Op} {env0 : TyEnv} {p q : Eff Op} {T : EffTy}
    {path : List Nat} (hp : HasTy s env0 p T) (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), focusAt s env0 p path = some ⟨q, env, t⟩

/-- **The replacement law at the focus function's answer.** In a typed program, a program that
has the answered type in the answered environment, under an extension of the signature, stands
in the focus's place, and the whole keeps its type. No environment and no type is existential:
the function names both. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal hasTy_replace_focusAt {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {T : EffTy}
    {path : List Nat} {f : Focus Op} (hp : HasTy s env0 p T)
    (hf : focusAt s env0 p path = some f) {s' : Signature Op} {q' p' : Eff Op}
    (hext : SigExtends s s') (hq' : HasTy s' f.env q' f.ty)
    (hrep : (Node.eff p).replaceAt path (.eff q') = some (.eff p')) : HasTy s' env0 p' T

/-- **At the checker: the focus function answers at every address of a program** that the
checker admits. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal check_focusAt {s : Signature Op} {env0 : TyEnv} {p0 : List Nat} {p q : Eff Op}
    {T : EffTy} {path : List Nat} (hp : Checker.check s env0 p0 p = .ok T)
    (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), focusAt s env0 p path = some ⟨q, env, t⟩

/-- **At the checker: the replacement law at the focus function's answer.** In a program that
the checker admits, take the focus that the function answers. For every program that the
checker admits at the focus's type in the focus's environment, under an extension of the
signature, the replaced program exists, and the checker admits it at the whole's type. The
focus is checked, and not the program again. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal check_replace_focusAt {s : Signature Op} {env0 : TyEnv} {p0 : List Nat} {p : Eff Op}
    {T : EffTy} {path : List Nat} {f : Focus Op} (hp : Checker.check s env0 p0 p = .ok T)
    (hf : focusAt s env0 p path = some f) {s' : Signature Op} {q' : Eff Op} {pq : List Nat}
    (hext : SigExtends s s') (hq' : Checker.check s' f.env pq q' = .ok f.ty) :
    ∃ p', (Node.eff p).replaceAt path (.eff q') = some (.eff p') ∧
      ∀ p1, Checker.check s' env0 p1 p' = .ok T

end Effect4.Program
