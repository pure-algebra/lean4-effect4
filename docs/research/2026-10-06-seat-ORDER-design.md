# 2026-10-06 seat ORDER design: the order of a lifted rule in Lean core's classes

Status: research note (history, not authority). Base: `594d3bdb`. Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-order-brief.md`. Decisions rows 137, 293 and 299.

## Question

How does the estate unify its three order representations under Lean core's classes
(`Std.IsPreorder`, `Std.IsPartialOrder`, `Std.LawfulOrderSup`) without changing existing definitions
or breaking the axiom ceiling?

## What was read or run

| What | Evidence |
| --- | --- |
| Brief `docs/research/2026-10-05-claude-lead/briefs/seat-order-brief.md`, probe `docs/research/2026-10-06-order-classes-probe.lean.txt`, plan `docs/research/2026-10-06-next-slices-plan.md` | reading |
| Lean core order classes and lemmas under `Init/Data/Order/` (`Classes.lean`, `Lemmas.lean`, `Factories.lean`) | reading |
| The design probe `docs/research/2026-10-06-seat-ORDER-probe-design.lean.txt` | compiled with `lake env lean`: exit 0, zero warnings, axioms at `[propext, Quot.sound]` |
| The current order instances of `CTy` and `ErrTy` in `src/Effect4/Laws/Program/TypeAlgebra.lean` | reading |
| The combinator's order class `AnswerOrder` in `src/Effect4/Laws/Program/UnionRule.lean` | reading |

## Findings and Design Decisions

### 1. One generic law module: `Effect4.Laws.Program.Order`

A new law module `src/Effect4/Laws/Program/Order.lean` provides the algebraic properties of `max`
from core's classes alone:

- **Preorder bounds and monotonicity** (`[LE α] [Max α] [Std.IsPreorder α] [Std.LawfulOrderSup α]`):
  - `le_max_left (a b : α) : a ≤ max a b := Std.left_le_max`
  - `le_max_right (a b : α) : b ≤ max a b := Std.right_le_max`
  - `max_le {a b c : α} (h1 : a ≤ c) (h2 : b ≤ c) : max a b ≤ c := Std.max_le_iff.mpr ⟨h1, h2⟩`
  - `max_mono_left`, `max_mono_right`, and `max_mono` (monotonicity of `max` under `≤`).
- **Partial order equations** (`[LE α] [Max α] [Std.IsPartialOrder α] [Std.LawfulOrderSup α]`):
  - `max_comm (a b : α) : max a b = max b a`
  - `max_idem (a : α) : max a a = a`
  - `max_assoc (a b c : α) : max (max a b) c = max a (max b c)`
  - Instances for `Std.Commutative`, `Std.Associative`, and `Std.IdempotentOp`.
- **Axioms**: All four theorems reach only `[propext]`.

### 2. Equations of `CTy` and `ErrTy`

In `src/Effect4/Laws/Program/TypeAlgebra.lean`:
- `CTy.join_comm`, `CTy.join_assoc` and `CTy.join_idem` are direct applications of `max_comm`,
  `max_assoc` and `max_idem`.
- `ErrTy.join_comm`, `ErrTy.join_assoc` and `ErrTy.join_idem` apply the same generic equations.
- The hand list proofs unfolding `normalizeRow` stay only where raw `Ty.join` requires them.

### 3. Deriving `AnswerOrder` from core classes

`AnswerOrder` keeps its seven fields. This preserves every existing statement and avoids
touching callers. A constructor `AnswerOrder.ofCore` derives all seven fields for any carrier with
`[Std.IsPreorder α]`, `[Std.LawfulOrderSup α]`, `Answer.join = max`, and `Answer.bot ≤ a`:

```lean
@[instance_reducible] def AnswerOrder.ofCore {β : Type} [Answer β] [LE β] [Max β]
    [Std.IsPreorder β] [Std.LawfulOrderSup β]
    (join_eq : ∀ a b : β, Answer.join a b = max a b)
    (bot_le : ∀ a : β, Answer.bot ≤ a) : AnswerOrder β
```

`CTy` gains an `Answer` instance (`bot := CTy.never`, `join := max`) and its `AnswerOrder` instance
via `AnswerOrder.ofCore`.

On raw types, `subN` connects to `CTy`'s order by definition:
`theorem subN_iff_le (a b : Ty) : (Ty.subN a b = true) ↔ (CTy.ofRaw a ≤ CTy.ofRaw b) := Iff.rfl`.

### 4. The join law as an equation in antisymmetric carriers

`lift_union` proves `le c (Answer.join a b) ∧ le (Answer.join a b) c`.
In an antisymmetric carrier, antisymmetry collapses this into equality:

```lean
theorem lift_union_eq_of_antisymm {α : Type} [Answer α] [AnswerOrder α]
    (antisymm : ∀ a b : α, AnswerOrder.le a b → AnswerOrder.le b a → a = b)
    {rule : Ty → Option α} (mono : Below rule rule) (s t : Ty) :
    lift rule (.union s t) = (lift rule s).bind fun a => (lift rule t).map (Answer.join a)
```

This yields the join equation at `CTy` and at pairs `CTy × CTy` (decisions row 293, point 4).
Furthermore, `lift_unique_pair` states and proves the uniqueness of the lifted rule for a pair of
types `Ty × Ty` as an exact equation, discharging the second open item of row 293, point 4:

```lean
theorem lift_unique_pair {rule f : Ty → Option (Ty × Ty)}
    (normal : ∀ t, f t = f t.normalize)
    (never : f .never = some Answer.bot)
    (member : ∀ {m : Ty}, Ty.Normal m → m.isMember = true →
      f m = (rule m).map fun p => (p.1.normalize, p.2.normalize))
    (union : ∀ {m r : Ty}, Ty.Normal m → m.isMember = true → Ty.Normal r →
      Ty.Normal (.union m r) → f (.union m r) = (f m).bind fun a => (f r).map (Answer.join a))
    (t : Ty) : f t = lift rule t
```


### 5. The adjoint form in `≤`

`Eliminator.adjoint` translates directly to the lattice order:

```lean
theorem Eliminator.adjoint_le {rule : Ty → Option Ty} {C : Ty → Ty}
    (e : Eliminator rule C) (t : Ty) :
    ((lift rule t).isSome = true ↔ ∃ b, CTy.ofRaw t ≤ CTy.ofRaw (C b)) ∧
    ∀ {a : Ty}, lift rule t = some a →
      ∀ b : Ty, CTy.ofRaw a ≤ CTy.ofRaw b ↔ CTy.ofRaw t ≤ CTy.ofRaw (C b)
```

Proved by `Iff.rfl` from `Eliminator.adjoint`. It is a textbook Galois connection in `≤`.

### 6. One sentence for a slice view

`Eliminator.monotone` provides `Below rule rule`, which via `lift_mono` and `subN_iff_le` gives
`∀ s t, CTy.ofRaw s ≤ CTy.ofRaw t → CTy.ofRaw a ≤ CTy.ofRaw b`, the exact `mono` premise of
`SliceView` over an eliminator's answer.

## File and Anchoring Plan

1. New file: `src/Effect4/Laws/Program/Order.lean` (under existing area `Laws/Program`).
2. Anchor in `src/Effect4/Laws.lean`: directly before `import Effect4.Laws.Program.UnionRule`.
3. New test file: `Test/Program/Order.lean`.
4. Anchor in `Test/All.lean`: directly after `import Test.Program.UnionRule`.
5. Updates in `src/Effect4/Laws/Program/UnionRule.lean` and `src/Effect4/Laws/Program/TypeAlgebra.lean`.
