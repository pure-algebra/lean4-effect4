import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.References
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typing.Replace — the replacement law of the typing judgment

An **address** is a path of child indices from the root of a program (`Node.at_`,
`Program/Refs.lean`). The **focus** is the sub-program at an address.

**The law** (`hasTy_replace`). A typed program splits at an address into an environment and a
type of the focus. Every program of that type in that environment stands in the focus's place,
under every extension of the typing signature, and the whole keeps its type.

It is two statements of Carroll, Madhavapeddy and Omar 2026, *Bidirectional Type Slicing*, read
on our judgment (`vendor/papers/program-graphs/bidirectional-type-slicing-2607.12197v1.pdf`,
page 14 of the vendored PDF): a typed program decomposes at any focus (its Theorem 5.2), and a
context with a focus of the focus's type composes to a typed program (its Theorem 5.3). Nothing
transfers by citation: each statement is proved here, on `HasTy`
(`Laws/Program/Typing/HasTy.lean`). No rule is added to that judgment, and no context typing
judgment is written: the law states it.

The law is the law of two edits of a sketch (`Program/Sketch.lean`). To fill is to put a
program at an address. To omit is to put a hole there. The extension of the signature in the
statement is what lets a filling or an omission declare new holes.

## How it is proved

The six typing judgments are mutual, and a path crosses them: a program, a statement list, a
race, a fiber action, a layer, a layer spine. One judgment over nodes holds the six
(`NodeHasTy`), indexed by the node's sort (`NodeTy`). A path also crosses a statement, which
has no judgment of its own: a statement is typed with the statements after it.

- **One step** (`NodeHasTy.child_step`). A typed node's child is typed, and a node of the child's
  type stands in its place. It has one case for each arm of the generated `Node.child`
  (`Program/NodeLenses.lean`), in that function's order. Each case inverts one rule and applies
  it again, with the other premises moved along the extension (`hasTy_ext` and its five
  siblings, `Laws/Program/Signature.lean`). A constructor appended to the program family adds
  one case for each of its node children.
- **Two dead ends.** The empty list after a `return` and the empty tail of a one-layer spine
  are children with no typed replacement. No path to a program crosses one, and the step asks
  for that.
- **The path** (`NodeHasTy.replace`). One induction on the path, with no mutual induction.
- **The six statements** are its instances: `hasTy_replace`, `stmtsHasTy_replace`,
  `effsHasTy_replace`, `actionHasTy_replace`, `layerHasTy_replace`, `layersHasTy_replace`.
- **At the checker** (`check_replace`): the focus is checked, and not the program again. The
  replaced program exists (`Node.replaceAt_eff`).

## Placement

Concept `initial-algebras-folds`: the typing judgment follows the program's constructors, and
the law is its congruence at one address. Requirement R14, the proposed claim
`typed-replacement` (role substitution; pointer `NodeHasTy.replace`), under decisions rows 282
and 288. Consumers: `Sketch.check_fill` and `Sketch.check_omit` (`Laws/Program/Sketch.lean`),
and each edit of a program at a focus.

Reach: the six judgments, at every signature of every operation alphabet; a program as the
focus, at every address; every extension of the signature; the focus's type kept exactly.

The law does not establish:

- any behaviour: it relates no two runs;
- a focus of a smaller type, or of a type that is equal only after normalization;
- a term as the focus: a term has no address (`Node.child`);
- a program with a layer reference: the judgment has no rule for one;
- a function that computes the focus's environment and type. They are existential here. A tool
  needs that function, and the proof that it answers this law's pair (the receipt of slice
  REPLACE, its first open obligation).
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

/-! ## The judgment of a node -/

/-- The index of a node's typing judgment, by the node's sort. A statement's index holds the
statements after it. -/
inductive NodeTy (Op : Type) where
  /-- a program: its environment and its type -/
  | eff (env : TyEnv) (t : EffTy)
  /-- a statement list: its environment, the loop flag and its generator state -/
  | stmts (env : TyEnv) (inLoop : Bool) (g : GenTy)
  /-- a statement: the index of the list that it heads, and that list's tail -/
  | stmt (env : TyEnv) (inLoop : Bool) (tail : Stmts Op) (g : GenTy)
  /-- the entrants of a race -/
  | effs (env : TyEnv) (t : EffTy)
  /-- a fiber action -/
  | action (env : TyEnv) (t : EffTy)
  /-- a layer -/
  | layer (l : LayerTy)
  /-- a layer spine -/
  | layers (l : LayerTy)

/-- **A node has a type**: the typing judgment of its sort, at its index. It adds no rule to
the six judgments. A statement is typed with the statements after it, because no judgment types
a statement alone. A step of `typed-replacement`: the induction on a path reads it. -/
inductive NodeHasTy (s : Signature Op) : Node Op → NodeTy Op → Prop where
  | eff {env : TyEnv} {e : Eff Op} {t : EffTy} :
      HasTy s env e t → NodeHasTy s (.eff e) (.eff env t)
  | stmts {env : TyEnv} {inLoop : Bool} {b : Stmts Op} {g : GenTy} :
      StmtsHasTy s env inLoop b g → NodeHasTy s (.stmts b) (.stmts env inLoop g)
  | stmt {env : TyEnv} {inLoop : Bool} {st : Stmt Op} {tail : Stmts Op} {g : GenTy} :
      StmtsHasTy s env inLoop (.cons st tail) g →
      NodeHasTy s (.stmt st) (.stmt env inLoop tail g)
  | effs {env : TyEnv} {es : Effs Op} {t : EffTy} :
      EffsHasTy s env es t → NodeHasTy s (.effs es) (.effs env t)
  | action {env : TyEnv} {a : ActionTerm Op} {t : EffTy} :
      ActionHasTy s env a t → NodeHasTy s (.action a) (.action env t)
  | layer {l : LayerTerm Op} {L : LayerTy} :
      LayerHasTy s l L → NodeHasTy s (.layer l) (.layer L)
  | layers {ls : LayerTerms Op} {L : LayerTy} :
      LayersHasTy s ls L → NodeHasTy s (.layers ls) (.layers L)

/-! ## The law -/

/-- **The replacement law, at a node: the claim `typed-replacement`.** A typed node splits at an
address of a program into an environment and a type of the focus. Every program of that type in
that environment, under every extension of the signature, stands in the focus's place, and the
node keeps its type. The six statements below are its instances. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal NodeHasTy.replace {s : Signature Op} (path : List Nat) {n : Node Op} {τ : NodeTy Op}
    {q : Eff Op} (hn : NodeHasTy s n τ) (hat : n.at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {n' : Node Op}, SigExtends s s' → HasTy s' env q' t →
        n.replaceAt path (.eff q') = some n' → NodeHasTy s' n' τ

/-- **The replacement law, at a program.** A typed program splits at an address into an
environment and a type of the focus, and every program of that type in that environment stands
in the focus's place: the whole keeps its type, under every extension of the signature. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal hasTy_replace {s : Signature Op} {env0 : TyEnv} {p q : Eff Op} {T : EffTy}
    {path : List Nat} (hp : HasTy s env0 p T) (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' p' : Eff Op}, SigExtends s s' → HasTy s' env q' t →
        (Node.eff p).replaceAt path (.eff q') = some (.eff p') → HasTy s' env0 p' T

/-- The replacement law, at a statement list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal stmtsHasTy_replace {s : Signature Op} {env0 : TyEnv} {inLoop : Bool} {b : Stmts Op}
    {q : Eff Op} {g : GenTy} {path : List Nat} (hb : StmtsHasTy s env0 inLoop b g)
    (hat : (Node.stmts b).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {b' : Stmts Op}, SigExtends s s' → HasTy s' env q' t →
        (Node.stmts b).replaceAt path (.eff q') = some (.stmts b') →
        StmtsHasTy s' env0 inLoop b' g

/-- The replacement law, at the entrants of a race. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal effsHasTy_replace {s : Signature Op} {env0 : TyEnv} {es : Effs Op} {q : Eff Op}
    {T : EffTy} {path : List Nat} (he : EffsHasTy s env0 es T)
    (hat : (Node.effs es).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {es' : Effs Op}, SigExtends s s' → HasTy s' env q' t →
        (Node.effs es).replaceAt path (.eff q') = some (.effs es') → EffsHasTy s' env0 es' T

/-- The replacement law, at a fiber action. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal actionHasTy_replace {s : Signature Op} {env0 : TyEnv} {a : ActionTerm Op}
    {q : Eff Op} {T : EffTy} {path : List Nat} (ha : ActionHasTy s env0 a T)
    (hat : (Node.action a).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {a' : ActionTerm Op}, SigExtends s s' →
        HasTy s' env q' t → (Node.action a).replaceAt path (.eff q') = some (.action a') →
        ActionHasTy s' env0 a' T

/-- The replacement law, at a layer. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal layerHasTy_replace {s : Signature Op} {l : LayerTerm Op} {q : Eff Op} {L : LayerTy}
    {path : List Nat} (hl : LayerHasTy s l L) (hat : (Node.layer l).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {l' : LayerTerm Op}, SigExtends s s' →
        HasTy s' env q' t → (Node.layer l).replaceAt path (.eff q') = some (.layer l') →
        LayerHasTy s' l' L

/-- The replacement law, at a layer spine. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal layersHasTy_replace {s : Signature Op} {ls : LayerTerms Op} {q : Eff Op}
    {L : LayerTy} {path : List Nat} (hl : LayersHasTy s ls L)
    (hat : (Node.layers ls).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {ls' : LayerTerms Op}, SigExtends s s' →
        HasTy s' env q' t → (Node.layers ls).replaceAt path (.eff q') = some (.layers ls') →
        LayersHasTy s' ls' L

/-- **The law at the checker: the focus is checked, and not the program again.** A program that
the checker admits splits at an address into an environment and a type of the focus. For every
program that the checker admits at that type in that environment, under every extension of the
signature, the replaced program exists, and the checker admits it at the whole's type. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal check_replace {s : Signature Op} {env0 : TyEnv} {p0 : List Nat} {p q : Eff Op}
    {T : EffTy} {path : List Nat}
    (hp : Checker.check s env0 p0 p = .ok T) (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), (∀ pq, Checker.check s env pq q = .ok t) ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {pq : List Nat}, SigExtends s s' →
        Checker.check s' env pq q' = .ok t →
        ∃ p', (Node.eff p).replaceAt path (.eff q') = some (.eff p') ∧
          ∀ p1, Checker.check s' env0 p1 p' = .ok T

end Effect4.Program
