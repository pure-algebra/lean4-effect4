import Effect4.Program.Typing.Focus
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

/-- The environment of a node's typing judgment: what the index holds of the nodes above the
node, without the node's own type (`NodeEnv`, `Program/Typing/Focus.lean`). The step function
`Node.childEnv` computes the child's from the parent's (`NodeHasTy.child_step`). -/
def NodeTy.env : NodeTy Op → NodeEnv
  | .eff env _ => .env env
  | .stmts env inLoop _ => .body env inLoop
  | .stmt env inLoop _ _ => .body env inLoop
  | .effs env _ => .env env
  | .action env _ => .env env
  | .layer _ => .closed
  | .layers _ => .closed

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

/-! ## One step -/

/-- An empty statement list leads to no program. A step of `typed-replacement`: the dead end
after a `return` in `NodeHasTy.child_step`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.at_stmts_nil (rest : List Nat) (q : Eff Op) :
    (Node.stmts (.nil : Stmts Op)).at_ rest ≠ some (.eff q) := by
  cases rest with
  | nil => intro h; cases h
  | cons j rest => intro h; cases h

/-- An empty layer spine leads to no program. A step of `typed-replacement`: the dead end after
a one-layer spine in `NodeHasTy.child_step`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.at_layers_nil (rest : List Nat) (q : Eff Op) :
    (Node.layers (.nil : LayerTerms Op)).at_ rest ≠ some (.eff q) := by
  cases rest with
  | nil => intro h; cases h
  | cons j rest => intro h; cases h

/-- A typed spine after a typed head is a typed spine: the rule `LayersHasTy.cons` with a tail
that is not written as a `cons`. A typed spine is never empty. A step of `typed-replacement`:
the tail of a spine in `NodeHasTy.child_step`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem layersHasTy_cons {s : Signature Op} {head : LayerTerm Op} {ls : LayerTerms Op}
    {h t : LayerTy} (hh : LayerHasTy s head h) (ht : LayersHasTy s ls t) :
    LayersHasTy s (.cons head ls) (h.merge t) := by
  cases ht with
  | one hl => exact .cons hh (.one hl)
  | cons hl hr => exact .cons hh (.cons hl hr)

/-- **One step of the law.** A typed node's child that leads to a program is typed, and a node
of the child's type stands in its place: the parent keeps its type, under every extension of
the signature.

One case for each arm of `Node.child`, in that function's order, and one for each rule where a
node has several. Each case inverts the rule and applies it again: the new premise stands at
the child, and every other premise moves along the extension. The two dead ends read `hlead`.
A step of `typed-replacement`: `NodeHasTy.replace` folds it along a path. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem NodeHasTy.child_step {s : Signature Op} {n c : Node Op} {τ : NodeTy Op} {i : Nat}
    (hn : NodeHasTy s n τ) (hc : n.child i = some c)
    (hlead : ∃ rest q, c.at_ rest = some (.eff q)) :
    ∃ τc, NodeHasTy s c τc ∧
      ∀ {s' : Signature Op} {c' n' : Node Op}, SigExtends s s' → NodeHasTy s' c' τc →
        n.setChild i c' = some n' → NodeHasTy s' n' τ := by
  unfold Node.child at hc
  split at hc <;> cases hc
  -- eff (.suspend a0), 0
  · cases hn with | eff hp => cases hp with | suspend hb =>
    exact ⟨_, .eff hb, fun _ hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.suspend hx)⟩
  -- eff (.bind a0 _), 0
  · cases hn with | eff hp => cases hp with | bind hf hr =>
    exact ⟨_, .eff hf, fun h hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.bind hx (hasTy_ext h hr))⟩
  -- eff (.bind _ a1), 1
  · cases hn with | eff hp => cases hp with | bind hf hr =>
    exact ⟨_, .eff hr, fun h hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.bind (hasTy_ext h hf) hx)⟩
  -- eff (.gen a0), 0
  · cases hn with | eff hp => cases hp with | gen hb =>
    exact ⟨_, .stmts hb, fun _ hc' hs => by
      cases hc' with | stmts hx => cases hs; exact .eff (.gen hx)⟩
  -- eff (.catchCause a0 _), 0
  · cases hn with | eff hp => cases hp with | catchCause hb hh hj =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.catchCause hx (hasTy_ext h hh) hj)⟩
  -- eff (.catchCause _ a1), 1
  · cases hn with | eff hp => cases hp with | catchCause hb hh hj =>
    exact ⟨_, .eff hh, fun h hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.catchCause (hasTy_ext h hb) hx hj)⟩
  -- eff (.matchCause a0 _ _), 0
  · cases hn with | eff hp => cases hp with | matchCause hb hv hk hj =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; exact .eff (.matchCause hx (hasTy_ext h hv) (hasTy_ext h hk) hj)⟩
  -- eff (.matchCause _ a1 _), 1
  · cases hn with | eff hp => cases hp with | matchCause hb hv hk hj =>
    exact ⟨_, .eff hv, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; exact .eff (.matchCause (hasTy_ext h hb) hx (hasTy_ext h hk) hj)⟩
  -- eff (.matchCause _ _ a2), 2
  · cases hn with | eff hp => cases hp with | matchCause hb hv hk hj =>
    exact ⟨_, .eff hk, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; exact .eff (.matchCause (hasTy_ext h hb) (hasTy_ext h hv) hx hj)⟩
  -- eff (.onExit a0 _), 0
  · cases hn with | eff hp => cases hp with | onExit hb hf =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.onExit hx (hasTy_ext h hf))⟩
  -- eff (.onExit _ a1), 1
  · cases hn with | eff hp => cases hp with | onExit hb hf =>
    exact ⟨_, .eff hf, fun h hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.onExit (hasTy_ext h hb) hx)⟩
  -- eff (.exit a0), 0
  · cases hn with | eff hp => cases hp with | exit hb =>
    exact ⟨_, .eff hb, fun _ hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.exit hx)⟩
  -- eff (.uninterruptible a0), 0
  · cases hn with | eff hp => cases hp with | uninterruptible hb =>
    exact ⟨_, .eff hb, fun _ hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.uninterruptible hx)⟩
  -- eff (.interruptible a0), 0
  · cases hn with | eff hp => cases hp with | interruptible hb =>
    exact ⟨_, .eff hb, fun _ hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.interruptible hx)⟩
  -- eff (.withFiber a0), 0
  · cases hn with | eff hp => cases hp with | withFiber ha =>
    exact ⟨_, .action ha, fun _ hc' hs => by
      cases hc' with | action hx => cases hs; exact .eff (.withFiber hx)⟩
  -- eff (.scoped a0), 0
  · cases hn with | eff hp => cases hp with | «scoped» hb =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; rw [← h.bodyRequires]; exact .eff (.scoped hx)⟩
  -- eff (.acquireRelease a0 _), 0
  · cases hn with | eff hp => cases hp with | acquireRelease ha hr hne =>
    exact ⟨_, .eff ha, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; rw [← h.scopeKey]; exact .eff (.acquireRelease hx (hasTy_ext h hr) hne)⟩
  -- eff (.acquireRelease _ a1), 1
  · cases hn with | eff hp => cases hp with | acquireRelease ha hr hne =>
    exact ⟨_, .eff hr, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; rw [← h.scopeKey]; exact .eff (.acquireRelease (hasTy_ext h ha) hx hne)⟩
  -- eff (.provideLayer a0 _ _), 0
  · cases hn with | eff hp => cases hp with | provideLayer isLocal hl hb =>
    exact ⟨_, .layer hl, fun h hc' hs => by
      cases hc' with | layer hx =>
        cases hs; exact .eff (.provideLayer _ hx (hasTy_ext h hb))⟩
  -- eff (.provideLayer _ _ a2), 1
  · cases hn with | eff hp => cases hp with | provideLayer isLocal hl hb =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; exact .eff (.provideLayer _ (layerHasTy_ext h hl) hx)⟩
  -- eff (.provideService _ _ a2), 0
  · cases hn with | eff hp => cases hp with | provideService hk hv hsub hb =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs
        exact .eff (.provideService (h.service _ _ hk) ((h.termTy _ _).trans hv) hsub hx)⟩
  -- eff (.catchIf _ a1 _), 0
  · cases hn with | eff hp => cases hp with | catchIf hb ht hh hj =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; exact .eff (.catchIf hx ((h.termTy _ _).trans ht) (hasTy_ext h hh) hj)⟩
  -- eff (.catchIf _ _ a2), 1
  · cases hn with | eff hp => cases hp with | catchIf hb ht hh hj =>
    exact ⟨_, .eff hh, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; exact .eff (.catchIf (hasTy_ext h hb) ((h.termTy _ _).trans ht) hx hj)⟩
  -- eff (.select _ _ a2 _), 0
  · cases hn with | eff hp => cases hp with | select ht hd h0 h1 hj =>
    exact ⟨_, .eff h0, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; exact .eff (.select ((h.termTy _ _).trans ht) hd hx (hasTy_ext h h1) hj)⟩
  -- eff (.select _ _ _ a3), 1
  · cases hn with | eff hp => cases hp with | select ht hd h0 h1 hj =>
    exact ⟨_, .eff h1, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; exact .eff (.select ((h.termTy _ _).trans ht) hd (hasTy_ext h h0) hx hj)⟩
  -- eff (.iterate _ _ _ _ _ a5), 0
  · cases hn with | eff hp => cases hp with | iterate hi ht hb hst hr hs0 hs1 =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs
        exact .eff (.iterate ((h.termTy _ _).trans hi) ((h.termTy _ _).trans ht) hx
          ((h.termTy _ _).trans hst) ((h.termTy _ _).trans hr) hs0 hs1)⟩
  -- eff (.restore _ a1), 0
  · cases hn with | eff hp => cases hp with | restore hsv hb =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx => cases hs; exact .eff (.restore ((h.termTy _ _).trans hsv) hx)⟩
  -- action (.fork a0 _), 0
  · cases hn with | action ha => cases ha with | fork options hp =>
    exact ⟨_, .eff hp, fun _ hc' hs => by
      cases hc' with | eff hx => cases hs; exact .action (.fork _ hx)⟩
  -- action (.forkIn a0 _ _), 0
  · cases hn with | action ha => cases ha with | forkIn options hp hsc =>
    exact ⟨_, .eff hp, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; exact .action (.forkIn _ hx ((h.termTy _ _).trans hsc))⟩
  -- action (.forkScoped a0 _), 0
  · cases hn with | action ha => cases ha with | forkScoped options hp =>
    exact ⟨_, .eff hp, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; rw [← h.scopeKey]; exact .action (.forkScoped _ hx)⟩
  -- action (.raceAll a0), 0
  · cases hn with | action ha => cases ha with | raceAll he =>
    exact ⟨_, .effs he, fun _ hc' hs => by
      cases hc' with | effs hx => cases hs; exact .action (.raceAll hx)⟩
  -- layer (.effect _ a1), 0
  · cases hn with | layer hl => cases hl with | effect hb hk hsub =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; rw [← h.bodyRequires]; exact .layer (.effect hx (h.service _ _ hk) hsub)⟩
  -- layer (.effectDiscard a0), 0
  · cases hn with | layer hl => cases hl with | effectDiscard hb =>
    exact ⟨_, .eff hb, fun h hc' hs => by
      cases hc' with | eff hx =>
        cases hs; rw [← h.bodyRequires]; exact .layer (.effectDiscard hx)⟩
  -- layer (.provide a0 _), 0
  · cases hn with | layer hl => cases hl with | provide ha hb =>
    exact ⟨_, .layer ha, fun h hc' hs => by
      cases hc' with | layer hx => cases hs; exact .layer (.provide hx (layerHasTy_ext h hb))⟩
  -- layer (.provide _ a1), 1
  · cases hn with | layer hl => cases hl with | provide ha hb =>
    exact ⟨_, .layer hb, fun h hc' hs => by
      cases hc' with | layer hx => cases hs; exact .layer (.provide (layerHasTy_ext h ha) hx)⟩
  -- layer (.provideMerge a0 _), 0
  · cases hn with | layer hl => cases hl with | provideMerge ha hb =>
    exact ⟨_, .layer ha, fun h hc' hs => by
      cases hc' with | layer hx =>
        cases hs; exact .layer (.provideMerge hx (layerHasTy_ext h hb))⟩
  -- layer (.provideMerge _ a1), 1
  · cases hn with | layer hl => cases hl with | provideMerge ha hb =>
    exact ⟨_, .layer hb, fun h hc' hs => by
      cases hc' with | layer hx =>
        cases hs; exact .layer (.provideMerge (layerHasTy_ext h ha) hx)⟩
  -- layer (.merge a0 _), 0
  · cases hn with | layer hl => cases hl with | merge ha hb =>
    exact ⟨_, .layer ha, fun h hc' hs => by
      cases hc' with | layer hx => cases hs; exact .layer (.merge hx (layerHasTy_ext h hb))⟩
  -- layer (.merge _ a1), 1
  · cases hn with | layer hl => cases hl with | merge ha hb =>
    exact ⟨_, .layer hb, fun h hc' hs => by
      cases hc' with | layer hx => cases hs; exact .layer (.merge (layerHasTy_ext h ha) hx)⟩
  -- layer (.fresh a0), 0
  · cases hn with | layer hl => cases hl with | fresh hi =>
    exact ⟨_, .layer hi, fun _ hc' hs => by
      cases hc' with | layer hx => cases hs; exact .layer (.fresh hx)⟩
  -- layer (.orDie a0), 0
  · cases hn with | layer hl => cases hl with | orDie hi =>
    exact ⟨_, .layer hi, fun _ hc' hs => by
      cases hc' with | layer hx => cases hs; exact .layer (.orDie hx)⟩
  -- layer (.mergeAll a0), 0
  · cases hn with | layer hl => cases hl with | mergeAll hls =>
    exact ⟨_, .layers hls, fun _ hc' hs => by
      cases hc' with | layers hx => cases hs; exact .layer (.mergeAll hx)⟩
  -- stmts (.cons a0 _), 0: the statement, typed with the statements after it
  · cases hn with | stmts hb =>
    exact ⟨_, .stmt hb, fun _ hc' hs => by
      cases hc' with | stmt hx => cases hs; exact .stmts hx⟩
  -- stmts (.cons _ a1), 1: the statements after the head, by the head's rule
  · cases hn with | stmts hb =>
    cases hb with
    | bindYield he hr =>
      exact ⟨_, .stmts hr, fun h hc' hs => by
        cases hc' with | stmts hx => cases hs; exact .stmts (.bindYield (hasTy_ext h he) hx)⟩
    | yieldDiscard he hr =>
      exact ⟨_, .stmts hr, fun h hc' hs => by
        cases hc' with | stmts hx => cases hs; exact .stmts (.yieldDiscard (hasTy_ext h he) hx)⟩
    | ret ht =>
      obtain ⟨rest, q, hat⟩ := hlead
      exact absurd hat (Node.at_stmts_nil rest q)
    | ifElse ht ha hb hr hab hg =>
      exact ⟨_, .stmts hr, fun h hc' hs => by
        cases hc' with | stmts hx =>
          cases hs
          exact .stmts (.ifElse ((h.termTy _ _).trans ht) (stmtsHasTy_ext h ha)
            (stmtsHasTy_ext h hb) hx hab hg)⟩
    | whileTrue hb hr hg =>
      exact ⟨_, .stmts hr, fun h hc' hs => by
        cases hc' with | stmts hx =>
          cases hs; exact .stmts (.whileTrue (stmtsHasTy_ext h hb) hx hg)⟩
    | breakLoop hr =>
      exact ⟨_, .stmts hr, fun _ hc' hs => by
        cases hc' with | stmts hx => cases hs; exact .stmts (.breakLoop hx)⟩
  -- stmt (.bindYield a0), 0
  · cases hn with | stmt hb => cases hb with | bindYield he hr =>
    exact ⟨_, .eff he, fun h hc' hs => by
      cases hc' with | eff hx => cases hs; exact .stmt (.bindYield hx (stmtsHasTy_ext h hr))⟩
  -- stmt (.yieldDiscard a0), 0
  · cases hn with | stmt hb => cases hb with | yieldDiscard he hr =>
    exact ⟨_, .eff he, fun h hc' hs => by
      cases hc' with | eff hx => cases hs; exact .stmt (.yieldDiscard hx (stmtsHasTy_ext h hr))⟩
  -- stmt (.ifElse _ a1 _), 0
  · cases hn with | stmt hb => cases hb with | ifElse ht ha hb hr hab hg =>
    exact ⟨_, .stmts ha, fun h hc' hs => by
      cases hc' with | stmts hx =>
        cases hs
        exact .stmt (.ifElse ((h.termTy _ _).trans ht) hx (stmtsHasTy_ext h hb)
          (stmtsHasTy_ext h hr) hab hg)⟩
  -- stmt (.ifElse _ _ a2), 1
  · cases hn with | stmt hb => cases hb with | ifElse ht ha hb hr hab hg =>
    exact ⟨_, .stmts hb, fun h hc' hs => by
      cases hc' with | stmts hx =>
        cases hs
        exact .stmt (.ifElse ((h.termTy _ _).trans ht) (stmtsHasTy_ext h ha) hx
          (stmtsHasTy_ext h hr) hab hg)⟩
  -- stmt (.whileTrue a0), 0
  · cases hn with | stmt hb => cases hb with | whileTrue hb hr hg =>
    exact ⟨_, .stmts hb, fun h hc' hs => by
      cases hc' with | stmts hx =>
        cases hs; exact .stmt (.whileTrue hx (stmtsHasTy_ext h hr) hg)⟩
  -- effs (.cons a0 _), 0
  · cases hn with | effs he => cases he with | cons hh ht hj =>
    exact ⟨_, .eff hh, fun h hc' hs => by
      cases hc' with | eff hx => cases hs; exact .effs (.cons hx (effsHasTy_ext h ht) hj)⟩
  -- effs (.cons _ a1), 1
  · cases hn with | effs he => cases he with | cons hh ht hj =>
    exact ⟨_, .effs ht, fun h hc' hs => by
      cases hc' with | effs hx => cases hs; exact .effs (.cons (hasTy_ext h hh) hx hj)⟩
  -- layers (.cons a0 _), 0
  · cases hn with | layers hl =>
    cases hl with
    | one hh =>
      exact ⟨_, .layer hh, fun _ hc' hs => by
        cases hc' with | layer hx => cases hs; exact .layers (.one hx)⟩
    | cons hh hr =>
      exact ⟨_, .layer hh, fun h hc' hs => by
        cases hc' with | layer hx => cases hs; exact .layers (.cons hx (layersHasTy_ext h hr))⟩
  -- layers (.cons _ a1), 1
  · cases hn with | layers hl =>
    cases hl with
    | one hh =>
      obtain ⟨rest, q, hat⟩ := hlead
      exact absurd hat (Node.at_layers_nil rest q)
    | cons hh hr =>
      exact ⟨_, .layers hr, fun h hc' hs => by
        cases hc' with | layers hx =>
          cases hs; exact .layers (layersHasTy_cons (layerHasTy_ext h hh) hx)⟩

/-! ## The law -/

/-- **The law at the environment that the step function answers: the claim `focus-function`.**
A typed node splits at an address of a program into an environment and a type of the focus, and
the environment is the one that `Node.envAt` computes from the node's own. Every program of
that type in that environment, under every extension of the signature, stands in the focus's
place, and the node keeps its type. `NodeHasTy.replace` is this statement without the
function. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal NodeHasTy.replace_envAt {s : Signature Op} (path : List Nat) {n : Node Op}
    {τ : NodeTy Op} {q : Eff Op} (hn : NodeHasTy s n τ) (hat : n.at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), n.envAt s τ.env path = some (.env env) ∧ HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {n' : Node Op}, SigExtends s s' → HasTy s' env q' t →
        n.replaceAt path (.eff q') = some n' → NodeHasTy s' n' τ

/-- **The replacement law, at a node: the claim `typed-replacement`.** A typed node splits at an
address of a program into an environment and a type of the focus. Every program of that type in
that environment, under every extension of the signature, stands in the focus's place, and the
node keeps its type. The six statements below are its instances. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem NodeHasTy.replace {s : Signature Op} (path : List Nat) {n : Node Op} {τ : NodeTy Op}
    {q : Eff Op} (hn : NodeHasTy s n τ) (hat : n.at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {n' : Node Op}, SigExtends s s' → HasTy s' env q' t →
        n.replaceAt path (.eff q') = some n' → NodeHasTy s' n' τ := by
  induction path generalizing n τ with
  | nil =>
    have hnq : n = .eff q := by simpa only [Node.at_, Option.some.injEq] using hat
    subst hnq
    cases hn with
    | eff hq =>
      refine ⟨_, _, hq, fun {s' q' n'} _ hq' hrep => ?_⟩
      have hidx : (Node.eff q').ctorIdx = (Node.eff q).ctorIdx := rfl
      simp only [Node.replaceAt, if_pos hidx, Option.some.injEq] at hrep
      subst hrep
      exact .eff hq'
  | cons i rest ih =>
    cases hci : n.child i with
    | none => simp only [Node.at_, hci, Option.bind_none, reduceCtorEq] at hat
    | some c =>
      have hat' : c.at_ rest = some (.eff q) := by
        simpa only [Node.at_, hci, Option.bind_some] using hat
      obtain ⟨τc, hc, hstep⟩ := hn.child_step hci ⟨rest, q, hat'⟩
      obtain ⟨env, t, hq, hfill⟩ := ih hc hat'
      refine ⟨env, t, hq, fun {s' q' n'} hext hq' hrep => ?_⟩
      cases hrc : c.replaceAt rest (.eff q') with
      | none =>
        simp only [Node.replaceAt, hci, Option.bind_some, hrc, Option.bind_none,
          reduceCtorEq] at hrep
      | some c' =>
        have hset : n.setChild i c' = some n' := by
          simpa only [Node.replaceAt, hci, Option.bind_some, hrc] using hrep
        exact hstep hext (hfill hext hq' hrc) hset

/-- **The replacement law, at a program.** A typed program splits at an address into an
environment and a type of the focus, and every program of that type in that environment stands
in the focus's place: the whole keeps its type, under every extension of the signature. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem hasTy_replace {s : Signature Op} {env0 : TyEnv} {p q : Eff Op} {T : EffTy}
    {path : List Nat} (hp : HasTy s env0 p T) (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' p' : Eff Op}, SigExtends s s' → HasTy s' env q' t →
        (Node.eff p).replaceAt path (.eff q') = some (.eff p') → HasTy s' env0 p' T := by
  obtain ⟨env, t, hq, hfill⟩ := NodeHasTy.replace path (.eff hp) hat
  exact ⟨env, t, hq, fun hext hq' hrep => by cases hfill hext hq' hrep with | eff h => exact h⟩

/-- The replacement law, at a statement list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem stmtsHasTy_replace {s : Signature Op} {env0 : TyEnv} {inLoop : Bool} {b : Stmts Op}
    {q : Eff Op} {g : GenTy} {path : List Nat} (hb : StmtsHasTy s env0 inLoop b g)
    (hat : (Node.stmts b).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {b' : Stmts Op}, SigExtends s s' → HasTy s' env q' t →
        (Node.stmts b).replaceAt path (.eff q') = some (.stmts b') →
        StmtsHasTy s' env0 inLoop b' g := by
  obtain ⟨env, t, hq, hfill⟩ := NodeHasTy.replace path (.stmts hb) hat
  exact ⟨env, t, hq, fun hext hq' hrep => by cases hfill hext hq' hrep with | stmts h => exact h⟩

/-- The replacement law, at the entrants of a race. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem effsHasTy_replace {s : Signature Op} {env0 : TyEnv} {es : Effs Op} {q : Eff Op}
    {T : EffTy} {path : List Nat} (he : EffsHasTy s env0 es T)
    (hat : (Node.effs es).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {es' : Effs Op}, SigExtends s s' → HasTy s' env q' t →
        (Node.effs es).replaceAt path (.eff q') = some (.effs es') → EffsHasTy s' env0 es' T := by
  obtain ⟨env, t, hq, hfill⟩ := NodeHasTy.replace path (.effs he) hat
  exact ⟨env, t, hq, fun hext hq' hrep => by cases hfill hext hq' hrep with | effs h => exact h⟩

/-- The replacement law, at a fiber action. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem actionHasTy_replace {s : Signature Op} {env0 : TyEnv} {a : ActionTerm Op}
    {q : Eff Op} {T : EffTy} {path : List Nat} (ha : ActionHasTy s env0 a T)
    (hat : (Node.action a).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {a' : ActionTerm Op}, SigExtends s s' →
        HasTy s' env q' t → (Node.action a).replaceAt path (.eff q') = some (.action a') →
        ActionHasTy s' env0 a' T := by
  obtain ⟨env, t, hq, hfill⟩ := NodeHasTy.replace path (.action ha) hat
  exact ⟨env, t, hq, fun hext hq' hrep => by cases hfill hext hq' hrep with | action h => exact h⟩

/-- The replacement law, at a layer. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem layerHasTy_replace {s : Signature Op} {l : LayerTerm Op} {q : Eff Op} {L : LayerTy}
    {path : List Nat} (hl : LayerHasTy s l L) (hat : (Node.layer l).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {l' : LayerTerm Op}, SigExtends s s' →
        HasTy s' env q' t → (Node.layer l).replaceAt path (.eff q') = some (.layer l') →
        LayerHasTy s' l' L := by
  obtain ⟨env, t, hq, hfill⟩ := NodeHasTy.replace path (.layer hl) hat
  exact ⟨env, t, hq, fun hext hq' hrep => by cases hfill hext hq' hrep with | layer h => exact h⟩

/-- The replacement law, at a layer spine. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem layersHasTy_replace {s : Signature Op} {ls : LayerTerms Op} {q : Eff Op}
    {L : LayerTy} {path : List Nat} (hl : LayersHasTy s ls L)
    (hat : (Node.layers ls).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), HasTy s env q t ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {ls' : LayerTerms Op}, SigExtends s s' →
        HasTy s' env q' t → (Node.layers ls).replaceAt path (.eff q') = some (.layers ls') →
        LayersHasTy s' ls' L := by
  obtain ⟨env, t, hq, hfill⟩ := NodeHasTy.replace path (.layers hl) hat
  exact ⟨env, t, hq, fun hext hq' hrep => by cases hfill hext hq' hrep with | layers h => exact h⟩

/-- A program stands where a program stood: the replacement at an address of a program exists,
and it is a program. A step of `typed-replacement`: `check_replace` reads it, so that the law at
the checker answers the replaced program. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.replaceAt_eff {p q : Eff Op} (q' : Eff Op) {path : List Nat}
    (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ p', (Node.eff p).replaceAt path (.eff q') = some (.eff p') := by
  obtain ⟨result, hrep⟩ :=
    Node.replaceAt_exists hat (rfl : (Node.eff q').ctorIdx = (Node.eff q).ctorIdx)
  have hsort := (Node.replaceAt_spec hrep).2.1
  cases result with
  | eff p' => exact ⟨p', hrep⟩
  | stmts _ => cases hsort
  | stmt _ => cases hsort
  | action _ => cases hsort
  | effs _ => cases hsort
  | layer _ => cases hsort
  | layers _ => cases hsort

/-- **The law at the checker: the focus is checked, and not the program again.** A program that
the checker admits splits at an address into an environment and a type of the focus. For every
program that the checker admits at that type in that environment, under every extension of the
signature, the replaced program exists, and the checker admits it at the whole's type. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem check_replace {s : Signature Op} {env0 : TyEnv} {p0 : List Nat} {p q : Eff Op}
    {T : EffTy} {path : List Nat}
    (hp : Checker.check s env0 p0 p = .ok T) (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), (∀ pq, Checker.check s env pq q = .ok t) ∧
      ∀ {s' : Signature Op} {q' : Eff Op} {pq : List Nat}, SigExtends s s' →
        Checker.check s' env pq q' = .ok t →
        ∃ p', (Node.eff p).replaceAt path (.eff q') = some (.eff p') ∧
          ∀ p1, Checker.check s' env0 p1 p' = .ok T := by
  obtain ⟨env, t, hq, hfill⟩ := hasTy_replace (check_sound s p env0 p0 T hp) hat
  refine ⟨env, t, check_complete s q env t hq, fun {s' q' pq} hext hq' => ?_⟩
  obtain ⟨p', hrep⟩ := Node.replaceAt_eff q' hat
  exact ⟨p', hrep, check_complete s' p' env0 T (hfill hext (check_sound s' q' env pq t hq') hrep)⟩

end Effect4.Program
