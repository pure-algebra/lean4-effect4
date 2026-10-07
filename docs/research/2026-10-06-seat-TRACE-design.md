# 2026-10-06 seat SKETCH design: the focus function (slice TRACE, first half)

Status: a design note (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-trace-brief.md`, as amended, with decisions
row 292. Branch `seat/sketch`, after slice REPLACE (`15531103`). Lean elaborates each
declaration below, and the kernel accepts each proof at `[propext, Quot.sound]`, in the scratch
file filed as `docs/research/2026-10-06-seat-TRACE-design-probe.lean.txt`. The values of the
controls are in `docs/research/2026-10-06-seat-TRACE-design-values.lean.txt`, with its output
beside it. No file of the tree holds a declaration yet.

## 1. The question

A tool at an address asks three things: which sub-program stands there, in which environment,
at which type. The replacement law says that the last two exist
(`src/Effect4/Laws/Program/Typing/Replace.lean`). This slice computes them, and it proves that
the computed pair is the law's.

## 2. The types, as Lean elaborates them

```lean
inductive NodeEnv where                 -- what a node's typing judgment reads from above
  | env (env : TyEnv)                   -- a program, the entrants of a race, a fiber action
  | body (env : TyEnv) (inLoop : Bool)  -- a statement list, a statement
  | closed                              -- a layer, a layer spine
NodeEnv.tyEnv : NodeEnv → TyEnv         -- the variables in scope; none at a layer

Node.childEnv : Signature Op → NodeEnv → Node Op → Nat → Option NodeEnv   -- the step
Node.envAt : Signature Op → NodeEnv → Node Op → List Nat → Option NodeEnv -- its fold on a path

structure Focus (Op : Type) where       -- what stands at an address of a program
  program : Eff Op
  env : TyEnv
  ty : EffTy
focusAt : Signature Op → TyEnv → Eff Op → List Nat → Option (Focus Op)
Sketch.focusAt : Sketch → SigApp → List Nat → Option (Focus NativeOp)
```

## 3. The decisions

1. **Three shapes of environment.** The six judgments have three arities: `HasTy`, `EffsHasTy`
   and `ActionHasTy` read an environment; `StmtsHasTy` reads the loop flag too; the two layer
   judgments read nothing. `NodeEnv` has one constructor for each.
2. **The step has one case for each arm of `Node.child`**, in that function's order. It has
   one more, because the statements after a `bindYield` read the head's answer. Each case is
   the environment that the rule gives its child. Eleven cases read what the rule reads before
   the child. Eight read the type of an earlier sibling program, by `effTy`. Three read the
   type of a term of the node, by `termTy` and `Decision.arms`. A sibling with no type gives no
   environment.
3. **`focusAt` adds the checker's type.** It answers the sub-program, the environment by
   `Node.envAt` and the type by `effTy`. `Node.envAt` answers at every sort of node, and where
   the focus itself has no type. The TypeScript printer needs both. A term stands in a
   statement or in a fiber action too, and the term that it asks about can be the refused one.
4. **No table, no second checker, no monad.** `Checker.check` does not change. One call walks
   one path and checks each earlier sibling once. Those sub-programs are disjoint, so one call
   costs at most one check of the program (reading). A walk over every address costs more than
   one check: the receipt states the bound and names the linear form as a later need.
5. **A term has no address.** The printer reads the environment at the term's node and runs
   `termTy`. Four kinds of term slot read an extended environment: the test of `catchIf`, three
   terms of `iterate`, and an operation's binder term. The receipt gives the table.
6. **`NodeHasTy.child_step` gains one conjunct**: the function answers the child's environment.
   The 60 cases keep their text. The 58 with a child gain one component each: `rfl` in 47, and
   one lemma in 11. Then `NodeHasTy.replace_envAt` is one induction on the path, and `NodeHasTy.replace` is its
   corollary. The eight statements of slice REPLACE and its two laws on a sketch do not change.
7. **The word.** The dictionary's trace is the machine's list of run events. So this function is
   not called a trace: it is the focus function.

## 4. The statements

```lean
-- the step lemma of slice REPLACE, with one more conjunct
theorem NodeHasTy.child_step (hn : NodeHasTy s n τ) (hc : n.child i = some c)
    (hlead : ∃ rest q, c.at_ rest = some (.eff q)) :
    ∃ τc, NodeHasTy s c τc ∧ n.childEnv s τ.env i = some τc.env ∧
      ∀ {s' c' n'}, SigExtends s s' → NodeHasTy s' c' τc →
        n.setChild i c' = some n' → NodeHasTy s' n' τ
-- the law at the environment that the function answers: the claim `focus-function`
theorem NodeHasTy.replace_envAt (path : List Nat) (hn : NodeHasTy s n τ)
    (hat : n.at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), n.envAt s τ.env path = some (.env env) ∧ HasTy s env q t ∧
      ∀ {s' q' n'}, SigExtends s s' → HasTy s' env q' t →
        n.replaceAt path (.eff q') = some n' → NodeHasTy s' n' τ
-- the answer is the sub-program at the address, typed there; for every program
theorem focusAt_typed (hf : focusAt s env0 p path = some f) :
    (Node.eff p).at_ path = some (.eff f.program) ∧ HasTy s f.env f.program f.ty
-- at the root the answer is the checker's
theorem focusAt_nil : focusAt s env0 p [] = (effTy s env0 p).map fun t => ⟨p, env0, t⟩
-- on a typed program the function answers at every address of a program
theorem hasTy_focusAt (hp : HasTy s env0 p T) (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), focusAt s env0 p path = some ⟨q, env, t⟩
-- the replacement law at the function's answer, with no existential
theorem hasTy_replace_focusAt (hp : HasTy s env0 p T) (hf : focusAt s env0 p path = some f)
    (hext : SigExtends s s') (hq' : HasTy s' f.env q' f.ty)
    (hrep : (Node.eff p).replaceAt path (.eff q') = some (.eff p')) : HasTy s' env0 p' T
-- the same two at the checker
theorem check_focusAt (hp : Checker.check s env0 p0 p = .ok T)
    (hat : (Node.eff p).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), focusAt s env0 p path = some ⟨q, env, t⟩
theorem check_replace_focusAt (hp : Checker.check s env0 p0 p = .ok T)
    (hf : focusAt s env0 p path = some f) (hext : SigExtends s s')
    (hq' : Checker.check s' f.env pq q' = .ok f.ty) :
    ∃ p', (Node.eff p).replaceAt path (.eff q') = some (.eff p') ∧
      ∀ p1, Checker.check s' env0 p1 p' = .ok T
-- and at a sketch: the two edits, with the focus as a function
theorem Sketch.check_focusAt (hs : s.check app = .ok T)
    (hat : (Node.eff s.program).at_ path = some (.eff q)) :
    ∃ (env : TyEnv) (t : EffTy), s.focusAt app path = some ⟨q, env, t⟩
theorem Sketch.check_fill_focusAt (hs : s.check app = .ok T) (hf : s.focusAt app path = some f)
    (more : RowTable)
    (hq' : Checker.check (app.withHoles (s.holes ++ more)).signature f.env pq q' = .ok f.ty) :
    ∃ s', Sketch.fillAt { s with holes := s.holes ++ more } path q' = some s' ∧
      s'.check app = .ok T
theorem Sketch.check_omit_focusAt (hs : s.check app = .ok T) (hf : s.focusAt app path = some f)
    (name : String) (hans : f.ty.answer.closed = true) (herr : f.ty.error.closed = true)
    (hansN : f.ty.answer.normalize = f.ty.answer) (herrN : f.ty.error.normalize = f.ty.error)
    (formed : Formation.Formed (Formation.instantiatedSites
      (Row.hole name f.ty.answer f.ty.error f.ty.requires.elems).normalizeTypes [])) :
    ∃ s', s.omitAt app path (Row.hole name f.ty.answer f.ty.error f.ty.requires.elems) = some s' ∧
      s'.check app = .ok T
```

The binders are elided here, and the probe has each statement in full. Each new statement is
placed first as a planned goal with `@[semantics "initial-algebras-folds" (requirement := R14)]`
and proved in place. `NodeHasTy.child_step` is proved today, so it is never a goal: its
statement and its proof change in one commit.

## 5. Placement

Concept `initial-algebras-folds`. The claim is the registry's open part `focus-function`
(proposed; role inversion). The step function is the inversion of the typing rules at one
child, and its fold is the inversion along a path. Pointer: `NodeHasTy.replace_envAt`.

- Reach:
  - the six judgments, at every typing signature of every operation alphabet;
  - a program as the focus, at every address;
  - every extension of the typing signature;
  - `focusAt_typed` for every program, typed or not.
- It does not establish:
  - an environment under an earlier sibling that has no type: the function answers `none`
    there, and total marking is the slice that goes on;
  - the environment of a term slot as a function: the receipt gives the table;
  - a bound on a walk over every address, as a theorem;
  - any behaviour, a gap, or a focus of a smaller type.
- Consumers: `Sketch.check_fill_focusAt` and `Sketch.check_omit_focusAt` for a tool at a hole;
  the TypeScript printer at an eliminator; a slice view that walks down with the types.

## 6. The modules, and the controls

- `src/Effect4/Program/Typing/Focus.lean`, a Lean module (row 200): `NodeEnv`, the step, its
  fold, `Focus` and `focusAt`. `Sketch.focusAt` stands in `src/Effect4/Program/Sketch.lean`.
- `src/Effect4/Laws/Program/Typing/Replace.lean`: the step lemma and `NodeHasTy.replace_envAt`.
- `src/Effect4/Laws/Program/Typing/Focus.lean`: the statements on `focusAt`. The three on a
  sketch stand in `src/Effect4/Laws/Program/Sketch.lean`.
- `Test/Program/FocusControls.lean`, with these controls:
  - green: the focus at each of the seven addresses of the example of slice SKETCH;
  - proved: an omission at a focus that reads its environment, by the law;
  - the first consumer: a term of two members under `length`, read through the environment;
  - the same shape with two fiber types under a join. The checker refuses it as `notFiber`,
    and the focus has no type. The environment still answers the term's two members;
  - red: no address of a program; an earlier sibling with no type.

Not in this slice:

- any change of `Checker.check`, of `explain` or of a refusal;
- the TypeScript printer, and the conversion of an eliminator;
- a gap, a term hole, a type slice view, and total marking.
