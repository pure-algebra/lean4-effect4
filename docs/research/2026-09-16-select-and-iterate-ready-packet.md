# Ready packet: one value-decided fork (`select`) and one loop (`iterate`), with the code they retire

Written for the next slices after the option atoms, on the owner's steer of 2026-09-16: simplicity and solidity, cut code in favour of one deep module, keep the proven semantics. Everything below is drop-in against the tree at `812370b` plus the option-atoms working tree; every site named was read, and the arm shapes copy the neighbours they replace. The [constructs brief](/Users/pooks/Dev/lean4-effect4/docs/research/2026-09-16-core-constructs-brief.md) stays the design record; this packet supersedes its §2 and §3 where they differ (one constructor instead of two, the prelude print for the tag form) and refines its §4 (the loop interface).

## 0. The measurement that decides the shape

`branch` is one value-decided fork. It costs 71 lines in 18 files (`Agreement.lean` 16, generated `Fold.lean` 11, `Refs.lean` 7, `DenoteR.lean` 6, `Denote.lean` 5, `Read.lean` 5, and one or two in each of `Typing`, `Eff`, `Derived`, `Compile`, `Intro`, `Fragment`, `Sound`, `Inversion`, `HasTy`, `Handles`, `Agreement/Machine`, `Print`), plus the lemma families `suspendBodyAt_branch_{true,false,bad}`, `meaning_branch_{true,false,bad}`, `intro_branch`, `Straight.branch`, `Plain.branch`, `isBranch`, `denoteR_branch`, `compileEff_branch`, `inv_branch`, and the two TypeScript reader sites. Every one of those is the same arm with a different decision in the middle: evaluate the scrutinee once, choose child 0 or child 1, bind at most one value, `badShape` on the wrong shape.

`optionCase` and `caseTag` as two more constructors would each add the same 70-odd lines and the same lemma families: three copies of one idea. One constructor with a small `Decision` carrier costs one copy, and `branch` retires into it in S4 (the plan's redundant-syntax slice), so the tree ends with fewer lines than it has today.

The loop has the same shape of duplication in the machine: four interpreter fields (`loopTest`, `loopBody`, `loopStep`, `loopDone`) at 107 sites in 13 files, and none of them can express the refusal the plan's raw-program rule requires. Two fields can.

## 1. `select`

### 1.1 The decision carrier (new, `Program/Decision.lean` or beside `Term` in `Eff.lean`)

```lean
/-- How a value-decided fork selects its arm, and what the arm binds. One function each for
the runtime (`decide`) and the checker (`arms`); the compiler, the reference, the meaning,
`effTy` and `HasTy` all read them, so they agree by construction (the `catchIfError`
pattern). Child 0 is the arm the decision names first. -/
inductive Decision
  /-- `true` runs child 0, `false` child 1; neither binds. Today's `branch`. -/
  | bool
  /-- `none` runs child 0; `some a` runs child 1 with `a` bound. -/
  | option
  /-- A tagged pair `[tag, payload]` runs child 0 with the payload bound; every other
  value runs child 1 with the whole value bound, at the residual type (DI-39). -/
  | tag (tag : String)
deriving DecidableEq, Repr

namespace Decision

/-- The runtime selection: whether child 0 was chosen, and the value that child binds.
`none` is the wrong shape (`badShape`, as `branch` refuses a non-Boolean today). -/
def decide : Decision → Val → Option (Bool × Option Val)
  | .bool, .bool b => some (b, none)
  | .option, .none => some (true, none)
  | .option, .some a => some (false, some a)
  | .tag t, v =>
    match Val.tagPayload? t v with
    | some payload => some (true, some payload)
    | none => some (false, some v)
  | .bool, _ | .option, _ => none

/-- What child 0 and child 1 bind, from the scrutinee's type; `none` refuses the scrutinee.
`.bool` keeps `branch`'s syntactic test so the S4 retirement is an equality. -/
def arms : Decision → Ty → Option (List Ty × List Ty)
  | .bool, t => if t = .bool then some ([], []) else none
  | .option, t =>
    match t.normalize with
    | .option a => some ([], [a])
    | _ => none
  | .tag tag, t =>
    let c := t.normalize
    if Ty.taggedColumn c then (Ty.payloadTy tag c).map fun p => ([p], [Ty.diffTag tag c])
    else none

/-- How many values each child binds, for the readers' binder depth. -/
def binds : Decision → Nat × Nat
  | .bool => (0, 0)
  | .option => (0, 1)
  | .tag _ => (1, 1)

theorem arms_length (d : Decision) (t : Ty) (e0 e1 : List Ty) (h : d.arms t = some (e0, e1)) :
    (e0.length, e1.length) = d.binds := by
  cases d <;> simp only [arms, binds] at h ⊢ <;> split at h <;> simp_all

end Decision
```

The tagged-value reader, once, in `Store/Val.lean` or `Program/Typed.lean`:

```lean
/-- The payload of a tagged pair `[tag, payload]`; `none` on every other value. The one
reader of a tagged value; `NativeAtom.tagHit` is its Boolean image. -/
def Val.tagPayload? (tag : String) : Val → Option Val
  | .list [.str t, payload] => if t = tag then some payload else none
  | _ => none

theorem NativeAtom.tagHit_eq (tag : String) (v : Val) :
    NativeAtom.tagHit tag v = (Val.tagPayload? tag v).isSome := by
  cases v <;> simp [NativeAtom.tagHit, Val.tagPayload?]
  -- the list arm needs `rcases` on the two-element shape; keep `tagHit` as it is and bridge.
```

Leave `tagHit` as it is (the `catchIf` lemmas depend on its equations) and bridge with this lemma; do not redefine it.

The tag algebra beside `Ty.diffTag` (`Ty.lean:591`), over canonical types, exactly as the brief §3 states it: `taggedColumn` (no untagged product and no list among the members), `payloadTy` (the joined payloads of the members carrying the tag, `none` when there is none). `selTag` is not needed by the construct; leave it out until a consumer exists.

**The one safety theorem.** A typed scrutinee always decides, and the bound value has the arm's type:

```lean
theorem Decision.decide_typed (d : Decision) {t : Ty} {e0 e1 : List Ty} {v : Val}
    {allocated : List String}
    (harms : d.arms t = some (e0, e1)) (hv : Val.hasTy v t allocated = true) :
    ∃ first bound, d.decide v = some (first, bound) ∧
      List.Forall₂ (fun x ty => Val.hasTy x ty allocated = true)
        bound.toList (if first then e0 else e1)
```

Proof by `cases d`: `.bool` through `Val.hasTy_bool_inv` (`Laws/Program/Typed.lean:80`; it is stated at the empty table, so either generalize it to `_at` as the option one was, or normalize first); `.option` through `Val.hasTy_option_inv_at`, which the option-atoms working tree adds today at exactly the allocation-aware form this needs; `.tag` through the one new value lemma `payload_hasTy` (`taggedColumn c → Val.hasTy v c → Val.tagPayload? tag v = some p → payloadTy tag c = some P → Val.hasTy p P`, via `Val.hasTy_prod_inv_at` from `23c7ba9` and `hasTy_join_left/right`) and `Ty.diffTag_sound` for the miss. This theorem is the whole "no `badShape` on an admitted program" story for the construct, and the only place the three decisions are ever proved about separately.

### 1.2 The constructor (`Eff.lean`, appended after `catchIf`; no stored bytes move)

```lean
    /-- A value-decided fork, `branch` generalized: the scrutinee is evaluated once at the
    fork's environment, `decision.decide` selects child 0 or child 1 and the value that
    child binds (`Decision`). Child 0 and child 1 are typed at the environment extended by
    `decision.arms`. Printed as `t ? a : b`, `Option.match(s, { onNone, onSome })` or the
    prelude's `caseTag(s, "A", hit, miss)` by the decision. -/
    | select (scrutinee : Term) (decision : Decision) (arm0 arm1 : Eff Op)
```

(`by` cannot be a field name; `decision` is.) `Eff.weaken`: `| .select s d a0 a1 => .select (Term.weaken cut s) d (Eff.weaken cut a0) (Eff.weaken cut a1)`.

### 1.3 One point helper (`Compile.lean`, after `childWith2`)

```lean
/-- The point of child `i` with an optional value bound: `child` or `childWith`. -/
def childBind (p : Point) (i : Nat) : Option Val → Point
  | none => p.child i
  | some v => p.childWith i v
```

Every lemma the `bind` and `branch` arms use about `child`/`childWith` (`weight_child_lt`, `weight_childWith_lt`, `at_child_of`, `Point.childWith_fuel`) gives the `childBind` form by `cases` on the option; state the three that the proofs below need and no more.

### 1.4 Typing (`Typing.lean`, the arm; `HasTy.lean`, the rule)

```lean
    | .select s d a0 a1 => do
      let t ← termTy sig env s
      let (e0, e1) ← d.arms t
      let t0 ← effTy sig (env ++ e0) a0
      let t1 ← effTy sig (env ++ e1) a1
      let answer ← EffTy.joinAnswer t0.answer t1.answer
      some ⟨answer, t0.error.join t1.error, t0.requires.union t1.requires⟩
```

```lean
  /-- A value-decided fork: the arms are typed at the environments `Decision.arms` gives,
  their answers join as the least upper bound, both arms' errors and requirements are in the
  conclusion. `branch` is the `.bool` instance. -/
  | select {env : TyEnv} {s : Term} {d : Decision} {a0 a1 : Eff Op} {t : Ty}
      {e0 e1 : List Ty} {t0 t1 : EffTy} {answer : Ty} :
      termTy sig env s = some t →
      d.arms t = some (e0, e1) →
      HasTy sig (env ++ e0) a0 t0 →
      HasTy sig (env ++ e1) a1 t1 →
      EffTy.joinAnswer t0.answer t1.answer = some answer →
      HasTy sig env (.select s d a0 a1)
        ⟨answer, t0.error.join t1.error, t0.requires.union t1.requires⟩
```

- `inv_select` (`Inversion.lean`): the statement of `inv_branch` with the `arms` conjunct; the proof `refine Option.of_triple ?_; simp only [effTy]; mvcgen; all_goals simp_all` is the neighbours'. If `mvcgen` stops at the pair pattern, `rcases` the `arms` result before it.
- `effTy_sound`: `exact .select hs harms (effTy_sound sig a0 _ t0 h0) (effTy_sound sig a1 _ t1 h1) hj`.
- `effTy_weaken` (`Typing.lean:688`): add `.select _ _ _ _` to the alternative list; `arms` reads no environment, so the existing simp set (`termTy_weaken`, `List.append_assoc`, `effTy_weaken`) closes it as it closes `bind`'s `env ++ [answer]`.
- `Typing/Specs` (generated): `make gen-specs` if the group lists constructor rules.

### 1.5 Compile and reference

`compileEff`: `| .select _ _ _ _ => Prim.suspend (EffThunk.body p)`. `suspendBodyAt`:

```lean
      | some (Node.eff (.select s d _ _)) =>
        match (evalTerm p.env s).bind d.decide with
        | some (first, bound) => resolve root (p.childBind (cond first 0 1) bound)
        | none => badShape
```

Two lemmas replace `branch`'s three (`Agreement.lean:1352-1380`):

```lean
theorem suspendBodyAt_select_of_decide {root : NativeEff} {q : Point} {k : Nat} {s : Term}
    {d : Decision} {a0 a1 : NativeEff} {first : Bool} {bound : Option Val} (hf : q.fuel = k + 1)
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.select s d a0 a1)))
    (hd : (evalTerm q.env s).bind d.decide = some (first, bound)) :
    suspendBodyAt root (EffThunk.body q) = resolve root (q.childBind (cond first 0 1) bound) := by
  simp [suspendBodyAt, hf, h, hd]

theorem suspendBodyAt_select_bad … (hd : (evalTerm q.env s).bind d.decide = none) :
    suspendBodyAt root (EffThunk.body q) = badShape := by
  simp [suspendBodyAt, hf, h, hd]
```

`suspendBodyAt_of_at` (`Agreement.lean:1389`) gains the premise `hnsel : ∀ s d a b, e ≠ .select s d a b`; the classifier `isBranch` (`:1555`) answers `true` on `select` too (rename it `isFork` when `branch` goes).

Reference (`DenoteR.lean`, beside the `branch` arm at `:614`):

```lean
  | .select s d a0 a1, p => suspendR p (constructR fun completed =>
      match (evalTerm p.env s).bind d.decide with
      | some (true, bound) => rec a0 ({ p with completed }.childBind 0 bound)
      | some (false, bound) => rec a1 ({ p with completed }.childBind 1 bound)
      | none => .pure badShapeExit)
```

`denoteR_select` is `denoteR_branch` (`:846`) with this body; the proof `cases hf : p.fuel with | zero => exact (h hf).elim | succ f => budget hf` is unchanged. `intro_select` (`Intro.lean`, from `intro_branch` at `:1815`) takes both `hwc` and `hwcw` (the dispatch at `:2240-2246` already builds both); after `rcases hd : (evalTerm p.env s).bind d.decide with _ | ⟨first, bound⟩`, `cases first` and `cases bound` give four `resolve_of_at` steps of the `branch` shape, or two if `childBind` is kept opaque and its `at_`/weight lemmas are used. `Handles.lean:686` and `Agreement/Machine.lean:169`: the `branch` arms verbatim.

### 1.6 Meaning (the straight fragment)

`Fragment.lean`: `| .select _ a b => Straight a && Straight b`. `Denote.lean`:

```lean
  | .select s d a0 a1, env =>
    match (evalTerm env s).bind d.decide with
    | some (first, bound) => denote (cond first a0 a1) (env ++ bound.toList)
    | none => pure badShapeExit
```

Two equations replace `meaning_branch_{true,false,bad}` (`:257-275`):

```lean
theorem meaning_select_of_decide (s : Term) (d : Decision) (a0 a1 : NativeEff) (env : List Val)
    (st : Stores) (first : Bool) (bound : Option Val)
    (hd : (evalTerm env s).bind d.decide = some (first, bound)) :
    meaning (.select s d a0 a1) env st = meaning (cond first a0 a1) (env ++ bound.toList) st := by
  unfold meaning; simp only [denote, hd]

theorem meaning_select_bad … (hd : (evalTerm env s).bind d.decide = none) :
    meaning (.select s d a0 a1) env st = (badShapeExit, st) := by
  unfold meaning; simp only [denote, hd]; rfl
```

`Straight.select`, `Plain`, `Plain_eq_Straight`, `depth`, `steps` (`Agreement.lean:40-135`): the `branch` arms verbatim. The straight-agreement arm (`DenoteR.lean:1475`): the `branch` arm, with `rcases hd` in place of `split` and `cases first`. The plain-program step bound (`Agreement.lean:1748`): the `branch` arm with `childBind`, since `depth` and the child fuel are the same for both children.

### 1.7 The rest of the owners

- `Refs.lean` (`:74`, `:136`, `:243`, `:306`, `:398`): the five `branch` arms with `select s d`.
- `Derived.lean`, `Fold.lean`: generated. Add `Effect4.Program.Decision` to the `Program` and `Fold` carrier lists in `tools/Effect4Gen/manifest.json` and run `make gen`; `select` becomes ctor 27 (`Wire.lean`: appended, nothing moves), `Eff_select of term * decision * eff * eff` in `ocaml/eff/eff_types.ml` through `gen-eff`, `ts/eff/eff.gen.ts` through `gen-ts`.
- The conformance policy (`tools/Conform/Effect4/cases-policy.json`): none of the new arms has a `_ =>` default; nothing to list.

### 1.8 Printed forms and the readers

- `.bool`: `branch`'s image, unchanged: `Effect.suspend(() => t ? a : b)`. So retiring `branch` changes no golden, no corpus module and no tape.
- `.option`: `Effect.suspend(() => Option.match(s, { onNone: () => a0, onSome: (aN) => a1 }))`, in the carrier as `.call (.ident "Effect.suspend") [.arrow none (.call (.ident "Option.match") [printTerm s, .object [("onNone", .arrow none a), ("onSome", .lambda [Var.name n] b)]])]`. `Option` is already in every generated module's import line (`harness/truth/generated/*.ts:3`), and `Option.match` is the dual at the pin (`Option.ts:403`). Reader (`Read.lean:396`): one `readHead` arm under `.suspend`, placed before the generic `[.arrow none body]` arm, matching that object with the two field names and the binder `Var.name n`; `readable`: `s.scoped n && readable n a0 && readable (n + 1) a1`. `read.ts:1037`: the same test inside `readSuspend` before the `suspend` fallthrough, and a `select` case in the zipper at `:1463`.
- `.tag t`: the pinned carrier (`.lake/packages/typescript/TypeScript/Syntax.lean:24-107`) has no index expression, no equality and no `&&`, so the inline narrowing print of brief §3 needs three constructors in another package. Print through the prelude instead, with the same call shape as `Option.match`:

  ```ts
  export const caseTag = <T, K extends string, A, B>(
    value: T, tag: K,
    hit: (payload: Extract<T, readonly [K, unknown]>[1]) => A,
    miss: (rest: Exclude<T, readonly [K, unknown]>) => B,
  ): A | B => Array.isArray(value) && value[0] === tag ? hit((value as any)[1]) : miss(value as any)
  ```

  printed `Effect.suspend(() => caseTag(s, "A", (aN) => hit, (aN) => miss))`. The host's `Extract` is the selected members, its `[1]` is `payloadTy` (a union of payloads), `Exclude` is `diffTag`; they narrow exactly when `T` is a union of literal-tagged tuples and scalars, which is `taggedColumn`. The plan's preflight correction (`Array.isArray` refines to a mutable `any[]`) is the reason the types come from the conditional types on `T` and not from the runtime test: the test only selects, `Extract`/`Exclude` narrow. Confirm on the two-tag, repeated-tag and bare-scalar controls under strict type-check before freezing the row; those three are the target rule's evidence. The readers match the head `caseTag` with a string literal and two one-parameter lambdas at `n`.
- `Read.lean` proofs (`readable_weaken :3198`, `read_print :1774`, `print_readable :3277`): the `branch` arms with the binder depths from `Decision.binds`.

### 1.9 What S4 then deletes

`branch t a b ↦ select t .bool a b` is an equality of typing (`arms .bool` is `branch`'s test verbatim), of meaning (`decide .bool` is `branch`'s match), and of printed image; only the canonical bytes move (ctor 15 to 27), a wire re-pin under S1 policy. After it, the 71 `branch` lines and the ten lemma families named in §0 go, and the tree has one fork.

On the ordinals: `select` takes the next unretired tag of the current namespace (27 today), and when `branch` retires its 15 joins the retired set and is never reused. That is the rule S1 has to fix first, since the retired `choose` held 23 and `provideLayer` now holds 23 (Codex's progress note of 06:57), so the current namespace cannot define retirement by ordinal alone.

## 2. `iterate`

### 2.1 The loop interface: two fields instead of four

`PrimInterp` (`Frames.lean:262-271`) carries `loopTest : ν → β → Bool`, `loopBody : ν → β → κ`, `loopStep : ν → β → β → β`, `loopDone : ν → β`. The plan's raw-program rule (§3.8: a non-Boolean test, a failed step or a failed result is `badShapeExit`) cannot be expressed through them: a Boolean test has no refusal, a `β`-valued step has none, and `loopDone` cannot see the cursor or fail, since the frame wraps its answer in `success` (`Frames.lean:880`). Today's fallbacks are silent (`interpOf`, `Compile.lean:1357-1375`: a test that is not `true` stops, a failed step keeps the cursor, the answer is `unit`). What follows is the code-returning completion boundary with both clauses, initial and back-edge, that the plan's preflight correction of 2026-09-16 asks for; the brief's `β`-valued `loopDone` is withdrawn.

```lean
/-- What a loop does next: run the body under the frame at a cursor, or finish with a code. -/
inductive LoopNext (κ β : Type)
  | continue (cursor : β) (body : κ)
  | finish (code : κ)

  /-- Entering at the initial cursor: the test, then the body or the final code. -/
  loopEnter : ν → β → LoopNext κ β
  /-- Resuming with the previous cursor and the body's answer: the step, the test, then the
  body or the final code. A refusal is a finishing failure code. -/
  loopResume : ν → β → β → LoopNext κ β
```

Frame arm (`Frames.lean:876-880`):

```lean
  | whileLoop loop cursor, value, _ =>
    match interp.loopResume loop cursor value with
    | .continue next body => some (body, [whileLoop loop next])
    | .finish code => some (code, [])
```

and the entry (`:2506-2512`) the same over `loopEnter loop cursor`. The interpreter (`Compile.lean:1357-1375`) becomes one function, mirrored by nothing, since `InterpR` copies the fields (`InterpR.lean:290-296`):

```lean
/-- The loop at a point from a cursor: the test chooses the body at `childWith 0 cursor` or
the `result`; a malformed test or result is `badShape`. -/
def loopNextAt (root : NativeEff) (p : Point) (cursor : Val) : LoopNext NCode Val :=
  match loopAt root p with
  | some (test, _, result, _) =>
    match evalTerm (p.env ++ [cursor]) test with
    | some (Val.bool true) => .continue cursor (resolve root (p.childWith 0 cursor))
    | some (Val.bool false) =>
      match evalTerm (p.env ++ [cursor]) result with
      | some v => .finish (Prim.success v)
      | none => .finish badShape
    | _ => .finish badShape
  | none => .finish badShape

  loopEnter := fun
    | .loop p, cursor => loopNextAt root p cursor
    | _, cursor => .finish (Prim.success cursor)
  loopResume := fun
    | .loop p, cursor, answer =>
      match loopAt root p with
      | some (_, step, _, _) =>
        match evalTerm (p.env ++ [cursor, answer]) step with
        | some next => loopNextAt root p next
        | none => .finish badShape
      | none => .finish badShape
    | _, cursor, _ => .finish (Prim.success cursor)
```

(`loopAt` returns `(test, step, result, body)` once `iterate` exists.) The sites, all mechanical: `Frames.lean` 21, `Simulation/Hooks.lean` 20, `Simulation/Walk.lean` 13, `Laws/Machine/Handles.lean` 11 (the key bound `loopDone : ∀ n, (interp.loopDone n).keys ⊆ nk n` becomes a bound on the cursor and code of `loopEnter`/`loopResume`), `Simulation/Evaluate.lean` 7, `EvaluateR.lean` 7, `InterpR.lean` 6, `Program/Handles.lean` 6, `Compile.lean` 5, `Typing/Sound.lean` 5, `Stores.lean` 4, `Guard/{FrameOwned,Core}.lean` 1 each. Every `loopTest … = true` premise becomes `loopResume … = .continue next body`, every `= false` becomes `= .finish code`; `step_whileLoop_true/false` (`Evaluate.lean:300-306`) and `armA_whileLoop_stop` (`Frames.lean:1277`) are restated the same way.

The smaller cut, if this is judged too wide for one slice: only `loopDone : ν → β → κ`, with `result` evaluated there and the test re-checked so a malformed test refuses; the failed-step fallback stays silent and the register records the difference from the plan's rule. Recommendation: the two-field cut, because the same sites are otherwise touched twice (now for `loopDone`, again in S4 for the rule) and because the raw-program rule then lives in one function.

### 2.2 The constructor and its rule

Brief §4 as written: `| iterate (cursorTy : Ty) (initial test step result : Term) (body : Eff Op)`, the typing with `Ty.sub c0.normalize c.normalize ∧ Ty.sub c1.normalize c.normalize` at the annotation, `hasTy_sub` (`Program/Typed.lean:131`) as the invariant carrier across iterations, `iter` with `iter_succ` and `iter_uniform` as the only home of the budget. `whileLoop i t s b ↦ iterate c i t s (Term.lit .unit) b` with `c := termTy sig env i` is the S4 typed rewrite; its `effTy` equality is by unfolding (`sub_refl` at the annotation), its meaning equality is `iter_uniform` at `h := id`.

The printed annotation needs no carrier change either: the pinned carrier has `letDefinite (name) (type)` and `assign`, so `let aN: T; aN = initial;` is two existing statements, and the readers recognize the pair. The plan's annotation grammar (§3.8) and F3's reader still apply to `T`.

### 2.3 Nesting and the unfinished carrier

The plan's preflight correction is right that `iter_uniform` says nothing about nesting; it is cursor transport (the unit loop's migration, an index cursor against an `uncons` cursor). Nesting is carried by the answer type, not by a loop law. The budgeted meaning of the loop-bearing fragment answers `Option ExitV`, the plan's `(Option Exit × Stores)` once run through the store handler: `none` is "the budget ended inside", with every store written so far retained.

```lean
/-- The loop-bearing fragment at a budget: `none` is an unfinished program, its stores kept. -/
def denoteB (k : Nat) : NativeEff → List Val → Effects.Program StoreSig (Option ExitV)
  | .bind a b, env => (denoteB k a env).bind fun
    | none => pure none
    | some (.failure c) => pure (some (.failure c))
    | some (.success v) => denoteB k b (env ++ [v])
  | .iterate _ initial test step result body, env =>
    match evalTerm env initial with
    | some c₀ => iter (fun c =>
        match evalTerm (env ++ [c]) test with
        | some (.bool true) => (denoteB k body (env ++ [c])).map fun
          | none => .inl none
          | some (.failure cause) => .inl (some (.failure cause))
          | some (.success a) =>
            match evalTerm (env ++ [c, a]) step with
            | some c' => .inr c'
            | none => .inl (some badShapeExit)
        | some (.bool false) => pure (.inl (some ((evalTerm (env ++ [c]) result).elim badShapeExit .success)))
        | _ => pure (.inl (some badShapeExit))) k c₀
    | none => pure (some badShapeExit)
  | e, env => if Straight e then (denote e env).map some else pure (some outsideExit)
```

(`iter` at `Y := Option ExitV`, so an unfinished inner body is `.inl none` and stops the outer loop unfinished.) Three lemmas carry everything the plan's nesting clause asks for, and none of them mentions two loops: `denoteB_bind_none` (an unfinished first program leaves the sequence unfinished at the first program's stores, by the `bind` arm), `denoteB_straight` (`Straight e → denoteB k e env = (denote e env).map some`, so every straight-fragment theorem is a corollary, as the plan requires), and `denoteB_mono` (a `some` answer at `k` is the same `some` at every larger `k`, by induction on `iter`, the end-state note's `runLoop_mono` at this carrier). The relation to the machine stays existential (`Suffices_mono`: a fuel from which every larger fuel gives the same exit and stores); no syntactic step formula is claimed for nested loops.

## 3. Two lines for the option-atoms slice in flight

- `Val.hasTy_option_inv_at` at the allocation-aware form is `Decision.option`'s half of `decide_typed`; keep it exactly as it is in the working tree.
- `typeOf` for `.isSome` and `.getOrElse` match `.option _` syntactically, while `Decision.option.arms` matches `t.normalize`; `union (option a) never` and a bare `never` type through one and not the other. `| .isSome, [a] => match a.normalize with | .option _ => some .bool | _ => none`, and `getOrElse` on `a.normalize`, make the atoms and the eliminator agree on what an option type is. The checker admits more, never less, so nothing typed today changes. Optional in this slice; one line each.

## 4. Order

0. **Three refactors on the tree as it is, before the constructor exists**, each its own commit, built and checked before the next (ruling of 2026-09-16, `2026-09-16-algebraic-reading-assessment-and-order-ruling.md`; the register's B17, B5 and B6 attached them to this slice, and doing them first means `select` pays one row each instead of one arm each).
   - (a) B17, the binder table. It already exists: `childLevel` in `Laws/Codegen/HoistingReadable.lean:45`, private, eleven rows over `Node`, one consumer (`nodeReadable_child` and the two lemmas after it). Promote it to `Node.binders : Node Op → Nat → Nat` in `Program/Refs.lean` beside `Node.child` (values bound at child `i`), with the layer reset stated as its own fact (`Node.resetsLevel`, true for `layer (.effect _ _)` and `layer (.effectDiscard _)` at child 0), so that `childLevel n node i = if resetsLevel node i then 0 else n + binders node i` is the definition `HoistingReadable.lean` keeps. `select` adds one row: child 1 binds `decision.arms`' count (0 for `.bool`, 1 for `.option` and `.tag`). Owners that count binders (`readable`, `readEff`, `print`, `Test/Program/Gen.lean`, `Point.childBind`) read the table in every arm touched from now on, starting with `select`'s; `effTy` keeps the types and `Point.childWith` the values, each with one length lemma against the table. Do not rewrite the untouched literal arms (46 sites in `Read.lean`, 11 in `Print.lean`, 8 in `Gen.lean`) in this commit; state the residual count in the commit body.
   - (b) B5, delete `Plain`. `Agreement.lean:33` defines it and `:52` proves `Plain_eq_Straight`; `Straight` (`Fragment.lean:20`) is the one classifier and `Denote.lean:140-168` already has `Straight.suspend`, `.bind`, `.branch`, `.exit`, `.catchCause`, `.matchCause`, `.onExit`, `.perform_sync`. Port the three that have no twin (`Plain.not_gen`, `.not_whileLoop`, `.not_provideLayer`) to `Straight.*`, rewrite the consumer sites (`Agreement.lean`, about 20; `Agreement/Machine.lean`, about 25, including `plainCode_compileEff` and `NodePlain`; `RuntimeR.lean:280,293` and `Machine.lean:1807`, where the `rw [Plain_eq_Straight]` bridges disappear), and delete the definition, the equation and the eleven `Plain.*` lemmas. `PlainCode`, `PlainFrame`, `PlainStack`, `PlainName`, `NodePlain`, `PlainHead` (`Simulation/Evaluate.lean:455`) and `layersPlain` (`Codegen/Admit.lean:48`) are code-level and declaration-level predicates, not copies of `Straight`; they stay.
   - (c) B6, `Eff.suspendDecided : NativeEff → Bool`, true exactly for the forms `suspendBodyAt` decides itself (`suspend`, `branch`, `gen`, `whileLoop`, `provideLayer`; `select` joins when it lands), used inside `suspendBodyAt`'s match and as the single premise of `suspendBodyAt_of_at` (`Agreement.lean:1389`) in place of its five negative premises; `isBranch` (`:1555`) and `not_branch_of_isBranch_false` deleted; the two call sites that spell the five premises (`Agreement/Machine.lean:295-296` and the one in `Agreement.lean`) shrink to one argument.
1. `Decision`, `Val.tagPayload?`, the tag algebra, `decide_typed`. Pure, no machine, one new value lemma.
2. The constructor, `weaken`, the typing arm, the `HasTy` rule, `inv_select`, the `sound` arm, the `effTy_weaken` alternative; the `Node.binders` row, the `Straight` arm, the `suspendDecided` arm.
3. `childBind` (over the table's entry), compile, reference, meaning, the lemma families (two each), `intro_select`, the fragment and agreement arms.
4. Print, the two readers, `make gen`, the three controls for the tag print under strict type-check.
5. The loop interface cut, then `iterate`, then the `whileLoop` rewrite; `branch`'s rewrite and deletion in S4 with the wire re-pin.

## 5. Lanes and generators the packet must name (added 2026-09-16)

The plan's packet checklist (§5) asks for these per changed constructor; §1.7 above named only the wire and the conformance policy.

- **Generator.** `Test/Program/Gen.lean` needs a draw arm for `select` under all three decisions, or the derived constructor-coverage guard (`Gen.lean:17`, the `EffC` block of `Derived.lean`) fails. The pre-change corpus programs stay as controls; `harness/truth/corpus-results.tsv` changes only through the documented promotion, never by regenerating both sides of the comparison.
- **Every generated group.** `make gen` regenerates `Derived.lean`, `Fold.lean`, the OCaml `eff_types.ml` and goldens, the LCNF emission that becomes the engine (`ocaml/gen/*_gen.ml`) and `ts/eff/eff.gen.ts`; then `make check-gen` refuses any drift.
- **Wire.** Constructor tags are declaration positions (`Program/Wire.lean:16`), which is why `select` appends after `catchIf` and moves nothing, and why `branch`'s deletion (step 5) shifts every later tag and waits for S1.
- **Lanes.** After step 3: `make check` and `make check-ocaml` (the engine projection changed). After step 4: `make check-target` (the tag print's oracle row, B10), `make check-truth`, `make check-corpus`, and `make check-ingest-smoke` once the two TypeScript readers change. Report every number; a lane not run is reported as not run.
