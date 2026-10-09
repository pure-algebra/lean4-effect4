import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Program.DenoteRowsR

/-!
# Program.Agreement.Calls — one fiber with host calls, run under a reply tape

Slice H8 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310), by the frame
machine's route: the local run of `Program/Agreement.lean`, with the host calls of the fragment
`StraightRows` answered from a reply tape. A host call, as the compile writes it, is an external
registration (`asyncRoute`); the local run with calls (`localRunC`) gives it the answer that the
machine's answer decision prepares from the next exit of the reply tape (`prepareExternalAnswer`),
and waits when the tape is empty (`RunEnd.waits`). Every other step is the local step.

**The law** (`localRunC_compile`): a program of the fragment, compiled at an address of the root
and run with calls from any outer stack, goes where its meaning under the reply tape goes
(`meaningRows`, `Laws/Program/DenoteRows.lean`): to its exit's fiber over its stores with the
replies left, or, when the meaning is the frontier, to a host call with no reply left. At an
address the compile budget does not reach, the run may instead diverge at the compile's frontier
(`Diverges`). It is a step of `denoteRows_eq_session` (`Laws/Api/SessionMeaning.lean`); concept
`translation-simulation`, requirement R6. It says nothing of the command loop, which
`Agreement/Hosted.lean` relates to this run, nor of a second fiber, a scope or a loop.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Sched

variable {table : RowTable}

/-! ## The local run with calls -/

/-- A row answer that is no handle takes the value as it is, and allocates nothing. -/
theorem externalValue_data {ty : Ty} (hty : ∀ t, ty ≠ .handle t) {alloc : List String}
    {value : Val} {av : List String × Val} (hv : externalValue ty alloc value = some av) :
    av = (alloc, value) := by
  unfold externalValue at hv
  split at hv
  next target index => exact absurd rfl (hty target)
  next =>
    split at hv
    · cases hv
      rfl
    · cases hv

/-- **The answer at a data row is the reply's exit**, over the stores as they were: what the
machine's answer decision prepares (`prepareExternalAnswer`) for a host call of a row whose
answer is no handle. A step of `localRunC_compile`. -/
theorem prepareExternalAnswer_data {j : Nat} (hrow : dataRow table j = true) (v : Val)
    (w : List Nat) (ex : ExitV) (s : Stores) :
    prepareExternalAnswer table (some (Prim.async (EffName.external (.external j) v w) false none))
      (.ofExit ex) s = (s, Prim.ofExit ex) := by
  have hj := lt_of_dataRow hrow
  have hne : table.isEmpty = false := by
    cases table with
    | nil => simp only [List.length_nil, Nat.not_lt_zero] at hj
    | cons _ _ => rfl
  unfold dataRow at hrow
  rcases hr : externalRow table j with _ | row
  · rw [hr] at hrow
    cases hrow
  · rw [hr] at hrow
    cases ex with
    | success value =>
      simp only [prepareExternalAnswer, hne, hr, Bool.false_eq_true, if_false]
      cases hv : externalValue row.answer s.externals.allocated value with
      | none => rfl
      | some av =>
        -- a data row's answer is no handle: the value comes back as it is, nothing allocated
        have hav := externalValue_data (fun t ht => by
          simp only [ht, Bool.false_eq_true] at hrow) hv
        subst hav
        rfl
    | failure c =>
      simp only [prepareExternalAnswer, hne, Bool.false_eq_true, if_false]
      rfl

/-- **One local step with calls.** A host call takes the next exit of the reply tape, and the
fiber goes on with the answer the machine's answer decision prepares from it
(`prepareExternalAnswer`; at a data row, the exit itself over the same stores,
`prepareExternalAnswer_data`); with no reply left, the call is the frontier (`none`). Every
other step is the local step, and reads no reply. -/
def localStepC (table : RowTable) (root : NativeEff) (fr : NFiber) (s : Stores) (r : ReplyTape) :
    Option (LocalStep × ReplyTape) :=
  if IsCall fr.current then
    match r with
    | [] => none
    | ex :: rest =>
      let answer := prepareExternalAnswer table (some fr.current) (.ofExit ex) s
      some (.running { fr with current := answer.2 } answer.1, rest)
  else some (localStep root fr s, r)

/-- Where the local run with calls stops within its budget: the fiber's exit with its stores and
the replies left, or a host call with no reply left, where it waits. -/
inductive RunEnd where
  | exit (ex : ExitV) (s : Stores) (r : ReplyTape)
  | waits

/-- The local run with calls: `n` steps at most; where it stops, or `none` when the steps run
out first. -/
def localRunC (table : RowTable) (root : NativeEff) :
    Nat → NFiber → Stores → ReplyTape → Option RunEnd
  | 0, _, _, _ => none
  | n + 1, fr, s, r =>
    match localStepC table root fr s r with
    | some (.running fr' s', r') => localRunC table root n fr' s' r'
    | some (.finished ex s', r') => some (.exit ex s' r')
    | none => some .waits

/-- **A relation on final observations**: at every budget, the local run with calls from `fr`
given `c` more steps stops where the run from `fr'` stops (`RunEnd`), or neither stops. It is no
path: two waiting calls over different stores relate (the H8 review, finding H8R-01). A run that
waits and a run that diverges do not relate: the first stops with `RunEnd.waits`. -/
def ReachesC (table : RowTable) (root : NativeEff) (c : Nat) (fr : NFiber) (s : Stores)
    (r : ReplyTape) (fr' : NFiber) (s' : Stores) (r' : ReplyTape) : Prop :=
  ∀ n, localRunC table root (n + c) fr s r = localRunC table root n fr' s' r'

theorem ReachesC.refl (table : RowTable) (root : NativeEff) (fr : NFiber) (s : Stores)
    (r : ReplyTape) : ReachesC table root 0 fr s r fr s r := fun _ => rfl

theorem ReachesC.trans {root : NativeEff} {c₁ c₂ : Nat} {fr₁ fr₂ fr₃ : NFiber}
    {s₁ s₂ s₃ : Stores} {r₁ r₂ r₃ : ReplyTape} (h₁ : ReachesC table root c₁ fr₁ s₁ r₁ fr₂ s₂ r₂)
    (h₂ : ReachesC table root c₂ fr₂ s₂ r₂ fr₃ s₃ r₃) : ReachesC table root (c₁ + c₂) fr₁ s₁ r₁ fr₃ s₃ r₃ := by
  intro n
  rw [← Nat.add_assoc, Nat.add_right_comm, h₁, h₂]

/-- A step that is no call reads no reply. -/
theorem ReachesC.step {root : NativeEff} {fr fr' : NFiber} {s s' : Stores}
    (h : localStep root fr s = .running fr' s') (hc : IsCall fr.current = false) (r : ReplyTape) :
    ReachesC table root 1 fr s r fr' s' r := by
  intro n
  show localRunC table root (n + 1) fr s r = _
  simp only [localRunC, localStepC, hc, Bool.false_eq_true, if_false, h]

/-- Two fibers that are no call and take the same next step reach each other for free. -/
theorem ReachesC.same {root : NativeEff} {fr fr' : NFiber} (s : Stores) (r : ReplyTape)
    (h : ∀ s, localStep root fr s = localStep root fr' s) (hc : IsCall fr.current = false)
    (hc' : IsCall fr'.current = false) : ReachesC table root 0 fr s r fr' s r := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simp only [localRunC, localStepC, hc, hc', Bool.false_eq_true, if_false, h]

/-- **A host call takes the next reply**, as the answer its preparation gives. -/
theorem ReachesC.answer {root : NativeEff} {fr : NFiber} (s : Stores) (hc : IsCall fr.current = true)
    (ex : ExitV) (rest : ReplyTape) {s' : Stores} {code : NCode}
    (hp : prepareExternalAnswer table (some fr.current) (.ofExit ex) s = (s', code)) :
    ReachesC table root 1 fr s (ex :: rest) { fr with current := code } s' rest := by
  intro n
  show localRunC table root (n + 1) fr s (ex :: rest) = _
  simp only [localRunC, localStepC, hc, if_true, hp]

theorem isCall_ofExit (ex : ExitV) : IsCall (Prim.ofExit ex) = false := by cases ex <;> rfl

/-- **Where the local run with calls goes for an outcome of the meaning.** For an exit with its
stores and the replies left, it reaches the exit's fiber over the stack `K` with mask `i`; for
the frontier, it reaches a host call with no reply left. -/
def RunsTo (table : RowTable) (root : NativeEff) (K : List NCode) (i : Bool) (fr : NFiber) (s : Stores) (r : ReplyTape) :
    Option ((ExitV × Stores) × ReplyTape) → Prop
  | some ((ex, s'), r') => ∃ c, ReachesC table root c fr s r (fiberOf (Prim.ofExit ex) K i) s' r'
  | none => ∃ c fr' s', ReachesC table root c fr s r fr' s' [] ∧ IsCall fr'.current = true

/-- A run that reaches a fiber goes where that fiber's run goes. -/
theorem RunsTo.pre {root : NativeEff} {K : List NCode} {i : Bool} {c : Nat} {fr fr₁ : NFiber}
    {s s₁ : Stores} {r r₁ : ReplyTape} (h : ReachesC table root c fr s r fr₁ s₁ r₁) :
    ∀ {o : Option ((ExitV × Stores) × ReplyTape)}, RunsTo table root K i fr₁ s₁ r₁ o → RunsTo table root K i fr s r o
  | some ((_, _), _), ⟨c', h'⟩ => ⟨c + c', h.trans h'⟩
  | none, ⟨c', fr', s', h', hc⟩ => ⟨c + c', fr', s', h.trans h', hc⟩

/-- The frontier names no stack. -/
theorem RunsTo.frontier {root : NativeEff} {K K' : List NCode} {i i' : Bool} {fr : NFiber}
    {s : Stores} {r : ReplyTape} (h : RunsTo table root K i fr s r none) : RunsTo table root K' i' fr s r none := h

/-! ## The compile's frontier: where the local run diverges -/

/-- The compile's frontier: a suspension at an address the compile budget does not reach
(`compileEff_at_zero`). Its body is the frontier again (`suspendBodyAt_zero`). -/
def AtFrontier (fr : NFiber) : Prop :=
  ∃ (q : Point) (K : List NCode) (i : Bool), q.fuel = 0 ∧ fr = fiberOf (frontier q) K i

/-- **The local run with calls diverges**: it reaches the compile's frontier, where it stays
(`localRunC_frontier`). -/
def Diverges (table : RowTable) (root : NativeEff) (fr : NFiber) (s : Stores) (r : ReplyTape) :
    Prop :=
  ∃ c fr' s' r', ReachesC table root c fr s r fr' s' r' ∧ AtFrontier fr'

theorem Diverges.pre {root : NativeEff} {c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores}
    {r r₁ : ReplyTape} (hd : Diverges table root fr₁ s₁ r₁)
    (h : ReachesC table root c fr s r fr₁ s₁ r₁) : Diverges table root fr s r :=
  let ⟨c', fr', s', r', h', ha⟩ := hd
  ⟨c + c', fr', s', r', h.trans h', ha⟩

/-- Where the local run with calls goes for an outcome of the meaning, or the compile's
frontier, where it diverges. -/
def RunsToD (table : RowTable) (root : NativeEff) (K : List NCode) (i : Bool) (fr : NFiber)
    (s : Stores) (r : ReplyTape) (o : Option ((ExitV × Stores) × ReplyTape)) : Prop :=
  RunsTo table root K i fr s r o ∨ Diverges table root fr s r

theorem RunsToD.pre {root : NativeEff} {K : List NCode} {i : Bool} {c : Nat} {fr fr₁ : NFiber}
    {s s₁ : Stores} {r r₁ : ReplyTape} (h : ReachesC table root c fr s r fr₁ s₁ r₁)
    {o : Option ((ExitV × Stores) × ReplyTape)} :
    RunsToD table root K i fr₁ s₁ r₁ o → RunsToD table root K i fr s r o
  | .inl h' => .inl (RunsTo.pre h h')
  | .inr hd => .inr (hd.pre h)

theorem RunsToD.frontier {root : NativeEff} {K K' : List NCode} {i i' : Bool} {fr : NFiber}
    {s : Stores} {r : ReplyTape} (h : RunsToD table root K i fr s r none) :
    RunsToD table root K' i' fr s r none := h

/-- A compile out of budget is at the frontier at once. -/
theorem RunsToD.of_zero {root e : NativeEff} {p : Point} {K : List NCode} {i : Bool} {s : Stores}
    {r : ReplyTape} {o : Option ((ExitV × Stores) × ReplyTape)} (hf : p.fuel = 0) :
    RunsToD table root K i (fiberOf (compileEff e p) K i) s r o :=
  .inr ⟨0, _, s, r, ReachesC.refl table root _ s r, p, K, i, hf, by rw [compileEff_at_zero e hf]⟩

/-! ## The meaning under a reply tape, one arm at a time -/

/-- The run of a call tree under a reply tape: the stores and the replies threaded. -/
abbrev runRows (table : RowTable) {A : Type} (p : Effects.Program (RowsSig table) A) (s : Stores)
    (r : ReplyTape) : Option ((A × Stores) × ReplyTape) :=
  ((Effects.interpret (rowsHandler (tapeHandler table)) p).run s).run r

theorem runRows_bind (table : RowTable) {A B : Type} (p : Effects.Program (RowsSig table) A)
    (k : A → Effects.Program (RowsSig table) B) (s : Stores) (r : ReplyTape) :
    runRows table (p.bind k) s r =
      (runRows table p s r).bind fun x => runRows table (k x.1.1) x.1.2 x.2 := by
  simp only [runRows, Effects.interpret_bind, StateT.run_bind]
  show (((Effects.interpret (rowsHandler (tapeHandler table)) p).run s).run r).bind _ = _
  cases ((Effects.interpret (rowsHandler (tapeHandler table)) p).run s).run r with
  | none => rfl
  | some x => rfl

theorem meaningRows_pure (table : RowTable) (e : NativeEff) (env : List Val) (s : Stores)
    (r : ReplyTape) {ex : ExitV} (h : denoteRows table e env = Effects.Program.pure ex) :
    meaningRows table e env s r = some ((ex, s), r) := by
  show runRows table (denoteRows table e env) s r = _
  rw [h]
  rfl

theorem meaningRows_bindExit (table : RowTable) (b : NativeEff) (env : List Val) (s : Stores)
    (r : ReplyTape) (k : ExitV → Effects.Program (RowsSig table) ExitV) :
    runRows table ((denoteRows table b env).bind k) s r =
      (meaningRows table b env s r).bind fun x => runRows table (k x.1.1) x.1.2 x.2 :=
  runRows_bind table _ k s r

/-! ## The agreement: one fiber with calls, any outer stack -/

/-- A form of the fragment whose compile is an immediate exit means exactly that exit, with the
stores and the replies untouched. -/
theorem meaningRows_of_asExit (table : RowTable) (b : NativeEff) (q : Point) (s : Stores)
    (r : ReplyTape) {ex : ExitV} (hpl : StraightRows table b = true)
    (h : (compileEff b q).asExit? = some ex) : meaningRows table b q.env s r = some ((ex, s), r) := by
  have hy : inlineYield b q = some ex := by rw [inlineYield_eq_headExit, headExit_eq_asExit?]; exact h
  exact meaningRows_pure table b q.env s r (denoteRows_of_inlineYield table b q hpl hy)

/-- The position of a host row's operation; `none` for every other operation. -/
def externalIndex? : NativeOp → Option Nat
  | .external j => some j
  | _ => none

theorem eq_external_of_index {op : NativeOp} {j : Nat} (h : externalIndex? op = some j) :
    op = .external j := by
  cases op with
  | external k => cases h; rfl
  | _ => cases h

theorem ne_external_of_index {op : NativeOp} (h : externalIndex? op = none) : ∀ j, op ≠ .external j := by
  intro j hj
  subst hj
  simp only [externalIndex?, reduceCtorEq] at h

/-- `Straight` and the fragment agree on a call of a row that is no host's. -/
theorem straight_of_performRows {table : RowTable} {op : NativeOp} {r : Term}
    (h : StraightRows table (.perform op r) = true) (hop : ∀ i, op ≠ .external i) :
    Straight (.perform op r) = true := by
  cases op with
  | external i => exact absurd rfl (hop i)
  | _ => exact h

/-- **A program of the fragment, compiled at an address of the root, runs with calls where its
meaning under the reply tape goes** (slice H8): from any outer stack `K` and mask `i`, to its
exit's fiber over its stores with the replies left; or, when the meaning is the frontier, to a
host call with no reply left. Where the compile budget does not reach, the run may instead
diverge at the compile's frontier (`RunsToD`). A step of
`denoteRows_eq_session` (concept `translation-simulation`, R6); its consumer is that theorem's
assembly. Reach: `StraightRows`, every compile budget, every root, every reply tape. It does not
establish a run of the machine, nor anything of a fiber, a scope or a loop. -/
theorem localRunC_compile (table : RowTable) (root : NativeEff) :
    ∀ (e : NativeEff) (p : Point) (K : List NCode) (i : Bool) (s : Stores) (r : ReplyTape),
      StraightRows table e = true → Node.at_ (Node.eff root) p.path = some (Node.eff e) →
      RunsToD table root K i (fiberOf (compileEff e p) K i) s r (meaningRows table e p.env s r)
  | .succeed v, p, K, i, s, r, _, _ => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    rw [compileEff_succeed v hfu, meaningRows_pure table _ _ s r rfl]
    rcases hx : evalTerm p.env v with _ | x
    · dsimp only; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl table root _ s r⟩
    · exact Or.inl ⟨0, ReachesC.refl table root _ s r⟩
  | .fail e, p, K, i, s, r, _, _ => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    rw [compileEff_fail e hfu, meaningRows_pure table _ _ s r rfl]
    rcases hx : evalTerm p.env e with _ | x
    · dsimp only; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl table root _ s r⟩
    · exact Or.inl ⟨0, ReachesC.refl table root _ s r⟩
  | .failCause c, p, K, i, s, r, _, _ => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    rw [compileEff_failCause c hfu, meaningRows_pure table _ _ s r rfl]
    rcases hc : causeOf p.env c with _ | cause
    · dsimp only; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl table root _ s r⟩
    · exact Or.inl ⟨0, ReachesC.refl table root _ s r⟩
  | .sync t, p, K, i, s, r, _, h => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    rw [compileEff_sync t hfu, meaningRows_pure table _ _ s r rfl]
    have hs := step_sync_pure root p K i s
    rw [syncValueAt_pure h] at hs
    exact Or.inl ⟨1, ReachesC.step (table := table) hs rfl r⟩
  | .suspend b, p, K, i, s, r, hpl, h => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path = some (Node.eff b) :=
      at_child h 0
    have ih := localRunC_compile table root b ({ p with completed := [] }.child 0) K i s r hpl hb
    rw [Point.child_env] at ih
    rw [compileEff_suspend b hfu]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    rw [suspendBodyAt_suspend (q := { p with completed := [] }) hfu h, resolve_of_at hb] at hs
    exact RunsToD.pre (ReachesC.step (table := table) hs rfl r) ih
  | .perform op q, p, K, i, s, r, hpl, _ => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    rcases hext : externalIndex? op with _ | j
    swap
    · rw [eq_external_of_index hext]
      rw [eq_external_of_index hext] at hpl
      have hrow : dataRow table j = true := hpl
      have hj : j < table.length := lt_of_dataRow hrow
      rw [compileEff_perform (.external j) q hfu]
      show RunsToD table root K i (fiberOf (asyncRoute (.external j) q p) K i) s r _
      unfold asyncRoute
      rcases hx : evalTerm p.env q with _ | v
      · rw [meaningRows_pure table _ _ s r (show denoteRows table (.perform (.external j) q) p.env = _ by
          simp only [denoteRows, hx]; rfl)]
        dsimp only; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl table root _ s r⟩
      · rw [show meaningRows table (.perform (.external j) q) p.env s r =
            (((tapeHandler table).handle ⟨⟨j, hj⟩, v⟩).run r).map fun answer => ((answer.1, s), answer.2) from
          meaningUnder_call (tapeHandler table) j q p.env s r hx hj]
        dsimp only
        cases r with
        | nil => exact Or.inl ⟨0, _, s, ReachesC.refl table root _ s [], rfl⟩
        | cons ex rest =>
          exact Or.inl ⟨1, ReachesC.answer s rfl ex rest (prepareExternalAnswer_data hrow v p.path ex s)⟩
    · have hst := straight_of_performRows hpl (ne_external_of_index hext)
      have hkind := Straight.perform_sync hst
      rw [show meaningRows table (.perform op q) p.env s r = some (meaning (.perform op q) p.env s, r) from
        meaningUnder_straight (tapeHandler table) _ p.env s r hst]
      rw [compileEff_perform_sync op q hfu hkind]
      rcases hx : evalTerm p.env q with _ | x
      · rw [meaning_perform_noEval op q p.env s hkind hx]
        dsimp only; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl table root _ s r⟩
      · rcases ho : NativeOp.syncOpOf op p.env x with _ | o
        · rw [meaning_perform_noDecode op q p.env s hkind hx ho]
          simp only [ho]; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl table root _ s r⟩
        · rw [meaning_perform_sync op q p.env s hkind hx ho]
          simp only [ho]
          have hs := step_sync_op root o K i s
          rcases hstep : syncOpStep o s with _ | ⟨s', w⟩
          · simp only [hstep] at hs ⊢
            exact Or.inl ⟨1, ReachesC.step (table := table) hs rfl r⟩
          · simp only [hstep] at hs ⊢
            exact Or.inl ⟨1, ReachesC.step (table := table) hs rfl r⟩
  | .bind a b, p, K, i, s, r, hpl, h => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    have hpab : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hpl
    have ha : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff a) := at_child h 0
    rw [compileEff_bind a b hfu]
    rw [show meaningRows table (.bind a b) p.env s r =
        (meaningRows table a p.env s r).bind (fun x => runRows table
          (seqRows (fun v => denoteRows table b (p.env ++ [v])) x.1.1) x.1.2 x.2) from
      meaningRows_bindExit table a p.env s r _]
    have iha := localRunC_compile table root a (p.child 0)
      (Prim.onSuccess (compileEff a (p.child 0)) (EffName.cont p) :: K) i s r hpab.1 ha
    rw [Point.child_env] at iha
    have hpush := ReachesC.step (table := table)
      (step_push_onSuccess root (compileEff a (p.child 0)) (EffName.cont p) K i s) rfl r
    rcases hma : meaningRows table a p.env s r with _ | ⟨⟨ex, s'⟩, r'⟩
    · rw [hma] at iha
      exact RunsToD.frontier (RunsToD.pre hpush iha)
    · rw [hma] at iha
      rcases iha with iha | hdiv
      swap
      · exact Or.inr (hdiv.pre hpush)
      obtain ⟨ca, hra⟩ := iha
      cases ex with
      | success v =>
        have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 v).path = some (Node.eff b) :=
          at_childWith h 1 v
        have ihb := localRunC_compile table root b ({ p with completed := [] }.childWith 1 v) K i s' r'
          hpab.2 hb
        rw [Point.childWith_env] at ihb
        have hpop := ReachesC.step (table := table)
          (step_success_onSuccess root v (compileEff a (p.child 0)) (EffName.cont p) K i s') rfl r'
        simp only [interpAt] at hpop
        rw [contAOf_cont, resolve_of_at hb] at hpop
        exact RunsToD.pre ((hpush.trans hra).trans hpop) ihb
      | failure c =>
        have hpass := ReachesC.same (table := table) s' r' (fun s =>
          step_failure_pass_onSuccess root c (compileEff a (p.child 0)) (EffName.cont p) K i s) rfl rfl
        exact Or.inl ⟨1 + ca + 0, (hpush.trans hra).trans hpass⟩
  | .select t d a b, p, K, i, s, r, hpl, h => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    have hpab : StraightRows table a = true ∧ StraightRows table b = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hpl
    rw [compileEff_select t d a b hfu]
    have hs := step_suspend root (EffThunk.body p) K i s
    simp only [interpAt] at hs
    rcases hdec : (evalTerm p.env t).bind d.decide with _ | ⟨first, bound⟩
    · rw [suspendBodyAt_select_bad (q := { p with completed := [] }) hfu h hdec] at hs
      rw [meaningRows_pure table _ _ s r (show denoteRows table (.select t d a b) p.env = _ by
        simp only [denoteRows, hdec]; rfl)]
      rw [badShape_eq] at hs
      exact Or.inl ⟨1, ReachesC.step (table := table) hs rfl r⟩
    · rw [suspendBodyAt_select_of_decide (q := { p with completed := [] }) hfu h hdec] at hs
      cases first with
      | true =>
        rw [show meaningRows table (.select t d a b) p.env s r =
            meaningRows table a (p.env ++ bound.toList) s r by
          show runRows table (denoteRows table (.select t d a b) p.env) s r = _
          simp only [denoteRows, hdec]; rfl]
        cases bound with
        | none =>
          have ha : Node.at_ (Node.eff root) ({ p with completed := [] }.child 0).path = some (Node.eff a) :=
            at_child h 0
          have ih := localRunC_compile table root a ({ p with completed := [] }.child 0) K i s r hpab.1 ha
          rw [Point.child_env] at ih
          simp only [Bool.cond_true, Point.childBind] at hs
          rw [resolve_of_at ha] at hs
          simp only [Option.toList, List.append_nil]
          exact RunsToD.pre (ReachesC.step (table := table) hs rfl r) ih
        | some v =>
          have ha : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 0 v).path = some (Node.eff a) :=
            at_childWith h 0 v
          have ih := localRunC_compile table root a ({ p with completed := [] }.childWith 0 v) K i s r hpab.1 ha
          rw [Point.childWith_env] at ih
          simp only [Bool.cond_true, Point.childBind] at hs
          rw [resolve_of_at ha] at hs
          simp only [Option.toList]
          exact RunsToD.pre (ReachesC.step (table := table) hs rfl r) ih
      | false =>
        rw [show meaningRows table (.select t d a b) p.env s r =
            meaningRows table b (p.env ++ bound.toList) s r by
          show runRows table (denoteRows table (.select t d a b) p.env) s r = _
          simp only [denoteRows, hdec]; rfl]
        cases bound with
        | none =>
          have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.child 1).path = some (Node.eff b) :=
            at_child h 1
          have ih := localRunC_compile table root b ({ p with completed := [] }.child 1) K i s r hpab.2 hb
          rw [Point.child_env] at ih
          simp only [Bool.cond_false, Point.childBind] at hs
          rw [resolve_of_at hb] at hs
          simp only [Option.toList, List.append_nil]
          exact RunsToD.pre (ReachesC.step (table := table) hs rfl r) ih
        | some v =>
          have hb : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 v).path = some (Node.eff b) :=
            at_childWith h 1 v
          have ih := localRunC_compile table root b ({ p with completed := [] }.childWith 1 v) K i s r hpab.2 hb
          rw [Point.childWith_env] at ih
          simp only [Bool.cond_false, Point.childBind] at hs
          rw [resolve_of_at hb] at hs
          simp only [Option.toList]
          exact RunsToD.pre (ReachesC.step (table := table) hs rfl r) ih
  | .exit b, p, K, i, s, r, hpl, h => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    have hpb : StraightRows table b = true := hpl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    rw [show meaningRows table (.exit b) p.env s r =
        (meaningRows table b p.env s r).bind (fun x => runRows table
          (Effects.Program.pure (Exit.success (reifyExitVal x.1.1))) x.1.2 x.2) from
      meaningRows_bindExit table b p.env s r _]
    rcases hx : (compileEff b (p.child 0)).asExit? with _ | ex
    · rw [compileEff_exit_frame b hfu hx]
      have ih := localRunC_compile table root b (p.child 0)
        (Prim.exitFrame (compileEff b (p.child 0)) :: K) i s r hpb hb
      rw [Point.child_env] at ih
      have hpush := ReachesC.step (table := table) (step_push_exitFrame root (compileEff b (p.child 0)) K i s) rfl r
      rcases hmb : meaningRows table b p.env s r with _ | ⟨⟨ex, s'⟩, r'⟩
      · rw [hmb] at ih
        exact RunsToD.frontier (RunsToD.pre hpush ih)
      · rw [hmb] at ih
        rcases ih with ih | hdiv
        swap
        · exact Or.inr (hdiv.pre hpush)
        obtain ⟨cb, hrb⟩ := ih
        have hpop := ReachesC.step (table := table) (step_ofExit_exitFrame root ex (compileEff b (p.child 0)) K i s')
          (isCall_ofExit ex) r'
        exact Or.inl ⟨1 + cb + 1, (hpush.trans hrb).trans hpop⟩
    · -- the fold: the compiled program already is the meaning's exit (row D1)
      have hmb := meaningRows_of_asExit table b (p.child 0) s r hpb hx
      rw [Point.child_env] at hmb
      rw [compileEff_exit_fold b hfu hx, hmb]
      exact Or.inl ⟨0, ReachesC.refl table root _ s r⟩
  | .catchCause b hh, p, K, i, s, r, hpl, h => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    have hpbh : StraightRows table b = true ∧ StraightRows table hh = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hpl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    rw [compileEff_catchCause b hh hfu]
    rw [show meaningRows table (.catchCause b hh) p.env s r =
        (meaningRows table b p.env s r).bind (fun x => runRows table
          (match x.1.1 with
            | Exit.success v => Effects.Program.pure (Exit.success v)
            | Exit.failure c => denoteRows table hh (p.env ++ [Val.exitErr c])) x.1.2 x.2) from
      meaningRows_bindExit table b p.env s r _]
    have ih := localRunC_compile table root b (p.child 0)
      (Prim.onFailure (compileEff b (p.child 0)) (EffName.caught p) :: K) i s r hpbh.1 hb
    rw [Point.child_env] at ih
    have hpush := ReachesC.step (table := table)
      (step_push_onFailure root (compileEff b (p.child 0)) (EffName.caught p) K i s) rfl r
    rcases hmb : meaningRows table b p.env s r with _ | ⟨⟨ex, s'⟩, r'⟩
    · rw [hmb] at ih
      exact RunsToD.frontier (RunsToD.pre hpush ih)
    · rw [hmb] at ih
      rcases ih with ih | hdiv
      swap
      · exact Or.inr (hdiv.pre hpush)
      obtain ⟨cb, hrb⟩ := ih
      cases ex with
      | success v =>
        have hpass := ReachesC.same (table := table) s' r' (fun s =>
          step_success_pass_onFailure root v (compileEff b (p.child 0)) (EffName.caught p) K i s) rfl rfl
        exact Or.inl ⟨1 + cb + 0, (hpush.trans hrb).trans hpass⟩
      | failure c =>
        have hh' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 (Val.exitErr c)).path =
            some (Node.eff hh) := at_childWith h 1 (Val.exitErr c)
        have ihh := localRunC_compile table root hh ({ p with completed := [] }.childWith 1 (Val.exitErr c))
          K i s' r' hpbh.2 hh'
        rw [Point.childWith_env] at ihh
        have hpop := ReachesC.step (table := table)
          (step_failure_onFailure root c (compileEff b (p.child 0)) (EffName.caught p) K i s') rfl r'
        simp only [interpAt] at hpop
        rw [contEOf_caught, resolve_of_at hh'] at hpop
        exact RunsToD.pre ((hpush.trans hrb).trans hpop) ihh
  | .catchIf test b hh, p, K, i, s, r, hpl, h => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    have hpbh : StraightRows table b = true ∧ StraightRows table hh = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hpl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    rw [compileEff_catchIf test b hh hfu]
    rw [show meaningRows table (.catchIf test b hh) p.env s r =
        (meaningRows table b p.env s r).bind (fun x => runRows table
          (match x.1.1 with
            | Exit.success v => Effects.Program.pure (Exit.success v)
            | Exit.failure cause =>
              match caughtErrorValue? p.env test cause with
              | some value => denoteRows table hh (p.env ++ [value])
              | none => Effects.Program.pure (Exit.failure cause)) x.1.2 x.2) from
      meaningRows_bindExit table b p.env s r _]
    have ih := localRunC_compile table root b (p.child 0)
      (Prim.onFailure (compileEff b (p.child 0)) (EffName.caughtError p) :: K) i s r hpbh.1 hb
    rw [Point.child_env] at ih
    have hpush := ReachesC.step (table := table)
      (step_push_onFailure root (compileEff b (p.child 0)) (EffName.caughtError p) K i s) rfl r
    rcases hmb : meaningRows table b p.env s r with _ | ⟨⟨ex, s'⟩, r'⟩
    · rw [hmb] at ih
      exact RunsToD.frontier (RunsToD.pre hpush ih)
    · rw [hmb] at ih
      rcases ih with ih | hdiv
      swap
      · exact Or.inr (hdiv.pre hpush)
      obtain ⟨cb, hrb⟩ := ih
      cases ex with
      | success v =>
        have hpass := ReachesC.same (table := table) s' r' (fun s =>
          step_success_pass_onFailure root v (compileEff b (p.child 0)) (EffName.caughtError p) K i s) rfl rfl
        exact Or.inl ⟨1 + cb + 0, (hpush.trans hrb).trans hpass⟩
      | failure c =>
        have hpop := ReachesC.step (table := table)
          (step_failure_onFailure root c (compileEff b (p.child 0)) (EffName.caughtError p) K i s') rfl r'
        simp only [interpAt] at hpop
        have hcont : contEOf root (EffName.caughtError { p with completed := [] }) c =
            (match caughtErrorValue? p.env test c with
              | some value => resolve root ({ p with completed := [] }.childWith 1 value)
              | none => Prim.failure c) := by
          show (match Node.at_ (Node.eff root) p.path with
            | some (.eff (.catchIf test _ _)) =>
              match caughtErrorValue? p.env test c with
              | some value => resolve root ({ p with completed := [] }.childWith 1 value)
              | none => Prim.failure c
            | _ => Prim.failure c) = _
          rw [h]
        rw [hcont] at hpop
        show RunsToD table root K i _ s r (runRows table
          (match caughtErrorValue? p.env test c with
            | some value => denoteRows table hh (p.env ++ [value])
            | none => Effects.Program.pure (Exit.failure c)) s' r')
        rcases hcv : caughtErrorValue? p.env test c with _ | value
        · simp only [hcv] at hpop
          exact Or.inl ⟨1 + cb + 1, (hpush.trans hrb).trans hpop⟩
        · simp only [hcv] at hpop
          have hh' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 value).path =
              some (Node.eff hh) := at_childWith h 1 value
          have ihh := localRunC_compile table root hh ({ p with completed := [] }.childWith 1 value)
            K i s' r' hpbh.2 hh'
          rw [Point.childWith_env] at ihh
          rw [resolve_of_at hh'] at hpop
          exact RunsToD.pre ((hpush.trans hrb).trans hpop) ihh
  | .matchCause b v c, p, K, i, s, r, hpl, h => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    have hpbvc : StraightRows table b = true ∧ StraightRows table v = true ∧ StraightRows table c = true := by
      simpa only [StraightRows, Bool.and_eq_true, and_assoc] using hpl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    rw [compileEff_matchCause b v c hfu]
    rw [show meaningRows table (.matchCause b v c) p.env s r =
        (meaningRows table b p.env s r).bind (fun x => runRows table
          (match x.1.1 with
            | Exit.success y => denoteRows table v (p.env ++ [y])
            | Exit.failure cause => denoteRows table c (p.env ++ [Val.exitErr cause])) x.1.2 x.2) from
      meaningRows_bindExit table b p.env s r _]
    have ih := localRunC_compile table root b (p.child 0)
      (Prim.onSuccessAndFailure (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) :: K)
      i s r hpbvc.1 hb
    rw [Point.child_env] at ih
    have hpush := ReachesC.step (table := table) (step_push_onSuccessAndFailure root (compileEff b (p.child 0))
      (EffName.onValue p) (EffName.onCause p) K i s) rfl r
    rcases hmb : meaningRows table b p.env s r with _ | ⟨⟨ex, s'⟩, r'⟩
    · rw [hmb] at ih
      exact RunsToD.frontier (RunsToD.pre hpush ih)
    · rw [hmb] at ih
      rcases ih with ih | hdiv
      swap
      · exact Or.inr (hdiv.pre hpush)
      obtain ⟨cb, hrb⟩ := ih
      cases ex with
      | success x =>
        have hv' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 x).path = some (Node.eff v) :=
          at_childWith h 1 x
        have ihv := localRunC_compile table root v ({ p with completed := [] }.childWith 1 x) K i s' r'
          hpbvc.2.1 hv'
        rw [Point.childWith_env] at ihv
        have hpop := ReachesC.step (table := table) (step_success_onSuccessAndFailure root x
          (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s') rfl r'
        simp only [interpAt] at hpop
        rw [contAOf_onValue, resolve_of_at hv'] at hpop
        exact RunsToD.pre ((hpush.trans hrb).trans hpop) ihv
      | failure cause =>
        have hc' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 2 (Val.exitErr cause)).path =
            some (Node.eff c) := at_childWith h 2 (Val.exitErr cause)
        have ihc := localRunC_compile table root c ({ p with completed := [] }.childWith 2 (Val.exitErr cause))
          K i s' r' hpbvc.2.2 hc'
        rw [Point.childWith_env] at ihc
        have hpop := ReachesC.step (table := table) (step_failure_onSuccessAndFailure root cause
          (compileEff b (p.child 0)) (EffName.onValue p) (EffName.onCause p) K i s') rfl r'
        simp only [interpAt] at hpop
        rw [contEOf_onCause, resolve_of_at hc'] at hpop
        exact RunsToD.pre ((hpush.trans hrb).trans hpop) ihc
  | .onExit b f, p, K, i, s, r, hpl, h => by
    rcases hfu : p.fuel with _ | k
    · exact RunsToD.of_zero hfu
    have hpbf : StraightRows table b = true ∧ StraightRows table f = true := by
      simpa only [StraightRows, Bool.and_eq_true] using hpl
    have hb : Node.at_ (Node.eff root) (p.child 0).path = some (Node.eff b) := at_child h 0
    rw [compileEff_onExit b f hfu]
    rw [show meaningRows table (.onExit b f) p.env s r =
        (meaningRows table b p.env s r).bind (fun x => runRows table
          ((denoteRows table f (p.env ++ [reifyExitVal x.1.1])).bind fun fex =>
            Effects.Program.pure (Exit.restoreAfterFinalizer x.1.1 (finVoid fex))) x.1.2 x.2) from
      meaningRows_bindExit table b p.env s r _]
    have ih := localRunC_compile table root b (p.child 0)
      (Prim.onExit (compileEff b (p.child 0)) (EffName.fin p) false :: K) i s r hpbf.1 hb
    rw [Point.child_env] at ih
    have hpush := ReachesC.step (table := table)
      (step_push_onExit root (compileEff b (p.child 0)) (EffName.fin p) false K i s) rfl r
    rcases hmb : meaningRows table b p.env s r with _ | ⟨⟨ex, s'⟩, r'⟩
    · rw [hmb] at ih
      exact RunsToD.frontier (RunsToD.pre hpush ih)
    · rw [hmb] at ih
      rcases ih with ih | hdiv
      swap
      · exact Or.inr (hdiv.pre hpush)
      obtain ⟨cb, hrb⟩ := ih
      show RunsToD table root K i _ s r (runRows table
        ((denoteRows table f (p.env ++ [reifyExitVal ex])).bind fun fex =>
          Effects.Program.pure (Exit.restoreAfterFinalizer ex (finVoid fex))) s' r')
      rw [runRows_bind]
      change RunsToD table root K i _ s r ((meaningRows table f (p.env ++ [reifyExitVal ex]) s' r').bind _)
      -- the body's exit meets the frame: the finalizer runs under the mask
      have hf' : Node.at_ (Node.eff root) ({ p with completed := [] }.childWith 1 (reifyExitVal ex)).path =
          some (Node.eff f) := at_childWith h 1 (reifyExitVal ex)
      have hmeet := ReachesC.step (table := table) (step_ofExit_onExit root ex (compileEff b (p.child 0)) p K i s')
        (isCall_ofExit ex) r'
      rw [resolve_of_at hf'] at hmeet
      have hunmask (result : ExitV) (state : Stores) (rr : ReplyTape) : ReachesC table root 0
          (fiberOf (Prim.ofExit result) (maskStack i K) false) state rr
          (fiberOf (Prim.ofExit result) K i) state rr := by
        cases i
        · exact ReachesC.refl table root _ state rr
        · exact ReachesC.same (table := table) state rr (fun s => step_ofExit_pass_setInterruptible root _ K false s)
            (isCall_ofExit result) (isCall_ofExit result)
      cases ex with
      | success value =>
        let program := compileEff f ({ p with completed := [] }.childWith 1
          (reifyExitVal (.success value)))
        let restore := EffName.restore (.success value)
        have hpush₂ := ReachesC.step (table := table)
          (step_push_onSuccess root program restore (maskStack i K) false s') rfl r'
        have ihf := localRunC_compile table root f
          ({ p with completed := [] }.childWith 1 (reifyExitVal (.success value)))
          (Prim.onSuccess program restore :: maskStack i K) false s' r' hpbf.2 hf'
        rw [Point.childWith_env] at ihf
        rcases hmf : meaningRows table f (p.env ++ [reifyExitVal (.success value)]) s' r' with
          _ | ⟨⟨fex, s''⟩, r''⟩
        · rw [hmf] at ihf
          exact RunsToD.frontier (RunsToD.pre (((hpush.trans hrb).trans hmeet).trans hpush₂) ihf)
        · rw [hmf] at ihf
          rcases ihf with ihf | hdiv
          swap
          · exact Or.inr (hdiv.pre (((hpush.trans hrb).trans hmeet).trans hpush₂))
          obtain ⟨cf, hrf⟩ := ihf
          cases fex with
          | success finValue =>
            have hfin := ReachesC.step (table := table)
              (step_success_onSuccess root finValue program restore (maskStack i K) false s'') rfl r''
            change ReachesC table root 1 _ s'' r'' (fiberOf (Prim.success value) (maskStack i K) false) s'' r'' at hfin
            exact Or.inl ⟨1 + cb + 1 + 1 + cf + 1 + 0,
              (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hfin).trans
                (hunmask (.success value) s'' r'')⟩
          | failure finCause =>
            have hpass := ReachesC.same (table := table) s'' r'' (fun s =>
              step_failure_pass_onSuccess root finCause program restore (maskStack i K) false s) rfl rfl
            exact Or.inl ⟨1 + cb + 1 + 1 + cf + 0 + 0,
              (((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hrf).trans hpass).trans
                (hunmask (.failure finCause) s'' r'')⟩
      | failure cause =>
        let program := compileEff f ({ p with completed := [] }.childWith 1
          (reifyExitVal (.failure cause)))
        let restore := EffName.restore (.failure cause)
        let merge := EffName.merge (.failure cause)
        let outer := Prim.onSuccess (Prim.onFailure program merge) restore
        have hpush₂ := ReachesC.step (table := table)
          (step_push_onSuccess root (Prim.onFailure program merge) restore (maskStack i K) false s') rfl r'
        have hpush₃ := ReachesC.step (table := table)
          (step_push_onFailure root program merge (outer :: maskStack i K) false s') rfl r'
        have ihf := localRunC_compile table root f
          ({ p with completed := [] }.childWith 1 (reifyExitVal (.failure cause)))
          (Prim.onFailure program merge :: outer :: maskStack i K) false s' r' hpbf.2 hf'
        rw [Point.childWith_env] at ihf
        rcases hmf : meaningRows table f (p.env ++ [reifyExitVal (.failure cause)]) s' r' with
          _ | ⟨⟨fex, s''⟩, r''⟩
        · rw [hmf] at ihf
          exact RunsToD.frontier
            (RunsToD.pre ((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃) ihf)
        · rw [hmf] at ihf
          rcases ihf with ihf | hdiv
          swap
          · exact Or.inr (hdiv.pre ((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃))
          obtain ⟨cf, hrf⟩ := ihf
          cases fex with
          | success finValue =>
            have hpass := ReachesC.same (table := table) s'' r'' (fun s =>
              step_success_pass_onFailure root finValue program merge (outer :: maskStack i K) false s) rfl rfl
            have hfin := ReachesC.step (table := table) (step_success_onSuccess root finValue
              (Prim.onFailure program merge) restore (maskStack i K) false s'') rfl r''
            change ReachesC table root 1 _ s'' r'' (fiberOf (Prim.failure cause) (maskStack i K) false) s'' r'' at hfin
            exact Or.inl ⟨1 + cb + 1 + 1 + 1 + cf + 0 + 1 + 0,
              (((((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃).trans hrf).trans hpass).trans
                hfin).trans (hunmask (.failure cause) s'' r'')⟩
          | failure finCause =>
            have hmerge := ReachesC.step (table := table)
              (step_failure_onFailure root finCause program merge (outer :: maskStack i K) false s'') rfl r''
            change ReachesC table root 1 _ s'' r''
              (fiberOf (Prim.failure (Cause.combine cause finCause)) (outer :: maskStack i K) false) s'' r''
              at hmerge
            have hpass := ReachesC.same (table := table) s'' r'' (fun s => step_failure_pass_onSuccess root
              (Cause.combine cause finCause) (Prim.onFailure program merge) restore (maskStack i K) false s)
              rfl rfl
            exact Or.inl ⟨1 + cb + 1 + 1 + 1 + cf + 1 + 0 + 0,
              (((((((hpush.trans hrb).trans hmeet).trans hpush₂).trans hpush₃).trans hrf).trans hmerge).trans
                hpass).trans (hunmask (.failure (Cause.combine cause finCause)) s'' r'')⟩
  | .gen _, _, _, _, _, _, hpl, _
  | .uninterruptible _, _, _, _, _, _, hpl, _
  | .interruptible _, _, _, _, _, _, hpl, _
  | .yieldNow _, _, _, _, _, _, hpl, _
  | .awaitFiber _ _, _, _, _, _, _, hpl, _
  | .withFiber _, _, _, _, _, _, hpl, _
  | .scoped _, _, _, _, _, _, hpl, _
  | .acquireRelease _ _, _, _, _, _, _, hpl, _
  | .provideLayer _ _ _, _, _, _, _, _, hpl, _
  | .service _, _, _, _, _, _, hpl, _
  | .provideService _ _ _, _, _, _, _, _, hpl, _
  | .iterate _ _ _ _ _ _, _, _, _, _, _, hpl, _
  | .restore _ _, _, _, _, _, _, hpl, _
  | .defs _ _ _, _, _, _, _, _, hpl, _ => by
    simp only [StraightRows, Bool.false_eq_true] at hpl

end Effect4.Program.Agreement
