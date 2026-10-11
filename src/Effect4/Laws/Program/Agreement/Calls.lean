import Effect4.Laws.Program.Agreement.Segment
import Effect4.Laws.Program.DenoteRowsR
import Effect4.Laws.Program.HostRuns

/-!
# Program.Agreement.Calls — one fiber with host calls, run under a reply tape

Slice H8 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310), by the frame
machine's route: the local run of `Program/Agreement.lean`, with the host calls of the fragment
`StraightRows` answered from a reply tape. A host call, as the compile writes it, is an external
registration (`asyncRoute`); the local run with calls (`localRunC`, `Agreement/Segment.lean`)
gives it the answer that the machine's answer decision prepares from the next exit of the reply
tape (`prepareExternalAnswer`), and waits when the tape is empty (`RunEnd.waits`). Every other
step is the local step.

**What it holds.** Where the local run with calls goes for an outcome of the meaning (`RunsToD`):
to its exit's fiber, to a host call with no reply left, or, at an address the compile budget does
not reach, to a divergence at the compile's frontier (`Diverges`). The five atoms reach it
(`compilesD_succeed`, `compilesD_fail`, `compilesD_failCause`, `compilesD_sync`,
`compilesD_perform`). The law on the whole fragment, `localRunC_compile`, is the loop
agreement's straight instance (`Agreement/LoopCalls.lean`): the composite arms are proved once,
at a budget. Concept `translation-simulation`, requirement R6. It says nothing of the command
loop, which `Agreement/Hosted.lean` relates to this run, nor of a second fiber or a scope.
-/
set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Sched

variable {table : RowTable}

/-! ## A host call's answer at a data row -/

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


/-- **Where the local run with calls goes for an outcome of the meaning.** For an exit with its
stores and the host's state, it reaches the exit's fiber over the stack `K` with mask `i`; for
the frontier, it reaches a host call the host does not answer. -/
def RunsTo {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff) (K : List NCode)
    (i : Bool) (fr : NFiber) (s : Stores) (r : σ) : Option (ExitV × (Stores × σ)) → Prop
  | some (ex, (s', r')) => ∃ c, ReachesC host root c fr s r (fiberOf (Prim.ofExit ex) K i) s' r'
  | none => ∃ c fr' s' r', ReachesC host root c fr s r fr' s' r' ∧ IsCall fr'.current = true ∧
      hostAnswer host fr'.current r' = none

/-- A run that reaches a fiber goes where that fiber's run goes. -/
theorem RunsTo.pre {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ}
    (h : ReachesC host root c fr s r fr₁ s₁ r₁) :
    ∀ {o : Option (ExitV × (Stores × σ))}, RunsTo host root K i fr₁ s₁ r₁ o → RunsTo host root K i fr s r o
  | some (_, (_, _)), ⟨c', h'⟩ => ⟨c + c', h.trans h'⟩
  | none, ⟨c', fr', s', r', h', hc, ha⟩ => ⟨c + c', fr', s', r', h.trans h', hc, ha⟩

/-- The frontier names no stack. -/
theorem RunsTo.frontier {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K K' : List NCode} {i i' : Bool} {fr : NFiber} {s : Stores} {r : σ}
    (h : RunsTo host root K i fr s r none) : RunsTo host root K' i' fr s r none := h

/-! ## The compile's frontier: where the local run diverges -/

/-- The compile's frontier: a suspension at an address the compile budget does not reach
(`compileEff_at_zero`). Its body is the frontier again (`suspendBodyAt_zero`). -/
def AtFrontier (fr : NFiber) : Prop :=
  ∃ (q : Point) (K : List NCode) (i : Bool), q.fuel = 0 ∧ fr = fiberOf (frontier q) K i

/-- **The local run with calls diverges**: it reaches the compile's frontier, where it stays
(`localRunC_frontier`). -/
def Diverges {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff) (fr : NFiber)
    (s : Stores) (r : σ) : Prop :=
  ∃ c fr' s' r', ReachesC host root c fr s r fr' s' r' ∧ AtFrontier fr'

theorem Diverges.pre {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ} (hd : Diverges host root fr₁ s₁ r₁)
    (h : ReachesC host root c fr s r fr₁ s₁ r₁) : Diverges host root fr s r :=
  let ⟨c', fr', s', r', h', ha⟩ := hd
  ⟨c + c', fr', s', r', h.trans h', ha⟩

/-- Where the local run with calls goes for an outcome of the meaning, or the compile's
frontier, where it diverges. -/
def RunsToD {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff) (K : List NCode)
    (i : Bool) (fr : NFiber) (s : Stores) (r : σ) (o : Option (ExitV × (Stores × σ))) : Prop :=
  RunsTo host root K i fr s r o ∨ Diverges host root fr s r

theorem RunsToD.pre {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K : List NCode} {i : Bool} {c : Nat} {fr fr₁ : NFiber} {s s₁ : Stores} {r r₁ : σ}
    (h : ReachesC host root c fr s r fr₁ s₁ r₁) {o : Option (ExitV × (Stores × σ))} :
    RunsToD host root K i fr₁ s₁ r₁ o → RunsToD host root K i fr s r o
  | .inl h' => .inl (RunsTo.pre h h')
  | .inr hd => .inr (hd.pre h)

theorem RunsToD.frontier {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root : NativeEff}
    {K K' : List NCode} {i i' : Bool} {fr : NFiber} {s : Stores} {r : σ}
    (h : RunsToD host root K i fr s r none) : RunsToD host root K' i' fr s r none := h

/-- A compile out of budget is at the frontier at once. -/
theorem RunsToD.of_zero {σ : Type} {host : Effects.Comodel (RowSig table) σ} {root e : NativeEff}
    {p : Point} {K : List NCode} {i : Bool} {s : Stores} {r : σ} {o : Option (ExitV × (Stores × σ))}
    (hf : p.fuel = 0) : RunsToD host root K i (fiberOf (compileEff e p) K i) s r o :=
  .inr ⟨0, _, s, r, ReachesC.refl host root _ s r, p, K, i, hf, by rw [compileEff_at_zero e hf]⟩

/-! ## Facts the atoms and the composite arms share -/

/-- A form of the fragment whose compile is an immediate exit means exactly that exit, with the
stores and the host's state untouched. -/
theorem hostRun_of_asExit {σ : Type} (host : Effects.Comodel (RowSig table) σ) (b : NativeEff)
    (q : Point) (s : Stores) (r : σ) {ex : ExitV} (hpl : StraightRows table b = true)
    (h : (compileEff b q).asExit? = some ex) : hostRun host b q.env s r = some (ex, (s, r)) := by
  have hy : inlineYield b q = some ex := by rw [inlineYield_eq_headExit, headExit_eq_asExit?]; exact h
  exact hostRun_pure host b q.env s r (denoteRows_of_inlineYield table b q hpl hy)

/-- A host call's code, inside the table, is asked of the host at its row and request. -/
theorem hostAnswer_call {σ : Type} (host : Effects.Comodel (RowSig table) σ) {j : Nat}
    (hj : j < table.length) (v : Val) (w : List Nat) (r : σ) :
    hostAnswer host (Prim.async (EffName.external (.external j) v w) false none) r =
      host.answer ⟨⟨j, hj⟩, v⟩ r := by
  exact dif_pos hj

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

/-! ## The atoms -/

/-- **A program compiled at an address of the root runs where its meaning under the reply tape
goes**, from any outer stack, mask, stores and host state, or diverges at the compile's frontier
(`RunsToD`). `localRunC_compile` says it of every `StraightRows` program. -/
def CompilesD {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (e : NativeEff) : Prop :=
  ∀ (p : Point) (K : List NCode) (i : Bool) (s : Stores) (r : σ),
    Node.at_ (Node.eff root) p.path = some (Node.eff e) →
      RunsToD host root K i (fiberOf (compileEff e p) K i) s r (hostRun host e p.env s r)

/-- A success is its exit at once. An atom of `compilesBO` (`Agreement/LoopCalls.lean`). -/
theorem compilesD_succeed {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (v : Term) : CompilesD host root (.succeed v) := by
  intro p K i s r _
  rcases hfu : p.fuel with _ | k
  · exact RunsToD.of_zero hfu
  rw [compileEff_succeed v hfu, hostRun_pure host _ _ s r rfl]
  rcases hx : evalTerm p.env v with _ | x
  · dsimp only; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩
  · exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩

/-- A failure is its exit at once. An atom of `compilesBO`. -/
theorem compilesD_fail {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (e : Term) : CompilesD host root (.fail e) := by
  intro p K i s r _
  rcases hfu : p.fuel with _ | k
  · exact RunsToD.of_zero hfu
  rw [compileEff_fail e hfu, hostRun_pure host _ _ s r rfl]
  rcases hx : evalTerm p.env e with _ | x
  · dsimp only; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩
  · exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩

/-- A cause's failure is its exit at once. An atom of `compilesBO`. -/
theorem compilesD_failCause {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (c : CauseTerm) : CompilesD host root (.failCause c) := by
  intro p K i s r _
  rcases hfu : p.fuel with _ | k
  · exact RunsToD.of_zero hfu
  rw [compileEff_failCause c hfu, hostRun_pure host _ _ s r rfl]
  rcases hc : causeOf p.env c with _ | cause
  · dsimp only; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩
  · exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩

/-- A pure computation is its value after one step. An atom of `compilesBO`. -/
theorem compilesD_sync {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (t : Term) : CompilesD host root (.sync t) := by
  intro p K i s r h
  rcases hfu : p.fuel with _ | k
  · exact RunsToD.of_zero hfu
  rw [compileEff_sync t hfu, hostRun_pure host _ _ s r rfl]
  have hs := step_sync_pure root p K i s
  rw [syncValueAt_pure h] at hs
  exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩

/-- **A call of the fragment**: a host call asks the host at its row, and reads its answer or
waits; every other call is a store operation, one step. An atom of `compilesBO`. -/
theorem compilesD_perform {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) {op : NativeOp} {q : Term} (hpl : StraightRows table (.perform op q) = true) :
    CompilesD host root (.perform op q) := by
  intro p K i s r _
  rcases hfu : p.fuel with _ | k
  · exact RunsToD.of_zero hfu
  rcases hext : externalIndex? op with _ | j
  swap
  · rw [eq_external_of_index hext]
    rw [eq_external_of_index hext] at hpl
    have hrow : dataRow table j = true := hpl
    have hj : j < table.length := lt_of_dataRow hrow
    rw [compileEff_perform (.external j) q hfu]
    show RunsToD host root K i (fiberOf (asyncRoute (.external j) q p) K i) s r _
    unfold asyncRoute
    rcases hx : evalTerm p.env q with _ | v
    · rw [hostRun_pure host _ _ s r (show denoteRows table (.perform (.external j) q) p.env = _ by
        simp only [denoteRows, hx]; rfl)]
      dsimp only; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩
    · rw [hostRun_call host j q p.env s r hx hj]
      have hcall := hostAnswer_call host hj v p.path r
      rcases ha : host.answer ⟨⟨j, hj⟩, v⟩ r with _ | ⟨ex, r'⟩
      · show RunsToD host root K i _ s r none
        exact Or.inl ⟨0, _, s, r, ReachesC.refl host root _ s r, rfl, hcall.trans ha⟩
      · show RunsToD host root K i _ s r (some (ex, (s, r')))
        exact Or.inl ⟨1, ReachesC.answer s rfl (hcall.trans ha)
          (prepareExternalAnswer_data hrow v p.path ex s)⟩
  · have hst := straight_of_performRows hpl (ne_external_of_index hext)
    have hkind := Straight.perform_sync hst
    rw [hostRun_straight host _ p.env s r hst]
    rw [compileEff_perform_sync op q hfu hkind]
    rcases hx : evalTerm p.env q with _ | x
    · rw [meaning_perform_noEval op q p.env s hkind hx]
      dsimp only; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩
    · rcases ho : NativeOp.syncOpOf op p.env x with _ | o
      · rw [meaning_perform_noDecode op q p.env s hkind hx ho]
        simp only [ho]; rw [badShape_eq]; exact Or.inl ⟨0, ReachesC.refl host root _ s r⟩
      · rw [meaning_perform_sync op q p.env s hkind hx ho]
        simp only [ho]
        have hs := step_sync_op root o K i s
        rcases hstep : syncOpStep o s with _ | ⟨s', w⟩
        · simp only [hstep] at hs ⊢
          exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩
        · simp only [hstep] at hs ⊢
          exact Or.inl ⟨1, ReachesC.step (host := host) hs rfl r⟩

end Effect4.Program.Agreement
