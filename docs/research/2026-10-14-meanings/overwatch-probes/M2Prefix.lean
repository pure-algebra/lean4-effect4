import Effect4.Laws.Api.SessionMeaningLoop
import Effect4.Laws.Api.SessionMeaningBlocks

/-!
# Overwatch probe M2: the recorded-command invariant already exists

Concept: translation-simulation, R6. Claim: `recorded-call-tree-prefix`, role inversion, widened
past straight lines (decisions rows 388 and 390). Consumer: the meanings brief's slice M2, through
the block instance named at the foot of this file.

Question. The brief asks for a prefix connection at every command cut of a host-driven run. This
probe checks that the connection is the existing `tape_holds_host` (H8 and H9's session prefix),
and that the meaning side is one transfer lemma parametric in the meaning family.

Reach. Every program with plain hooks, every reached, funded and host-driven run, every host that
gave the recorded answers, every meaning family with a forward agreement at the compiled root.
No rest premise. The loop and block instances are checked here. The probe runs with the
meanings tree's oleans of these base modules: the main tree's oleans predate the context field of
`Pos.live`, and no module in the probe's import closure differs from `5f07927c8`.

Not established. No progress; no interruption meaning (the counterexample of
`MeaningsPrefixProbe` stays the red control); nothing for an unfunded run, whose `tapeOf` stops at
the first stopped row, so `hostDriven` says nothing of a decision after it.
-/

set_option autoImplicit false

namespace Effect4.Run.Overwatch

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

variable {table : RowTable}

/-- **One wait transfer for every meaning family.** A local run that leads from the compiled
root to a host call the host does not answer has, past a budget bound, every member of a forward
agreement family waiting at that call. The rows, loop and block instances differ only in the
family and its forward theorem. Proof: `localWaitC_to_rowsB`'s, with the family abstracted. -/
theorem waits_of_forward {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (cf : Nat) (R st : σ) (o : Nat → RowsEnd (Option ExitV) σ)
    (forward : ∀ k, RunsToDO host root [] true k (fiberOf (compile root cf) []) Stores.empty R (o k))
    {fr : NFiber} {s : Stores} {ctx : Ctx}
    (hL : Leads host root (.live (fiberOf (compile root cf) []) Stores.empty) R (.live fr s ctx) st)
    (hc : IsCall fr.current = true) (hstop : hostAnswer host fr.current st = none)
    {row : Nat} {request : Val} (hcall : callOf fr.current = some (row, request)) :
    ∃ lower, ∀ k, lower ≤ k → o k = .waiting row request s st := by
  obtain ⟨c, hw⟩ := RunJoinC.terminal hL (localRunC_waits hc hstop s 0 ctx)
  have hnodiv := waits_not_diverges hw
  refine ⟨c, fun k hk => ?_⟩
  have hR := forward k
  rcases hm : o k with ⟨_ | ex, s', r'⟩ | ⟨row', request', s', r'⟩
  · rw [hm] at hR
    rcases hR with ⟨d, fr', s₁, r₁, reachedCtx, hkd, hd⟩ | hdiv
    · have h₁ := localRunC_mono c (d - c) _ _ _ hw
      rw [Nat.add_sub_cancel' (by omega), hd.none] at h₁
      cases h₁
    · exact absurd hdiv hnodiv
  · rw [hm] at hR
    rcases hR with ⟨d, hd⟩ | hdiv
    · have he := (hd 1).trans (localRunC_ofExit_nil ex true s' r' 0)
      cases localRunC_agree hw he
    · exact absurd hdiv hnodiv
  · rw [hm] at hR
    rcases hR with ⟨d, fr', reachedCtx, hd, hc', hcall', ha'⟩ | hdiv
    · have hw' := (hd 1).trans (localRunC_waits hc' ha' s' 0 reachedCtx)
      have hagree := localRunC_agree hw hw'
      injection hagree with hcur hs hst _
      subst hs hst
      rw [← hcur, hcall] at hcall'
      cases hcall'
      rfl
    · exact absurd hdiv hnodiv

/-- Reader: the existing loop lemma `localWaitC_to_rowsB` is the instance at the loop family. -/
theorem localWaitC_to_rowsB_instance {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (hfrag : LoopedDataRows table root = true) (cf : Nat) (R st : σ)
    {fr : NFiber} {s : Stores} {ctx : Ctx}
    (hL : Leads host root (.live (fiberOf (compile root cf) []) Stores.empty) R (.live fr s ctx) st)
    (hc : IsCall fr.current = true) (hstop : hostAnswer host fr.current st = none)
    {row : Nat} {request : Val} (hcall : callOf fr.current = some (row, request)) :
    ∃ lower, ∀ k, lower ≤ k →
      runRowsO host (denoteRowsB table k root []) Stores.empty R = .waiting row request s st :=
  waits_of_forward host root cf R st (fun k => runRowsO host (denoteRowsB table k root []) Stores.empty R)
    (fun k => localRunC_compileBO host root k root (rootPoint cf) [] true Stores.empty R hfrag rfl)
    hL hc hstop hcall

/-- **The recorded-command invariant at every funded cut.** `session_settled` without its rest
premise: the machine of a reached, funded, host-driven run is in a form of `Holds`, at a position
the local run with calls reaches under every host that gave the recorded answers. -/
theorem session_holds (s : Run) (hreach : Run.Reached s) (hfund : funded s = true)
    (hhost : hostDriven s = true) (hroot : PlainHooks s.built.program)
    {σ : Type} (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ)
    (hA : HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
      (Api.load s.built.program s.budget.compileFuel) st st') :
    ∃ p, Holds s.built.program s.budget.compileFuel s.machine p ∧
      Leads host s.built.program
        (.live (fiberOf (compile s.built.program s.budget.compileFuel) []) Stores.empty) st p st' := by
  have hmach := funded_replays s hreach hfund
  obtain ⟨p, hH, hL⟩ := tape_holds_host s.built.program s.built.table s.budget.fuel hroot
    s.budget.compileFuel host (tapeOf s) _ _ st st' (Or.inl ⟨rfl, rfl⟩)
    (session_answered s hfund) hhost hA
  rw [← hmach] at hH
  exact ⟨p, hH, hL⟩

/-- **Every pending call of a funded host-driven run is a wait of the meaning**, for every
program with plain hooks and every meaning family with a forward agreement at the compiled root.
This is `rows_loop_frontier_host` with its fragment and its family abstracted and its rest premise
dropped: a loaded machine and a yield hold no request (`requestOf_load`, `requestOf_Myield`). -/
theorem awaits_of_forward (s : Run) (hreach : Run.Reached s) (hfund : funded s = true)
    (hhost : hostDriven s = true) (hroot : PlainHooks s.built.program)
    {σ : Type} (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ)
    (hA : HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
      (Api.load s.built.program s.budget.compileFuel) st st')
    (o : Nat → RowsEnd (Option ExitV) σ)
    (forward : ∀ k, RunsToDO host s.built.program [] true k
      (fiberOf (compile s.built.program s.budget.compileFuel) []) Stores.empty st (o k)) :
    ∀ a ∈ Program.awaits s.machine, ∃ row, a.op = .external row ∧
      ((∀ (hrow : row < s.built.table.length), host.answer ⟨⟨row, hrow⟩, a.request⟩ st' = none) →
        ∃ lower, ∀ k, lower ≤ k → o k = .waiting row a.request s.machine.state st') := by
  intro a ha
  obtain ⟨p, hH, hL⟩ := session_holds s hreach hfund hhost hroot host st st' hA
  have hreq : Program.requestOf s.machine a.fiber a.token ≠ none := by
    rw [requestOf_of_mem_awaits s.machine a ha]
    exact Option.some_ne_none _
  rcases hH with ⟨hm, -⟩ | ⟨cur, K, i, s', n, tr, t, ctx, hm, -, -⟩ |
    ⟨cur, K, i, s', n, tr, t, ctx, hm, hp, hc, -⟩ | ⟨ex, fr, s', n, tr, nt, ctx, hm, -, -⟩
  · rw [hm] at hreq
    exact (requestOf_load hreq).elim
  · rw [hm] at hreq
    exact (requestOf_Myield hreq).elim
  · obtain ⟨j, v, w, rfl⟩ := eq_call_of_isCall hc
    rw [hm, awaits_Mcall_call (ctx := ctx), List.mem_singleton] at ha
    subst ha
    refine ⟨j, rfl, fun hno => ?_⟩
    rw [hp] at hL
    have hstop : hostAnswer host (Prim.async (EffName.external (.external j) v w) false none) st' =
        none := by
      rcases Nat.lt_or_ge j s.built.table.length with hj | hj
      · rw [hostAnswer_call host hj v w st']
        exact hno hj
      · exact dif_neg (Nat.not_lt.mpr hj)
    obtain ⟨lower, hlow⟩ := waits_of_forward host s.built.program s.budget.compileFuel st st' o
      forward hL hc hstop rfl
    refine ⟨lower, fun k hk => ?_⟩
    rw [hlow k hk, hm]
    rfl
  · rw [hm] at hreq
    exact (requestOf_Mexit hreq).elim

/-- Reader, the loop instance: `rows_loop_frontier_host`'s conclusion at every funded host-driven
cut, with no rest premise. -/
theorem loop_awaits_at_every_cut (s : Run) (hreach : Run.Reached s) (hfund : funded s = true)
    (hhost : hostDriven s = true) (hroot : LoopedRows s.built.program = true)
    (hfrag : LoopedDataRows s.built.table s.built.program = true)
    {σ : Type} (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ)
    (hA : HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
      (Api.load s.built.program s.budget.compileFuel) st st') :
    ∀ a ∈ Program.awaits s.machine, ∃ row, a.op = .external row ∧
      ((∀ (hrow : row < s.built.table.length), host.answer ⟨⟨row, hrow⟩, a.request⟩ st' = none) →
        ∃ lower, ∀ k, lower ≤ k →
          runRowsO host (denoteRowsB s.built.table k s.built.program []) Stores.empty st =
            .waiting row a.request s.machine.state st') :=
  awaits_of_forward s hreach hfund hhost (PlainHooks.of_loopedRows hroot) host st st' hA
    (fun k => runRowsO host (denoteRowsB s.built.table k s.built.program []) Stores.empty st)
    (fun k => localRunC_compileBO host s.built.program k s.built.program
      (rootPoint s.budget.compileFuel) [] true Stores.empty st hfrag rfl)

/-- Reader, the block instance (slice M2's target): every pending call of a reached, funded,
host-driven `BlockRows` run is a wait of the block meaning past a budget bound, under every host
that gave the recorded answers. It is `H9Blocks`'s pending-call form, at every funded cut. -/
theorem block_awaits_at_every_cut (s : Run) (hreach : Run.Reached s) (hfund : funded s = true)
    (hhost : hostDriven s = true) (hblock : BlockRows s.built.table s.built.program = true)
    {σ : Type} (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ)
    (hA : HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
      (Api.load s.built.program s.budget.compileFuel) st st') :
    ∀ a ∈ Program.awaits s.machine, ∃ row, a.op = .external row ∧
      ((∀ (hrow : row < s.built.table.length), host.answer ⟨⟨row, hrow⟩, a.request⟩ st' = none) →
        ∃ lower, ∀ k, lower ≤ k →
          runRowsO host (denoteBlockB s.built.table (bodiesOf s.built.program) k []
            s.built.program emptyCtx []) Stores.empty st =
            .waiting row a.request s.machine.state st') :=
  awaits_of_forward s hreach hfund hhost (PlainHooks.of_blockRows hblock) host st st' hA
    (fun k => runRowsO host (denoteBlockB s.built.table (bodiesOf s.built.program) k []
      s.built.program emptyCtx []) Stores.empty st)
    (fun k => compilesBlk_root host s.built.program hblock k (rootPoint s.budget.compileFuel)
      [] true Stores.empty st emptyCtx rfl rfl)

end Effect4.Run.Overwatch
