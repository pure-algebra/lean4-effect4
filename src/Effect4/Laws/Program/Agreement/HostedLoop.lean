import Effect4.Laws.Program.Agreement.LoopCalls

/-!
# Program.Agreement.HostedLoop — the local run with calls against the budgeted meaning

Slice L1 of `docs/research/2026-10-10-host-meaning-widening/README.md` (§1.5, §5.1 Q5 and Q6a):
the machine half of H8 and H9 on loops. `Agreement/Hosted.lean` closes the straight H8 with
`meaning_settled`, whose one straight step is the forward agreement `localRunC_compile`.
Everything else it reads (`Leads`, `Settled`, `tape_holds_host`) already holds on `LoopedRows`.
So the loop closing step needs three facts about the budgeted meaning (`denoteRowsB`):

* **forward** (Q5, `localRunC_compileB`, `Agreement/LoopCalls.lean`): at every budget, the local
  run with calls goes where the budgeted meaning goes, or diverges at the compile's frontier; at
  a budget cut it is still going after the budget's count of steps;
* **reverse** (Q6a, `localRunC_to_rowsB`): a finite local exit is some budget's finished
  approximant, by Q5 at that budget and the run's determinism;
* **stability** (Q2, `hostRunB_stable`, `Laws/Program/DenoteRowsB.lean`): a finished approximant
  stays finished at every larger budget.

From them: a waiting root has no finished approximant (`hostRunB_waits`), an exited root has its
exit at every budget past a bound (`hostRunB_exits`), and H8's closing step follows at the reply
host (`meaning_settledB_tape`). Concept `translation-simulation`, requirement R6. No global
compile-depth premise enters: a visited compile frontier is excluded by the settled machine, as
in `meaning_settled`. It says nothing of a waiting position's stores or request (Q4, Q6b), a
scope, a fork or an interruption.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

variable {table : RowTable}

/-- **The reverse agreement on loops** (Q6a): a local run with calls that exits from the root's
start within `c` steps is the finished approximant at budget `c`, with the same exit, stores and
host state. Q5 at budget `c`: a wait or a divergence never exits, a cut is still going after `c`
steps, so the approximant finishes, and the run is deterministic (`localRunC_agree`). A step of
`h8_loopedRows` and `denoteRowsB_eq_session_host`, through `hostRunB_exits`. It says nothing of
a waiting run (Q6b). -/
@[semantics "translation-simulation" (requirement := R6)]
theorem localRunC_to_rowsB {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    (root : NativeEff) (hfrag : LoopedDataRows table root = true) (cf : Nat) (R : σ) {c : Nat}
    {ex : ExitV} {s' : Stores} {r' : σ}
    (h : localRunC host root c (fiberOf (compile root cf) []) Stores.empty R = some (.exit ex s' r')) :
    ∃ k, hostRunB host k root [] Stores.empty R = some (some ex, (s', r')) := by
  refine ⟨c, ?_⟩
  have hR : RunsToDB host root [] true c (fiberOf (compile root cf) []) Stores.empty R
      (hostRunB host c root [] Stores.empty R) :=
    localRunC_compileB host root c root (rootPoint cf) [] true Stores.empty R hfrag rfl
  have hnodiv : ¬ Diverges host root (fiberOf (compile root cf) []) Stores.empty R := by
    rintro ⟨d, fr', s₁, r₁, hd, hfront⟩
    have h₁ := localRunC_mono c d _ _ _ h
    rw [hd c, localRunC_frontier _ s₁ r₁ hfront] at h₁
    cases h₁
  rcases hm : hostRunB host c root [] Stores.empty R with _ | ⟨_ | ex₂, s₂, r₂⟩
  · rw [hm] at hR
    rcases hR with ⟨d, fr', s₁, r₁, hd, hc, ha⟩ | hdiv
    · have hw := (hd 1).trans (localRunC_waits hc ha s₁ 0)
      cases localRunC_agree h hw
    · exact absurd hdiv hnodiv
  · rw [hm] at hR
    rcases hR with ⟨d, fr', s₁, r₁, hkd, hd⟩ | hdiv
    · have h₁ := localRunC_mono c (d - c) _ _ _ h
      rw [Nat.add_sub_cancel' hkd, ← Nat.zero_add d, hd 0] at h₁
      cases h₁
    · exact absurd hdiv hnodiv
  · rw [hm] at hR
    rcases hR with ⟨d, hd⟩ | hdiv
    · have he := (hd 1).trans (localRunC_ofExit_nil ex₂ true s₂ r₂ 0)
      cases localRunC_agree h he
      rfl
    · exact absurd hdiv hnodiv

/-- **A root waiting on a call the host does not answer has no finished approximant**, at any
budget. Q5 at the root: a finished approximant would make the run exit, or reach the compile's
frontier, and it waits. -/
theorem hostRunB_waits {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (hfrag : LoopedDataRows table root = true) (cf : Nat) (R st : σ) {fr : NFiber} {s : Stores}
    (hL : Leads host root (.live (fiberOf (compile root cf) []) Stores.empty) R (.live fr s) st)
    (hc : IsCall fr.current = true) (hstop : hostAnswer host fr.current st = none) (k : Nat)
    {ex : ExitV} {r : Stores × σ} : hostRunB host k root [] Stores.empty R ≠ some (some ex, r) := by
  intro hm
  obtain ⟨c, hreach⟩ := hL
  have hw : ∀ n, localRunC host root (n + 1 + c) (fiberOf (compile root cf) []) Stores.empty R =
      some (.waits _ _ _) := fun n => (hreach (n + 1)).trans (localRunC_waits hc hstop s n)
  have hR : RunsToDB host root [] true k (fiberOf (compile root cf) []) Stores.empty R
      (hostRunB host k root [] Stores.empty R) :=
    localRunC_compileB host root k root (rootPoint cf) [] true Stores.empty R hfrag rfl
  obtain ⟨s₂, r₂⟩ := r
  rw [hm] at hR
  rcases hR with ⟨d, hd⟩ | ⟨d, fr', s', r', hd, hfront⟩
  · have he := (hd 1).trans (localRunC_ofExit_nil ex true s₂ r₂ 0)
    cases localRunC_agree (hw 0) he
  · have h₁ := localRunC_mono (0 + 1 + c) d _ _ _ (hw 0)
    rw [hd (0 + 1 + c), localRunC_frontier _ s' r' hfront] at h₁
    cases h₁

/-- **An exited root has its exit at every budget past a bound**: Q6a finds one budget, Q2 keeps
it at every larger one. -/
theorem hostRunB_exits {σ : Type} (host : Effects.Comodel (RowSig table) σ) (root : NativeEff)
    (hfrag : LoopedDataRows table root = true) (cf : Nat) (R st : σ) {ex : ExitV} {s : Stores}
    (hL : Leads host root (.live (fiberOf (compile root cf) []) Stores.empty) R (.done ex s) st) :
    ∃ lower, ∀ k, lower ≤ k → hostRunB host k root [] Stores.empty R = some (some ex, (s, st)) := by
  obtain ⟨c, hrun⟩ := hL
  obtain ⟨k₀, hk₀⟩ := localRunC_to_rowsB host root hfrag cf R hrun
  exact ⟨k₀, fun _ hk => hostRunB_stable host hk root [] Stores.empty R hk₀⟩

/-- **H8's closing step on loops**: at the reply host read to its end, past a budget bound, the
coarse observation of the budgeted meaning is the settled machine's exit over its stores, and the
frontier when the root waits. `meaning_settled_tape` is its straight instance. -/
theorem meaning_settledB_tape (root : NativeEff) (hfrag : LoopedDataRows table root = true)
    (cf : Nat) (R : ReplyTape) {m : Api.Machine} {p : Pos} (hS : Settled root m p)
    (harmed : m.armed = [])
    (hL : Leads (tapeHost table) root (.live (fiberOf (compile root cf) []) Stores.empty) R p []) :
    ∃ lower, ∀ k, lower ≤ k → coarseRowsB table k root [] Stores.empty R =
      ((m.fiber? Api.root).bind RunFiber.exit).map fun ex => ((ex, m.state), []) := by
  rcases hS with ⟨cur, K, i, s, n, tr, t, rfl, rfl, -⟩ |
    ⟨cur, K, i, s, n, tr, t, rfl, rfl, hc, -⟩ | ⟨ex, fr, s, n, tr, nt, rfl, rfl, -⟩
  · cases harmed
  · refine ⟨0, fun k _ => ?_⟩
    rw [Mcall_fiber?]
    show coarseRowsB table k root [] Stores.empty R = none
    unfold coarseRowsB
    rw [meaningUnderB_eq_hostRunB]
    rcases hm : hostRunB (tapeHost table) k root [] Stores.empty R with _ | ⟨_ | ex', r⟩
    · rfl
    · rfl
    · exact absurd hm (hostRunB_waits (tapeHost table) root hfrag cf R [] hL hc
        (hostAnswer_tape_nil cur) k)
  · obtain ⟨lower, hlow⟩ := hostRunB_exits (tapeHost table) root hfrag cf R [] hL
    refine ⟨lower, fun k hk => ?_⟩
    rw [Mexit_exit]
    unfold coarseRowsB
    rw [meaningUnderB_eq_hostRunB, hlow k hk]
    rfl

end Effect4.Program.Agreement
