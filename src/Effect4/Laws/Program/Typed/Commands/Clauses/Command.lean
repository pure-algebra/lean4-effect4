import Effect4.Laws.Program.Typed.Commands.Clauses.Spawn

/-!
# Laws.Program.Typed.Commands.Clauses.Command — the command-shaped evaluator clauses

Concept 4 (the configuration invariant `I`); steps of `M6Ledger.step_deliver` and
`M6Ledger.step_loop` through `evaluate_keeps` (`FiberClauseKeeps`). Three fiber operations whose
work is a machine step beside the fiber's own: `interruptAll` queues one `interruptTarget` per
target and the `afterInterrupt` that awaits them (`Machine/Fibers.lean:1556-1564`), `runIn` links
a fiber to a scope inline (`linkScope`, `:1005-1037`, the `link` command's step), and
`dropObservers` filters every fiber's token observers (`:1434-1441`).

Not established here: progress, or that the queued commands' own steps are typed (their
`StepPreserves` are `Commands/Race.lean`'s and `Commands/Bookkeeping.lean`'s).
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## `interruptAll` -/

/-- The interrupts `interruptAll` queues: each reads nothing, owns nothing and carries no key. -/
theorem configTyped_cons_interrupts {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {q : List RCmd} (typed : ConfigTyped root rootTy w m q) (targets : List FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    ConfigTyped root rootTy w m
      ((targets.map fun t => (Cmd.interruptTarget t who extra : RCmd)) ++ q) := by
  induction targets with
  | nil => exact typed
  | cons t ts ih =>
    rw [List.map_cons, List.cons_append]
    exact configTyped_cons_plain ih _ trivial trivial trivial (fun _ h => by cases h) trivial rfl
      (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)

/-- **`interruptAll`** (`fiberInterruptAll`, `Machine/Fibers.lean:1556-1564`, `internal/effect.ts:888-915`,
D6b): the answer frame saved first; each target's interrupt queued, then `afterInterrupt` for the
host, whose reply (`unit`, the targets awaited) walks the saved stack. The targets are declared
(the row's pre), so the await's columns exist (`FiberListColumns` at `unknown`). -/
theorem clause_interruptAll (root : ProgramSource) (rootTy : EffTy) (targets : List FiberId)
    (who : Option FiberId) : FiberClauseKeeps root rootTy (.interruptAll targets who) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, pre, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have old := ev.typed.machine.fiber hmem
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [ev.running] at idle
      cases idle
  -- the saved answer frame, an arrow from `unit` to the code's type
  let fr' : RSaved := { f.frame with stack := .answer (seqR next) :: f.frame.stack }
  let g : RFiber := { f with frame := fr' }
  have typedNext' : ∀ w', w.leHost w' → ∀ ans : Val, ans = Val.unit →
      TypedProg root w' tin (next ans) :=
    fun w' o ans post => typedNext w' o ans post
  have frame := Evaluating.unitAnswerFrame typedNext'
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  have fresh : FiberTyped root w ((m.update f).update g) g :=
    fiberTyped_frame old ev.look ev.running fr'
      (fun ty' d => by
        rw [same ty' d]
        exact ⟨_, positionStack_of_host (hostStack_push frame stack)⟩)
      ⟨prov.recorded, prov.deferred⟩
      (fun _ h => by
        change raceRegistrationR f.frame.current = some _ at h
        rw [hc, raceRegistrationR_typed current] at h
        cases h)
  have edited : ConfigTyped root rootTy w (m.update g) rest := by
    rw [← rupdate_rupdate m (show g.id = f.id from rfl)]
    exact configTyped_frame_edit ev.typed rfl ev.look ev.running fr' fresh
  obtain ⟨f0, hf0, _⟩ := ev.stale
  have lookG : (m.update g).fiber? f.id = some g :=
    rfiber?_update_self (f := f0) (g := g) (by rw [rfiber?_id hf0]; exact hf0) (rfiber?_id hf0).symm
  have after : ConfigTyped root rootTy w (m.update g)
      (.afterInterrupt f.id y (.awaitAll targets) :: rest) := by
    refine configTyped_cons_afterAwaitAll edited y targets ⟨g, lookG, ev.running, notParked⟩
      (by rw [commandOwner_rupdate]; exact owner_free ev.typed.queue rfl) fun x hx => ?_
    rw [lookG] at hx
    cases hx
    refine ⟨.unknown, .unknown, fun t ht => ?_, ty, declared,
      hostStack_push frame (hostStack_races (m := m.update f) (m' := m.update g)
        (racesKept_of_eq fun _ => rfl) stack), ⟨prov.recorded, prov.deferred⟩⟩
    obtain ⟨fty, hfty⟩ := Option.isSome_iff_exists.mp (pre t ht)
    exact ⟨fty, hfty, subN_unknown _, subN_unknown _⟩
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (FiberAction.interruptAll (interpRAt root.program m.completedExits) m g y targets
      who))
  refine ⟨w, leHost_refl w, ?_⟩
  show ConfigTyped root rootTy w (m.update g)
    ((targets.map fun t => (Cmd.interruptTarget t (some (who.getD g.id))
      ((interpRAt root.program m.completedExits).stackAnnotations g.id) : RCmd)) ++
      [Cmd.afterInterrupt g.id y (ParkKind.awaitAll targets)] ++ rest)
  rw [List.append_assoc]
  exact configTyped_cons_interrupts after targets _ _

end Effect4.Program.Typed
