import Effect4.Laws.Program.Typed.World
import Effect4.Laws.Machine.ForkLedger
import Effect4.Laws.Program.InterpR
import Effect4.Laws.Auto.Obligations

/-!
Accepted local source/allocation bridge; its proof obligation remains explicit.
Owner: downstream Typed/ForkSource, not World: it imports the reference interpreter and should not raise World's floor.

A source-addressed spawn takes its program from the first child of the stamped
site. For fork/forkIn/forkScoped the site is the action Point; for a race entrant
it is the current list-cell Point. Their source decoders/callers establish that
this is the actual site; this law does not claim every reachable Origin is one of
those source forms. Internal forks with no source Point are outside this law.
The explicit source-body type is used to extend Γ at the actual newly allocated
id. Env typing is deliberately not claimed here: FitsIn would check only coarse
handles; M3 must supply value membership/the typed residual program premise.

This fixes the absence of a source connection in the generic fork_extension
statement without claiming the M3 world-quantified fork protocol or reachable
preservation. Keep both statements with their different responsibilities.
-/
set_option autoImplicit false
namespace Effect4.Program.Typed.M2ForkSourceWanted
open Effect4 Effect4.Machine Effect4.Program.Sched

/-- Fresh source fork: Γ receives the checked body type at the id spawn returns,
the appended ledger record has the same site, and the new fiber has the source-denoted body.
This is an append statement, not a first-match origin lookup on an arbitrary machine. -/
theorem source_fork_extension (root : NativeEff) (site : Point) (body : NativeEff)
    (env : TyEnv) (ty : EffTy) (w : World) (m : RState) (parent : RFiber)
    (options : Supervision.ForkOptions)
    (_bodyAt : Node.at_ (.eff root) (site.child 0).path = some (.eff body))
    (_bodyTy : Checker.check nativeSignature env (site.child 0).path body = .ok ty)
    (_state : w.state = m.state)
    (_ids : w.ids = m.fibers.map (fun f => f.id))
    (_fresh : w.Γ ⟨m.nextId⟩ = none) : ProofGraph.Obligation
    (let spawned := spawn (interpR root) m parent (denoteAt root (site.child 0))
        options site.path
     let newer := w.addFiber spawned.2.2 ty
     w.le newer ∧
     newer.state = spawned.1.state ∧
     newer.ids = spawned.1.fibers.map (fun f => f.id) ∧
     newer.Γ spawned.2.2 = some ty ∧
     ∃ child, child ∈ spawned.1.fibers ∧ child.id = spawned.2.2 ∧
       spawned.1.forks = m.forks ++
         [ForkRecord.mk child.id parent.id options.daemon site.path] ∧
       child.frame.current = denoteAt root (site.child 0) ∧
       Node.at_ (.eff root) (site.child 0).path = some (.eff body) ∧
       Checker.check nativeSignature env (site.child 0).path body = .ok ty) := ⟨⟩

theorem fork_source_extension (root : NativeEff) (site : Point) (body : NativeEff)
    (env : TyEnv) (ty : EffTy) (w : World) (m : RState) (parent : RFiber)
    (options : Supervision.ForkOptions)
    (bodyAt : Node.at_ (.eff root) (site.child 0).path = some (.eff body))
    (bodyTy : Checker.check nativeSignature env (site.child 0).path body = .ok ty)
    (hstate : w.state = m.state)
    (hids : w.ids = m.fibers.map (fun f => f.id))
    (fresh : w.Γ ⟨m.nextId⟩ = none) :
    (let spawned := spawn (interpR root) m parent (denoteAt root (site.child 0))
        options site.path
     let newer := w.addFiber spawned.2.2 ty
     w.le newer ∧
     newer.state = spawned.1.state ∧
     newer.ids = spawned.1.fibers.map (fun f => f.id) ∧
     newer.Γ spawned.2.2 = some ty ∧
     ∃ child, child ∈ spawned.1.fibers ∧ child.id = spawned.2.2 ∧
       spawned.1.forks = m.forks ++
         [ForkRecord.mk child.id parent.id options.daemon site.path] ∧
       child.frame.current = denoteAt root (site.child 0) ∧
       Node.at_ (.eff root) (site.child 0).path = some (.eff body) ∧
       Checker.check nativeSignature env (site.child 0).path body = .ok ty) := by
  intro spawned newer
  refine ⟨(fork_extension w spawned.2.2 ty fresh).1, ?_, ?_, insert_here _ _ _, ?_⟩
  · show w.state = spawned.1.state
    rw [hstate]
    rfl
  · show w.ids ++ [spawned.2.2] = spawned.1.fibers.map (fun f => f.id)
    rw [hids]
    change m.fibers.map (fun f : RFiber => f.id) ++ [spawned.2.2] =
      (m.fibers ++ [_]).map (fun f : RFiber => f.id)
    rw [List.map_append]
    rfl
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl, rfl, bodyAt, bodyTy⟩

/-- The source-addressed allocation also answers the exact new-id origin lookup,
provided both runtime lookups are fresh. World Γ freshness alone does not supply them.
Use this beside fork_source_extension, which owns the source/type and append facts. -/
theorem source_fork_originOf (root : NativeEff) (site : Point) (m : RState) (parent : RFiber)
    (options : Supervision.ForkOptions)
    (_fiberFresh : m.fiber? ⟨m.nextId⟩ = none)
    (_recordFresh : m.forkRecord? ⟨m.nextId⟩ = none) : ProofGraph.Obligation
    (let spawned := spawn (interpR root) m parent (denoteAt root (site.child 0)) options site.path
     spawned.1.originOf spawned.2.2 = some (.forked parent.id options.daemon site.path)) := ⟨⟩

@[aesop unsafe 90% apply (rule_sets := [Effect4.TypedState])]
theorem fork_source_originOf (root : NativeEff) (site : Point) (m : RState) (parent : RFiber)
    (options : Supervision.ForkOptions)
    (fiberFresh : m.fiber? ⟨m.nextId⟩ = none)
    (recordFresh : m.forkRecord? ⟨m.nextId⟩ = none) :
    (let spawned := spawn (interpR root) m parent (denoteAt root (site.child 0)) options site.path
     spawned.1.originOf spawned.2.2 = some (.forked parent.id options.daemon site.path)) := by
  change (spawn (interpR root) m parent (denoteAt root (site.child 0)) options site.path).1.originOf
    ⟨m.nextId⟩ = some (.forked parent.id options.daemon site.path)
  exact ForkLedger.spawn_originOf_new (interpR root) m parent (denoteAt root (site.child 0))
    options site.path fiberFresh recordFresh

attribute [aesop unsafe 90% apply (rule_sets := [Effect4.TypedState])] fork_source_extension

end Effect4.Program.Typed.M2ForkSourceWanted


#obligation_proved Effect4.Program.Typed.M2ForkSourceWanted.source_fork_extension := @Effect4.Program.Typed.M2ForkSourceWanted.fork_source_extension

#obligation_proved Effect4.Program.Typed.M2ForkSourceWanted.source_fork_originOf := @Effect4.Program.Typed.M2ForkSourceWanted.fork_source_originOf
#typed_state_obligations Effect4.Program.Typed.M2ForkSourceWanted ceiling 1 using aesop (rule_sets := [Effect4.Stores, Effect4.TypedState])
