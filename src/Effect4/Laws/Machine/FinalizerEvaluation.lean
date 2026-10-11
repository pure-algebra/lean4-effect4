import Effect4.Laws.Machine.FinalizerBookkeeping

/-!
# Finalizer accounting at every primitive evaluation

Concept: scope-lifetime-finalization, R11, at most one start per registration.
The consumer is `Program.FinalizerRun.funded_reachable`, then `Atomic.cleans_once`.
The evaluator retains the table's credits and spends only the selected fiber's credits.
Reach: every primitive and interpreter, under distinct stored fiber identities.
Source-use uniqueness, log provenance, progress, and host agreement remain separate.
-/

set_option autoImplicit false
namespace Effect4.Machine.FinalizerCredits
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- A delegated frame step changes its selected frame and the trace only. -/
theorem stepFrame_kept (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool) :
    IterKept choose m f (evaluatePrim.stepFrame interp m f y) := by
  refine ⟨?_, ?_, ?_, stepFrame_debit choose interp m f y⟩
  all_goals unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  all_goals dsimp only
  all_goals split <;> aesop (add safe apply [Eq.refl])

/-- A finalizer-program start uses the same debit as the pure frame step. -/
theorem finalizerOr_kept (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (y : Bool)
    (exit : Exit β ε δ ι α) :
    IterKept choose m f (evaluatePrim.finalizerOr interp m f y exit) := by
  have views : let next := evaluatePrim.finalizerOr interp m f y exit
      total choose next.machine = total choose m ∧
      (∀ id, atFiber choose next.machine id = atFiber choose m id) ∧ next.fiber.id = f.id := by
    unfold evaluatePrim.finalizerOr
    dsimp only
    split
    · split
      · exact ⟨rfl, fun _ => rfl, rfl⟩
      · have kept := stepFrame_kept choose interp m f y
        exact ⟨kept.1, kept.2.1, kept.2.2.1⟩
    · have kept := stepFrame_kept choose interp m f y
      exact ⟨kept.1, kept.2.1, kept.2.2.1⟩
  exact ⟨views.1, views.2.1, views.2.2, finalizerOr_debit choose interp m f y exit⟩

/-- The interrupt action edits the target, while retaining the caller's frame. -/
theorem interruptAs_kept (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (f : RunFiber ν σ β ε δ ι α χ) (y : Bool) (target who : FiberId) :
    IterKept choose m f (evaluatePrim.interruptAs interp m f y target who) := by
  unfold evaluatePrim.interruptAs
  split
  · exact IterKept.of_same (.refl choose m) rfl rfl
  · rename_i old found
    exact IterKept.of_same
      ((same_interruptUpdate choose interp m unique target old found (some who)
        (interp.stackAnnotations f.id)).trans
        (same_emit choose _ [.interruptRecorded (some who) target] rfl rfl)) rfl rfl

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Starting an empty child retains the caller's credits and the complete table projection. -/
theorem fork_neutral (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (site : List Nat)
    (immediately : Bool) :
    let born := spawn interp m f program options site
    let begun := start born.1 born.2.1 born.2.2 immediately
    Same choose m begun.1 ∧ begun.2.1.id = f.id ∧
      fiberCredits choose begun.2.1 = fiberCredits choose f := by
  refine ⟨(same_spawn choose interp m f program options site).trans
    (same_start choose _ _ _ immediately), ?_⟩
  cases immediately <;> exact ⟨rfl, rfl⟩

/-- Neutral mask frames carry no `onExit` credit. -/
theorem uninterruptible_credit (choose : ν → Bool) (f : FrameFiber ν σ β ε δ ι α) :
    stack choose f.uninterruptible.stack = stack choose f.stack := by
  unfold FrameFiber.uninterruptible
  split <;> rfl

/-- Entering an interruptible region also pushes only a neutral mask frame. -/
theorem interruptibleRegion_credit (choose : ν → Bool) (f : FrameFiber ν σ β ε δ ι α) :
    stack choose f.interruptibleRegion.1.stack = stack choose f.stack := by
  unfold FrameFiber.interruptibleRegion FrameFiber.setFiberInterruptible
  split <;> rfl

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Every fiber action keeps the table projection and the caller's finalizer credits. -/
theorem withFiber_kept (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (f : RunFiber ν σ β ε δ ι α χ) (y : Bool) (action : WithFiberAction ν σ β ε δ ι α χ) :
    IterKept choose m f (evaluatePrim.withFiber interp m f y action) := by
  unfold evaluatePrim.withFiber
  dsimp only
  split
  · rename_i program options site
    have facts := fork_neutral choose interp
      (if options.daemon then m else { m with middlewareInstalled := true }) f
      program options site options.startImmediately
    apply IterKept.of_same _ facts.2.1 facts.2.2
    have neutral : Same choose m
        (if options.daemon then m else { m with middlewareInstalled := true }) := by
      split <;> exact .refl choose m
    exact neutral.trans facts.1
  · rename_i program options scope site
    have facts := fork_neutral choose interp m f program { options with daemon := true }
      site options.startImmediately
    exact IterKept.of_same facts.1 facts.2.1 facts.2.2
  · rename_i program options site
    split
    · have facts := fork_neutral choose interp m f program { options with daemon := true }
        site options.startImmediately
      exact IterKept.of_same facts.1 facts.2.1 facts.2.2
    · exact IterKept.of_same (.refl choose m) rfl rfl
  · split <;> exact IterKept.of_same (.refl choose m) rfl rfl
  · exact IterKept.of_same (same_linkScope choose interp m unique _ _ _ _ _) rfl rfl
  · exact IterKept.of_same (.refl choose m) rfl rfl
  · exact interruptAs_kept choose interp m unique f y _ _
  · split <;> exact IterKept.of_same (.refl choose m) rfl rfl
  · exact IterKept.of_same (.refl choose m) rfl rfl
  · exact IterKept.of_same (same_countdown choose interp m unique f _ _ _) (by
        unfold countdownPark
        dsimp only
        split <;> rfl)
      (countdown_credit choose interp m f _ _ _)
  · exact IterKept.of_same (same_countdown choose interp m unique f _ _ _) (by
        unfold countdownPark
        dsimp only
        split <;> rfl)
      (countdown_credit choose interp m f _ _ _)
  · exact IterKept.of_same (.refl choose m) rfl rfl
  · exact IterKept.of_same (same_countdown choose interp m unique f _ _ _) (by
        unfold countdownPark
        dsimp only
        split <;> rfl)
      (countdown_credit choose interp m f _ _ _)
  · exact IterKept.of_same (same_beginRace choose interp m f y _ _ _) rfl rfl
  · exact IterKept.of_same (same_beginRace choose interp m f y _ _ _) rfl rfl
  · exact IterKept.of_same (.refl choose m) rfl (uninterruptible_credit choose f.frame)
  · exact IterKept.of_same (.refl choose m) rfl (interruptibleRegion_credit choose f.frame)
  · exact IterKept.of_same (same_emit choose m [.contextSet f.id _] rfl rfl) rfl rfl
  · exact IterKept.of_same (.refl choose m) rfl rfl
  · exact IterKept.of_same (.refl choose m) rfl rfl
  · split <;> exact IterKept.of_same (.refl choose m) rfl rfl
  · exact IterKept.of_same (same_forkFinalizers choose interp m f _) rfl rfl
  · exact IterKept.of_same (.refl choose m) rfl rfl
  · exact IterKept.of_same (same_map choose m _ (fun _ => rfl) (fun _ => rfl)) rfl rfl
  · split <;> exact IterKept.of_same (.refl choose m) rfl rfl
  · exact IterKept.of_same (.refl choose m) rfl (uninterruptible_credit choose f.frame)

/-- Every primitive evaluation satisfies the same local debit and table projection. -/
theorem evaluatePrim_kept (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (f : RunFiber ν σ β ε δ ι α χ) (y : Bool) :
    IterKept choose m f (evaluatePrim interp m f y) := by
  unfold evaluatePrim
  split
  · exact IterKept.of_same (same_emit choose _ [.parkedOn f.id m.nextToken] rfl rfl) rfl rfl
  · dsimp only
    split
    · exact IterKept.of_same (.refl choose m) rfl rfl
    · split <;> exact IterKept.of_same
        (same_emit choose _ [.parkedOn f.id m.nextToken] rfl rfl) rfl rfl
  · split
    · exact IterKept.of_same (.refl choose m) rfl rfl
    · unfold registerRace
      split <;> exact IterKept.of_same (.refl choose m) rfl rfl
    · rename_i targets _
      have same := same_countdown choose interp m unique f targets .exitsValue false
      have credit := countdown_credit choose interp m f targets .exitsValue false
      have key := (countdownPark_keepsMask (MaskAged.refl m) interp f targets .exitsValue false).2.1
      split
      rename_i after next parked equation
      rw [equation] at same credit key
      exact IterKept.of_same same key credit
    · rename_i target mode _
      split
      · exact IterKept.of_same (.refl choose m) rfl rfl
      · rename_i old found
        split
        · exact IterKept.of_same (.refl choose m) rfl rfl
        · refine IterKept.of_same ?_ rfl rfl
          let bumped : RunMachine ν σ β ε δ ι α χ St := { m with nextToken := m.nextToken + 1 }
          let observed : RunFiber ν σ β ε δ ι α χ :=
            { old with observers := old.observers ++ [.resumeAwait f.id m.nextToken mode] }
          exact (same_update choose bumped old observed unique
            (by change m.fiber? old.id = some old
                simpa only [RunMachine.id_of_fiber? found] using found) rfl rfl).trans
            (same_emit choose (bumped.update observed) [.parkedOn f.id m.nextToken] rfl rfl)
    · split
      · split
        · exact withFiber_kept choose interp m unique f y _
        · exact stepFrame_kept choose interp m f y
      · split <;> exact IterKept.of_same (.refl choose m) rfl rfl
      · exact finalizerOr_kept choose interp m f y _
      · exact finalizerOr_kept choose interp m f y _
      · exact stepFrame_kept choose interp m f y

end Effect4.Machine.FinalizerCredits
