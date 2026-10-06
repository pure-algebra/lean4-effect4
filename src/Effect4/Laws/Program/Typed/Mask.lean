import Effect4.Laws.Program.Typed.LayerArm
import Effect4.Laws.Program.Intro
import Effect4.Laws.Program.Simulation.Evaluate
import Effect4.Laws.Program.Authoring.Mask

/-!
# Laws.Program.Typed.Mask — the mask that restores: its image, its body, its boundaries

Decisions rows 227, 239 and 244 to 246; the mask's second note
(`docs/research/2026-10-05-claude-lead/mask-second-note.md`, F3, F7 and F10). Three registry
claims (`tools/Tools/SemanticsRegistry.lean`) have their statements here, in the order of the
note's F10. No statement names a module that uses the mask.

* **`saved-mask-image-membership`** (concept `store-typing`, requirement R4) is
  `saved_mask_image_membership`, a `SavedMaskImage`: membership at `Ty.maskRestore` is exactly
  the two saved images, in `Fits` and in the shape check; the image is no Boolean and a Boolean
  is no image, and no subtyping relates the two types; the target is reserved against an
  external allocation, a host answer column and a service carrier; an image holds no handle,
  so every world, every store and every environment keep its membership.
* **`scoped-body-substitution-boundary`** (concept `residual-program-typing`, requirement R4)
  is `scoped_body_substitution_boundary`, a `RestoreBodyBoundary`: a restore site is one node
  that binds nothing, with its checked body at child 0; both saved choices run that one body
  in the node's environment; a typed point at the node denotes a typed program, its saved
  term evaluates to an image, and its body's point is typed at the node's type.
* **`saved-mask-restoration`** (concept `scope-lifetime-finalization`, requirement R11) is
  `saved_mask_restoration`, a `MaskRestoration`: the five statements of the note's F7, at the
  boundaries of regions. Each boundary is one step of the machine or one pass of a saved
  frame.

Each top node is a decomposition: its proof cites one theorem for each field, so its status is
derived from theirs (`#plan_status`). No field rests on a planned goal.

Reach. `Fits` at any world; the frame machine's clause `evaluatePrim.withFiber` and the hook
every passed frame runs, `Prim.ensure` (`src/Effect4/Machine/Frames.lean`), at any interpreter;
the compile `compileEff` at a positive compile budget; the typed state at a source whose layer
references are well formed, at a world whose service table is the source's.

What they do not establish. No reply admission: a host answer is refused at the column, and
`externalValue` is not restated here. No agreement with a target. No progress. **No statement
that the flag at a region's completed exit is its entry flag for a body that changes no
flag itself**: a region that changes the flag saves the earlier flag in a frame, and that
frame's pass returns it (`MaskRestoration.saved`, `.returned`); a region that changes nothing
pushes no frame, and its exit flag is what its body left. That every sub-region of an
arbitrary body returns its own flag is an invariant of runs that no theorem states yet (the
receipt's open part). The finite controls are `Test/Program/MaskContract.lean`, S7 and S9.
No statement that every step of the body has one flag: a body may hold regions of its own.

Consumers. The Queue's waiting wrapper and the Semaphore's protected permit read
`MaskRestoration` for the flag at their registration and at their wait, `RestoreBodyBoundary`
for the typed body of a restore site, and `SavedMaskImage` wherever a saved value is stored or
passed.
-/

set_option autoImplicit false

/-! ## The frame's two region entries, as functions of the flag -/

namespace Effect4.FrameFiber

universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

/-- After `uninterruptible` the flag is false, whatever it was.
census: interrupt.uninterruptible-mask -/
@[semantics "scope-lifetime-finalization"]
theorem uninterruptible_flag (self : FrameFiber ν σ β ε δ ι α) :
    self.uninterruptible.interruptible = false := by
  cases h : self.interruptible with
  | false => rw [uninterruptible_already_masked self h]; exact h
  | true => rw [uninterruptible_masks self h]

/-- `uninterruptible` saves the earlier flag exactly when it changes it: the restoring frame
holds `true`, and it is pushed only on an interruptible fiber.
census: interrupt.uninterruptible-mask -/
@[semantics "scope-lifetime-finalization"]
theorem uninterruptible_stack (self : FrameFiber ν σ β ε δ ι α) :
    self.uninterruptible.stack =
      if self.interruptible = true then Prim.setInterruptible true :: self.stack
      else self.stack := by
  cases h : self.interruptible with
  | false => rw [uninterruptible_already_masked self h, if_neg Bool.false_ne_true]
  | true => rw [uninterruptible_masks self h, if_pos rfl]

/-- After the `interruptible` region's entry the flag is true, whatever it was. -/
@[semantics "scope-lifetime-finalization"]
theorem interruptibleRegion_flag (self : FrameFiber ν σ β ε δ ι α) :
    self.interruptibleRegion.fst.interruptible = true := by
  cases h : self.interruptible with
  | false => rw [interruptibleRegion_masked self h]; rfl
  | true => rw [interruptibleRegion_already self h]; exact h

/-- The `interruptible` region saves the earlier flag exactly when it changes it: the
re-masking frame holds `false`, and it is pushed only on a masked fiber. -/
@[semantics "scope-lifetime-finalization"]
theorem interruptibleRegion_stack (self : FrameFiber ν σ β ε δ ι α) :
    self.interruptibleRegion.fst.stack =
      if self.interruptible = true then self.stack
      else Prim.setInterruptible false :: self.stack := by
  cases h : self.interruptible with
  | false =>
    rw [interruptibleRegion_masked self h, setFiberInterruptible_pushes,
      if_neg Bool.false_ne_true]
  | true => rw [interruptibleRegion_already self h, if_pos rfl]

/-- A masked fiber that becomes interruptible with a cause pending fails at once, before the
region's body, with that cause. -/
@[semantics "scope-lifetime-finalization"]
theorem interruptibleRegion_pending (self : FrameFiber ν σ β ε δ ι α) (cause : Cause ε δ ι α)
    (masked : self.interruptible = false) (pending : self.interruptedCause = some cause) :
    self.interruptibleRegion.snd = some (Prim.failure cause) := by
  rw [interruptibleRegion_masked self masked]
  exact setFiberInterruptible_immediate_failure self cause pending

/-- With no cause pending the region's entry fails nothing. -/
@[semantics "scope-lifetime-finalization"]
theorem interruptibleRegion_clean (self : FrameFiber ν σ β ε δ ι α)
    (clean : self.interruptedCause = none) : self.interruptibleRegion.snd = none := by
  cases h : self.interruptible with
  | false =>
    rw [interruptibleRegion_masked self h]
    exact setFiberInterruptible_no_pending self clean
  | true => rw [interruptibleRegion_already self h]

end Effect4.FrameFiber

/-! ## The machine's clauses for the mask's three actions

Each is an equation on the machine's own definition (`evaluatePrim.withFiber`,
`src/Effect4/Machine/Fibers.lean`), as the clauses of `Laws/Machine/Clauses.lean` are. -/

-- The `DecidableEq` section variables are what the machine's definitions take.
set_option linter.unusedSectionVars false

namespace Effect4.Machine

universe u v

open Effect4

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- `uninterruptibleMask((restore) => succeed(restore))` (`internal/effect.ts:4340-4352`;
decisions row 245): the fiber masked as `uninterruptible` masks it, and the saved state of the
flag at the entry answered as the next code. Nothing else of the machine or the fiber moves.
census: interrupt.uninterruptible-mask -/
@[semantics "scope-lifetime-finalization"]
theorem withFiber_getInterruptible (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) :
    evaluatePrim.withFiber interp m f yielding WithFiberAction.getInterruptible =
      ⟨m, { f with frame := { f.frame.uninterruptible with
          current := Prim.success (interp.restoreValue f.frame.interruptible) } },
        yielding, Outcome.continue_, []⟩ := by
  simp only [evaluatePrim.withFiber]

/-- `uninterruptible(body)` (`internal/effect.ts:4302-4310`): the fiber masked, the body next. -/
@[semantics "scope-lifetime-finalization"]
theorem withFiber_setInterruptible_false (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (body : Prim ν σ β ε δ ι α) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.setInterruptible body false) =
      ⟨m, { f with frame := { f.frame.uninterruptible with current := body } },
        yielding, Outcome.continue_, []⟩ := by
  simp only [evaluatePrim.withFiber]

/-- `interruptible(body)` (`internal/effect.ts:4331-4338`): the region's entry, then the body, or
the pending cause's failure in its place. -/
@[semantics "scope-lifetime-finalization"]
theorem withFiber_setInterruptible_true (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (body : Prim ν σ β ε δ ι α) :
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.setInterruptible body true) =
      ⟨m, { f with frame := { f.frame.interruptibleRegion.fst with
          current := f.frame.interruptibleRegion.snd.getD body } },
        yielding, Outcome.continue_, []⟩ := by
  simp only [evaluatePrim.withFiber]

/-- **A region's entry sets its own flag**, at every fiber and whatever stands around it: the
flag after the step is the action's. A region inside a mask's body, in a restore site or
outside one, follows this one rule (the note's F7, statement 3). -/
@[semantics "scope-lifetime-finalization"]
theorem withFiber_setInterruptible_flag (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (body : Prim ν σ β ε δ ι α) (flag : Bool) :
    (evaluatePrim.withFiber interp m f yielding
      (WithFiberAction.setInterruptible body flag)).fiber.frame.interruptible = flag := by
  cases flag with
  | false =>
    rw [withFiber_setInterruptible_false]
    exact FrameFiber.uninterruptible_flag f.frame
  | true =>
    rw [withFiber_setInterruptible_true]
    exact FrameFiber.interruptibleRegion_flag f.frame

/-- **A region's entry saves the earlier flag exactly when it changes it**: the frame it pushes
holds the flag the fiber had, and it is pushed only when that flag is not the region's. -/
@[semantics "scope-lifetime-finalization"]
theorem withFiber_setInterruptible_stack (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (body : Prim ν σ β ε δ ι α) (flag : Bool) :
    (evaluatePrim.withFiber interp m f yielding
      (WithFiberAction.setInterruptible body flag)).fiber.frame.stack =
      if f.frame.interruptible = flag then f.frame.stack
      else Prim.setInterruptible f.frame.interruptible :: f.frame.stack := by
  cases flag with
  | false =>
    rw [withFiber_setInterruptible_false]
    show f.frame.uninterruptible.stack = _
    rw [FrameFiber.uninterruptible_stack]
    cases f.frame.interruptible <;> rfl
  | true =>
    rw [withFiber_setInterruptible_true]
    show f.frame.interruptibleRegion.fst.stack = _
    rw [FrameFiber.interruptibleRegion_stack]
    cases f.frame.interruptible <;> rfl

end Effect4.Machine

namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Agreement

/-! ## 1. The saved image and its membership (`saved-mask-image-membership`)

`fits_maskRestore_iff`, `fits_savedMask` and `fits_maskRestore_inv` are in
`Typed/Membership.lean`, beside the arm of `Fits` they read. -/

/-- **The shape check at the saved state's type is exactly the two saved images**, at every
allocation table: no handle kind takes the reserved target, an external handle may not take it,
and the frame's other arm reads the image's own reader. -/
@[semantics "store-typing"]
theorem hasTy_maskRestore_iff (allocated : List String) (v : Val) :
    Val.hasTy v Ty.maskRestore allocated = true ↔ ∃ flag, v = Val.savedMask flag := by
  constructor
  · intro h
    change Val.hasTy v (.handle Ty.maskRestoreTarget) allocated = true at h
    simp only [Val.hasTy] at h
    split at h
    · split at h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd (Bool.and_eq_true_iff.mp h).1 (by decide)
      · exact Bool.noConfusion h
    · rcases Bool.or_eq_true_iff.mp h with h | h
      · exact absurd (Bool.and_eq_true_iff.mp h).1 (by decide)
      · obtain ⟨flag, hflag⟩ := Option.isSome_iff_exists.mp (Bool.and_eq_true_iff.mp h).2
        exact ⟨flag, Val.savedMask?_exact hflag⟩
  · rintro ⟨flag, rfl⟩
    cases flag <;> rfl

/-- An image is valid in every store: it holds no handle (`Value.maskImage_handleFree`). So a
cell, a promise and a scope's exit may hold it, and the store's validity does not read it. -/
@[semantics "store-typing"]
theorem savedMask_validIn (s : Stores) (flag : Bool) : (Val.savedMask flag).validIn s = true := by
  rw [Val.validIn_eq_handles, Value.maskImage_handleFree flag]
  rfl

/-- The statements of the claim `saved-mask-image-membership` (decisions row 244). -/
structure SavedMaskImage : Prop where
  /-- Membership at the saved state's type is exactly the two canonical images, in every
  world. -/
  member : ∀ (w : World) (v : Val), Fits w v Ty.maskRestore ↔ ∃ flag, v = Val.savedMask flag
  /-- The shape check agrees, at every allocation table. -/
  shape : ∀ (allocated : List String) (v : Val),
    Val.hasTy v Ty.maskRestore allocated = true ↔ ∃ flag, v = Val.savedMask flag
  /-- The image is exact: its reader answers the bit, and only an image reads back. -/
  reads : ∀ flag : Bool, Val.savedMask? (Val.savedMask flag) = some flag
  exact : ∀ (v : Val) (flag : Bool), Val.savedMask? v = some flag → v = Val.savedMask flag
  /-- An image is no member of `bool`, and a Boolean is no member of the saved state's type. -/
  notBool : ∀ (w : World) (flag : Bool), ¬ Fits w (Val.savedMask flag) .bool
  boolNot : ∀ (w : World) (b : Bool), ¬ Fits w (Val.bool b) Ty.maskRestore
  /-- No subtyping relates the two types, so no widening of one reaches the other. -/
  unrelated : Ty.sub Ty.maskRestore.normalize Ty.bool.normalize = false ∧
    Ty.sub Ty.bool.normalize Ty.maskRestore.normalize = false
  /-- The target is reserved. No external allocation takes it. -/
  external : externalHandleTarget Ty.maskRestoreTarget = false ∧
    ∀ (allocated : List String) (index : Nat),
      externalValue Ty.maskRestore allocated (.nat index) = none
  /-- The column scan finds the type at the column's own position, so a host answer or error
  column that mentions it is refused (`rowChecks`, `Program/SigApp.lean`). -/
  column : ∀ pos : Path, findInternalHandle pos Ty.maskRestore = some pos
  /-- No service carries it in the first profile. -/
  carrier : flatCarrier Ty.maskRestore = false
  /-- An image holds no handle. -/
  handleFree : ∀ flag : Bool, Store.Val.handles (Val.savedMask flag) = []
  /-- So a member is live in every world and valid in every store. -/
  live : ∀ (w : World) (v : Val), Fits w v Ty.maskRestore → Live w v
  valid : ∀ (s : Stores) (flag : Bool), (Val.savedMask flag).validIn s = true
  /-- And its membership reads no world: a typed store, a typed environment and a later world
  keep it, as any two worlds do. -/
  worldFree : ∀ (w w' : World) (v : Val), Fits w v Ty.maskRestore → Fits w' v Ty.maskRestore

/-- **The saved state's membership** (the claim `saved-mask-image-membership`; concept
`store-typing`, requirement R4; decisions row 244). The image is the frame `ctor 7` over the
bit (`Value.maskImage`, `src/Effect4/Machine/Value.lean`): data, with no handle.

Reach: `Fits` at any world, `Val.hasTy` at any allocation table, the three refusals at their
own functions. It does not establish reply admission: `externalValue` asked at the type admits
an image as it admits any handle-free member, and the refusal of a host answer is the column
scan at table admission. Its consumers are the getter's typed clause and M5 arm
(`clause_getInterruptible`, `getInterruptible_arm`), the restore node's arm (`restore_arm`),
and every store that holds a saved value. -/
@[semantics "store-typing" (requirement := R4)]
theorem saved_mask_image_membership : SavedMaskImage where
  member := fits_maskRestore_iff
  shape := hasTy_maskRestore_iff
  reads := Val.savedMask?_savedMask
  exact := fun _ _ h => Val.savedMask?_exact h
  notBool := fun _ _ h => h
  boolNot := fun _ _ h => absurd h.1 (by decide)
  unrelated := by decide +kernel
  external := ⟨by decide, fun allocated index => by
    show (if externalHandleTarget Ty.maskRestoreTarget && index == allocated.length then
      some (allocated ++ [Ty.maskRestoreTarget], Value.external index) else none) = none
    rw [show externalHandleTarget Ty.maskRestoreTarget = false by decide]
    rfl⟩
  column := fun pos => by
    show (if internalHandleTargets.contains Ty.maskRestoreTarget then some pos else none) =
      some pos
    rw [if_pos (by decide)]
  carrier := by decide
  handleFree := Value.maskImage_handleFree
  live := fun _ _ h => handle_fits_live h
  valid := savedMask_validIn
  worldFree := fun w w' v h => (fits_maskRestore_iff w' v).mpr ((fits_maskRestore_iff w v).mp h)

/-! ## 2. The restore node's body (`scoped-body-substitution-boundary`) -/

section RestoreNode

variable {root : NativeEff} {p : Point} {saved : Term} {body : NativeEff} {k : Nat}

/-- At a restore node the point's action is `interruptible` over the body resolved at child 0.
`compileEff` names this action only at a true bit. -/
@[semantics "residual-program-typing"]
theorem actionAt_restore
    (hat : Node.at_ (.eff root) p.path = some (.eff (.restore saved body))) :
    actionAt root p =
      some (WithFiberAction.setInterruptible (resolve root (p.child 0)) true) := by
  unfold actionAt
  rw [hat]

/-- The body resolved at child 0 is the body compiled at child 0, in the node's environment. -/
@[semantics "residual-program-typing"]
theorem resolve_restore_body
    (hat : Node.at_ (.eff root) p.path = some (.eff (.restore saved body))) :
    resolve root (p.child 0) = compileEff body (p.child 0) := by
  have child : Node.at_ (.eff root) (p.child 0).path = some (.eff body) := at_child_of hat 0
  unfold resolve
  rw [child]

/-- **A false bit is the identity on the node**: the compiled code is the body's own, at
child 0. The node spends no step, pushes no frame and changes no flag.
census: interrupt.uninterruptible-mask -/
@[semantics "residual-program-typing"]
theorem compileEff_restore_false (hf : p.fuel = k + 1)
    (hsaved : evalTerm p.env saved = some (Val.savedMask false)) :
    compileEff (.restore saved body) p = compileEff body (p.child 0) := by
  rw [compileEff_restore saved body hf, hsaved, Option.bind_some, Val.savedMask?_savedMask]

/-- **A true bit is `interruptible` over the body**: the node compiles to its point's action.
census: interrupt.uninterruptible-mask -/
@[semantics "residual-program-typing"]
theorem compileEff_restore_true (hf : p.fuel = k + 1)
    (hsaved : evalTerm p.env saved = some (Val.savedMask true)) :
    compileEff (.restore saved body) p = Prim.withFiber (EffThunk.act p) := by
  rw [compileEff_restore saved body hf, hsaved, Option.bind_some, Val.savedMask?_savedMask]

end RestoreNode

section TypedRestore

variable {root : ProgramSource} {w : World} {p : Point} {ty : EffTy} {saved : Term}
  {body : NativeEff}

/-- **The saved term of a typed restore node evaluates to a saved image**: the node never
takes its wrong-shape refusal (`Checker.inv_restore`, `evalTerm_progress_env`,
`fits_maskRestore_inv`). -/
@[semantics "residual-program-typing"]
theorem restore_saved_evaluates
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.restore saved body)))
    (hpt : PointTyped root w p ty) :
    ∃ flag, evalTerm p.env saved = some (Val.savedMask flag) := by
  obtain ⟨env, hcheck, henv, -⟩ := hpt.at_node hat
  rw [Eff.expandIn_restore] at hcheck
  obtain ⟨hsaved, -⟩ := Checker.inv_restore _ _ _ _ _ _ hcheck
  obtain ⟨v, hv, hvfit⟩ := evalTerm_progress_env henv hsaved
  obtain ⟨flag, rfl⟩ := fits_maskRestore_inv hvfit
  exact ⟨flag, hv⟩

/-- **The body's point is typed at the node's type**, with the node's environment and view: a
restore site binds nothing, and a mask changes no column of the type. -/
@[semantics "residual-program-typing"]
theorem restore_body_typed
    (hat : Node.at_ (.eff root.program) p.path = some (.eff (.restore saved body)))
    (hpt : PointTyped root w p ty) : PointTyped root w (p.child 0) ty := by
  obtain ⟨env, hcheck, henv, hview⟩ := hpt.at_node hat
  rw [Eff.expandIn_restore] at hcheck
  obtain ⟨-, hcb⟩ := Checker.inv_restore _ _ _ _ _ _ hcheck
  exact pointTyped_child hat rfl rfl hcb henv hview

end TypedRestore

/-- The statements of the claim `scoped-body-substitution-boundary`, for the restore node
(decisions rows 245 and 246). -/
structure RestoreBodyBoundary : Prop where
  /-- The node's one child is its body, child 0; the saved term is no child. -/
  child : ∀ (saved : Term) (body : NativeEff),
    (Node.eff (.restore saved body) : Node NativeOp).child 0 = some (.eff body) ∧
      (Node.eff (.restore saved body) : Node NativeOp).child 1 = none
  /-- The node binds nothing at any child. -/
  binds : ∀ (saved : Term) (body : NativeEff) (i : Nat),
    (Node.eff (.restore saved body) : Node NativeOp).binders i = 0
  /-- The checker reads the saved term at the saved state's type, and the body at child 0, in
  the node's own environment and at the node's type. -/
  checked : ∀ (sig : Signature NativeOp) (env : TyEnv) (path : List Nat) (saved : Term)
    (body : NativeEff) (t : EffTy), Checker.check sig env path (.restore saved body) = .ok t →
      termTy sig env saved = some Ty.maskRestore ∧
        Checker.check sig env (path ++ [0]) body = .ok t
  /-- Both saved choices run the one body compiled at child 0, whose environment is the
  node's: a false bit is that code, and a true bit is `interruptible` over it. -/
  bodyEnv : ∀ p : Point, (p.child 0).env = p.env
  falseBit : ∀ (p : Point) (saved : Term) (body : NativeEff) (k : Nat), p.fuel = k + 1 →
    evalTerm p.env saved = some (Val.savedMask false) →
      compileEff (.restore saved body) p = compileEff body (p.child 0)
  trueBit : ∀ (root : NativeEff) (p : Point) (saved : Term) (body : NativeEff) (k : Nat),
    p.fuel = k + 1 → evalTerm p.env saved = some (Val.savedMask true) →
    Node.at_ (.eff root) p.path = some (.eff (.restore saved body)) →
      compileEff (.restore saved body) p = Prim.withFiber (EffThunk.act p) ∧
        actionAt root p = some (WithFiberAction.setInterruptible (compileEff body (p.child 0)) true)
  /-- The frame machine's code and the reference term are related at the node, as at every
  node (`code_intro`): the simulation reads one body at one address on both sides. -/
  related : ∀ (root : NativeEff) (p : Point) (saved : Term) (body : NativeEff),
    Node.at_ (.eff root) p.path = some (.eff (.restore saved body)) →
      CodeMeans root (compileEff (.restore saved body) p) (denoteR root (.restore saved body) p)
  /-- At a typed point the saved term evaluates to an image, so no lookup fails. -/
  evaluates : ∀ (root : ProgramSource) (w : World) (p : Point) (ty : EffTy) (saved : Term)
    (body : NativeEff),
    Node.at_ (.eff root.program) p.path = some (.eff (.restore saved body)) →
      PointTyped root w p ty → ∃ flag, evalTerm p.env saved = some (Val.savedMask flag)
  /-- The body's point is typed at the node's type, in the node's environment and view. -/
  bodyTyped : ∀ (root : ProgramSource) (w : World) (p : Point) (ty : EffTy) (saved : Term)
    (body : NativeEff),
    Node.at_ (.eff root.program) p.path = some (.eff (.restore saved body)) →
      PointTyped root w p ty → PointTyped root w (p.child 0) ty
  /-- A typed point at the node denotes a typed program at the node's type: the typed stack
  and the typed captures of M5, at either saved choice. -/
  typed : ∀ (root : ProgramSource) (w : World) (p : Point) (ty : EffTy) (saved : Term)
    (body : NativeEff), root.program.layerRefsWF = true → w.serviceTy = root.sig.serviceTy →
    Node.at_ (.eff root.program) p.path = some (.eff (.restore saved body)) →
      PointTyped root w p ty → TypedProg root w ty (denoteR root.program (.restore saved body) p)
  /-- A saved value passed as data keeps its choice: it reads back as the bit it was made from,
  and it holds no handle, so it carries no activation of its mask. -/
  data : ∀ flag : Bool, Val.savedMask? (Val.savedMask flag) = some flag ∧
    Store.Val.handles (Val.savedMask flag) = []
  /-- The mask adds no scoped constructor: the surface's builder is the program's own
  expansion over `bind`, and it keeps the authoring scope judgment. -/
  derived : ∀ (saved : String) (body : Authoring.Src NativeOp), body.Scoped →
    (Authoring.uninterruptibleMask saved body).Scoped

/-- **The restore node's body** (the claim `scoped-body-substitution-boundary`, for the mask;
concept `residual-program-typing`, requirement R4; decisions rows 245 and 246).

Reach: the checker at any signature and path; the compile at a positive budget; the typed
state at a source whose layer references are well formed and a world whose service table is
the source's (`denotesTyped`). It does not establish agreement with a target. The claim's
second half, a later constructor that binds a scope, has no statement: the mask adds none.
Its consumers are the Queue's waiting wrapper and the Semaphore's protected permit, which
descend into a restore site's body by `bodyTyped`. -/
@[semantics "residual-program-typing" (requirement := R4)]
theorem scoped_body_substitution_boundary : RestoreBodyBoundary where
  child := fun _ _ => ⟨rfl, rfl⟩
  binds := fun _ _ _ => rfl
  checked := fun sig env path saved body t h => Checker.inv_restore sig env path saved body t h
  bodyEnv := fun _ => rfl
  falseBit := fun _ _ _ _ hf hsaved => compileEff_restore_false hf hsaved
  trueBit := fun _ _ _ _ _ hf hsaved hat =>
    ⟨compileEff_restore_true hf hsaved, by rw [actionAt_restore hat, resolve_restore_body hat]⟩
  related := fun root p saved body hat => code_intro root (.restore saved body) p hat
  evaluates := fun _ _ _ _ _ _ hat hpt => restore_saved_evaluates hat hpt
  bodyTyped := fun _ _ _ _ _ _ hat hpt => restore_body_typed hat hpt
  typed := fun root w p ty saved body hwf htie hat hpt =>
    denotesTyped root hwf w htie p (.restore saved body) ty hat hpt
  data := fun flag => ⟨Val.savedMask?_savedMask flag, Value.maskImage_handleFree flag⟩
  derived := fun saved _ hb => Authoring.uninterruptibleMask_scoped saved hb

/-! ## 3. The flag at the boundaries of regions (`saved-mask-restoration`)

The five statements of the note's F7. A boundary is a step of the frame machine
(`evaluatePrim`, at the program's interpreter and any completed view) or the pass of a saved
frame (`Prim.ensure`, the hook every passed frame runs, on either arm of any exit). -/

section MachineSteps

variable {root : NativeEff} {p : Point}

/-- The getter's node, stepped: the fiber masked, and the image of the flag at its entry
answered. Nothing else of the machine or the fiber moves. -/
@[semantics "scope-lifetime-finalization"]
theorem getInterruptible_step (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun) (y : Bool)
    (hcur : f.frame.current = Prim.withFiber (EffThunk.act p))
    (hat : Node.at_ (.eff root) p.path = some (.eff (.withFiber .getInterruptible))) :
    evaluatePrim (interpAt root c) m f y =
      ⟨m, { f with frame := { f.frame.uninterruptible with
          current := Prim.success (Val.savedMask f.frame.interruptible) } },
        y, Outcome.continue_, []⟩ := by
  have hact : (interpOf root).withFiberOf (EffThunk.act p) =
      some WithFiberAction.getInterruptible := by
    show actionAt root p = _
    unfold actionAt
    rw [hat]
  rw [evaluatePrim_withFiber root c m f y hcur hact, withFiber_getInterruptible]
  rfl

/-- A restore site at a true bit, stepped: the `interruptible` region's entry over the body
compiled at child 0. -/
@[semantics "scope-lifetime-finalization"]
theorem restore_true_step (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun) (y : Bool)
    {saved : Term} {body : NativeEff}
    (hcur : f.frame.current = Prim.withFiber (EffThunk.act p))
    (hat : Node.at_ (.eff root) p.path = some (.eff (.restore saved body))) :
    evaluatePrim (interpAt root c) m f y =
      ⟨m, { f with frame := { f.frame.interruptibleRegion.fst with
          current := f.frame.interruptibleRegion.snd.getD (compileEff body (p.child 0)) } },
        y, Outcome.continue_, []⟩ := by
  have hact : (interpOf root).withFiberOf (EffThunk.act p) =
      some (WithFiberAction.setInterruptible (compileEff body (p.child 0)) true) := by
    show actionAt root p = _
    rw [actionAt_restore hat, resolve_restore_body hat]
  rw [evaluatePrim_withFiber root c m f y hcur hact, withFiber_setInterruptible_true]

end MachineSteps

/-- The statements of the claim `saved-mask-restoration` (decisions rows 227 and 244 to 246;
the note's F7). `FMachine` and `FRun` are the frame machine and its fiber at the program's
alphabets; `FFiber` is the fiber's frame. -/
structure MaskRestoration : Prop where
  /-- **1. At the body's entry the flag is false.** The getter masks the fiber and answers the
  image of the flag at its entry. -/
  getter : ∀ (root : NativeEff) (p : Point) (c : List (FiberId × ExitV)) (m : FMachine)
    (f : FRun) (y : Bool), f.frame.current = Prim.withFiber (EffThunk.act p) →
    Node.at_ (.eff root) p.path = some (.eff (.withFiber .getInterruptible)) →
      (evaluatePrim (interpAt root c) m f y).fiber.frame.interruptible = false ∧
        (evaluatePrim (interpAt root c) m f y).fiber.frame.current =
          Prim.success (Val.savedMask f.frame.interruptible)
  /-- The body's own mask, `uninterruptible`, leaves the flag false and runs the body next. -/
  bodyEntry : ∀ (interp : FInterp) (m : FMachine) (f : FRun) (y : Bool) (body : NCode),
    (evaluatePrim.withFiber interp m f y
        (WithFiberAction.setInterruptible body false)).fiber.frame.interruptible = false ∧
      (evaluatePrim.withFiber interp m f y
        (WithFiberAction.setInterruptible body false)).fiber.frame.current = body
  /-- **2. At a restore site's entry a true bit makes the flag true**: the node is the
  `interruptible` region over its body at child 0, and the body runs next unless a cause is
  pending. -/
  siteTrue : ∀ (root : NativeEff) (p : Point) (saved : Term) (body : NativeEff) (k : Nat)
    (c : List (FiberId × ExitV)) (m : FMachine) (f : FRun) (y : Bool), p.fuel = k + 1 →
    evalTerm p.env saved = some (Val.savedMask true) →
    Node.at_ (.eff root) p.path = some (.eff (.restore saved body)) →
    f.frame.current = compileEff (.restore saved body) p →
      (evaluatePrim (interpAt root c) m f y).fiber.frame.interruptible = true ∧
        (f.frame.interruptedCause = none →
          (evaluatePrim (interpAt root c) m f y).fiber.frame.current =
            compileEff body (p.child 0))
  /-- **A false bit leaves the flag as it is**: the node's code is its body's code, so the
  node is the identity on the fiber that runs it. It does not mask that fiber. -/
  siteFalse : ∀ (p : Point) (saved : Term) (body : NativeEff) (k : Nat), p.fuel = k + 1 →
    evalTerm p.env saved = some (Val.savedMask false) →
      compileEff (.restore saved body) p = compileEff body (p.child 0)
  /-- **3. A region inside the body follows its own rule**, in a restore site and outside one:
  at every fiber, the flag after a region's entry is the region's. -/
  nested : ∀ (interp : FInterp) (m : FMachine) (f : FRun) (y : Bool) (body : NCode)
    (flag : Bool), (evaluatePrim.withFiber interp m f y
      (WithFiberAction.setInterruptible body flag)).fiber.frame.interruptible = flag
  /-- **4. A region saves the earlier flag exactly when it changes it.** The frame it pushes
  holds the flag the fiber had at the entry. -/
  saved : ∀ (interp : FInterp) (m : FMachine) (f : FRun) (y : Bool) (body : NCode)
    (flag : Bool), (evaluatePrim.withFiber interp m f y
      (WithFiberAction.setInterruptible body flag)).fiber.frame.stack =
        if f.frame.interruptible = flag then f.frame.stack
        else Prim.setInterruptible f.frame.interruptible :: f.frame.stack
  /-- The getter saves the same way: its restoring frame holds `true`, on an interruptible
  fiber only. -/
  getterSaved : ∀ (interp : FInterp) (m : FMachine) (f : FRun) (y : Bool),
    (evaluatePrim.withFiber interp m f y WithFiberAction.getInterruptible).fiber.frame.stack =
      if f.frame.interruptible = true then Prim.setInterruptible true :: f.frame.stack
      else f.frame.stack
  /-- **At each completed exit the saved frame returns the flag it holds**, and it pushes
  nothing. The pass does not read the exit: it is the same on a success, a failure and an
  interruption. So a region that changed the flag ends with the flag of its entry. -/
  returned : ∀ (flag : Bool) (fr : FFiber),
    ((Prim.setInterruptible flag : NCode).ensure fr).fst.interruptible = flag ∧
      ((Prim.setInterruptible flag : NCode).ensure fr).fst.stack = fr.stack
  /-- **5. An exit that leaves the fiber interruptible with a cause pending fails there, with
  that cause.** -/
  pendingExit : ∀ (cause : CauseV) (fr : FFiber), fr.interruptedCause = some cause →
    ((Prim.setInterruptible true : NCode).ensure fr).snd = some (Prim.failure cause)
  /-- An exit that leaves the fiber masked fails nothing, and neither does an exit with no
  cause pending. -/
  maskedExit : ∀ fr : FFiber, ((Prim.setInterruptible false : NCode).ensure fr).snd = none
  cleanExit : ∀ (flag : Bool) (fr : FFiber), fr.interruptedCause = none →
    ((Prim.setInterruptible flag : NCode).ensure fr).snd = none
  /-- The entry of an `interruptible` region on a masked fiber with a cause pending fails at
  once with that cause, before the region's body: a restore site's entry at a true bit too. -/
  pendingEntry : ∀ (interp : FInterp) (m : FMachine) (f : FRun) (y : Bool) (body : NCode)
    (cause : CauseV), f.frame.interruptible = false → f.frame.interruptedCause = some cause →
      (evaluatePrim.withFiber interp m f y
        (WithFiberAction.setInterruptible body true)).fiber.frame.current = Prim.failure cause

/-- **The mask's law at the boundaries of regions** (the claim `saved-mask-restoration`;
concept `scope-lifetime-finalization`, requirement R11; decisions rows 227 and 244 to 246).

Reach: the frame machine at the program's interpreter, any completed view, any fiber and any
machine; the compile at a positive budget; both saved bits; any exit. It does not establish
progress, and it names no module that uses the mask. **It does not state that a region which
changes no flag ends with its entry flag**: such a region pushes no frame, and its exit flag
is what its body left (the module's head; the receipt's open part). The reference machine's
clause is related to the frame's by the simulation (`evaluate_rel`'s cases `actMask` and
`actGetInterruptible`, `Laws/Program/Simulation/Evaluate.lean`), and it keeps the typed state
(`clause_mask`, `clause_getInterruptible`). Its consumers are the Queue's waiting wrapper and
the Semaphore's protected permit. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem saved_mask_restoration : MaskRestoration where
  getter := fun root p c m f y hcur hat => by
    rw [getInterruptible_step c m f y hcur hat]
    exact ⟨FrameFiber.uninterruptible_flag f.frame, rfl⟩
  bodyEntry := fun interp m f y body => by
    rw [withFiber_setInterruptible_false]
    exact ⟨FrameFiber.uninterruptible_flag f.frame, rfl⟩
  siteTrue := fun root p saved body k c m f y hf hsaved hat hcur => by
    rw [compileEff_restore_true hf hsaved] at hcur
    rw [restore_true_step c m f y hcur hat]
    refine ⟨FrameFiber.interruptibleRegion_flag f.frame, fun clean => ?_⟩
    show f.frame.interruptibleRegion.snd.getD (compileEff body (p.child 0)) = _
    rw [FrameFiber.interruptibleRegion_clean f.frame clean]
    rfl
  siteFalse := fun _ _ _ _ hf hsaved => compileEff_restore_false hf hsaved
  nested := fun interp m f y body flag => withFiber_setInterruptible_flag interp m f y body flag
  saved := fun interp m f y body flag => withFiber_setInterruptible_stack interp m f y body flag
  getterSaved := fun interp m f y => by
    rw [withFiber_getInterruptible]
    exact FrameFiber.uninterruptible_stack f.frame
  returned := fun flag fr =>
    ⟨Prim.ensure_setInterruptible_flag flag fr, Prim.ensure_setInterruptible_stack flag fr⟩
  pendingExit := fun cause fr pending => by
    rw [Prim.ensure_setInterruptible_substitutes cause fr pending]
  maskedExit := fun fr => Prim.ensure_setInterruptible_false_no_replacement fr
  cleanExit := fun flag fr clean => by
    rw [Prim.ensure_setInterruptible_no_pending flag fr clean]
  pendingEntry := fun interp m f y body cause masked pending => by
    rw [withFiber_setInterruptible_true]
    show f.frame.interruptibleRegion.snd.getD body = _
    rw [FrameFiber.interruptibleRegion_pending f.frame cause masked pending]
    rfl

end Effect4.Program.Typed
