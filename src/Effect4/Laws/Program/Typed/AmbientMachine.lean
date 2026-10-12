import Effect4.Laws.Program.Typed.Stack
import Effect4.Laws.Program.Typed.MaskEntry

/-!
# Laws.Program.Typed.AmbientMachine — the row-indexed judgment at the machine

The machine's typed state types code with the row-indexed judgment (decisions row 349): a
fiber's current code and saved stack at a row its actual context covers. This module holds the
shared layer the machine clauses instantiate.

* **Administrative code.** The machine installs many programs of its own: replies, awaits,
  interrupts, finalizer compositions, cancellations. None reads or writes the context, enters a
  region or names a source point. `AdminCode` states that shape, and `ambientProgAt_of_admin`
  lifts their existing type-only typing to the row-indexed judgment at every row and entry bit.
* **Machine positions.** A saved frame's position pairs a completion position with the entry bit
  its callbacks resume at. An answer frame saved inside a protected region resumes protected
  (decisions row 349's masked entry, `MaskEntry.lean`), so the bit is the frame's, not a constant.

Placement: concept `residual-program-typing`, R4 and R9; claim `typed-state-reachable`.
Consumers: the walk below, the scheduler and assembly clauses, the command proofs.
What this module does not establish: that a reachable machine's fibers meet these clauses; that
is the preservation proof's.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## Administrative code -/

/-- The fiber operations whose row-indexed pre, post and input are the type-only ones: every
operation but the context reader and writer, the region and child entries, the races and the
scope's exit marker. -/
def adminOp : FiberOp → Bool
  | .mask _ (.raceCleanup _) => true
  | .getContext | .setContext _ | .mask _ _ | .fork _ _ _ | .forkIn _ _ _ _ | .forkScoped _ _ _
  | .scoped _ | .gen _ | .loop _ _ | .raceAll _ _ | .raceAllFirst _ _ | .scopeExit _ _ _ => false
  | _ => true

/-- A program built only from administrative operations and store operations other than a foreign
finalizer registration. -/
inductive AdminCode : RProgram → Prop where
  | pure (ex : ExitV) : AdminCode (.pure ex)
  | store (op : SyncOp) (k : Val → RProgram)
      (notForeign : ∀ scope capture, op ≠ .scopeAdd scope (.foreign capture))
      (next : ∀ v, AdminCode (k v)) : AdminCode (.vis (.inl op) k)
  | fiber (op : FiberOp) (k : op.answer → RProgram) (admin : adminOp op = true)
      (next : ∀ a, AdminCode (k a)) : AdminCode (.vis (.inr op) k)

theorem ambientFiberPre_of_admin (root : ProgramSource) {w : World} (available : Env.Requirement)
    {op : FiberOp} {cert : FiberCert op} (admin : adminOp op = true) (pre : fiberPre root w op cert) :
    ambientFiberPre root w available op cert := by
  revert admin pre
  cases op with
  | mask flag body =>
    intro admin pre
    cases body <;> simp only [adminOp, Bool.false_eq_true] at admin
    cases pre
    refine ⟨.raceCleanup _, fun a h => absurd h (Row.not_mem_empty a), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ h
      cases h
    · intro _ _ _ h
      cases h
    · intro _ h
      cases h
    · intro _ _ _ h
      cases h
    · intro _ h
      rcases h with h | ⟨_, h | h⟩ <;> cases h
    · intro _ _ _ h
      cases h
  | _ => intro admin pre; simp only [adminOp, Bool.false_eq_true] at admin <;> exact pre

theorem fiberPost_of_admin {w : World} (available : Env.Requirement) {op : FiberOp}
    {cert : FiberCert op} {answer : op.answer} (admin : adminOp op = true)
    (post : ambientFiberPost w available op cert answer) : fiberPost w op cert answer := by
  revert admin post
  cases op with
  | mask flag body => intro _ post; exact post
  | _ => intro admin post; simp only [adminOp, Bool.false_eq_true] at admin <;> exact post

theorem ambientFiberInput_admin (available : Env.Requirement) {op : FiberOp} (answer : op.answer)
    (admin : adminOp op = true) : ambientFiberInput available op answer = available := by
  revert admin
  cases op with
  | mask flag body =>
    intro admin
    cases body <;> simp only [adminOp, Bool.false_eq_true] at admin
    cases flag <;> rfl
  | _ => intro admin; simp only [adminOp, Bool.false_eq_true] at admin <;> rfl

/-- Administrative code carries no scope-exit callback at its head. -/
theorem AdminCode.noCallback {p : RProgram} (admin : AdminCode p) : scopeExitCallback? p = none := by
  cases admin with
  | pure => rfl
  | store => rfl
  | fiber op k isAdmin =>
    revert isAdmin
    cases op with
    | mask _ _ => intro _; rfl
    | _ => intro isAdmin; simp only [adminOp, Bool.false_eq_true] at isAdmin <;> rfl

/-- Administrative code is closed under sequencing. -/
theorem AdminCode.bind {p : RProgram} {k : ExitV → RProgram} (admin : AdminCode p)
    (next : ∀ ex, AdminCode (k ex)) : AdminCode (p.bind k) := by
  induction admin with
  | pure ex => exact next ex
  | store op k' notForeign _ ih => exact .store op _ notForeign ih
  | fiber op k' isAdmin _ ih => exact .fiber op _ isAdmin ih

/-- A guard over administrative code is administrative. -/
theorem AdminCode.guard (kind : GuardKind) {body : RProgram} (h : AdminCode body) :
    AdminCode (guardR kind body) := by
  refine .fiber _ _ rfl fun o => ?_
  cases o with
  | none => exact h.bind fun _ => .fiber _ _ rfl fun _ => .pure _
  | some e => exact .pure e

/-- Returning a constant exit after a success is administrative. -/
theorem AdminCode.seq (ex : ExitV) (e : ExitV) : AdminCode (seqR (fun _ => .pure ex) e) := by
  cases e <;> exact .pure _

/-- A value-answering administrative operation is administrative code. -/
theorem AdminCode.fiberVal (op : FiberOp) (h : op.answer = Val) (admin : adminOp op = true) :
    AdminCode (fiberValR op h) :=
  .fiber _ _ admin fun _ => .pure _

/-- A restore over administrative code is administrative. -/
theorem restoreR_admin {code : RProgram} (h : AdminCode code) (name : EffName) :
    AdminCode (restoreR code name) := by
  unfold restoreR
  split
  · exact (AdminCode.guard _ h).bind (AdminCode.seq _)
  · exact .pure _

/-- A race's settlement code is administrative: its cleanup region and the accepted exit. -/
theorem denoteRaceSettle_admin (race : Nat) (cleanup : Bool) (ex : ExitV) :
    AdminCode (denoteRaceSettle race cleanup ex) := by
  unfold denoteRaceSettle
  split
  · refine AdminCode.bind (.fiber _ _ rfl fun o => ?_) fun e => ?_
    · cases o with
      | none => exact AdminCode.bind (.fiber _ _ rfl fun _ => .pure _) fun _ => .fiber _ _ rfl fun _ => .pure _
      | some e => exact .pure e
    · cases e <;> exact .pure _
  · exact .pure ex

/-- The selected row of a constant-row position is its row. -/
theorem ambientInput_const (ty : EffTy) (row : Env.Requirement) (exit : ExitV) :
    ambientInput ((ty, row, row) : AmbientPosition) exit = row := by
  cases exit <;> rfl

/-- A guard's callback input at a constant-row position keeps the row. -/
theorem ambientGuardInput_const (kind : GuardKind) (ty : EffTy) (row : Env.Requirement)
    (exit : ExitV) :
    ambientGuardInput kind ((ty, row, row) : AmbientPosition) exit =
      (row, (ambientGuardInput kind ((ty, row, row) : AmbientPosition) exit).2) := by
  cases exit <;> rfl

/-- An exit at a constant-row position is within its row. -/
theorem ambientExit_const {w : World} {ty : EffTy} {row : Env.Requirement} {exit : ExitV}
    (typed : ExitOk w ty exit) : AmbientExit w row ((ty, row, row) : AmbientPosition) exit :=
  ⟨typed, by cases exit <;> exact Row.subset_refl _⟩

/-- **The lift**: administrative code typed by the type-only judgment is typed by the row-indexed
judgment at every row and entry bit, at the constant-row position of its type. Its operations'
pres, posts and inputs are the type-only ones (`ambientFiberPre_of_admin`, `fiberPost_of_admin`,
`ambientFiberInput_admin`), and a constant-row position bounds every exit by its own row. -/
theorem ambientProgAt_of_admin (root : ProgramSource) {w : World} {ty : EffTy} {p : RProgram}
    (typed : TypedProg root w ty p) (admin : AdminCode p) (row : Env.Requirement) (bit : Bool) :
    AmbientProgAt root w (row, bit) ((ty, row, row) : AmbientPosition) p := by
  revert admin bit
  unfold TypedProg at typed
  generalize (() : Unit) = input at typed
  induction typed with
  | pure exit =>
    intro _ bit
    exact .pure (ambientExit_const exit) ⟨Or.inr (Row.subset_refl _), Row.subset_refl _⟩
  | store cert pre _ _ ih =>
    intro admin bit
    cases admin with
    | store op k notForeign next =>
      refine .store cert ⟨pre, fun scope capture same => absurd same (notForeign scope capture)⟩
        (fun later ordered answer post => ih later ordered answer post (next answer) bit)
        ⟨Or.inr (Row.subset_refl _), Row.subset_refl _⟩
  | fiber notGuard notUnguard notFinish notScopeExit cert pre _ _ ih =>
    intro admin bit
    cases admin with
    | fiber op k isAdmin next =>
      refine .fiber notGuard notUnguard notFinish notScopeExit cert
        (ambientFiberPre_of_admin root row isAdmin pre) ?_ ⟨Or.inr (Row.subset_refl _), Row.subset_refl _⟩
      intro later ordered answer post
      show AmbientProgAt root later (ambientFiberInput row _ answer, bit) _ _
      rw [ambientFiberInput_admin row answer isAdmin]
      exact ih later ordered answer (fiberPost_of_admin row isAdmin post) (next answer) bit
  | guard mid _ _ skip _ ihBody ihRun =>
    intro admin bit
    cases admin with
    | fiber op k isAdmin next =>
      refine .guard ((mid, row, row) : AmbientPosition) (ihBody (next none) bit) ?_ ?_
        ⟨Or.inr (Row.subset_refl _), Row.subset_refl _⟩
      · intro later ordered exit post
        rw [ambientGuardInput_const]
        exact ihRun later ordered exit ⟨post.1, post.2.1⟩ (next (some exit)) _
      · intro later ordered exit exits arm
        exact ⟨skip later ordered exit exits.1 arm, by cases exit <;> exact Row.subset_refl _⟩
  | unguard payload _ =>
    intro _ bit
    exact .unguard (ambientExit_const payload) ⟨Or.inr (Row.subset_refl _), Row.subset_refl _⟩
  | finishFinalizer payload _ =>
    intro _ bit
    exact .finishFinalizer (ambientExit_const payload) ⟨Or.inr (Row.subset_refl _), Row.subset_refl _⟩
  | scopedGuard mid prev sc _ callback _ _ _ _ _ =>
    intro admin _
    cases admin with
    | fiber op k isAdmin next =>
      have head := callback (.success .unit)
      rw [(next (some (.success .unit))).noCallback] at head
      cases head

/-- **The lift into the row-only judgment**, as `ambientProgAt_of_admin`: the hook protocols type
resumed code with `AmbientProg`. -/
theorem ambientProg_of_admin (root : ProgramSource) {w : World} {ty : EffTy} {p : RProgram}
    (typed : TypedProg root w ty p) (admin : AdminCode p) (row : Env.Requirement) :
    AmbientProg root w row ((ty, row, row) : AmbientPosition) p := by
  revert admin
  unfold TypedProg at typed
  generalize (() : Unit) = input at typed
  induction typed with
  | pure exit =>
    intro _
    exact .pure (ambientExit_const exit) ⟨Row.subset_refl _, Row.subset_refl _⟩
  | store cert pre _ _ ih =>
    intro admin
    cases admin with
    | store op k notForeign next =>
      exact .store cert ⟨pre, fun scope capture same => absurd same (notForeign scope capture)⟩
        (fun later ordered answer post => ih later ordered answer post (next answer))
        ⟨Row.subset_refl _, Row.subset_refl _⟩
  | fiber notGuard notUnguard notFinish notScopeExit cert pre _ _ ih =>
    intro admin
    cases admin with
    | fiber op k isAdmin next =>
      refine .fiber notGuard notUnguard notFinish notScopeExit cert
        (ambientFiberPre_of_admin root row isAdmin pre) ?_ ⟨Row.subset_refl _, Row.subset_refl _⟩
      intro later ordered answer post
      show AmbientProg root later (ambientFiberInput row _ answer) _ _
      rw [ambientFiberInput_admin row answer isAdmin]
      exact ih later ordered answer (fiberPost_of_admin row isAdmin post) (next answer)
  | guard mid _ _ skip _ ihBody ihRun =>
    intro admin
    cases admin with
    | fiber op k isAdmin next =>
      refine .guard ((mid, row, row) : AmbientPosition) (ihBody (next none)) ?_ ?_ ⟨Row.subset_refl _, Row.subset_refl _⟩
      · intro later ordered exit post
        show AmbientProg root later (ambientInput ((mid, row, row) : AmbientPosition) exit) _ _
        rw [ambientInput_const]
        exact ihRun later ordered exit ⟨post.1, post.2.1⟩ (next (some exit))
      · intro later ordered exit exits arm
        exact ⟨skip later ordered exit exits.1 arm, by cases exit <;> exact Row.subset_refl _⟩
  | unguard payload _ =>
    intro _
    exact .unguard (ambientExit_const payload) ⟨Row.subset_refl _, Row.subset_refl _⟩
  | finishFinalizer payload _ =>
    intro _
    exact .finishFinalizer (ambientExit_const payload) ⟨Row.subset_refl _, Row.subset_refl _⟩
  | scopedGuard mid prev sc _ callback _ _ _ _ _ =>
    intro admin
    cases admin with
    | fiber op k isAdmin next =>
      have head := callback (.success .unit)
      rw [(next (some (.success .unit))).noCallback] at head
      cases head

/-! ## Exits at a position's own row -/

/-- A failure's row is the position's failure row. -/
theorem ambientInput_failure (position : AmbientPosition) (c : CauseV) :
    ambientInput position (.failure c) = position.failureRow := by
  cases position <;> rfl

/-- An exit at a result position, bounded by some row, is bounded by its own selected row. -/
theorem ambientExit_self {w : World} {row : Env.Requirement} {t : EffTy} {s f : Env.Requirement}
    {ex : ExitV} (h : AmbientExit w row ((t, s, f) : AmbientPosition) ex) :
    AmbientExit w (ambientInput ((t, s, f) : AmbientPosition) ex) ((t, s, f) : AmbientPosition) ex ∧
      Row.Subset (ambientInput ((t, s, f) : AmbientPosition) ex) row :=
  ⟨⟨h.1, Row.subset_refl _⟩, h.2⟩

/-- A typed failure at a position, bounded by its failure row. -/
theorem ambientExit_failure {w : World} {row : Env.Requirement} {position : AmbientPosition}
    {c : CauseV} (typed : ExitOk w position.type (.failure c)) (bound : Row.Subset position.failureRow row) :
    AmbientExit w row position (.failure c) := by
  cases position with
  | result t s f => exact ⟨typed, bound⟩
  | capturedContext g => exact ⟨typed, bound, bound⟩

/-! ## Machine stacks

A machine stack position pairs a completion position with the fiber's mask flag while control is
at it. The mask frames change the flag; every other frame keeps it, and its callback resumes at
it. So a callback saved inside a protected region resumes protected, and the walk proves the flag
at each pop from the frames themselves. -/

/-- A machine stack position: a completion position and the mask flag there. -/
abbrev MachinePos := AmbientPosition × Bool

/-- A saved frame as a row-indexed arrow that tracks the mask flag. Callbacks return to result
positions. A frame that can inject a recorded interrupt where a success was expected
(`restoreMask`, `finalizerMask`, an `onExit` callback's pushed mask, a passed async hook) bounds
its failure row by its success row. -/
inductive MFrame (root : ProgramSource) (w : World) : MachinePos → MachinePos → ScopeFrame → Prop
  | resume {p : AmbientPosition} {t : EffTy} {s f : Env.Requirement} {b : Bool}
      (kind : GuardKind) (next : ExitV → RProgram) (ordinary : kind ≠ .onExit false)
      (run : ∀ w', w.leHost w' → ∀ ex, AmbientExit w' (ambientInput p ex) p ex →
        kind.hasExitArm ex = true → AmbientProgAt root w' (ambientInput p ex, b) (t, s, f) (next ex))
      (skip : ∀ w', w.leHost w' → ∀ ex, AmbientExit w' (ambientInput p ex) p ex →
        kind.hasExitArm ex = false → AmbientExit w' (ambientInput p ex) (t, s, f) ex)
      (inject : kind = .onExit true → b = true → Row.Subset f s) :
      MFrame root w (p, b) ((t, s, f), b) (.resume kind next)
  | protect {p : AmbientPosition} {t : EffTy} {s f : Env.Requirement} {b : Bool}
      (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, AmbientExit w' (ambientInput p ex) p ex →
        AmbientProgAt root w' (ambientInput p ex, false) (t, s, f) (next ex))
      (inject : b = true → Row.Subset f s) :
      MFrame root w (p, b) ((t, s, f), b) (.resume (.onExit false) next)
  | scopedResume {p : AmbientPosition} {t : EffTy} {s f : Env.Requirement} {b : Bool}
      (next : ExitV → RProgram) (prev : Ctx) (sc : Nat)
      (callback : ∀ ex, scopeExitCallback? (next ex) = some (prev, sc, ex))
      (hook : ∀ w', w.leHost w' → (frameProtocols root).scopeExit w' prev sc)
      (widen : ∀ w', w.leHost w' → ∀ ex, AmbientExit w' (ambientInput p ex) p ex →
        AmbientExit w' prev.services.keysRow (t, s, f) ex)
      (inject : b = true → Row.Subset f s) :
      MFrame root w (p, b) ((t, s, f), b) (.resume (.onExit false) next)
  | answer {p : AmbientPosition} {t : EffTy} {s f : Env.Requirement} {b : Bool}
      (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, AmbientExit w' (ambientInput p ex) p ex →
        AmbientProgAt root w' (ambientInput p ex, b) (t, s, f) (next ex)) :
      MFrame root w (p, b) ((t, s, f), b) (.answer next)
  | restoreMask {p : AmbientPosition} {inner : Bool} (flag : Bool)
      (inject : flag = true → ∀ v, Row.Subset p.failureRow (ambientInput p (.success v))) :
      MFrame root w (p, inner) (p, flag) (.restoreMask flag)
  | finalizerMask {p : AmbientPosition} {inner : Bool} (flag : Bool)
      (inject : flag = true → ∀ v, Row.Subset p.failureRow (ambientInput p (.success v))) :
      MFrame root w (p, inner) (p, flag) (.finalizerMask flag)
  | asyncFinalizer {a : EffTy} {s f : Env.Requirement} {b : Bool} (name : EffName)
      (protocol : ∀ w', w.leHost w' → AmbientAsyncFinalizer root w' s f a a name)
      (inject : Row.Subset f s) :
      MFrame root w ((a, s, f), b) ((a, s, f), b) (.asyncFinalizer name)
  | iter {a c : EffTy} {s f : Env.Requirement} {b : Bool} (name : EffName)
      (protocol : ∀ w', w.leHost w' → AmbientIteratorProtocol root w' s f a c name)
      (rows : Row.Subset f s) :
      MFrame root w ((a, s, f), b) ((c, s, f), b) (.iter name)
  | loop {a c : EffTy} {s f : Env.Requirement} {b : Bool} (name : EffName) (cursor : Val)
      (protocol : ∀ w', w.leHost w' → AmbientLoopProtocol root w' s f a c name cursor)
      (rows : Row.Subset f s) :
      MFrame root w ((a, s, f), b) ((c, s, f), b) (.loop name cursor)

/-- A machine stack: the shared path over `MFrame`. -/
abbrev MStack (root : ProgramSource) (w : World) := Effect4.Contracts.Path (MFrame root w)

/-- A world extension keeps every frame: each clause already quantifies over later worlds. -/
theorem MFrame.mono {root : ProgramSource} {w w' : World} (ord : w.leHost w')
    {tin tout : MachinePos} {frame : ScopeFrame} (h : MFrame root w tin tout frame) :
    MFrame root w' tin tout frame := by
  cases h with
  | resume kind next ordinary run skip inject =>
    exact .resume kind next ordinary (fun w'' o => run w'' (leHost_trans _ _ _ ord o))
      (fun w'' o => skip w'' (leHost_trans _ _ _ ord o)) inject
  | protect next run inject => exact .protect next (fun w'' o => run w'' (leHost_trans _ _ _ ord o)) inject
  | scopedResume next prev sc callback hook widen inject =>
    exact .scopedResume next prev sc callback (fun w'' o => hook w'' (leHost_trans _ _ _ ord o))
      (fun w'' o => widen w'' (leHost_trans _ _ _ ord o)) inject
  | answer next run => exact .answer next (fun w'' o => run w'' (leHost_trans _ _ _ ord o))
  | restoreMask flag inject => exact .restoreMask flag inject
  | finalizerMask flag inject => exact .finalizerMask flag inject
  | asyncFinalizer name protocol inject =>
    exact .asyncFinalizer name (fun w'' o => protocol w'' (leHost_trans _ _ _ ord o)) inject
  | iter name protocol rows => exact .iter name (fun w'' o => protocol w'' (leHost_trans _ _ _ ord o)) rows
  | loop name cursor protocol rows =>
    exact .loop name cursor (fun w'' o => protocol w'' (leHost_trans _ _ _ ord o)) rows

theorem MStack.mono {root : ProgramSource} {w w' : World} (ord : w.leHost w')
    {tin tout : MachinePos} {stack : List ScopeFrame} (h : MStack root w tin tout stack) :
    MStack root w' tin tout stack :=
  h.map fun _ _ _ frame => frame.mono ord

/-! ## The machine interpreter's hook laws -/

/-- What the walk needs of an interpreter's named hooks, at one world, over the row-indexed
protocols. -/
structure MHookLaws (root : ProgramSource) (interp : RInterp) (w : World) : Prop where
  asyncFinalizer : ∀ s f a name, AmbientAsyncFinalizer root w s f a a name →
    ∀ cause, ExitOk w a (.failure cause) → cause.hasInterrupts = true →
      AmbientProg root w f (a, s, f) (interp.cancelThenFail name cause)
  iterator : ∀ s f a c name, AmbientIteratorProtocol root w s f a c name →
    a.error = c.error ∧ ∀ v, Fits w v a.answer →
      match (interp.iterNext name v).2 with
      | .done result => ExitOk w c (.success result)
      | .halt cause => ExitOk w c (.failure cause)
      | .resume code name' => ∃ a', AmbientProg root w s (a', s, f) code ∧
          ∀ w', w.leHost w' → AmbientIteratorProtocol root w' s f a' c name'
  loop : ∀ s f a c name cursor, AmbientLoopProtocol root w s f a c name cursor →
    a.error = c.error ∧ ∀ v, Fits w v a.answer →
      match interp.loopResume name cursor v with
      | .continue cursor' body => ∃ a', AmbientProg root w s (a', s, f) body ∧
          ∀ w', w.leHost w' → AmbientLoopProtocol root w' s f a' c name cursor'
      | .finish code => AmbientProg root w s (c, s, f) code

/-- The machine's interpreter meets the row-indexed hook laws wherever its completed view is
typed (decisions row 190 (c)). -/
theorem mHookLaws_interpRAt (root : ProgramSource) (w : World) (completed : List (FiberId × ExitV))
    (view : ViewTyped w completed) : MHookLaws root (interpRAt root.program completed) w where
  asyncFinalizer _ _ _ _ h := h.2 w (leHost_refl w)
  iterator s f a c name h := by
    obtain ⟨errors, _, next⟩ := h.unfold
    refine ⟨errors, fun v hv => ?_⟩
    have step := next w (leHost_refl w) completed view v hv
    revert step
    cases ((interpRAt root.program completed).iterNext name v).2 with
    | done result => exact id
    | halt cause => exact id
    | resume code name' =>
      intro step
      obtain ⟨a', typed, tail⟩ := step
      exact ⟨a', typed, fun _ ord => ambientIteratorProtocol_mono ord tail⟩
  loop s f a c name cursor h := by
    obtain ⟨errors, _, next⟩ := h.unfold
    refine ⟨errors, fun v hv => ?_⟩
    have step := next w (leHost_refl w) completed view v hv
    revert step
    cases (interpRAt root.program completed).loopResume name cursor v with
    | «continue» cursor' body =>
      intro step
      obtain ⟨a', typed, tail⟩ := step
      exact ⟨a', typed, fun _ ord => ambientLoopProtocol_mono ord tail⟩
    | finish code => exact id

/-! ## Inversions -/

theorem ambientProgAt_pure_inv {root : ProgramSource} {w : World} {input : AmbientEntryInput}
    {position : AmbientPosition} {ex : ExitV} (h : AmbientProgAt root w input position (.pure ex)) :
    AmbientExit w input.1 position ex := by
  cases h with
  | pure exit _ => exact exit

theorem ambientProgAt_unguard_inv {root : ProgramSource} {w : World} {input : AmbientEntryInput}
    {position : AmbientPosition} {ex : ExitV} {k : ExitV → RProgram}
    (h : AmbientProgAt root w input position (.vis (.inr (.unguard ex)) k)) :
    AmbientExit w input.1 position ex := by
  cases h with
  | fiber _ notUnguard _ _ _ _ _ _ => exact absurd rfl (notUnguard ex)
  | unguard payload _ => exact payload

/-- An ordinary callback's entry bounds its result position's failure row by its input row. -/
theorem ambientProgAt_failure_bound {root : ProgramSource} {w : World} {row : Env.Requirement}
    {position : AmbientPosition} {code : RProgram} (h : AmbientProgAt root w (row, true) position code) :
    Row.Subset position.failureRow row :=
  (ProgramArrow.entry h).1.resolve_left Bool.noConfusion

/-- A position whose failure row a success's row covers is well formed: what an injected
interruption reads. -/
theorem AmbientPosition.wf_of_success {p : AmbientPosition} (v : Val)
    (h : Row.Subset p.failureRow (ambientInput p (.success v))) : p.WF := by
  cases p with
  | result t s f => exact h
  | capturedContext g => trivial

/-! ## The walk -/

/-- The walk ran a `scoped` guard's slot: the current code is the scope's exit callback, whose
exit is typed at the captured context's row, over the remaining stack. -/
def MCallbackSaved (root : ProgramSource) (w : World) (tout : MachinePos) (x : RSaved) : Prop :=
  ∃ tin prev sc ex, scopeExitCallback? x.current = some (prev, sc, ex) ∧
    AmbientExit w prev.services.keysRow tin.1 ex ∧ (frameProtocols root).scopeExit w prev sc ∧
    tin.2 = x.interruptible ∧ MStack root w tin tout x.stack ∧ InterruptProvenance x

/-- The walk's outcomes at a covered row: code typed at a covered row over the remaining stack,
with the position's flag the frame's mask; a scope's exit callback; or the stack's exit. -/
def MWalkTyped (root : ProgramSource) (w : World) (covered : Env.Requirement) (tout : MachinePos) :
    RSaved × Option ExitV → Prop
  | (frame, none) =>
    (∃ (row : Env.Requirement) (tin : MachinePos), Row.Subset row covered ∧
      tin.2 = frame.interruptible ∧ AmbientProgAt root w (row, tin.2) tin.1 frame.current ∧
      MStack root w tin tout frame.stack ∧ InterruptProvenance frame) ∨
    MCallbackSaved root w tout frame
  | (frame, some ex) => AmbientExit w (ambientInput tout.1 ex) tout.1 ex ∧
      Row.Subset (ambientInput tout.1 ex) covered ∧ frame.interruptible = tout.2

/-- **The ambient walk.** Delivering an exit, bounded by its own row and covered, to a typed
machine stack whose top flag is the frame's mask either installs code typed at a covered row
over the remaining stack, hands a scope's exit callback over, or completes at the stack's final
position. The rows only shrink along the walk; each pop's mask flag is the frame's. -/
theorem ambient_popR_typed (root : ProgramSource) (interp : RInterp) (w : World)
    (laws : MHookLaws root interp w) (covered : Env.Requirement) :
    ∀ (stack : List ScopeFrame) (tin tout : MachinePos) (ex : ExitV) (frame : RSaved),
      MStack root w tin tout stack →
      AmbientExit w (ambientInput tin.1 ex) tin.1 ex → Row.Subset (ambientInput tin.1 ex) covered →
      frame.interruptible = tin.2 → InterruptProvenance frame →
      MWalkTyped root w covered tout (popR interp ex stack frame) := by
  intro stack
  induction stack with
  | nil =>
    intro tin tout ex frame hstack hex hcov hmask _
    cases hstack
    exact ⟨hex, hcov, hmask⟩
  | cons slot rest ih =>
    intro tin tout ex frame hstack hex hcov hmask hp
    cases hstack with
    | cons head tail =>
    cases head with
    | restoreMask flag inject =>
      obtain ⟨current, stack, interruptible, ic, deferred⟩ := frame
      cases ic with
      | none => exact ih _ _ _ _ tail hex hcov rfl ⟨hp.recorded, hp.deferred⟩
      | some c =>
        cases flag with
        | false =>
          cases ex <;> simp only [popR, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;>
            exact ih _ _ _ _ tail hex hcov rfl ⟨hp.recorded, hp.deferred⟩
        | true =>
          cases ex with
          | success v =>
            simp only [popR, Bool.not_false, Bool.and_self, ↓reduceIte]
            refine .inl ⟨_, _, hcov, rfl, ?_, tail, ⟨hp.recorded, hp.deferred⟩⟩
            exact .pure (ambientExit_failure (strongExit_of_clean w _ c (recorded_clean hp rfl)
              (recorded_noShapeDefect _ hp rfl)) (inject rfl v))
              ⟨Or.inr (inject rfl v), AmbientPosition.wf_of_success v (inject rfl v)⟩
          | failure c' =>
            simp only [popR, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact ih _ _ _ _ tail hex hcov rfl ⟨hp.recorded, hp.deferred⟩
    | finalizerMask flag inject =>
      obtain ⟨current, stack, interruptible, ic, deferred⟩ := frame
      cases ic with
      | none => exact ih _ _ _ _ tail hex hcov rfl ⟨hp.recorded, hp.deferred⟩
      | some c =>
        cases flag with
        | false =>
          cases ex <;> simp only [popR, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;>
            exact ih _ _ _ _ tail hex hcov rfl ⟨hp.recorded, hp.deferred⟩
        | true =>
          cases ex with
          | success v =>
            simp only [popR, Bool.not_false, Bool.and_self, ↓reduceIte]
            refine .inl ⟨_, _, hcov, rfl, ?_, tail, ⟨hp.recorded, hp.deferred⟩⟩
            exact .pure (ambientExit_failure (strongExit_of_clean w _ c (recorded_clean hp rfl)
              (recorded_noShapeDefect _ hp rfl)) (inject rfl v))
              ⟨Or.inr (inject rfl v), AmbientPosition.wf_of_success v (inject rfl v)⟩
          | failure c' =>
            simp only [popR, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact ih _ _ _ _ tail hex hcov rfl ⟨hp.recorded, hp.deferred⟩
    | @resume p t s f b kind next ordinary run skip inject =>
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      change i = _ at hmask
      subst hmask
      have hp' : ∀ (c : RProgram) (s : List ScopeFrame) (b : Bool),
          InterruptProvenance ⟨c, s, b, ic, deferred⟩ := fun _ _ _ => ⟨hp.recorded, hp.deferred⟩
      have skipped : ∀ ex, AmbientExit w (ambientInput p ex) p ex → kind.hasExitArm ex = false →
          Row.Subset (ambientInput p ex) covered → ∀ frame : RSaved, frame.interruptible = i →
          InterruptProvenance frame → MWalkTyped root w covered tout (popR interp ex rest frame) := by
        intro ex' hex' arm cov' frame' mask' prov'
        obtain ⟨self, sub⟩ := ambientExit_self (skip w (leHost_refl w) ex' hex' arm)
        exact ih _ _ _ _ tail self (Row.subset_trans sub cov') mask' prov'
      have preempted : ∀ (c ic' : CauseV), AmbientExit w (ambientInput p (.failure c)) p (.failure c) →
          kind.hasExitArm (.failure c) = true → i = true → ic = some ic' →
          Row.Subset (ambientInput p (.failure c)) covered → ∀ frame : RSaved, frame.interruptible = i →
          InterruptProvenance frame →
          MWalkTyped root w covered tout (popR interp (.failure (Cause.sanitize c ic')) rest frame) := by
        intro c ic' hex' arm interruptible recorded cov' frame' mask' prov'
        subst interruptible
        have bound := ambientProgAt_failure_bound (run w (leHost_refl w) _ hex' arm)
        refine ih _ _ _ _ tail ⟨strongExit_of_clean w _ _ (sanitize_clean_exit hp c recorded)
          (sanitize_noShapeDefect _ hp c recorded hex'.1.2), Row.subset_refl _⟩
          (Row.subset_trans bound cov') mask' prov'
      cases kind with
      | onSuccess =>
        cases ex with
        | success v =>
          simp only [popR]
          exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl, tail, hp' _ _ _⟩
        | failure c =>
          simp only [popR]
          cases ic <;> exact skipped _ hex rfl hcov _ rfl (hp' _ _ _)
      | onFailure =>
        cases ex with
        | success v =>
          simp only [popR]
          exact skipped _ hex rfl hcov _ rfl (hp' _ _ _)
        | failure c =>
          simp only [popR]
          cases i <;> cases ic
          · exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl, tail, hp' _ _ _⟩
          · exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl, tail, hp' _ _ _⟩
          · exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl, tail, hp' _ _ _⟩
          · exact preempted c _ hex rfl rfl rfl hcov _ rfl (hp' _ _ _)
      | all =>
        cases ex with
        | success v =>
          simp only [popR]
          exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl, tail, hp' _ _ _⟩
        | failure c =>
          simp only [popR]
          cases i <;> cases ic
          · exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl, tail, hp' _ _ _⟩
          · exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl, tail, hp' _ _ _⟩
          · exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl, tail, hp' _ _ _⟩
          · exact preempted c _ hex rfl rfl rfl hcov _ rfl (hp' _ _ _)
      | onExit b' =>
        cases b' with
        | false => exact absurd rfl ordinary
        | true =>
          have pushed : MStack root w (((t, s, f) : AmbientPosition), i) tout (.finalizerMask i :: rest) :=
            .cons (.finalizerMask (p := ((t, s, f) : AmbientPosition)) i fun same _ => inject rfl same) tail
          cases ex with
          | success v =>
            simp only [popR]
            exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl, pushed, hp' _ _ _⟩
          | failure c =>
            simp only [popR]
            cases i <;> cases ic
            · exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl,
                .cons (.finalizerMask (p := ((t, s, f) : AmbientPosition)) false fun same _ => nomatch same) tail, hp' _ _ _⟩
            · exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl,
                .cons (.finalizerMask (p := ((t, s, f) : AmbientPosition)) false fun same _ => nomatch same) tail, hp' _ _ _⟩
            · exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex rfl, pushed, hp' _ _ _⟩
            · exact preempted c _ hex rfl rfl rfl hcov _ rfl (hp' _ _ _)
    | @protect p t s f b next run inject =>
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      change i = _ at hmask
      subst hmask
      cases ex <;> simp only [popR] <;>
        exact .inl ⟨_, _, hcov, rfl, run w (leHost_refl w) _ hex,
          .cons (.finalizerMask (p := ((t, s, f) : AmbientPosition)) i fun same _ => inject same) tail,
          ⟨hp.recorded, hp.deferred⟩⟩
    | @scopedResume p t s f b next prev sc callback hook widen inject =>
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      change i = _ at hmask
      subst hmask
      cases ex <;> simp only [popR] <;>
        exact .inr ⟨_, prev, sc, _, callback _, widen w (leHost_refl w) _ hex, hook w (leHost_refl w),
          rfl, .cons (.finalizerMask (p := ((t, s, f) : AmbientPosition)) i fun same _ => inject same) tail,
          ⟨hp.recorded, hp.deferred⟩⟩
    | answer next run =>
      have hrun := run w (leHost_refl w) ex hex
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      change i = _ at hmask
      subst hmask
      simp only [popR]
      split
      · rename_i ex' heq
        rw [heq] at hrun
        obtain ⟨self, sub⟩ := ambientExit_self (ambientProgAt_pure_inv hrun)
        exact ih _ _ _ _ tail self (Row.subset_trans sub hcov) rfl ⟨hp.recorded, hp.deferred⟩
      · rename_i ex' k heq
        rw [heq] at hrun
        obtain ⟨self, sub⟩ := ambientExit_self (ambientProgAt_unguard_inv hrun)
        exact ih _ _ _ _ tail self (Row.subset_trans sub hcov) rfl ⟨hp.recorded, hp.deferred⟩
      · exact .inl ⟨_, _, hcov, rfl, hrun, tail, ⟨hp.recorded, hp.deferred⟩⟩
    | @asyncFinalizer a s f b name protocol inject =>
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      change i = _ at hmask
      subst hmask
      cases ex with
      | failure c =>
        have code : AmbientProgAt root w (f, false) ((a, s, f) : AmbientPosition)
            (if c.hasInterrupts then interp.cancelThenFail name c else .pure (.failure c)) := by
          split
          · rename_i hint
            exact ambientProg_entry root
              (laws.asyncFinalizer _ _ _ name (protocol w (leHost_refl w)) c hex.1 hint) false
          · exact .pure hex ⟨Or.inl rfl, inject⟩
        simp only [popR]
        cases i
        · exact .inl ⟨_, (((a, s, f) : AmbientPosition), false), hcov, rfl, code, tail,
            ⟨hp.recorded, hp.deferred⟩⟩
        · exact .inl ⟨_, (((a, s, f) : AmbientPosition), false), hcov, rfl, code,
            .cons (.restoreMask (p := ((a, s, f) : AmbientPosition)) true fun _ _ => inject) tail,
            ⟨hp.recorded, hp.deferred⟩⟩
      | success v =>
        simp only [popR]
        cases i <;> cases ic
        · exact ih _ _ _ _ tail hex hcov rfl ⟨hp.recorded, hp.deferred⟩
        · exact ih _ _ _ _ tail hex hcov rfl ⟨hp.recorded, hp.deferred⟩
        · exact ih _ _ _ _ tail hex hcov rfl ⟨hp.recorded, hp.deferred⟩
        · refine .inl ⟨_, (((a, s, f) : AmbientPosition), true), hcov, rfl,
            .pure (ambientExit_failure (strongExit_of_clean w _ _
            (pendingCause_clean ⟨hp.recorded, hp.deferred⟩)
            (pendingCause_noShapeDefect _ ⟨hp.recorded, hp.deferred⟩)) inject) ⟨Or.inr inject, inject⟩,
            tail, ⟨hp.recorded, hp.deferred⟩⟩
    | @iter a c s f b name protocol rows =>
      obtain ⟨errors, step⟩ := laws.iterator _ _ _ _ name (protocol w (leHost_refl w))
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      change i = _ at hmask
      subst hmask
      cases ex with
      | failure c =>
        simp only [popR]
        exact ih _ _ _ _ tail ⟨strongExit_failure_of_error errors hex.1, Row.subset_refl _⟩ hcov rfl
          ⟨hp.recorded, hp.deferred⟩
      | success v =>
        have h := step v hex.1.1
        cases hs : (interp.iterNext name v).2 with
        | done result =>
          rw [hs] at h
          simp only [popR, hs]
          exact .inl ⟨_, (((c, s, f) : AmbientPosition), i), hcov, rfl,
            .pure ⟨h, Row.subset_refl _⟩ ⟨Or.inr rows, rows⟩, tail, ⟨hp.recorded, hp.deferred⟩⟩
        | halt cause =>
          rw [hs] at h
          simp only [popR, hs]
          exact .inl ⟨_, (((c, s, f) : AmbientPosition), i), hcov, rfl, .pure ⟨h, rows⟩ ⟨Or.inr rows, rows⟩,
            tail, ⟨hp.recorded, hp.deferred⟩⟩
        | resume code name' =>
          rw [hs] at h
          obtain ⟨a', typed, next⟩ := h
          simp only [popR, hs]
          exact .inl ⟨_, (((a', s, f) : AmbientPosition), i), hcov, rfl, ambientProg_entry root typed _,
            .cons (.iter _ next rows) tail, ⟨hp.recorded, hp.deferred⟩⟩
    | @loop a c s f b name cursor protocol rows =>
      obtain ⟨errors, step⟩ := laws.loop _ _ _ _ name cursor (protocol w (leHost_refl w))
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      change i = _ at hmask
      subst hmask
      cases ex with
      | failure c =>
        simp only [popR]
        exact ih _ _ _ _ tail ⟨strongExit_failure_of_error errors hex.1, Row.subset_refl _⟩ hcov rfl
          ⟨hp.recorded, hp.deferred⟩
      | success v =>
        have h := step v hex.1.1
        cases hs : interp.loopResume name cursor v with
        | «continue» cursor' body =>
          rw [hs] at h
          obtain ⟨a', typed, next⟩ := h
          simp only [popR, hs]
          exact .inl ⟨_, (((a', s, f) : AmbientPosition), i), hcov, rfl, ambientProg_entry root typed _,
            .cons (.loop _ _ next rows) tail, ⟨hp.recorded, hp.deferred⟩⟩
        | finish code =>
          rw [hs] at h
          simp only [popR, hs]
          exact .inl ⟨_, (((c, s, f) : AmbientPosition), i), hcov, rfl, ambientProg_entry root h _, tail,
            ⟨hp.recorded, hp.deferred⟩⟩

end Effect4.Program.Typed
