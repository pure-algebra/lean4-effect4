import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Typed.Seq

/-!
# Scope presence: the posts that answer a scope handle (`E4-TYPED-CE-018`, decisions row 156)

Codex's second-eyes review of seat I's head `509d243c`
(`docs/research/2026-10-01-landing/codex-second-eyes/`: `review.md`, `ScopeAllocationPost.lean`,
`scope-allocation-post.log`; nine theorems at `[propext, Quot.sound]`, five guards) found that
the five posts that answer a scope handle (`storePost`'s `scopeMake`, `scopeFork`, `memoBuild`,
`memoRelease`; `fiberPost`'s `ambientScope`) said only `∃ sc, ans = scopeHandle sc`, while row
139 made the close and fork rows demand the scope's presence. So the continuation of an
allocation had to be typed at a scope no world need hold: the checked source `forkAfterMake`
(make a sequential scope, fork a unit child into it; checked at `pure (fiberOf unit never)`, run
to `fiber 1` at fuel 40) had no `TypedProg` derivation at any world where scope 0 is absent,
which refuted the exact `DenotesTyped` proposition at its root point; and membership at
`Ty.scope` read the target name only, so an absent scope's handle fit.

Decisions row 156 (integration seat I2, 2026-10-01): one predicate, `ScopeLive w sc` (the
world's store holds an entry for `sc`, `Laws/Program/Typed/World.lean`), read by the scope arm
of `HandleFits`, by the five posts (as `Fits w' ans Ty.scope`), by the scope arms of `storePre`
and `fiberPre`, and by `TypedProg`'s `scopeExit` constructor; it persists along the world order
(`scopeLive_mono`). The adequacy instances (`Typed/Adequacy.lean`) prove that the store step
installs or holds the scope it answers.

**History**, red against the old definitions: Codex's three refutations restated over
`OldPostTypedProg`, a local copy of the judgment with the old posts (`oldStorePost`,
`oldFiberPost`) and the old `scopeExit` constructor, every other clause the current one; his two
one-line controls pinned failing against the current post and membership by
`#guard_msgs (error)`. **Flips and positive controls**, over the current judgment:
`scopeMake_post_needs_presence`, `absent_scope_refused`, `makeThenClose_typed` and
`forkAfterMake_typed` at every world (so at Codex's `startingWorld`: `makeThenClose_at_start`,
`forkAfterMake_at_start`), and `forkAfterMake_denotes`, `Assembly.lean`'s `DenotesTyped`
proposition at `point`. Codex's candidate post (`presentScopeAnswer`) is the landed one
(`scopeMake_post_iff`). The checker certificate (`forkAfterMake_checked`, `decide +kernel`) and
the runtime `#guard`s are kept.
-/

set_option autoImplicit false

namespace Test.Counterexamples.Machine.Semantics.ScopePresence

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def unitTy : EffTy := EffTy.pure .unit

/-- The checked source's type: a fiber handle at `(unit, never)`. -/
def fiberTy : EffTy := EffTy.pure (.fiberOf .unit .never)

/-- Codex's allocation followed by its close. -/
def makeThenClose : RProgram :=
  .vis (.inl (.scopeMake .sequential)) fun value =>
    match Val.scope? value with
    | some scope => .vis (.inr (.closeScope scope (.success .unit))) Effects.Program.pure
    | none => .pure badShapeExit

/-- Codex's checked source: the ordinary allocator followed by a scoped fork into it. -/
def forkAfterMake : NativeEff :=
  .bind (.perform (.scopeMake .sequential) (.lit .unit))
    (.withFiber (.forkIn (.succeed (.lit .unit)) ⟨true, false, .inherit⟩ (.var 0)))

/-- The root point at fuel 20. -/
def point : Point := ⟨[], [], 20, [], [], 0⟩

/-- Codex's starting world: the root declared at the checked type, the empty store (no scope). -/
def startingWorld : W where
  ids := [Api.root]
  state := Stores.empty
  Γ := fun id => if id = Api.root then some fiberTy else none
  «Π» := fun _ => none
  Ρ := fun _ => none
  Θ := fun _ _ => none

/-! ## Kept from the probe: the checker certificate and the runtime -/

#guard Api.typeOf forkAfterMake [] = some fiberTy

/-- The source checker's certificate, kernel checked. -/
theorem forkAfterMake_checked :
    Checker.check (nativeSignature []) [] [] forkAfterMake = .ok fiberTy := by decide +kernel

/- The run answers the forked fiber's handle at fuel 40. -/
#guard (Api.runSync forkAfterMake 40).2 = .success (Val.fiber ⟨1⟩)

/- A real allocation answers scope 0 and installs its store entry. -/
#guard ((syncOpStep (.scopeMake .sequential) Stores.empty).map (·.2)) = some (Val.scopeHandle 0)
#guard ((syncOpStep (.scopeMake .sequential) Stores.empty).map
  (fun pair => (pair.1.scopes.entryAt 0).isSome)) = some true

/- A number cannot stand in for a scope handle at the checker. -/
#guard Api.typeOf (.withFiber (.forkIn (.succeed (.lit .unit))
  ⟨true, false, .inherit⟩ (.lit (.nat 0)))) [] = none

/-- The root point is admitted at the checked type, at every world. -/
theorem point_admitted (w : W) : PointTyped (forkAfterMake : ProgramSource) w point fiberTy :=
  ⟨forkAfterMake, [], rfl, forkAfterMake_checked, envTyped_nil w⟩

/-! ## History: the judgment with the posts before row 156

The posts are the current ones except the five scope-handle arms; the judgment is the current
one except that it reads those posts and that its `scopeExit` constructor reads no pre. -/

/-- The store posts before row 156: the four scope-handle arms said only that the answer is some
scope's handle; every other arm is the current one. -/
def oldStorePost (w' : W) : (op : SyncOp) → StoreCert op → Val → Prop
  | .scopeMake _, _, ans | .scopeFork _ _, _, ans | .memoBuild _ _, _, ans =>
    ∃ sc, ans = Val.scopeHandle sc
  | .memoRelease _ _, _, ans => ans = Val.unit ∨ ∃ sc, ans = Val.scopeHandle sc
  | op, cert, ans => storePost w' op cert ans

/-- The fiber posts before row 156: the ambient-scope read answered some scope's handle; every
other arm is the current one. -/
def oldFiberPost (w' : W) : (op : FiberOp) → FiberCert op → op.answer → Prop
  | .ambientScope, _, ans => ∃ sc, ans = Val.scopeHandle sc
  | op, cert, ans => fiberPost w' op cert ans

/-- `TypedProg` before row 156: the old posts, and a `scopeExit` constructor that reads no pre. -/
inductive OldPostTypedProg (root : ProgramSource) : W → EffTy → RProgram → Prop
  | pure {w : W} {ty : EffTy} {ex : ExitV} (exit : ExitOk w ty ex) :
      OldPostTypedProg root w ty (.pure ex)
  | store {w : W} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
      (cert : StoreCert op) (pre : storePre root w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, oldStorePost w' op cert ans →
        OldPostTypedProg root w' ty (k ans)) :
      OldPostTypedProg root w ty (.vis (.inl op) k)
  | fiber {w : W} {ty : EffTy} {op : FiberOp} {k : op.answer → RProgram}
      (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
      (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
      (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex)
      (cert : FiberCert op) (pre : fiberPre root w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, oldFiberPost w' op cert ans →
        OldPostTypedProg root w' ty (k ans)) :
      OldPostTypedProg root w ty (.vis (.inr op) k)
  | guard {w : W} {ty : EffTy} {kind : GuardKind} {k : Option ExitV → RProgram}
      (mid : EffTy) (body : OldPostTypedProg root w mid (k none))
      (run : ∀ w', w.leHost w' → ∀ ex, fiberPost w' (.guard_ kind) mid (some ex) →
        OldPostTypedProg root w' ty (k (some ex)))
      (skip : ∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → kind.hasExitArm ex = false →
        ExitOk w' ty ex) :
      OldPostTypedProg root w ty (.vis (.inr (.guard_ kind)) k)
  | unguard {w : W} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex) : OldPostTypedProg root w ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer {w : W} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex) :
      OldPostTypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k)
  | scopeExit {w : W} {ty : EffTy} {prev : Ctx} {sc : Nat} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex)
      (next : ∀ w', w.leHost w' → ∀ ans, OldPostTypedProg root w' ty (k ans)) :
      OldPostTypedProg root w ty (.vis (.inr (.scopeExit prev sc ex)) k)

namespace OldPostTypedProg

theorem store_inv {root : ProgramSource} {w : W} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
    (h : OldPostTypedProg root w ty (.vis (.inl op) k)) :
    ∃ cert : StoreCert op, storePre root w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, oldStorePost w' op cert ans →
        OldPostTypedProg root w' ty (k ans) := by
  cases h with
  | store cert pre next => exact ⟨cert, pre, next⟩

theorem fiber_inv {root : ProgramSource} {w : W} {ty : EffTy} {op : FiberOp}
    {k : op.answer → RProgram} (h : OldPostTypedProg root w ty (.vis (.inr op) k))
    (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
    (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
    (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex) :
    ∃ cert : FiberCert op, fiberPre root w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, oldFiberPost w' op cert ans →
        OldPostTypedProg root w' ty (k ans) := by
  cases h with
  | fiber _ _ _ _ cert pre next => exact ⟨cert, pre, next⟩
  | guard _ _ _ _ => exact absurd rfl (notGuard _)
  | unguard _ => exact absurd rfl (notUnguard _)
  | finishFinalizer _ => exact absurd rfl (notFinish _)
  | scopeExit _ _ => exact absurd rfl (notScopeExit _ _ _)

theorem guard_inv {root : ProgramSource} {w : W} {ty : EffTy} {kind : GuardKind}
    {k : Option ExitV → RProgram} (h : OldPostTypedProg root w ty (.vis (.inr (.guard_ kind)) k)) :
    ∃ mid : EffTy, OldPostTypedProg root w mid (k none) ∧
      ∀ w', w.leHost w' → ∀ ex, fiberPost w' (.guard_ kind) mid (some ex) →
        OldPostTypedProg root w' ty (k (some ex)) := by
  cases h with
  | fiber notGuard _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
  | guard mid body run _ => exact ⟨mid, body, run⟩

theorem unguard_payload_inv {root : ProgramSource} {w : W} {ty : EffTy} {ex : ExitV}
    {k : ExitV → RProgram} (h : OldPostTypedProg root w ty (.vis (.inr (.unguard ex)) k)) :
    ExitOk w ty ex := by
  cases h with
  | fiber _ notUnguard _ _ _ _ _ => exact absurd rfl (notUnguard ex)
  | unguard payload => exact payload

end OldPostTypedProg

/-- **History (Codex's `missing_answer_allowed`)**: the old allocation post admitted a scope's
handle at every world, whether or not the world holds the scope. -/
theorem old_missing_answer_allowed (w : W) (scope : Nat) :
    oldStorePost w (.scopeMake .sequential) () (Val.scopeHandle scope) := ⟨scope, rfl⟩

/-- **History (Codex's `makeThenClose_refused`)**: under the old allocation post and row 139's
close pre, the allocation followed by its close had no derivation at a world where the answered
scope is absent, since the continuation had to be typed at that world. -/
theorem old_makeThenClose_refused (root : ProgramSource) (w : W) (ty : EffTy) (scope : Nat)
    (absent : w.state.scopes.entryAt scope = none) :
    ¬ OldPostTypedProg root w ty makeThenClose := by
  intro typed
  obtain ⟨_, _, next⟩ := OldPostTypedProg.store_inv typed
  have close := next w (leHost_refl w) (Val.scopeHandle scope) ⟨scope, rfl⟩
  change OldPostTypedProg root w ty
    (.vis (.inr (.closeScope scope (.success .unit))) Effects.Program.pure) at close
  obtain ⟨_, pre, _⟩ := OldPostTypedProg.fiber_inv close
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  change (w.state.scopes.entryAt scope).isSome = true at pre
  rw [absent] at pre
  exact Bool.noConfusion pre

/-- **History (Codex's `forkAfterMake_denotation_refused`)**: under the old posts the checked
source's denotation at `point` had no derivation at a world where scope 0 is absent. -/
theorem old_forkAfterMake_denotation_refused (w : W) (ty : EffTy)
    (absent : w.state.scopes.entryAt 0 = none) :
    ¬ OldPostTypedProg (forkAfterMake : ProgramSource) w ty
      (denoteR forkAfterMake forkAfterMake point) := by
  intro typed
  obtain ⟨_, body, run⟩ := OldPostTypedProg.guard_inv typed
  obtain ⟨_, _, next⟩ := OldPostTypedProg.store_inv body
  have marker := next w (leHost_refl w) (Val.scopeHandle 0) ⟨0, rfl⟩
  have payload := OldPostTypedProg.unguard_payload_inv marker
  have continuation := run w (leHost_refl w) (.success (Val.scopeHandle 0)) ⟨rfl, payload⟩
  obtain ⟨_, _, constructed⟩ := OldPostTypedProg.fiber_inv continuation
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have fork := constructed w (leHost_refl w) [] (fun _ h => nomatch h)
  obtain ⟨_, pre, _⟩ := OldPostTypedProg.fiber_inv fork
    (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have live : (w.state.scopes.entryAt 0).isSome = true := pre.2
  rw [absent] at live
  exact Bool.noConfusion live

/-- **History (Codex's `m5_denotation_shape_false`)**: over the old posts, the `DenotesTyped`
proposition was false for the checked source, at `startingWorld` and `point`. -/
theorem old_denotation_shape_false :
    ¬ (∀ (w : W) (p : Point) (e : NativeEff) (ty : EffTy),
      Node.at_ (.eff forkAfterMake) p.path = some (.eff e) →
      PointTyped (forkAfterMake : ProgramSource) w p ty →
      OldPostTypedProg (forkAfterMake : ProgramSource) w ty (denoteR forkAfterMake e p)) := by
  intro law
  exact old_forkAfterMake_denotation_refused startingWorld _ rfl
    (law startingWorld point forkAfterMake _ rfl (point_admitted startingWorld))

/-! ## Codex's one-line controls, pinned failing against the current definitions -/

-- The old allocation post's witness: the current post is membership at `Ty.scope`, which reads
-- presence, so the anonymous constructor no longer elaborates.
/--
error: Application type mismatch: The argument
  scope
has type
  Nat
of sort `Type` but is expected to have type
  Ty.scopeTarget = Ty.scopeTarget
of sort `Prop` in the application
  And.intro scope
-/
#guard_msgs (error) in
example (w : W) (scope : Nat) :
    storePost w (.scopeMake .sequential) () (Val.scopeHandle scope) := ⟨scope, rfl⟩

-- The old membership's witness: a handle of an absent scope fit `Ty.scope`.
/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.10 = ?m.10
but is expected to have type
  Typed.Fits startingWorld (Val.scopeHandle 0) Ty.scope
in the application
  And.intro rfl
-/
#guard_msgs (error) in
example : Fits startingWorld (Val.scopeHandle 0) Ty.scope ∧
    startingWorld.state.scopes.entryAt 0 = none := ⟨rfl, rfl⟩

/-! ## The flips and the positive controls, over the current judgment -/

/-- **Flip of `absent_scope_still_fits` (row 156)**: an absent scope's handle does not fit
`Ty.scope`. -/
theorem absent_scope_refused : ¬ Fits startingWorld (Val.scopeHandle 0) Ty.scope := by
  intro h
  obtain ⟨_, same, live⟩ := fits_scope_inv h
  cases same
  exact absurd live (by decide)

/-- **Flip of `missing_answer_allowed` (row 156)**: the allocation post admits a handle only for a
scope the answer world holds; `startingWorld` holds none. -/
theorem scopeMake_post_needs_presence :
    ¬ storePost startingWorld (.scopeMake .sequential) () (Val.scopeHandle 0) :=
  fun post => absent_scope_refused post

/-- Codex's candidate post (`presentScopeAnswer`: some scope's handle, the scope present at the
answer world) is the landed allocation post: membership at `Ty.scope` owns the shape. -/
theorem scopeMake_post_iff (w : W) (strategy : FinalizerStrategy) (ans : Val) :
    storePost w (.scopeMake strategy) () ans ↔ ∃ sc, ans = Val.scopeHandle sc ∧ ScopeLive w sc :=
  ⟨fits_scope_inv, fun ⟨sc, same, live⟩ => same ▸ fits_scopeHandle w sc live⟩

/-- Codex's passing control `close_live`, read through `ScopeLive`: the close rule accepts a
present scope. -/
theorem close_live (root : ProgramSource) (w : W) (scope : Nat) (live : ScopeLive w scope) :
    TypedProg root w unitTy
      (.vis (.inr (.closeScope scope (.success .unit))) Effects.Program.pure) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () live
    (fun _ _ _ post => TypedProg.pure post)

/-- Codex's passing control `allocation_alone_typed`: the allocator alone answers at `Ty.scope`
(its post is now membership there). -/
theorem allocation_alone_typed (root : ProgramSource) (w : W) :
    TypedProg root w (EffTy.pure Ty.scope) (storeR (.scopeMake .sequential)) := by
  refine TypedProg.store () trivial ?_
  intro w' _ ans post
  exact TypedProg.pure (strongExit_success w' _ _ post)

/-- **`makeThenClose` is typed at every world (row 156)**: the allocation's post gives the
answered scope's presence at the answer world, which the close demands. The flip of Codex's
`makeThenClose_refused`. -/
theorem makeThenClose_typed (root : ProgramSource) (w : W) :
    TypedProg root w unitTy makeThenClose := by
  refine TypedProg.store (op := .scopeMake .sequential) () trivial ?_
  intro w' _ ans post
  obtain ⟨sc, rfl, live⟩ := fits_scope_inv post
  exact close_live root w' sc live

/-- At Codex's `startingWorld`, whose store holds no scope. -/
theorem makeThenClose_at_start (root : ProgramSource) :
    TypedProg root startingWorld unitTy makeThenClose :=
  makeThenClose_typed root startingWorld

/-- The forked child's certificate: the child at `[1, 0, 0]`, in the environment the bind's
continuation binds (the allocation's answer at `Ty.scope`), checks at `unit`. -/
theorem child_checked :
    Checker.check (nativeSignature []) [Ty.scope] [1, 0, 0] (.succeed (.lit .unit)) = .ok unitTy := by
  decide +kernel

/-- The fork node the denotation reaches once the allocation has answered scope `sc`: the
`forkIn` action at the child's point, in scope `sc`, at the action node's site. -/
theorem fork_node (completed : List (FiberId × ExitV)) (sc : Nat) :
    denoteR forkAfterMake
        (.withFiber (.forkIn (.succeed (.lit .unit)) ⟨true, false, .inherit⟩ (.var 0)))
        ({ point with completed }.childWith 1 (Val.scopeHandle sc)) =
      .vis (.inr (.forkIn
        ((({ point with completed }.childWith 1 (Val.scopeHandle sc)).child 0).child 0)
        ⟨true, false, .inherit⟩ sc [1, 0])) (fun v => .pure (.success v)) := rfl

/-- **The checked source's denotation is typed at every world (row 156)**: the allocation's post
gives the scope's presence at its answer world, the fork's pre demands it at every later world
(`scopeLive_mono`), and the fork's post declares the child at `unit`, below the handle's columns.
The flip of Codex's `forkAfterMake_denotation_refused`. -/
theorem forkAfterMake_typed (w : W) :
    TypedProg (forkAfterMake : ProgramSource) w fiberTy
      (denoteR forkAfterMake forkAfterMake point) := by
  show TypedProg _ w fiberTy (denoteR forkAfterMake
    (.bind (.perform (.scopeMake .sequential) (.lit .unit))
      (.withFiber (.forkIn (.succeed (.lit .unit)) ⟨true, false, .inherit⟩ (.var 0)))) point)
  rw [denoteR_bind _ _ _ _ (by decide)]
  refine seq_typed _ (mid := EffTy.pure Ty.scope) ?_ ?_ rfl
  · show TypedProg _ w _ (.vis (.inl (.scopeMake .sequential)) fun v => .pure (.success v))
    refine TypedProg.store () trivial ?_
    intro w' _ ans post
    exact TypedProg.pure (strongExit_success w' _ _ post)
  · intro w' _ v hv
    obtain ⟨sc, rfl, live⟩ := fits_scope_inv hv
    refine TypedProg.fiber (op := .construction) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial ?_
    intro w'' ord completed _
    show TypedProg _ w'' fiberTy (denoteR forkAfterMake
        (.withFiber (.forkIn (.succeed (.lit .unit)) ⟨true, false, .inherit⟩ (.var 0)))
        ({ point with completed }.childWith 1 (Val.scopeHandle sc)))
    rw [fork_node completed sc]
    have present : ScopeLive w'' sc := scopeLive_mono ord.1 live
    refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) unitTy ⟨?_, present⟩ ?_
    · exact ⟨.succeed (.lit .unit), [Ty.scope], rfl, child_checked,
        envTyped_append (envTyped_nil w'') (fits_scopeHandle w'' sc present)⟩
    · intro w''' _ ans post
      obtain ⟨id, rfl, declared⟩ := post
      exact TypedProg.pure (strongExit_success w''' _ _ ⟨unitTy, declared, Ty.subN_refl _, Ty.subN_refl _⟩)

/-- At Codex's `startingWorld`, whose store holds no scope. -/
theorem forkAfterMake_at_start :
    TypedProg (forkAfterMake : ProgramSource) startingWorld fiberTy
      (denoteR forkAfterMake forkAfterMake point) :=
  forkAfterMake_typed startingWorld

/-- **`DenotesTyped` at `point` (row 156)**: `Assembly.lean`'s `DenotesTyped` proposition for the
checked source, read at its root point, holds at every world. The flip of Codex's
`m5_denotation_shape_false`, which refuted it at this point and `startingWorld`. -/
theorem forkAfterMake_denotes : ∀ (w : W) (e : NativeEff) (ty : EffTy),
    Node.at_ (.eff (forkAfterMake : ProgramSource).program) point.path = some (.eff e) →
    PointTyped (forkAfterMake : ProgramSource) w point ty →
    TypedProg (forkAfterMake : ProgramSource) w ty
      (denoteR (forkAfterMake : ProgramSource).program e point) := by
  intro w e ty node admitted
  change some (Node.eff forkAfterMake) = some (.eff e) at node
  cases node
  obtain ⟨e', env, node', checked, envTyped⟩ := admitted
  change some (Node.eff forkAfterMake) = some (.eff e') at node'
  cases node'
  have empty : env = [] := List.eq_nil_of_length_eq_zero envTyped.1
  subst empty
  have same : (Except.ok ty : Except _ EffTy) = .ok fiberTy :=
    checked.symm.trans forkAfterMake_checked
  cases same
  exact forkAfterMake_typed w

end Test.Counterexamples.Machine.Semantics.ScopePresence

open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms forkAfterMake_checked
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms point_admitted
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms OldPostTypedProg.store_inv
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms OldPostTypedProg.fiber_inv
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms OldPostTypedProg.guard_inv
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms OldPostTypedProg.unguard_payload_inv
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms old_missing_answer_allowed
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms old_makeThenClose_refused
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms old_forkAfterMake_denotation_refused
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms old_denotation_shape_false
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms scopeMake_post_needs_presence
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms absent_scope_refused
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms scopeMake_post_iff
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms close_live
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms allocation_alone_typed
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms makeThenClose_typed
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms makeThenClose_at_start
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms child_checked
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms fork_node
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms forkAfterMake_typed
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms forkAfterMake_at_start
open Test.Counterexamples.Machine.Semantics.ScopePresence in
#print axioms forkAfterMake_denotes
