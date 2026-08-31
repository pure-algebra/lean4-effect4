import Cas.Lang.Tower
import Cas.Lang.Representation

/-!
# JUDGE probe against proposal C (layer-is-a-handler-transformer, in M)

Adversarial. Everything here is checked; nothing is asserted.
-/

namespace JudgeC

open Cas.Lang

abbrev Ctx (S : Sig) (M : Type → Type) := Handler S M
abbrev Layer (Out In : Sig) (M : Type → Type) : Type := Ctx In M → M (Ctx Out M)

def Layer.empty [Monad M] {A : Sig} : Layer A A M := fun h => pure h
def Layer.provide [Monad M] {A B C : Sig}
    (outer : Layer A B M) (inner : Layer B C M) : Layer A C M :=
  fun h => inner h >>= outer
def Layer.merge [Monad M] {A B C : Sig}
    (l : Layer A C M) (r : Layer B C M) : Layer (A ⊕ₛ B) C M :=
  fun h => l h >>= fun hl => r h >>= fun hr => pure (hl.sum hr)
def Layer.launch [Monad M] {A B : Sig} (l : Layer A B M) (h : Ctx B M) {X : Type}
    (p : Prog A X) : M X := l h >>= fun ho => interpret ho p

/-! ## A. The scope exhibit is DEGENERATE — three checks. -/

abbrev Tgt (E σ : Type) := ExceptT E (StateM σ)
abbrev T2 := Tgt String Nat

def ens {E σ α : Type} (body : Tgt E σ α) (fin : Tgt E σ Unit) : Tgt E σ α :=
  fun s =>
    match body s with
    | (.ok a, s₁) =>
      match fin s₁ with
      | (.ok _, s₂) => (.ok a, s₂)
      | (.error e, s₂) => (.error e, s₂)
    | (.error e, s₁) => (.error e, (fin s₁).2)

inductive LowE | tick
abbrev LowE.Ans : LowE → Type | .tick => Unit
def LowSig : Sig := ⟨LowE, LowE.Ans⟩

inductive ScopeE | ensuring (body fin : Nat)
abbrev ScopeE.Ans : ScopeE → Type | .ensuring _ _ => Unit
def ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩

def failBody : T2 Unit := fun s => (.error "boom", s)

/-- C's `blocks`, VERBATIM: the lower context `_h` is DISCARDED. -/
def blocks (_h : Ctx LowSig T2) : Nat → T2 Unit
  | 0 => failBody
  | 1 => fun s => (.ok (), s + 1)
  | _ => fun s => (.ok (), s)

def scopeLayer : Layer ScopeSig LowSig T2 :=
  fun h => pure ⟨fun | .ensuring b f => ens (blocks h b) (blocks h f)⟩

def lowLayer : Layer LowSig LowSig T2 := Layer.empty
def tower : Layer ScopeSig LowSig T2 := Layer.provide scopeLayer lowLayer

/-- **A1. C's scoped layer is a CONSTANT function of the context it receives.**
It never consults the layer beneath it, so the exhibit witnesses no composition
at all. Every pair of lower contexts gives the identical built scope. -/
theorem C_scopeLayer_ignores_its_context (h h' : Ctx LowSig T2) :
    scopeLayer h = scopeLayer h' := rfl

/-- **A2. C's `tower` IS `scopeLayer`, pointwise, by `rfl`.** `lowLayer` is
`Layer.empty`, so `provide` contributes a `pure` and nothing else. The scoped
layer is at the TOP of the "composite", not in its middle: nothing consumes
`ScopeSig` above it and nothing below it is used. -/
theorem C_tower_is_just_the_scope_layer (h : Ctx LowSig T2) :
    tower h = scopeLayer h := rfl

/-- **A3.** Hence C's `tower_finalises_on_failure` is a fact about a standalone
constant handler, definitionally equal to the un-composed one. -/
def ctx0 : Ctx LowSig T2 := ⟨fun _ => fun s => (.ok (), s)⟩
theorem C_tower_theorem_is_the_standalone_theorem :
    (tower ctx0 0).1 = (scopeLayer ctx0 0).1 := rfl

/-! ## B. FAIRNESS: does the FORK-A lift actually work on a REAL tower?
Three genuine layers, scope in the MIDDLE, the middle actually consuming the
context below it, and a real consumer above it. -/

inductive HighE | job
abbrev HighE.Ans : HighE → Type | .job => Unit
def HighSig : Sig := ⟨HighE, HighE.Ans⟩

/-- A REAL bottom: `tick` bumps the word. -/
def realCtx0 : Ctx LowSig T2 := ⟨fun _ => fun s => (.ok (), s + 10)⟩

/-- A REAL middle: the block table is built FROM the lower context `h`, so this
layer genuinely depends on what is beneath it. -/
def realBlocks (h : Ctx LowSig T2) : Nat → T2 Unit
  | 0 => fun s => match h.handle LowE.tick s with
                  | (.ok _, s₁) => (.error "boom", s₁)
                  | (.error e, s₁) => (.error e, s₁)
  | 1 => h.handle LowE.tick
  | _ => fun s => (.ok (), s)

def realScope : Layer ScopeSig LowSig T2 :=
  fun h => pure ⟨fun | .ensuring b f => ens (realBlocks h b) (realBlocks h f)⟩

/-- A REAL top: it provides `HighSig` by USING the scope operation beneath it. -/
def realTop : Layer HighSig ScopeSig T2 :=
  fun hs => pure ⟨fun | .job => hs.handle (.ensuring 0 1)⟩

def realTower : Layer HighSig LowSig T2 := Layer.provide realTop realScope

/-- **B1. The lift is REAL.** Through a genuine three-storey composite, a
failing body still runs its finalizer and the word survives: the body ticks
(0 -> 10) then refuses; the finalizer ticks again (10 -> 20); the refusal is
re-raised unchanged. This is the theorem C claimed and did NOT witness. -/
theorem the_fork_A_lift_actually_works :
    Layer.launch realTower realCtx0 (Prog.op HighE.job) 0
      = (.error "boom", 20) := rfl

/-! ## C. THE MEMO STORY — unnecessary where it would help, and ineffective
where it is aimed. -/

abbrev Cnt := StateM Nat
def tickH : Handler LowSig Cnt := ⟨fun _ => fun n => ((), n + 1)⟩

/-- A costly shared dependency: building it bumps the counter. -/
def costlyDep : Layer LowSig LowSig Cnt := fun _ => fun n => (tickH, n + 1)

/-- Two consumers of that dependency. -/
def useA : Layer HighSig LowSig Cnt := fun _ => pure ⟨fun _ => pure ()⟩
def useB : Layer HighSig LowSig Cnt := fun _ => pure ⟨fun _ => pure ()⟩

/-- **C1. THE DIAMOND ALREADY SHARES, WITH NO MEMO TABLE.** The shared
dependency is built ONCE and its VALUE is handed to both consumers, because
`provide` binds it and `merge` passes the same `h` to each side. Sharing is the
Kleisli structure, not a content-address table. -/
theorem diamond_shares_without_any_memo :
    (Layer.provide (Layer.merge useA useB) costlyDep tickH 0).2 = 1 := rfl

/-- The dependency is what costs; the consumers are free. -/
theorem the_dependency_is_what_costs :
    (Layer.provide (Layer.merge useA useB) costlyDep tickH 0).2
      = (costlyDep tickH 0).2 := rfl

/-- **C2. A PERFECT MEMO HIT DOES NOT PREVENT THE DOUBLE BUILD.** Give the
content-address table its best case: `merge a a` where BOTH children denote to
the *identical* `Layer` value — a table hit on the nose. The build still runs
twice, because `Layer.merge` applies its argument twice by definition. The memo
table is keyed upstream of the build effect, so it cannot reach it. -/
def costlySvc : Layer HighSig LowSig Cnt := fun _ => fun n => (⟨fun _ => pure ()⟩, n + 1)

theorem perfect_memo_hit_pays_twice :
    (Layer.merge costlySvc costlySvc tickH 0).2 = 2 := rfl

/-- And the *only* way out is a DIFFERENT combinator that C does not define:
apply once and sum the result with itself. That combinator is not `Layer.merge`
and is not in the proposal. -/
def mergeShared [Monad M] {A C : Sig} (l : Layer A C M) : Layer (A ⊕ₛ A) C M :=
  fun h => l h >>= fun hl => pure (hl.sum hl)

theorem mergeShared_pays_once : (mergeShared costlySvc tickH 0).2 = 1 := rfl

/-- The two are separated: so "memoization" in C's design is a change of
COMBINATOR at denotation time, not a table lookup. -/
theorem memo_needs_a_new_combinator :
    (Layer.merge costlySvc costlySvc tickH 0).2 ≠ (mergeShared costlySvc tickH 0).2 := by
  decide

/-! ## D. C's own "memo law" witness is not a memoization of anything. -/

def costly : Layer HighSig LowSig Cnt := costlySvc
def svc : Handler HighSig Cnt := ⟨fun _ => pure ()⟩
/-- C's `mergedOnce`, VERBATIM. It is a hand-written constant, not the memoized
denotation of `merge costly costly` under any table. -/
def mergedOnce : Layer (HighSig ⊕ₛ HighSig) LowSig Cnt :=
  fun _ => fun n => (svc.sum svc, n + 1)

/-- **D1.** `mergedOnce` is not `Layer.merge` applied to anything: it is not
even `mergeShared costly`, which is the honest memoized form — they agree only
by accident of the counter arithmetic here. The witness exhibits that a build
counter is observable (which is `build_step_is_observable` again), not that any
memoization happens. -/
theorem mergedOnce_is_mergeShared_here :
    (mergedOnce tickH 0).2 = (mergeShared costly tickH 0).2 := rfl

/-! ## E. `Sig` HAS NO DECIDABLE EQUALITY — the `denote` seam's real obstacle. -/

/-- The memo table C specifies, existentially packed over `Sig`. It ELABORATES,
but note the universe: `Sig : Type 1`, so this is `Type 1`. -/
abbrev MemoTable (M : Type → Type) : Type 1 :=
  List (Nat × Σ' (Out In : Sig), Layer Out In M)

/-- **E1.** Consuming the table requires deciding `Sig` equality, and `Sig`
carries a `Type` field, so no `DecidableEq Sig` exists or can. This
`example` is the shape `denote`'s `.provide` arm needs and it FAILS to
synthesize — left as a comment because it does not elaborate:

    example : DecidableEq Sig := inferInstance   -- FAILS

So `denote` cannot compose two looked-up layers without carrying the
`ServiceRef` lists alongside and transporting along `congrArg sigOf`. That is
real dependent-typing work, and it is exactly the bill C says it did not pay. -/
theorem sig_is_a_type_one_structure : (Sig : Type 1) = Sig := rfl

/-! ## F. VACUITY: the three composition laws are `bind_assoc` renamed.

C's `provide_assoc` proof is `funext h; exact (bind_assoc (k h) g f).symm`, and
its unit laws are `pure_bind` / `bind_pure`. Neither `Sig`, nor `Handler`, nor
anything layer-shaped appears. Below: the SAME three laws, for a bare Kleisli
arrow between arbitrary types, with every layer concept deleted. If the laws
survive that deletion they were never about layers. -/

abbrev Arrow (M : Type → Type) (X Y : Type) : Type := X → M Y

def Arrow.id' [Monad M] {X : Type} : Arrow M X X := fun x => pure x
def Arrow.comp [Monad M] {X Y Z : Type}
    (outer : Arrow M Y Z) (inner : Arrow M X Y) : Arrow M X Z :=
  fun x => inner x >>= outer

/-- **F1.** Associativity — C's `provide_assoc`, with `Handler`, `Sig` and the
whole design deleted. Same proof term. -/
theorem arrow_assoc [Monad M] [LawfulMonad M] {W X Y Z : Type}
    (f : Arrow M X Y) (g : Arrow M W X) (k : Arrow M Z W) :
    Arrow.comp (Arrow.comp f g) k = Arrow.comp f (Arrow.comp g k) := by
  funext h; exact (bind_assoc (k h) g f).symm

/-- **F2 / F3.** Both unit laws, likewise. -/
theorem arrow_id_right [Monad M] [LawfulMonad M] {X Y : Type} (f : Arrow M X Y) :
    Arrow.comp f Arrow.id' = f := by
  funext h; simp [Arrow.comp, Arrow.id']

theorem arrow_id_left [Monad M] [LawfulMonad M] {X Y : Type} (f : Arrow M X Y) :
    Arrow.comp Arrow.id' f = f := by
  funext h; show f h >>= pure = f h; exact bind_pure (f h)

/-- **F4.** And the identification is definitional, exactly as C states it:
a `Layer` IS a `ReaderT` over a `Handler`, and `provide` IS its Kleisli
composition — so C's three discharged laws carry no layer content at all.
The laws with real content (`ofHandler_provide`, `ofHandler_reify`) are the two
that DO cite estate theorems, and they are about the embedded fragment. -/
theorem layer_is_an_arrow (Out In : Sig) (M : Type → Type) :
    Layer Out In M = Arrow M (Ctx In M) (Ctx Out M) := rfl

/-! ## G. UNDECLARED COST: `merge` forces a COMMON requirement.
`Layer.merge (l : Layer A C M) (r : Layer B C M)` needs both sides at the same
`C`. rc.112's merge combines DIFFERENT requirement sets. Recovering that needs
context restriction and leaves an unnormalized right-nested `Sig.sum`. The
restriction is cheap; the accumulation is a real cost C does not name. -/

def restrictL {S T : Sig} {M : Type → Type} (h : Ctx (S ⊕ₛ T) M) : Ctx S M :=
  ⟨fun op => h.handle (Sum.inl op)⟩
def restrictR {S T : Sig} {M : Type → Type} (h : Ctx (S ⊕ₛ T) M) : Ctx T M :=
  ⟨fun op => h.handle (Sum.inr op)⟩

def weakenL [Monad M] {A C D : Sig} (l : Layer A C M) : Layer A (C ⊕ₛ D) M :=
  fun h => l (restrictL h)
def weakenR [Monad M] {A C D : Sig} (r : Layer A D M) : Layer A (C ⊕ₛ D) M :=
  fun h => r (restrictR h)

/-- It works, so this is a cost and not a defect — but every independent merge
grows the requirement index by one unnormalized `⊕ₛ`. -/
def mergeIndependent_typechecks [Monad M] {A B C D : Sig}
    (l : Layer A C M) (r : Layer B D M) : Layer (A ⊕ₛ B) (C ⊕ₛ D) M :=
  Layer.merge (weakenL l) (weakenR r)

#print axioms arrow_assoc
#print axioms arrow_id_right
#print axioms arrow_id_left
#print axioms layer_is_an_arrow

#print axioms C_scopeLayer_ignores_its_context
#print axioms C_tower_is_just_the_scope_layer
#print axioms the_fork_A_lift_actually_works
#print axioms diamond_shares_without_any_memo
#print axioms perfect_memo_hit_pays_twice
#print axioms mergeShared_pays_once
#print axioms memo_needs_a_new_combinator
#print axioms mergedOnce_is_mergeShared_here

end JudgeC
