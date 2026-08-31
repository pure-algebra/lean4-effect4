import Cas.Lang.Tower
import Cas.Lang.Representation

/-!
# Effect Core v1 — design proposal C, checked

`Layer` as a HANDLER TRANSFORMER, in the only form that survives the estate's
own falsifier: a transformer **in the target monad**.

    Layer Out In M  :=  Handler In M → M (Handler Out M)

Design probe. Outside every lake target; adds nothing to `Cas`; mutates
nothing in `library/`.

    cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/layer/propose-C.lean
-/

namespace ProposeC

open Cas.Lang

/-! ## §0 — two estate facts, re-derived locally

This file imports no `Cas.Backend` module, so `Handler.ext` (`Universal.lean:128`)
and `through_assoc` (`:739`) / `through_id_right` (`:757`) are re-proved here from
`interpret_through` (`Cas/Lang/Tower.lean:71`) and `interpret_id`
(`Cas/Lang/Representation.lean:68`), which ARE imported and ARE on main. -/

theorem handler_ext {S : Sig} {M : Type → Type v} {h g : Handler S M}
    (e : ∀ op, h.handle op = g.handle op) : h = g := by
  cases h; cases g; exact congrArg Handler.mk (funext e)

theorem through_assoc' {S T U : Sig} {M : Type → Type} [Monad M] [LawfulMonad M]
    (t : Handler S (Prog T)) (u : Handler T (Prog U)) (h : Handler U M) :
    (t.through u).through h = t.through (u.through h) :=
  handler_ext fun op => interpret_through u h (t.handle op)

theorem through_id_right' {S T : Sig} (t : Handler S (Prog T)) :
    t.through (idHandler (S := T)) = t :=
  handler_ext fun op => interpret_id (t.handle op)

/-! ## §1 — the types

`Ctx` is not a new carrier: the requirements environment IS a handler.
`Layer` is `ReaderT (Ctx In M) M (Ctx Out M)` — rc.112's
`build(...) : Effect<Context<ROut>, E, RIn>` with `Context` read as `Handler`
and `Effect<_, E, RIn>` read as `ReaderT (Handler RIn M) M`. -/

abbrev Ctx (S : Sig) (M : Type → Type) := Handler S M

abbrev Layer (Out In : Sig) (M : Type → Type) : Type := Ctx In M → M (Ctx Out M)

/-- The `ReaderT` reading is definitional, not analogical. -/
theorem layer_is_readerT (Out In : Sig) (M : Type → Type) :
    Layer Out In M = ReaderT (Ctx In M) M (Ctx Out M) := rfl

variable {M : Type → Type} {A B C D : Sig}

/-- `Layer.empty` — the identity context transformer. -/
def Layer.empty [Monad M] : Layer A A M := fun h => pure h

/-- `Layer.provide` — Kleisli composition in the category of contexts. -/
def Layer.provide [Monad M] (outer : Layer A B M) (inner : Layer B C M) :
    Layer A C M := fun h => inner h >>= outer

/-- `Layer.merge` — `Handler.sum` under the build effect. -/
def Layer.merge [Monad M] (l : Layer A C M) (r : Layer B C M) :
    Layer (A ⊕ₛ B) C M :=
  fun h => l h >>= fun hl => r h >>= fun hr => pure (hl.sum hr)

/-- `Layer.build` IS application. It is not a separate combinator. -/
def Layer.build (l : Layer A B M) (h : Ctx B M) : M (Ctx A M) := l h

/-- `Layer.launch` — build, then interpret. Derived, one line. -/
def Layer.launch [Monad M] (l : Layer A B M) (h : Ctx B M) {X : Type}
    (p : Prog A X) : M X := l h >>= fun ho => interpret ho p

/-! ## §2 — the composition laws -/

theorem provide_assoc [Monad M] [LawfulMonad M]
    (f : Layer A B M) (g : Layer B C M) (k : Layer C D M) :
    (f.provide g).provide k = f.provide (g.provide k) := by
  funext h; exact (bind_assoc (k h) g f).symm

theorem provide_empty_right [Monad M] [LawfulMonad M] (f : Layer A B M) :
    f.provide Layer.empty = f := by
  funext h; simp [Layer.provide, Layer.empty]

theorem provide_empty_left [Monad M] [LawfulMonad M] (f : Layer A B M) :
    Layer.empty.provide f = f := by
  funext h; show f h >>= pure = f h; exact bind_pure (f h)

/-! ## §3 — the estate's tower is EXACTLY the build-free fragment

`Handler.through`'s first argument embeds as a layer whose build is `pure`.
The embedding's functor law IS `through_assoc`; its retraction IS
`through_id_right`. Both already owned by the estate. -/

def Layer.ofHandler [Monad M] (t : Handler A (Prog B)) : Layer A B M :=
  fun h => pure (t.through h)

/-- **The embedding is a functor, and `through_assoc` is why.** -/
theorem ofHandler_provide [Monad M] [LawfulMonad M]
    (t : Handler A (Prog B)) (u : Handler B (Prog C)) :
    (Layer.ofHandler (M := M) t).provide (Layer.ofHandler u)
      = Layer.ofHandler (t.through u) := by
  funext h
  simp [Layer.provide, Layer.ofHandler, through_assoc' t u h]

/-- **The retraction, and `through_id_right` is why.** -/
theorem ofHandler_reify (t : Handler A (Prog B)) :
    Layer.ofHandler (M := Prog B) t idHandler = pure t := by
  simp [Layer.ofHandler, through_id_right']

/-- **The image of `ofHandler` is exactly the build-free layers.** -/
theorem ofHandler_build_is_pure [Monad M] (t : Handler A (Prog B)) (h : Ctx B M) :
    Layer.ofHandler t h = pure (t.through h) := rfl

/-! ## §4 — the falsifier the estate's carrier cannot pass: THE BUILD STEP -/

inductive LowE | tick
abbrev LowE.Ans : LowE → Type | .tick => Unit
def LowSig : Sig := ⟨LowE, LowE.Ans⟩

inductive HighE | use
abbrev HighE.Ans : HighE → Type | .use => Unit
def HighSig : Sig := ⟨HighE, HighE.Ans⟩

/-- The counting target: the acquisition counter is the observation. -/
abbrev Cnt := StateM Nat

def tickH : Handler LowSig Cnt := ⟨fun _ => fun n => ((), n + 1)⟩

/-- The service implemented as a program over the lower signature: it acquires
(one `tick`) before answering. This is `Handler.through`'s first argument —
the estate's Layer. -/
def acquiring : Handler HighSig (Prog LowSig) :=
  ⟨fun _ => (Prog.op LowE.tick).bind fun _ => .pure ()⟩

def twoUses : Prog HighSig Unit :=
  (Prog.op HighE.use).bind fun _ => Prog.op HighE.use

/-- **`through` pays per USE.** Two uses, two acquisitions. -/
theorem through_pays_twice :
    (interpret (acquiring.through tickH) twoUses 0).2 = 2 := rfl

/-- The same service as a LAYER: acquire once, in the build; hand back a
handler that answers without acquiring. -/
def acquiringLayer : Layer HighSig LowSig Cnt :=
  fun h => h.handle LowE.tick >>= fun _ => pure ⟨fun _ => pure ()⟩

/-- **The layer pays per BUILD.** Two uses, one acquisition. -/
theorem layer_pays_once :
    (Layer.launch acquiringLayer tickH twoUses 0).2 = 1 := rfl

/-- The two are observably different at the same target on the same program. -/
theorem build_step_is_observable :
    (interpret (acquiring.through tickH) twoUses 0).2
      ≠ (Layer.launch acquiringLayer tickH twoUses 0).2 := by
  rw [through_pays_twice, layer_pays_once]; decide

/-- **`acquiringLayer` is outside the image of `ofHandler`**: its build is not
`pure`. So `Layer` is a strictly larger type than the estate's carrier, and the
build step is what it is larger by. -/
theorem acquiringLayer_build_is_not_pure (k : Ctx HighSig Cnt) :
    acquiringLayer tickH 0 ≠ (pure k : Cnt (Ctx HighSig Cnt)) 0 := by
  intro hk
  have h1 : (1 : Nat) = 0 := congrArg Prod.snd hk
  exact absurd h1 (by decide)

/-! ## §5 — merge double-builds, so memoization is a LAW, not an optimization -/

def costly : Layer HighSig LowSig Cnt :=
  fun _ => fun n => (⟨fun _ => pure ()⟩, n + 1)

def svc : Handler HighSig Cnt := ⟨fun _ => pure ()⟩

/-- Merging a layer with itself builds it twice. -/
theorem merge_double_builds : ((Layer.merge costly costly) tickH 0).2 = 2 := rfl

/-- The memoized build of the same composite. -/
def mergedOnce : Layer (HighSig ⊕ₛ HighSig) LowSig Cnt :=
  fun _ => fun n => (svc.sum svc, n + 1)

theorem memo_builds_once : (mergedOnce tickH 0).2 = 1 := rfl

/-- **The memoization law is NOT vacuous once there is a build step.** The two
composites deliver the same service and are separated by the build counter. -/
theorem memo_is_observable :
    ((Layer.merge costly costly) tickH 0).1.handle (Sum.inl HighE.use)
        = (mergedOnce tickH 0).1.handle (Sum.inl HighE.use)
      ∧ ((Layer.merge costly costly) tickH 0).2 ≠ (mergedOnce tickH 0).2 :=
  ⟨rfl, by decide⟩

/-! ### And merge is NOT commutative in the build

`Handler.sum_unique` pins the SERVICE half of merge and says nothing about the
build half. A "merge is a commutative monoid" row is refuted at this carrier.
rc.112's `"parallel"` scope on `Layer.mergeAll` is exactly this hazard. -/

def bumpBy (k : Nat) : Layer HighSig LowSig Cnt :=
  fun _ => fun n => (⟨fun _ => pure ()⟩, n * 2 + k)

/-- **`Handler.sum_unique` (`Cas/Backend/SumAlgebra.lean:212`) pins the SERVICE
half of merge and cannot reach the BUILD half.** The two orders deliver the
identical merged handler — so `sum_unique`'s premises hold of both — and are
still separated by the build counter. Merge is therefore not commutative, and
its universal property is owed a second, build-level statement that the estate
does not have. -/
theorem sum_unique_does_not_reach_the_build :
    ((Layer.merge (bumpBy 1) (bumpBy 0)) tickH 1).1
        = ((Layer.merge (bumpBy 0) (bumpBy 1)) tickH 1).1
      ∧ ((Layer.merge (bumpBy 1) (bumpBy 0)) tickH 1).2
        ≠ ((Layer.merge (bumpBy 0) (bumpBy 1)) tickH 1).2 :=
  ⟨rfl, by decide⟩

theorem merge_is_not_commutative_in_the_build :
    ((Layer.merge (bumpBy 1) (bumpBy 0)) tickH 1).2
      ≠ ((Layer.merge (bumpBy 0) (bumpBy 1)) tickH 1).2 := by decide

/-! ## §6 — scope: the R18 target, reached WITHOUT changing the carrier

`Tgt E σ` IS `ExceptT E (StateM σ)` — state OUTSIDE error, the order R18 forces
(`EnsuringRepair.lean:361`, `RefW := ExceptT Refusal (StateM Word)`). -/

abbrev Tgt (E σ : Type) := ExceptT E (StateM σ)

/-- `ensuring` at this target: the finalizer runs on BOTH paths, at the state
the body left; on the failing path the body's error is what is reported.
Shape from `EnsuringRepair.ensuringT` (`:547`). -/
def ens {E σ α : Type} (body : Tgt E σ α) (fin : Tgt E σ Unit) : Tgt E σ α :=
  fun s =>
    match body s with
    | (.ok a, s₁) =>
      match fin s₁ with
      | (.ok _, s₂) => (.ok a, s₂)
      | (.error e, s₂) => (.error e, s₂)
    | (.error e, s₁) => (.error e, (fin s₁).2)

/-- **Law 1 — the finalizer runs on failure, no premise on it, state survives.**
The law `Except.error` with no state slot cannot have (`EC1-CE045`). -/
theorem ens_runs_on_failure {E σ α : Type} (body : Tgt E σ α) (fin : Tgt E σ Unit)
    (s s₁ : σ) (e : E) (hb : body s = (.error e, s₁)) :
    ens body fin s = (.error e, (fin s₁).2) := by
  simp [ens, hb]

/-- **Law 2 — the finalizer never replaces the failure.** -/
theorem ens_never_replaces {E σ α : Type} (body : Tgt E σ α) (fin : Tgt E σ Unit)
    (s s₁ : σ) (e : E) (hb : body s = (.error e, s₁)) :
    (ens body fin s).1 = .error e := by
  simp [ens, hb]

/-- **Law 3 — the finalizer runs on success, after the body.** -/
theorem ens_runs_on_success {E σ α : Type} (body : Tgt E σ α) (fin : Tgt E σ Unit)
    (s s₁ s₂ : σ) (a : α) (hb : body s = (.ok a, s₁))
    (hf : fin s₁ = (.ok (), s₂)) :
    ens body fin s = (.ok a, s₂) := by
  simp [ens, hb, hf]

/-- **Law 4 — LIFO, structurally.** A nested `ensuring` runs inner before
outer on the failing path, and the outer finalizer sees the state the inner one
left. `ens` is a term former, not a registry, so the order is syntactic. -/
theorem ens_LIFO {E σ α : Type} (body : Tgt E σ α) (fi fo : Tgt E σ Unit)
    (s s₁ : σ) (e : E) (hb : body s = (.error e, s₁)) :
    ens (ens body fi) fo s = (.error e, (fo (fi s₁).2).2) := by
  simp [ens, hb]

def failBody : Tgt String Nat Unit := fun s => (.error "boom", s)
def finA : Tgt String Nat Unit := fun s => (.ok (), s + 1)
def finB : Tgt String Nat Unit := fun s => (.ok (), s + 2)

/-- **Non-vacuity.** Two finalizers leaving different states are SEPARATED on a
failing body — the pair `reraise_is_finalizer_blind` proves the word-forgetting
target identifies. -/
theorem ens_separates_finalizers :
    (ens failBody finA 0).2 ≠ (ens failBody finB 0).2 := by decide

/-! ### The scoped layer sits in the MIDDLE of a tower

`Handler.through`'s middle must be `Prog T`-valued, so the estate's carrier has
a floor at the scoped layer (R18's closing paragraph). `Layer` has no `Prog` in
it, so the scoped layer is an ordinary layer and composes by `provide`.
`ScopeSig` is the R18-ruled signature: children are first-order ids. -/

inductive ScopeE | ensuring (body fin : Nat)
abbrev ScopeE.Ans : ScopeE → Type | .ensuring _ _ => Unit
def ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩

abbrev T2 := Tgt String Nat

/-- A block table: first-order ids to computations at the lower signature. -/
def blocks (_h : Ctx LowSig T2) : Nat → T2 Unit
  | 0 => failBody
  | 1 => fun s => (.ok (), s + 1)
  | _ => fun s => (.ok (), s)

/-- **The scoped layer.** It requires `LowSig`, provides `ScopeSig`, and is a
`Layer` — not a `Handler _ (Prog _)`, which `EC1-CE041` proves it cannot be. -/
def scopeLayer : Layer ScopeSig LowSig T2 :=
  fun h => pure ⟨fun | .ensuring b f => ens (blocks h b) (blocks h f)⟩

def lowLayer : Layer LowSig LowSig T2 := Layer.empty

/-- The scoped layer in the MIDDLE of a composite. -/
def tower : Layer ScopeSig LowSig T2 := scopeLayer.provide lowLayer

def ctx0 : Ctx LowSig T2 := ⟨fun _ => fun s => (.ok (), s)⟩

def builtScope : Except String (Ctx ScopeSig T2) × Nat := tower ctx0 0

theorem tower_builds_without_failing : builtScope.1.isOk = true := rfl

/-- Through the built tower, a failing body still runs its finalizer and the
state survives. The floor is lifted; the R18 law holds at the composite. -/
theorem tower_finalises_on_failure :
    (match builtScope.1 with
      | .ok hs => hs.handle (.ensuring 0 1) 0
      | .error _ => (.ok (), 99)) = (.error "boom", 1) := rfl

/-! ## §7 — what does NOT hold

`ofHandler` is a section of evaluation-at-`idHandler` (`ofHandler_reify`), so
the estate's carrier embeds faithfully; `ofHandler_build_is_pure` +
`acquiringLayer_build_is_not_pure` show the embedding is NOT surjective. The
type is deliberately larger. Nothing constrains a `Layer` to be natural in `M`,
and no Lean-internal parametricity can supply that — the constraint has to come
from the content side (`Cas.Schema.SystemNode`), not from the type. -/

#print axioms through_assoc'
#print axioms ofHandler_provide
#print axioms ofHandler_reify
#print axioms provide_assoc
#print axioms provide_empty_left
#print axioms provide_empty_right
#print axioms through_pays_twice
#print axioms layer_pays_once
#print axioms build_step_is_observable
#print axioms acquiringLayer_build_is_not_pure
#print axioms merge_double_builds
#print axioms memo_is_observable
#print axioms merge_is_not_commutative_in_the_build
#print axioms sum_unique_does_not_reach_the_build
#print axioms ens_runs_on_failure
#print axioms ens_never_replaces
#print axioms ens_LIFO
#print axioms ens_runs_on_success
#print axioms ens_separates_finalizers
#print axioms tower_finalises_on_failure

end ProposeC
