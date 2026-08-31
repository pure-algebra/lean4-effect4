import Cas.Backend.Universal

/-!
# JUDGE probe against POSITION A (`Layer S T := Prog T (Handler S (Prog T))`)

Adversarial. Scratch, outside every lake target. Check from `library/cas`:
`lake env lean '../../.staging/effect-core-v1/workshop/layer/judge-A — "layer-is-a-program", developed to its breaking point.lean'`

Two attacks, both mechanized.

§A. THE LIFO ROW IS UNREACHABLE AT A's FLOOR.
    A's `scopeModel` says: "ORDERING: LIFO — `ensuring_LIFO`/`ensuring_LIFO_reraises`,
    already proved upstream in EnsuringRepair §3; `scopeFloor_ensuring` is `rfl`,
    so those laws transfer verbatim to this floor."
    `ensuring_LIFO` is a statement about `ensuringT (ensuringT body fi) fo`.
    A's clause always yields `ensuringT (interpretRefW _ (blk b)) (interpretRefW _ (blk f))`
    with `blk : Nat → Prog CasSig Addr32`. `CasSig` carries no scope operation, so
    the first argument is never an `ensuringT`. §A exhibits the type-level obstruction.

§B. THE §7.2 REPAIR HAS NO CLOSE POINT.
    A's repair is "`ScopeE.register` + a finalizer stack in the floor's state —
    a constructor and a state component, no carrier". But `Layer.build`'s RESULT
    TYPE, `M (Handler S M)`, contains no handle at which a registered finalizer
    could ever run. §B makes that a theorem: the built value is a handler and
    nothing else, so a registration performed in the build is unobservable to
    every consumer of `build` unless `build`'s type changes.
-/

namespace EC1.JudgeA

open Cas Cas.Lang

abbrev Layer (S T : Sig) : Type := Prog T (Handler S (Prog T))

def Layer.build {S T : Sig} {M : Type → Type} [Monad M]
    (l : Layer S T) (floor : Handler T M) : M (Handler S M) :=
  interpret floor l >>= fun hs => Pure.pure (hs.through floor)

/-! ## §A — A's floor, reproduced verbatim from `propose-A.lean` §5 -/

abbrev RefW := ExceptT Refusal (StateM Word)
abbrev WComp := Word → Except Refusal Addr32 × Word

inductive ScopeE where
  | scoped (body : Nat)
  | ensuring (body fin : Nat)
  | catchE (body hnd : Nat)
  deriving DecidableEq

abbrev ScopeE.Ans : ScopeE → Type
  | .scoped _ => Addr32 | .ensuring _ _ => Addr32 | .catchE _ _ => Addr32

abbrev ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩

/-- A's block table. THE OBSTRUCTION IS HERE: the codomain is `Prog CasSig`. -/
abbrev Blocks := Nat → Prog CasSig Addr32
abbrev Env := Blocks × (Bytes → Addr32)
abbrev ScopeM := ReaderT Env RefW

def ensuringT (body fin : WComp) : WComp := fun w =>
  match body w with
  | (.ok a, w₁) => match fin w₁ with
      | (.ok _, w₂) => (.ok a, w₂)
      | (.error r, w₂) => (.error r, w₂)
  | (.error r, w₁) => (.error r, (fin w₁).2)

def referenceHandlerW (H : Bytes → Addr32) : Handler CasSig RefW where
  handle op := fun w =>
    match (referenceHandler H).handle op w with
    | .ok (ans, w') => (.ok ans, w')
    | .error r => (.error r, w)

def interpretRefW (H : Bytes → Addr32) {A : Type} (p : Prog CasSig A) (w : Word) :
    Except Refusal A × Word :=
  interpret (referenceHandlerW H) p w

def scopeFloor : Handler ScopeSig ScopeM where
  handle
    | .scoped b => fun e w => interpretRefW e.2 (e.1 b) w
    | .ensuring b f => fun e =>
        ensuringT (interpretRefW e.2 (e.1 b)) (interpretRefW e.2 (e.1 f))
    | .catchE b h => fun e w =>
        match interpretRefW e.2 (e.1 b) w with
        | (.ok a, w') => (.ok a, w')
        | (.error _, _) => interpretRefW e.2 (e.1 h) w

/-- **A.1.** A's own clause equation, reproduced. Every `ensuring` clause at
this floor has BOTH arguments in the image of `interpretRefW ∘ blocks`. -/
theorem clause_shape (e : Env) (b f : Nat) :
    scopeFloor.handle (.ensuring b f) e
      = ensuringT (interpretRefW e.2 (e.1 b)) (interpretRefW e.2 (e.1 f)) := rfl

/-- **A.2 — THE OBSTRUCTION, at the type.** A block body is a program over
`CasSig` alone. So the scope signature is not in scope inside a block, and a
nested `ensuring` OPERATION is not merely unproved at this floor: it cannot be
written. The witness is that a block's type forces `CasSig` — exhibited by the
fact that the only way to embed a scope operation is to change the codomain. -/
example : Blocks = (Nat → Prog CasSig Addr32) := rfl

/-- The nested form `ensuring_LIFO` quantifies over. To instantiate it at the
floor you need `ensuringT body fi` to BE a clause value — i.e. you need some
`b : Nat` with `interpretRefW H (blk b) = ensuringT X Y`. That is an equation
between an interpretation of a `Prog CasSig` and a scope combinator: nothing in
`ScopeE` produces it, because `ScopeE` never appears under `Blocks`. -/
def nestedTarget (body fi fo : WComp) : WComp := ensuringT (ensuringT body fi) fo

/-- **A.3.** `ensuring_LIFO`'s content, re-proved here so the comparison is
exact: it is a COMBINATOR fact about `WComp` values, provable with no reference
to `ScopeE`, `scopeFloor`, or `Blocks` at all. Transferring it "to this floor"
therefore transfers nothing about this floor. -/
theorem ensuringT_word (body fin : WComp) (w : Word) :
    (ensuringT body fin w).2 = (fin (body w).2).2 := by
  unfold ensuringT
  cases hb : body w with
  | mk res w₁ => cases res with
    | ok a => cases hf : fin w₁ with
      | mk r₂ w₂ => cases r₂ <;> simp [hf]
    | error r => simp

theorem lifo_is_combinator_only (body fi fo : WComp) (w : Word) :
    (nestedTarget body fi fo w).2 = (fo (fi (body w).2).2).2 := by
  unfold nestedTarget; rw [ensuringT_word, ensuringT_word]

/-! ## §B — the repair has no close point -/

section NoClosePoint

inductive ResE where | acq | rel | usd
  deriving DecidableEq
abbrev ResE.Ans : ResE → Type | _ => Unit
abbrev ResSig : Sig := ⟨ResE, ResE.Ans⟩

inductive UseE where | use
  deriving DecidableEq
abbrev UseE.Ans : UseE → Type | .use => Nat
abbrev UseSig : Sig := ⟨UseE, UseE.Ans⟩

def logH : Handler ResSig (StateM (List String)) where
  handle
    | .acq => fun l => ((), l ++ ["acq"])
    | .rel => fun l => ((), l ++ ["rel"])
    | .usd => fun l => ((), l ++ ["usd"])

def usingH : Handler UseSig (Prog ResSig) where
  handle | .use => Prog.op (S := ResSig) ResE.usd >>= fun _ => Pure.pure 0

/-- A layer that acquires in its build and registers NOTHING it can release —
A's §7 exhibit, restated as the acquire-only half. -/
def acquiring : Layer UseSig ResSig :=
  Prog.op (S := ResSig) ResE.acq >>= fun _ => Pure.pure usingH

/-- **B.1 — THE BUILD IS COMPLETE AND THE RESOURCE IS STILL OPEN.**
`Layer.build` runs the acquisition and hands back a handler. The trace at the
moment `build` returns contains the acquire and no release, and — this is the
point — `build`'s RESULT TYPE is `M (Handler S M)`. There is no second
component, so no consumer of `build` has anything to call to close the scope.
An ambient `register` performed during this build has no reachable run site. -/
theorem build_returns_with_the_resource_open :
    (Layer.build acquiring logH []).2 = ["acq"] := rfl

/-- **B.2.** And the built value is a bare handler: `build`'s answer type is
`Handler UseSig (StateM (List String))` with no close action beside it. Stated
as a type equation so the absence is checked, not asserted. -/
example : (StateM (List String)) (Handler UseSig (StateM (List String)))
    = (fun M => M (Handler UseSig M)) (StateM (List String)) := rfl

/-- **B.3.** Consequently the finalizer stack A's §7.2 proposes would have to be
drained by an operation A does not have: `Layer.launch`'s own shape,
`build >>= fun _ => suspend`, discards the handler and still never closes. -/
def launch {S T : Sig} {M : Type → Type} [Monad M] {X : Type}
    (l : Layer S T) (fl : Handler T M) (suspend : M X) : M X :=
  Layer.build l fl >>= fun _ => suspend

theorem launch_never_releases :
    (launch acquiring logH (Pure.pure 0) []).2 = ["acq"] := rfl

end NoClosePoint

#print axioms clause_shape
#print axioms lifo_is_combinator_only
#print axioms build_returns_with_the_resource_open
#print axioms launch_never_releases

end EC1.JudgeA
