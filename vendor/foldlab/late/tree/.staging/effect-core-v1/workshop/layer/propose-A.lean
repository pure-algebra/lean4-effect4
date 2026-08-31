import Cas.Backend.Universal

/-!
# Effect Core v1 — design pass, POSITION A: "a layer is a program"

Scratch. Outside every lake target. Adds nothing to `Cas`, moves no bytes,
touches no ledger. Check from `library/cas`:

```
lake env lean ../../.staging/effect-core-v1/workshop/layer/propose-A.lean
```

## The claim

There is no `Layer` type. A layer is

    Layer S T  :=  Prog T (Handler S (Prog T))

— a PROGRAM over the lower signature `T` whose VALUE is the handler for the
higher signature `S`. This is rc.112's `build(memoMap, scope) : Effect<Context<ROut>, E, RIn>`
with the two substitutions the ground work already proved: a `Context` IS a
handler (requirements-environment collapse), and `Effect<_, _, RIn>` IS
`Prog RIn`. `Prog` and `Handler` already exist; `Layer` is their application
at a handler-valued answer type, not a new inductive.

Distinguish this from the weaker reading `Handler S (Prog T)` (the bare type
of `Handler.through`'s first argument). That reading has NO BUILD STEP: it
inlines acquisition into every operation. The `Prog T (·)` prefix IS the
build step, and §4 shows the difference is observable, not cosmetic.

## Receipts

`lake env lean` exit 0, no errors, no warnings. 20 `#print axioms` lines at the
foot: 9 axiom-free, the rest `[propext]` / `[Quot.sound]` / `[propext, Quot.sound]`.
No `sorry`, no `sorryAx`, no `Classical.choice`, no `native_decide`, no `axiom`.

§7 is a SELF-REFUTATION exhibit, kernel-checked: it proves this design cannot
give a layer ownership of a finalizer that outlives its own build.
-/

namespace EC1.ProposeA

open Cas Cas.Lang

/-! ## §1 — the carrier and the four operations -/

/-- **THE CARRIER.** No new inductive. `abbrev`, so it is definitionally
transparent: `Layer S T` and `Prog T (Handler S (Prog T))` are the same type,
with the same eliminator, the same equality, and the same `LawfulMonad`. -/
abbrev Layer (S T : Sig) : Type := Prog T (Handler S (Prog T))

/-- `Prog`'s bind, spelled so `interpret_bind` matches syntactically. -/
theorem progBind {S : Sig} {A B : Type} (p : Prog S A) (f : A → Prog S B) :
    (p >>= f) = p.bind f := rfl

/-- `interpret_bind` at the `>>=` spelling. -/
theorem interpret_bind' {S : Sig} {M : Type → Type} [Monad M] [LawfulMonad M]
    {A B : Type} (h : Handler S M) (p : Prog S A) (f : A → Prog S B) :
    interpret h (p >>= f) = interpret h p >>= fun a => interpret h (f a) :=
  interpret_bind h p f

/-- `interpret` on a finished program, at the `Pure.pure` spelling. -/
theorem interpret_pure' {S : Sig} {M : Type → Type} [Monad M] {A : Type}
    (h : Handler S M) (a : A) : interpret h (Pure.pure a) = Pure.pure a := rfl

/-- A layer that acquires nothing: the handler is already in hand. This is
`Layer.succeed` / `Layer.effectContext` at a value, and it is `pure`. -/
def Layer.of {S T : Sig} (h : Handler S (Prog T)) : Layer S T := Pure.pure h

/-- `Layer.empty` — the identity of composition. It is `pure idHandler`. -/
def Layer.empty (S : Sig) : Layer S S := Pure.pure (idHandler (S := S))

/-- **`provide`.** Build the inner layer, interpret the outer layer's BUILD
through the inner handler, then compose the two handlers with `Handler.through`.
Every ingredient is an estate operation: `bind`, `interpret`, `through`. -/
def Layer.provide {S T U : Sig} (inner : Layer T U) (outer : Layer S T) :
    Layer S U :=
  inner >>= fun ht => interpret ht outer >>= fun hs => Pure.pure (hs.through ht)

/-- **`merge`.** Build both, sum the handlers. `Handler.sum` is merge. -/
def Layer.merge {S T U : Sig} (a : Layer S U) (b : Layer T U) :
    Layer (S ⊕ₛ T) U :=
  a >>= fun ha => b >>= fun hb => Pure.pure (ha.sum hb)

/-- **`build`.** NOT primitive: it is `interpret` at the tower's floor,
followed by `through` to push the built handler's residual clauses down.
`M` is where the tower stops being `Prog` — §5. -/
def Layer.build {S T : Sig} {M : Type → Type} [Monad M]
    (l : Layer S T) (floor : Handler T M) : M (Handler S M) :=
  interpret floor l >>= fun hs => Pure.pure (hs.through floor)

/-- **Consuming a layer from a program** — Effect's `Effect.provide`. -/
def Layer.run {S T : Sig} {A : Type} (l : Layer S T) (p : Prog S A) : Prog T A :=
  l >>= fun h => interpret h p

/-! ## §2 — the laws, each discharged by an existing estate theorem -/

/-- `through` distributes over `sum`. Discharged by `Handler.ext`
(`Universal.lean:128`); `Handler.sum_unique` (`SumAlgebra.lean:212`) is the
categorical form of the same fact. -/
theorem through_sum {S T U : Sig} {M : Type → Type} [Monad M]
    (a : Handler S (Prog U)) (b : Handler T (Prog U)) (floor : Handler U M) :
    (a.sum b).through floor = (a.through floor).sum (b.through floor) :=
  Handler.ext fun op => by cases op <;> rfl

/-- **LAW 1 — `build_empty`.** Building the empty layer is the floor itself.
Discharged by `through_id_left` (`Universal.lean:765`). -/
theorem build_empty {S : Sig} {M : Type → Type} [Monad M] [LawfulMonad M]
    (floor : Handler S M) :
    Layer.build (Layer.empty S) floor = Pure.pure floor := by
  show (Pure.pure (idHandler (S := S)) >>= fun hs => Pure.pure (hs.through floor))
      = Pure.pure floor
  rw [pure_bind, through_id_left rightUnit_of_lawful floor]

/-- **LAW 2 — `build_provide`. THE theorem of this design.**
Building a composite layer IS building the inner one and then building the
outer one against the handler that came out. `provide` is composition of
builds — no graph, no scheduler, no memo map.

Discharged entirely by existing theorems: `interpret_bind`
(`Handler.lean:53`), `interpret_through` (`Tower.lean:71`), `through_assoc`
(`Universal.lean:739`). -/
theorem build_provide {S T U : Sig} {M : Type → Type} [Monad M] [LawfulMonad M]
    (inner : Layer T U) (outer : Layer S T) (floor : Handler U M) :
    Layer.build (Layer.provide inner outer) floor
      = Layer.build inner floor >>= fun ht => Layer.build outer ht := by
  simp only [Layer.build, Layer.provide, interpret_bind', interpret_pure', bind_assoc,
    pure_bind]
  refine bind_congr fun ht => ?_
  rw [interpret_through]
  refine bind_congr fun hs => ?_
  rw [through_assoc leftUnit_of_lawful bindAssoc_of_lawful]

/-- **LAW 3 — `build_merge`.** Building a merge is building both and summing.
Discharged by `interpret_bind` and `through_sum` (hence `Handler.ext` /
`Handler.sum_unique`). -/
theorem build_merge {S T U : Sig} {M : Type → Type} [Monad M] [LawfulMonad M]
    (a : Layer S U) (b : Layer T U) (floor : Handler U M) :
    Layer.build (Layer.merge a b) floor
      = Layer.build a floor >>= fun ha =>
          Layer.build b floor >>= fun hb => Pure.pure (ha.sum hb) := by
  simp only [Layer.build, Layer.merge, interpret_bind', interpret_pure', bind_assoc,
    pure_bind]
  refine bind_congr fun ha => ?_
  refine bind_congr fun hb => ?_
  rw [through_sum]

/-- **LAW 4 — `run_provide`.** Providing a composite to a program is providing
the pieces in order. Discharged by `interpret_bind` + `interpret_through`. -/
theorem run_provide {S T U : Sig} {A : Type}
    (inner : Layer T U) (outer : Layer S T) (p : Prog S A) :
    Layer.run (Layer.provide inner outer) p
      = Layer.run inner (Layer.run outer p) := by
  simp only [Layer.run, Layer.provide, interpret_bind', bind_assoc, pure_bind]
  refine bind_congr fun ht => ?_
  refine bind_congr fun hs => ?_
  rw [interpret_through]

/-- **LAW 5 — `run_empty`.** Discharged by `interpret_id`
(`Representation.lean:68`). -/
theorem run_empty {S : Sig} {A : Type} (p : Prog S A) :
    Layer.run (Layer.empty S) p = p := by
  show (Pure.pure (idHandler (S := S)) >>= fun h => interpret h p) = p
  rw [pure_bind, interpret_id]

/-- **LAW 6 — `provide_assoc`, ON THE NOSE.** Not merely up to observation:
the three-layer stack composes associatively as a value of the carrier.
Discharged by `interpret_bind`, `interpret_through`, `through_assoc`. -/
theorem provide_assoc {S T U V : Sig}
    (c : Layer U V) (b : Layer T U) (a : Layer S T) :
    Layer.provide (Layer.provide c b) a
      = Layer.provide c (Layer.provide b a) := by
  simp only [Layer.provide, interpret_bind', interpret_pure', bind_assoc, pure_bind]
  refine bind_congr fun hv => ?_
  refine bind_congr fun hu => ?_
  rw [interpret_through]
  refine bind_congr fun hs => ?_
  rw [through_assoc leftUnit_of_lawful bindAssoc_of_lawful]

/-- **LAW 7 — `provide_empty_left`.** Discharged by `interpret_id` +
`through_id_left`. -/
theorem provide_empty_right {S T : Sig} (l : Layer S T) :
    Layer.provide l (Layer.empty S) = l := by
  simp only [Layer.provide, Layer.empty, interpret_pure', pure_bind]
  have h : (fun ht : Handler S (Prog T) =>
        (Pure.pure ((idHandler (S := S)).through ht) : Layer S T))
      = fun ht => Pure.pure ht :=
    funext fun ht => congrArg Pure.pure (through_id_left rightUnit_of_lawful ht)
  rw [h]
  exact bind_pure l

/-- **LAW 7b — `provide_empty_left`.** The other unit. Discharged by
`interpret_id` (`Representation.lean:68`) and `through_id_right`
(`Universal.lean:757`). Together with LAW 6 and LAW 7, `provide` is a
CATEGORY on signatures with `Layer.empty` as identity — the layer-level
reading of `through_monoid`'s three facts, stated where they actually are
one (across signatures, not at a single one). -/
theorem provide_empty_left {S T : Sig} (l : Layer S T) :
    Layer.provide (Layer.empty T) l = l := by
  simp only [Layer.provide, Layer.empty, pure_bind, interpret_id]
  have h : (fun hs : Handler S (Prog T) =>
        (Pure.pure (hs.through (idHandler (S := T))) : Layer S T))
      = fun hs => Pure.pure hs :=
    funext fun hs => congrArg Pure.pure (through_id_right hs)
  rw [h]
  exact bind_pure l

/-! ## §3 — memoization is `bind`; `fresh` is the absence of a binder

rc.112 needs a `MemoMap` keyed on JS reference identity because its `Layer`
is a graph of closures with no binding structure. A layer that IS a program
gets sharing from the monad: to share a build, BIND it once and pass the
handler. There is no memo key, so nothing has to be hashed, and `fresh(l)`
does not collapse to `l` under content addressing — `fresh` is simply what
you get when you do not bind.

`Layer.shared` below is `Prog.bind`, renamed. It is not a new operation. -/

/-- Sharing, spelled. Definitionally `>>=`. -/
def Layer.shared {S T U : Sig} (c : Layer U T) (k : Handler U (Prog T) → Layer S T) :
    Layer S T := c >>= k

theorem shared_is_bind {S T U : Sig} (c : Layer U T)
    (k : Handler U (Prog T) → Layer S T) : Layer.shared c k = c >>= k := rfl

/-! ### `unwrap`, `flatMap`, `suspend` — free, because a layer is a monad

`REIFICATION` C6 refutes a node/edge representation of the layer graph:
rc.112's `flatMap` (`Layer.ts:3038`), `unwrap` (`:1580` — which stores a
`Layer` INSIDE a `Context`) and `suspend` compute successors from runtime
values, so there are no static edges to reify. That objection does not reach
this design: the carrier is already the free monad, so `flatMap` is `>>=`,
`unwrap` is `join`, and `suspend` is `pure ∘ (·)` under a `vis`. Nothing to
add. -/

/-- `Layer.unwrap` — a layer computed by a program. It is `join`. -/
def Layer.unwrap {S T : Sig} (m : Prog T (Layer S T)) : Layer S T := m >>= id

theorem unwrap_is_join {S T : Sig} (m : Prog T (Layer S T)) :
    Layer.unwrap m = m >>= id := rfl

/-! ### Restriction — how a consumer of one service uses a merged layer

`Handler` is CONTRAVARIANT in its signature: a handler for more operations
restricts to a handler for fewer. That is the estate's counterpart of
rc.112's `interface Layer<in ROut, …>` (`Layer.ts:98`), and it is what makes
`merge` a PRODUCT rather than an opaque bundle. -/

/-- Restrict a summed handler to its left summand. -/
def restrictL {S T : Sig} {M : Type → Type} (h : Handler (S ⊕ₛ T) M) :
    Handler S M := ⟨fun op => h.handle (Sum.inl op)⟩

/-- Restrict a summed handler to its right summand. -/
def restrictR {S T : Sig} {M : Type → Type} (h : Handler (S ⊕ₛ T) M) :
    Handler T M := ⟨fun op => h.handle (Sum.inr op)⟩

/-- **LAW 8 — `merge` is a product.** Its projections recover the parts.
Discharged by `Handler.ext`; `Handler.sum_unique` (`SumAlgebra.lean:212`) is
the matching universal property in the other direction. -/
theorem merge_projections {S T : Sig} {M : Type → Type}
    (a : Handler S M) (b : Handler T M) :
    restrictL (a.sum b) = a ∧ restrictR (a.sum b) = b :=
  ⟨Handler.ext fun _ => rfl, Handler.ext fun _ => rfl⟩

/-! ## §4 — the build step is observable, and so is the absence of sharing

The exhibit that separates `Prog T (Handler S (Prog T))` from the weaker
`Handler S (Prog T)`, and separates a shared diamond from an unshared one.
A one-operation lower signature, counted in the target's state. -/

section Exhibit

inductive TickE where | tick
  deriving DecidableEq

abbrev TickE.Ans : TickE → Type | .tick => Unit

abbrev TickSig : Sig := ⟨TickE, TickE.Ans⟩

inductive UseE where | use
  deriving DecidableEq

abbrev UseE.Ans : UseE → Type | .use => Nat

abbrev UseSig : Sig := ⟨UseE, UseE.Ans⟩

/-- The floor: count the acquisitions. -/
def counter : Handler TickSig (StateM Nat) where
  handle | .tick => fun n => ((), n + 1)

/-- A layer whose BUILD performs one acquisition and then answers `use`
without further effect. The acquisition is in the `Prog` prefix — this is
the build step, and it is exactly what `Handler S (Prog T)` cannot express. -/
def acquiring : Layer UseSig TickSig :=
  Prog.op (S := TickSig) TickE.tick >>= fun _ =>
    Pure.pure { handle := fun _ => Pure.pure 0 }

/-- The same service written WITHOUT a build step: acquisition inlined into
the clause. This is the `Handler S (Prog T)` reading of position A. -/
def inlined : Handler UseSig (Prog TickSig) where
  handle | .use => Prog.op (S := TickSig) TickE.tick >>= fun _ => Pure.pure 0

/-- A consumer that uses the service twice. -/
def consumer : Prog UseSig Nat :=
  Prog.op (S := UseSig) UseE.use >>= fun a =>
    Prog.op (S := UseSig) UseE.use >>= fun b => Pure.pure (a + b)

/-- **The build step is real.** With a build, two uses cost ONE acquisition. -/
theorem build_acquires_once :
    (interpret counter (Layer.run acquiring consumer) 0).2 = 1 := rfl

/-- Without a build, two uses cost TWO. `Handler S (Prog T)` is not a layer:
`Handler.through` is layer composition WITH THE BUILD ERASED. -/
theorem inlined_acquires_per_use :
    (interpret counter (interpret inlined consumer) 0).2 = 2 := rfl

theorem build_step_is_observable :
    (interpret counter (Layer.run acquiring consumer) 0).2
      ≠ (interpret counter (interpret inlined consumer) 0).2 := by decide

/-- A trivial upper layer, so a diamond can be drawn. -/
def upper : Layer UseSig UseSig := Layer.empty UseSig

/-- The diamond, UNSHARED: the same acquiring layer named twice. -/
def diamondFresh : Layer (UseSig ⊕ₛ UseSig) TickSig :=
  Layer.merge (Layer.provide acquiring upper) (Layer.provide acquiring upper)

/-- The diamond, SHARED: the acquisition bound once, the handler passed to
both arms. This is `Layer.provideMerge`, and it is `>>=`. -/
def diamondShared : Layer (UseSig ⊕ₛ UseSig) TickSig :=
  Layer.shared acquiring fun hc =>
    Layer.merge (Layer.provide (Layer.of hc) upper)
      (Layer.provide (Layer.of hc) upper)

theorem fresh_acquires_twice :
    (Layer.build diamondFresh counter 0).2 = 2 := rfl

theorem shared_acquires_once :
    (Layer.build diamondShared counter 0).2 = 1 := rfl

/-- **Sharing is a semantic difference, and `bind` is what expresses it.**
No memo map, no reference identity, no content key. -/
theorem sharing_is_observable :
    (Layer.build diamondFresh counter 0).2
      ≠ (Layer.build diamondShared counter 0).2 := by decide

end Exhibit

/-! ## §5 — Scope: a SIGNATURE summand, and the tower's floor

R18 forced `ExceptT Refusal (StateM Word)` for finalization, and observed
that `Handler.through`'s middle must be `Prog T`-valued, so the tower has a
floor at the scoped layer. This design's answer:

**Scope is not a field of `Layer` and not a carrier. It is a signature.**
A scoped layer is a layer over `T ⊕ₛ ScopeSig`. Its clauses stay
`Prog (T ⊕ₛ ScopeSig)`-valued — so `Handler.through` composes them, and every
law of §2 applies unchanged. `ensuring` is an OPERATION, not a combinator on
the carrier. The tower leaves `Prog` exactly once, at `Layer.build`'s floor
handler, which is the sum of the lower handler and the scope handler, landing
in the R18-adequate target.

The two things that must be checked, and are, below:
1. the R18-adequate target is a `LawfulMonad`, so §2's laws reach the floor;
2. an `ensuring` clause lives in it and observes failure. -/

section Scope

/-- R18's forced target: state OUTSIDE error, so the word survives the
error branch (`EnsuringRepair.lean:361`). -/
abbrev RefW := ExceptT Refusal (StateM Word)

/-- Scope operations, children as first-order block addresses — R18 clause 1,
defunctionalization by address. No `HHandler`, no higher-order carrier. -/
inductive ScopeE where
  | scoped (body : Nat)
  | ensuring (body fin : Nat)
  | catchE (body hnd : Nat)
  deriving DecidableEq

abbrev ScopeE.Ans : ScopeE → Type
  | .scoped _ => Addr32
  | .ensuring _ _ => Addr32
  | .catchE _ _ => Addr32

abbrev ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩

/-- The environment the floor reads: the block table and the address
function. NOTE, stated not hidden: the SHIPPED table must be first-order
(`GProg`-shaped, per R7); `Blocks` here is a denotational stand-in, adequate
for the typecheck below and NOT a proposal for the stored form. -/
abbrev Blocks := Nat → Prog CasSig Addr32

abbrev Env := Blocks × (Bytes → Addr32)

/-- The scoped target. -/
abbrev ScopeM := ReaderT Env RefW

/-- **Check 1.** The R18-adequate target is a lawful monad, so every law in
§2 instantiates at the scoped floor. Nothing about `Layer` degrades there. -/
example : LawfulMonad RefW := inferInstance
example : LawfulMonad ScopeM := inferInstance

/-- A computation in the word-carrying target. -/
abbrev WComp := Word → Except Refusal Addr32 × Word

/-- `ensuring` on the target's values (`EnsuringRepair.lean:547`, copied):
the finalizer runs on BOTH paths, and the body's refusal is re-raised
unchanged. -/
def ensuringT (body fin : WComp) : WComp := fun w =>
  match body w with
  | (.ok a, w₁) =>
    match fin w₁ with
    | (.ok _, w₂) => (.ok a, w₂)
    | (.error r, w₂) => (.error r, w₂)
  | (.error r, w₁) => (.error r, (fin w₁).2)

/-- The word-carrying reference handler (`EnsuringRepair.lean:367`). -/
def referenceHandlerW (H : Bytes → Addr32) : Handler CasSig RefW where
  handle op := fun w =>
    match (referenceHandler H).handle op w with
    | .ok (ans, w') => (.ok ans, w')
    | .error r => (.error r, w)

def interpretRefW (H : Bytes → Addr32) {A : Type} (p : Prog CasSig A) (w : Word) :
    Except Refusal A × Word :=
  interpret (referenceHandlerW H) p w

/-- The scope half of the floor. An ORDINARY `Handler`; children are `Nat`
block addresses; the clause is `ensuringT`. -/
def scopeFloor : Handler ScopeSig ScopeM where
  handle
    | .scoped b => fun e w => interpretRefW e.2 (e.1 b) w
    | .ensuring b f => fun e =>
        ensuringT (interpretRefW e.2 (e.1 b)) (interpretRefW e.2 (e.1 f))
    | .catchE b h => fun e w =>
        match interpretRefW e.2 (e.1 b) w with
        | (.ok a, w') => (.ok a, w')
        | (.error _, _) => interpretRefW e.2 (e.1 h) w

/-- The CAS half, lifted into the reader — the address function comes from
the environment, so the floor is one handler, not two runtimes. -/
def casFloor : Handler CasSig ScopeM where
  handle op := fun e => (referenceHandlerW e.2).handle op

/-- **THE FLOOR.** `Handler.sum` — the same merge that composes layers
composes the floor. This is the ONLY place the tower leaves `Prog`. -/
def floor : Handler (CasSig ⊕ₛ ScopeSig) ScopeM := casFloor.sum scopeFloor

/-- **Check 2.** A scoped layer is a layer over the summed signature, and
`Layer.build` applies at the floor with no change. -/
example {S : Sig} (l : Layer S (CasSig ⊕ₛ ScopeSig)) :
    ScopeM (Handler S ScopeM) := Layer.build l floor

/-- **Check 3.** §2's central law instantiates at the scoped floor. -/
example {S T : Sig} (inner : Layer T (CasSig ⊕ₛ ScopeSig)) (outer : Layer S T) :
    Layer.build (Layer.provide inner outer) floor
      = Layer.build inner floor >>= fun ht => Layer.build outer ht :=
  build_provide inner outer floor

/-! ### The finalization laws, at the clause -/

theorem ensuringT_ok (body fin : WComp) (w w₁ w₂ : Word) (a v : Addr32)
    (hb : body w = (.ok a, w₁)) (hf : fin w₁ = (.ok v, w₂)) :
    ensuringT body fin w = (.ok a, w₂) := by
  simp only [ensuringT, hb, hf]

theorem ensuringT_error (body fin : WComp) (w w₁ w₂ : Word) (r : Refusal)
    (hb : body w = (.error r, w₁)) (hf : (fin w₁).2 = w₂) :
    ensuringT body fin w = (.error r, w₂) := by
  simp only [ensuringT, hb, hf]

/-- **The clause IS the combinator**, by `rfl` — so the four `ensuring` laws
of `EnsuringRepair.lean` §3 transfer to this floor verbatim. -/
theorem scopeFloor_ensuring (e : Env) (b f : Nat) :
    scopeFloor.handle (.ensuring b f) e
      = ensuringT (interpretRefW e.2 (e.1 b)) (interpretRefW e.2 (e.1 f)) := rfl

/-- Failure is observed: the finalizer's word survives the body's refusal.
This is the R18 obligation, discharged at the layer floor. -/
theorem finalizer_observes_failure (e : Env) (b f : Nat) (w w₁ : Word)
    (r : Refusal) (hb : interpretRefW e.2 (e.1 b) w = (.error r, w₁)) :
    scopeFloor.handle (.ensuring b f) e w
      = (.error r, (interpretRefW e.2 (e.1 f) w₁).2) := by
  rw [scopeFloor_ensuring]
  exact ensuringT_error _ _ w w₁ _ r hb rfl

end Scope

/-! ## §7 — WHERE THIS DESIGN BREAKS, kernel-checked

The honest limit of position A, stated as an exhibit rather than a caveat.

A layer's whole purpose is to acquire something and release THAT thing. In
this carrier the only sequencing available is `bind`, and a `bind`'s
continuation is INSIDE the program — so a release written into the build runs
before the built handler is ever handed out. The correctly-scoped expression
exists, but its TYPE is a run over the lower signature, not a `Layer`:
lexical scope moves ownership from the layer to the consumer.

This is exactly rc.112's `MemoMapEntry.observers` / `layerScope` (`Layer.ts:236,390–419`)
being unrepresentable here, and it is the one place where "there is no `Layer`
type" costs something real. §7.2 names the repair: an ambient-registration
operation, which is a `ScopeSig` CONSTRUCTOR and a floor-state component — not
a carrier. -/

section Lifetime

inductive ResE where | acq | rel | usd
  deriving DecidableEq

abbrev ResE.Ans : ResE → Type | _ => Unit

abbrev ResSig : Sig := ⟨ResE, ResE.Ans⟩

/-- The floor, logging the acquisition trace — the observation a memoization
or finalization law has to be stated at, since the word cannot see it
(`put` is word-idempotent on residents). -/
def logH : Handler ResSig (StateM (List String)) where
  handle
    | .acq => fun l => ((), l ++ ["acq"])
    | .rel => fun l => ((), l ++ ["rel"])
    | .usd => fun l => ((), l ++ ["usd"])

/-- The built service: one logged use per call. -/
def usingH : Handler UseSig (Prog ResSig) where
  handle | .use => Prog.op (S := ResSig) ResE.usd >>= fun _ => Pure.pure 0

/-- A layer that tries to own its own release. -/
def selfReleasing : Layer UseSig ResSig :=
  Prog.op (S := ResSig) ResE.acq >>= fun _ =>
    Prog.op (S := ResSig) ResE.rel >>= fun _ => Pure.pure usingH

/-- **THE BREAK.** The release lands before either use. -/
theorem selfReleasing_releases_too_early :
    (interpret logH (Layer.run selfReleasing consumer) []).2
      = ["acq", "rel", "usd", "usd"] := rfl

/-- The correctly-scoped expression — and its type is `Prog ResSig Nat`, a
RUN, not a `Layer UseSig ResSig`. -/
def correctlyScoped : Prog ResSig Nat :=
  Prog.op (S := ResSig) ResE.acq >>= fun _ =>
    interpret usingH consumer >>= fun n =>
      Prog.op (S := ResSig) ResE.rel >>= fun _ => Pure.pure n

theorem correctlyScoped_releases_last :
    (interpret logH correctlyScoped []).2 = ["acq", "usd", "usd", "rel"] := rfl

/-- The gap is observable in the acquisition trace. A `Layer` in this design
CANNOT own a finalizer that outlives its own build. -/
theorem lifetime_gap_is_observable :
    (interpret logH (Layer.run selfReleasing consumer) []).2
      ≠ (interpret logH correctlyScoped []).2 := by decide

end Lifetime

/-! ### §7.2 — the named repair, and what it costs

`ScopeSig` gains ONE constructor,

    | register (fin : BlockId) (args : List Addr32)

pushing a finalizer onto the ambient scope, with `scoped body` already
present as the delimiter that discharges the stack. Then a layer's build
registers and the consumer's `scoped` releases, which is rc.112's
`Scope.addFinalizerExit` + `Scope.close` exactly.

Two costs, both named, neither a carrier:

1. the floor's state grows from `Word` to `Word × List (BlockId × List Addr32)`.
   R18's ruling is about transformer ORDER (state outside error) and that is
   preserved, but the four `ensuring` laws of `EnsuringRepair.lean` §3 are
   stated at `WComp = Word → Except Refusal Addr32 × Word` and must be
   RESTATED at the wider state. NEW WORK, owed by this design.
2. `ScopeE.ensuring`'s children currently take no arguments
   (`EnsuringRepair.lean:589`, `runBlocks … []`), so a finalizer cannot close
   over what the build acquired unless it is an `Addr32` reachable from the
   word. On the CAS plane that is free; off it, `register` must carry `args`,
   which is the field above. A CONSTRUCTOR FIELD, not a type. -/

/-! ## §6 — `launch` and `memoize` do not belong

`memoize` is `>>=` (§3, `shared_is_bind`). `launch` is `build` followed by
the target's suspension; it is a property of the floor's monad, not of the
carrier — there is nothing to add to `Layer` for it. Both are DERIVED, and
neither needs a row of its own. -/

/-- `launch` as a derived combinator: build, discard the handler, suspend.
`k` is the floor's own suspension — never a `Layer` field. -/
def Layer.launch {S T : Sig} {M : Type → Type} [Monad M] {X : Type}
    (l : Layer S T) (floor : Handler T M) (suspend : M X) : M X :=
  Layer.build l floor >>= fun _ => suspend

theorem launch_is_build_then_suspend {S T : Sig} {M : Type → Type} [Monad M]
    {X : Type} (l : Layer S T) (fl : Handler T M) (suspend : M X) :
    Layer.launch l fl suspend = Layer.build l fl >>= fun _ => suspend := rfl

end EC1.ProposeA

#print axioms EC1.ProposeA.build_empty
#print axioms EC1.ProposeA.build_provide
#print axioms EC1.ProposeA.build_merge
#print axioms EC1.ProposeA.run_provide
#print axioms EC1.ProposeA.run_empty
#print axioms EC1.ProposeA.provide_assoc
#print axioms EC1.ProposeA.provide_empty_right
#print axioms EC1.ProposeA.provide_empty_left
#print axioms EC1.ProposeA.through_sum
#print axioms EC1.ProposeA.build_step_is_observable
#print axioms EC1.ProposeA.sharing_is_observable
#print axioms EC1.ProposeA.build_acquires_once
#print axioms EC1.ProposeA.fresh_acquires_twice
#print axioms EC1.ProposeA.shared_acquires_once
#print axioms EC1.ProposeA.finalizer_observes_failure
#print axioms EC1.ProposeA.merge_projections
#print axioms EC1.ProposeA.unwrap_is_join
#print axioms EC1.ProposeA.selfReleasing_releases_too_early
#print axioms EC1.ProposeA.correctlyScoped_releases_last
#print axioms EC1.ProposeA.lifetime_gap_is_observable
#print axioms EC1.ProposeA.scopeFloor_ensuring
