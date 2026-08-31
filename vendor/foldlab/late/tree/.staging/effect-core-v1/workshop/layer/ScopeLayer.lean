import Cas.Backend.Universal
import Cas.Backend.SumAlgebra
/-!
# `ScopeLayer` — a checked model of Scope and Layer

Not a Lake target. Adds nothing to `Cas`, moves no bytes, edits no ledger,
mutates nothing in `library/`.

Checked: `cd library/cas && lake env lean <this file>` — exit 0, no errors, no
warnings, 67 theorems, 67 `#print axioms` receipts, no `sorry`, no `axiom`, no
`native_decide`, no `Classical.choice`. Ceiling `[propext, Quot.sound]`.

## What is here

* **§2 SCOPE** — a region with acquisition, REGISTRATION and release at R18's
  forced target `ExceptT Refusal (StateM σ)` (state OUTSIDE error, because
  `EC1-CE045` proved `Except.error` has no state slot). Release on success,
  release on FAILURE with the refusal unchanged, LIFO for nested acquisitions.
  Non-vacuous: the blocks are real `Prog CasSig` programs run through a handler
  defined from the estate's own `referenceHandler`, so the release order is read
  off the store word.
* **§3 LAYER** — `Layer := Prog LayerSig (Handler SvcSig (Prog LayerSig))`.
  Composition is associative with a two-sided identity, and the proof
  INSTANTIATES the estate's `through_monoid` (`Cas/Backend/Universal.lean:785`)
  rather than reproving it. The same laws are then carried through the build
  prefix by `interpret_bind` and `interpret_through`.
* **§4 PROVIDE / EXCLUDE** — the residual row, proved to remove exactly what it
  supplies, bridged to the builder, and shown NON-ASSOCIATIVE at both planes.
* **§5** — the floor, and the whole design running end to end on a two-resource
  system.
* **§6** — what could not be modeled, named precisely.
* **§7** — the reuse ledger.

## The three findings a reader should not miss

1. **`through_monoid` IS the right anchor — through `lift`.** Four proposals
   concluded it was not, because `Svc = Handler SvcSig (Prog LayerSig)` is not
   an endomorphism. True, and beside the point: `lift : Svc → Handler LayerSig
   (Prog LayerSig)` IS one, and it is an injective homomorphism (`lift_hom`,
   `lift_inj`, `lift_injSvc`). So the estate's own monoid theorem discharges all
   three layer laws with two one-line lemmas and no new algebra.

2. **`provideMerge` is associative; `provide` is not — at BOTH planes.** The
   packet's dispute dissolves. `Handler.through` is `provideMerge`, and its row
   is associative as a LITERAL LIST EQUALITY (`provideMerge_requires_assoc`).
   Effect's `provide` is `provideMerge` followed by a MASK to the outer's
   services, and the mask breaks associativity on the row
   (`provide_requires_not_assoc`) AND in the meaning
   (`provide_is_not_associative_in_the_meaning`). The row is not
   over-approximating; it reports a real semantic difference. That is why rc.112
   ships both operations.

3. **The row is sound one way and provably unsound the other.**
   `build_forwards_of_not_provides` is unconditional: what the row does not claim
   to provide, the built context really forwards. The converse is FALSE —
   `provides_can_overclaim` exhibits two mutually-implementing layers whose
   composite advertises a key it forwards — and no check on the DESCRIPTION can
   catch it, because the bodies are opaque block references.

## The one structural move (R7)

Services are VALUE-level keys at ONE signature. A type-indexed service set is
not first-order content, so no `Sig` is ever computed from stored data. That is
what makes the residual row list arithmetic instead of a type equation, and it
is why §4.4's bridge is statable at all.
-/


namespace Cas.Workshop.ScopeLayer

open Cas.Lang
open Cas (Bytes Addr32 Node Word Binding Ref)


/-! ## §1 Signatures — one service signature, keys are values -/

abbrev SvcKey := String
abbrev BlockId := Nat

/-- The service language: ask for a service by key. One operation, because
under R7 the service SET is content, not a type index. -/
inductive SvcE where
  | ask (key : SvcKey)
  deriving DecidableEq, Repr

abbrev SvcE.Ans : SvcE → Type
  | .ask _ => Addr32

abbrev SvcSig : Sig := ⟨SvcE, SvcE.Ans⟩

/-- The scope language. Children are first-order `BlockId`s — R18 clause 1, no
`HHandler`, no higher-order handler carrier.

`acquire` runs its acquisition block and REGISTERS `release` on the ambient
finalizer stack; `scoped` is the DELIMITER that drains what was registered
inside it, LIFO. Separating the two is what lets a resource outlive the build
step that acquired it — the lifetime gap position A proved against its own
bracket-only design. -/
inductive ScopeE where
  | acquire (acq release : BlockId)
  | scoped  (body : BlockId)
  deriving DecidableEq, Repr

abbrev ScopeE.Ans : ScopeE → Type
  | _ => Addr32

abbrev ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩

/-- The layer language: services plus scope. `Sig.sum` is the estate's, unchanged. -/
abbrev LayerSig : Sig := SvcSig ⊕ₛ ScopeSig

/-! ## §2 SCOPE

R18's ruled target, generically in the state. `EC1-CE045` proved
`Except.error` has no word slot, so `StateT Word (Except Refusal)` cannot
finalize; the repair is the other transformer order. -/

/-- R18's target shape, unfolded. -/
abbrev Tgt (σ α : Type) := σ → Except Refusal α × σ

/-- The identification is DEFINITIONAL, not analogical. -/
theorem Tgt_is_exceptT_over_state (σ α : Type) :
    Tgt σ α = ExceptT Refusal (StateM σ) α := rfl

/-- `ensuring`, verbatim from the ruled repair
(`workshop/counterexamples/EnsuringRepair.lean:547`), generalized in the state
and answer type. Staging files are not importable, so this is re-declared, not
cited. -/
def ensuringT {σ α : Type} (body fin : Tgt σ α) : Tgt σ α := fun s =>
  match body s with
  | (.ok a, s₁) =>
    match fin s₁ with
    | (.ok _, s₂) => (.ok a, s₂)
    | (.error r, s₂) => (.error r, s₂)
  | (.error r, s₁) => (.error r, (fin s₁).2)

/-- EXIT-INDEXED finalization: a separate block per exit. Two block ids, never a
closure over an `Exit` value, so R7 holds at the finalizer. -/
def ensuringExitT {σ α : Type} (body onOk onErr : Tgt σ α) : Tgt σ α := fun s =>
  match body s with
  | (.ok a, s₁) =>
    match onOk s₁ with
    | (.ok _, s₂) => (.ok a, s₂)
    | (.error r, s₂) => (.error r, s₂)
  | (.error r, s₁) => (.error r, (onErr s₁).2)

/-- The amendment is CONSERVATIVE over the ruled repair: on the diagonal the two
are the same function. So the four ruled `ensuring` laws transfer by rewriting. -/
theorem ensuringExitT_diagonal {σ α : Type} (body fin : Tgt σ α) :
    ensuringExitT body fin fin = ensuringT body fin := rfl

/-! ### The four ruled laws, at this target -/

/-- **LAW 1.** The finalizer runs on success; the BODY's result survives and the
FINALIZER's state is what is reported. -/
theorem ensuringExitT_runs_on_success {σ α : Type} (body onOk onErr : Tgt σ α)
    (s s₁ s₂ : σ) (a v : α)
    (hb : body s = (.ok a, s₁)) (hf : onOk s₁ = (.ok v, s₂)) :
    ensuringExitT body onOk onErr s = (.ok a, s₂) := by
  simp only [ensuringExitT, hb, hf]

/-- **LAW 2.** The finalizer runs on FAILURE, its state survives the error
branch, and the body's refusal is re-raised unchanged. NO premise on the
finalizer's outcome. This is the law `StateT Word (Except Refusal)` cannot
state, because its error branch has no state slot. -/
theorem ensuringExitT_runs_on_failure {σ α : Type} (body onOk onErr : Tgt σ α)
    (s s₁ s₂ : σ) (r : Refusal) (res : Except Refusal α)
    (hb : body s = (.error r, s₁)) (hf : onErr s₁ = (res, s₂)) :
    ensuringExitT body onOk onErr s = (.error r, s₂) := by
  simp only [ensuringExitT, hb, hf]

/-- **LAW 3.** A finalizer can never replace a refusal — not even by refusing
itself. No premise on either finalizer. -/
theorem ensuringExitT_never_replaces {σ α : Type} (body onOk onErr : Tgt σ α)
    (s s₁ : σ) (r : Refusal) (hb : body s = (.error r, s₁)) :
    (ensuringExitT body onOk onErr s).1 = .error r := by
  simp only [ensuringExitT, hb]

/-- The state an `ensuringExit` leaves, on every path — the equation the
ordering laws are built from. -/
theorem ensuringExitT_state {σ α : Type} (body onOk onErr : Tgt σ α) (s : σ) :
    (ensuringExitT body onOk onErr s).2
      = match body s with
        | (.ok _, s₁) => (onOk s₁).2
        | (.error _, s₁) => (onErr s₁).2 := by
  unfold ensuringExitT
  cases hb : body s with
  | mk res s₁ =>
    cases res with
    | ok a => cases hf : onOk s₁ with | mk r₂ s₂ => cases r₂ <;> simp [hf]
    | error r => simp

/-- **LAW 4 — the exit indices are not redundant.** Success and failure select
DIFFERENT finalizers, so exit-indexing is a real obligation and not a
restatement of the ruled form. -/
theorem ensuringExitT_reads_the_exit {σ : Type} (onOk onErr : Tgt σ Nat) (s : σ) :
    (ensuringExitT (fun t => (.ok 0, t)) onOk onErr s).2 = (onOk s).2
      ∧ (ensuringExitT (fun t => (.error (.failed "x"), t)) onOk onErr s).2
          = (onErr s).2 := by
  constructor
  · rw [ensuringExitT_state]
  · rw [ensuringExitT_state]


/-! ### §2.2 The region — acquisition, registration, release

`ensuring` alone is a BRACKET: it releases when its own body returns. A LAYER's
resource must outlive the build step that acquired it, so acquisition and
delimitation are two operations and the finalizer stack is state. The stack is
`List BlockId` — first-order content, no closures — and the target stays
`ExceptT Refusal (StateM σ)`, so R18's transformer order is preserved and the
four laws above apply to the drain unchanged. -/

/-- Pending releases, innermost first. First-order: block addresses, never
functions. -/
abbrev FinStack := List BlockId

/-- R18's word, widened by the finalizer stack. Still a state. -/
abbrev ScopeState := Word × FinStack

/-- A block's meaning at the target. The interpreter's parameter — in the
shipped form it is resolved from content, exactly as `Defun.embedFrom` takes its
environment. -/
abbrev Blocks := BlockId → Tgt ScopeState Addr32

/-- **ACQUISITION + REGISTRATION.** Run the acquisition block; on success push
its release block on the ambient stack. On failure nothing is registered —
there is no resource to release. -/
def acquireT (run : Blocks) (acq rel : BlockId) : Tgt ScopeState Addr32 := fun s =>
  match run acq s with
  | (.ok a, s₁) => (.ok a, (s₁.1, rel :: s₁.2))
  | (.error r, s₁) => (.error r, s₁)

/-- **RELEASE.** Drain the stack head-first. Because `acquireT` conses, the head
is the most recent acquisition: draining head-first IS LIFO. Each finalizer's
state effect is kept whatever it answered. -/
def drainT (run : Blocks) : FinStack → Tgt ScopeState Addr32
  | [], s => (.ok Falsifier.zeroAddr, s)
  | b :: rest, s => drainT run rest (run b s).2

/-- Close a region: drain its own stack and leave it empty. -/
def closeScope (run : Blocks) : Tgt ScopeState Addr32 := fun s =>
  drainT run s.2 (s.1, [])

/-- **THE REGION.** Run the body against a FRESH stack, drain that stack on BOTH
exits, restore the enclosing stack. Nesting is therefore automatic: an inner
region drains before the outer one ever sees the state. -/
def scopedT (run : Blocks) (body : Tgt ScopeState Addr32) : Tgt ScopeState Addr32 :=
  fun s =>
    let r := ensuringExitT body (closeScope run) (closeScope run) (s.1, [])
    (r.1, (r.2.1, s.2))

/-! ### §2.3 The region's laws -/

/-- Registration: a successful acquisition leaves its release on top. -/
theorem acquireT_registers (run : Blocks) (acq rel : BlockId) (s s₁ : ScopeState)
    (a : Addr32) (h : run acq s = (.ok a, s₁)) :
    acquireT run acq rel s = (.ok a, (s₁.1, rel :: s₁.2)) := by
  simp only [acquireT, h]

/-- A FAILED acquisition registers nothing — there is no resource to release. -/
theorem acquireT_registers_nothing_on_failure (run : Blocks) (acq rel : BlockId)
    (s s₁ : ScopeState) (r : Refusal) (h : run acq s = (.error r, s₁)) :
    acquireT run acq rel s = (.error r, s₁) := by
  simp only [acquireT, h]

/-- The drain steps head-first. This equation IS the LIFO order. -/
theorem drainT_cons (run : Blocks) (b : BlockId) (rest : FinStack)
    (s : ScopeState) :
    drainT run (b :: rest) s = drainT run rest (run b s).2 := rfl

/-- Two acquisitions in order leave the SECOND on top, so the drain runs it
first. Registration order and release order are opposite by construction. The
premise is that an ACQUISITION does not itself pop the stack — discharged for
every store block by `onWord_preserves_the_stack` below. -/
theorem registration_is_LIFO (run : Blocks) (a₁ r₁ a₂ r₂ : BlockId)
    (s s₁ s₂ : ScopeState) (x y : Addr32)
    (h₁ : run a₁ s = (.ok x, s₁)) (h₂ : run a₂ (s₁.1, r₁ :: s₁.2) = (.ok y, s₂))
    (hstack : s₂.2 = r₁ :: s₁.2) :
    (acquireT run a₂ r₂ (acquireT run a₁ r₁ s).2).2.2 = r₂ :: r₁ :: s₁.2 := by
  simp only [acquireT, h₁, h₂, hstack]

/-- **RELEASE ON THE SUCCESS PATH.** The body's answer survives and the region's
state is the DRAIN's. The premise on the drain's outcome is the one asymmetry the
ruled repair also carries: a REFUSING finalizer does replace a success, because
nothing else would be honest. -/
theorem scopedT_releases_on_success (run : Blocks) (body : Tgt ScopeState Addr32)
    (s s₁ s₂ : ScopeState) (a v : Addr32) (h : body (s.1, []) = (.ok a, s₁))
    (hd : drainT run s₁.2 (s₁.1, []) = (.ok v, s₂)) :
    scopedT run body s = (.ok a, (s₂.1, s.2)) := by
  simp only [scopedT, ensuringExitT, closeScope, h, hd]

/-- Unconditionally, and on BOTH exits: the state a region leaves is the DRAIN's.
No premise on any finalizer. -/
theorem scopedT_state_is_the_drains (run : Blocks) (body : Tgt ScopeState Addr32)
    (s : ScopeState) :
    (scopedT run body s).2.1
      = (drainT run (body (s.1, [])).2.2 ((body (s.1, [])).2.1, [])).2.1 := by
  show (ensuringExitT body (closeScope run) (closeScope run) (s.1, [])).2.1 = _
  rw [ensuringExitT_state]
  cases hb : body (s.1, []) with
  | mk res s₁ => cases res <;> simp [closeScope]

/-- **RELEASE ON THE FAILURE PATH — the R18 law.** The body refuses; the
finalizers STILL run, their state survives the error branch, and the body's
refusal is re-raised unchanged. No premise on any finalizer. This is precisely
what `StateT Word (Except Refusal)` cannot state (`EC1-CE045`,
`reraise_is_finalizer_blind`): its `.error` constructor has no state slot. -/
theorem scopedT_releases_on_failure (run : Blocks) (body : Tgt ScopeState Addr32)
    (s s₁ : ScopeState) (r : Refusal) (h : body (s.1, []) = (.error r, s₁)) :
    scopedT run body s = (.error r, ((drainT run s₁.2 (s₁.1, [])).2.1, s.2)) := by
  simp only [scopedT, ensuringExitT, closeScope, h]

/-- A finalizer can never replace the region's refusal — not even by refusing
itself. -/
theorem scopedT_never_replaces (run : Blocks) (body : Tgt ScopeState Addr32)
    (s s₁ : ScopeState) (r : Refusal) (h : body (s.1, []) = (.error r, s₁)) :
    (scopedT run body s).1 = .error r := by
  simp only [scopedT, ensuringExitT, h]

/-- A region restores the enclosing finalizer stack on BOTH exits: what was
registered inside it does not leak out. -/
theorem scopedT_restores_the_stack (run : Blocks) (body : Tgt ScopeState Addr32)
    (s : ScopeState) : (scopedT run body s).2.2 = s.2 := rfl

/-! ### §2.4 Non-vacuity — the order is observable in the estate's own store word

Blocks are real `Prog CasSig` programs interpreted by a handler DEFINED FROM the
estate's `referenceHandler`, at R18's word-carrying order. The store word is a
LIST in admission order, so the release order is literally readable off it. The
address function is the estate's own `Falsifier.lenAddr` — length-sensitive, no
digest in the kernel (`EC1-CE006`'s device). -/

/-- The word-carrying reference target. Defined FROM `referenceHandler` clause by
clause, so it cannot drift from the reference meaning; a refusal stops at the
word the operation was reached with, which is `step`'s own triage. -/
def refHandlerW (H : Bytes → Addr32) : Handler CasSig (ExceptT Refusal (StateM Word)) where
  handle op := fun w =>
    match (referenceHandler H).handle op w with
    | .ok (ans, w') => (.ok ans, w')
    | .error r => (.error r, w)

/-- An ordinary `interpret`, so `interpret_bind` applies to it unchanged. -/
def runCas (H : Bytes → Addr32) (p : Prog CasSig Addr32) : Word → Except Refusal Addr32 × Word :=
  interpret (refHandlerW H) p

/-- Lift a word computation to the scope state: the finalizer stack is untouched
by store work. -/
def onWord (m : Word → Except Refusal Addr32 × Word) : Tgt ScopeState Addr32 :=
  fun s => ((m s.1).1, ((m s.1).2, s.2))

/-- Nodes separated by payload LENGTH, so `lenAddr` separates their addresses. -/
def nOf (k : Nat) : Node := ⟨0, 0, List.replicate k 7, []⟩

/-- The observable: the payload length of each admitted binding, in admission
order. Reading it off the word gives the execution order. -/
def trace (w : Word) : List Nat := w.map (fun b => b.node.payload.length)

def blkPut (k : Nat) : Tgt ScopeState Addr32 :=
  onWord (runCas Falsifier.lenAddr (Cas.Lang.put (nOf k)))
def blkFail : Tgt ScopeState Addr32 :=
  onWord (runCas Falsifier.lenAddr (failWith "boom"))

/-- Store work never touches the finalizer stack — the premise of
`registration_is_LIFO`, discharged for every block used below. -/
theorem onWord_preserves_the_stack (m : Word → Except Refusal Addr32 × Word)
    (s : ScopeState) : (onWord m s).2.2 = s.2 := rfl

/-- Blocks 0/1 acquire and release the OUTER resource; 2/3 the INNER one;
4 refuses. -/
def demoBlocks : Blocks
  | 0 => blkPut 0
  | 1 => blkPut 1
  | 2 => blkPut 2
  | 3 => blkPut 3
  | 4 => blkFail
  | _ => blkPut 9

/-- A body that acquires two resources and succeeds. -/
def bodyOk : Tgt ScopeState Addr32 := fun s =>
  match acquireT demoBlocks 0 1 s with
  | (.ok _, s₁) => acquireT demoBlocks 2 3 s₁
  | e => e

/-- The same body, refusing after both acquisitions. -/
def bodyFails : Tgt ScopeState Addr32 := fun s =>
  match acquireT demoBlocks 0 1 s with
  | (.ok _, s₁) =>
    match acquireT demoBlocks 2 3 s₁ with
    | (.ok _, s₂) => demoBlocks 4 s₂
    | e => e
  | e => e

/-- **RELEASE ON SUCCESS, LIFO, non-vacuous.** Acquire outer (0), acquire inner
(2), release inner (3), release outer (1). The order is a fact about the
estate's own store word. -/
theorem demo_success_releases_LIFO :
    trace (scopedT demoBlocks bodyOk ([], [])).2.1 = [0, 2, 3, 1] := by decide

/-- **RELEASE ON FAILURE, LIFO, non-vacuous, refusal unchanged.** Same order,
and the body's refusal is what the region reports. -/
theorem demo_failure_releases_LIFO :
    (scopedT demoBlocks bodyFails ([], [])).1 = .error (.failed "boom")
      ∧ trace (scopedT demoBlocks bodyFails ([], [])).2.1 = [0, 2, 3, 1] :=
  ⟨rfl, by decide⟩

/-- LIFO is not vacuous: the reversed order is a DIFFERENT word, so the claim
has content in this carrier. -/
theorem demo_LIFO_is_observable :
    trace (scopedT demoBlocks bodyOk ([], [])).2.1 ≠ [0, 2, 1, 3] := by decide

/-! ### §2.5 Receipts for §2 -/

#print axioms Tgt_is_exceptT_over_state
#print axioms ensuringExitT_diagonal
#print axioms ensuringExitT_runs_on_success
#print axioms ensuringExitT_runs_on_failure
#print axioms ensuringExitT_never_replaces
#print axioms ensuringExitT_state
#print axioms ensuringExitT_reads_the_exit
#print axioms acquireT_registers
#print axioms acquireT_registers_nothing_on_failure
#print axioms drainT_cons
#print axioms registration_is_LIFO
#print axioms scopedT_releases_on_success
#print axioms scopedT_state_is_the_drains
#print axioms scopedT_releases_on_failure
#print axioms scopedT_never_replaces
#print axioms scopedT_restores_the_stack
#print axioms onWord_preserves_the_stack
#print axioms demo_success_releases_LIFO
#print axioms demo_failure_releases_LIFO
#print axioms demo_LIFO_is_observable

/-! ## §3 LAYER

The converged carrier. Two `abbrev`s over two types already in `library/cas`:
no inductive, no eliminator, no new equality, `LawfulMonad` inherited from
`Prog`. Erasing both names changes nothing.

`Svc` is Effect's `Context<R>` read as a handler; the `Prog LayerSig (·)` prefix
is the BUILD step — the thing `Handler.through` alone provably cannot express.
Scope is a signature SUMMAND, so an acquiring layer is an ORDINARY layer and
every law below applies to it unchanged: R18's "the tower has a floor at the
scoped layer" becomes one bottom handler, not a per-layer fork. -/

/-- The built context: one meaning per service key, in the layer language. -/
abbrev Svc : Type := Handler SvcSig (Prog LayerSig)

/-- THE TYPE. A program in the layer language whose value is a built context. -/
abbrev Layer : Type := Prog LayerSig Svc

/-- Forwarding an ask to whatever is below. Named, because `Sig.sum` is not
reducible: an anonymous `Prog.op (Sum.inl …)` leaves goals that `rw` cannot
match at its own transparency. -/
def fwd (q : SvcKey) : Prog LayerSig Addr32 :=
  Prog.op (S := LayerSig) (Sum.inl (SvcE.ask q))

/-- The empty context: forward every ask to whatever is below. -/
def injSvc : Svc := ⟨fun | .ask q => fwd q⟩

/-- Scope operations pass through every context untouched — they are answered
only at the floor. -/
def scopePass : Handler ScopeSig (Prog LayerSig) :=
  ⟨fun op => Prog.op (S := LayerSig) (Sum.inr op)⟩

/-- A context, read as a handler for the WHOLE layer language. This is the
embedding that makes the estate's endomorphism monoid reachable. -/
def lift (h : Svc) : Handler LayerSig (Prog LayerSig) := Handler.sum h scopePass

/-- **COMPOSITION.** `Handler.through` (`Cas/Lang/Tower.lean:65`) and nothing
else: the outer context's unanswered asks are resolved by the inner one, and its
implementations run in the inner one's language. This is Effect's
`Layer.provideMerge` at the value plane. -/
def Svc.andThen (outer inner : Svc) : Svc := outer.through (lift inner)

/-! ### §3.1 `lift` is a monoid embedding into the estate's own monoid

`through_monoid` (`Cas/Backend/Universal.lean:785`) is stated at
`Handler S (Prog S)` — ENDOMORPHISMS at one signature — and the estate's own
docstring at :776-784 says that across signatures the three facts are a
CATEGORY, not a monoid. Four of the five proposals concluded from this that
`through_monoid` is the wrong anchor for a layer, because `Svc` is
`Handler SvcSig (Prog LayerSig)` and those are not endomorphisms.

They are right about `Svc` and wrong about the design: `lift` lands in
`Handler LayerSig (Prog LayerSig)`, which IS the endomorphism setting, and it is
an injective homomorphism. So `through_monoid` applies VERBATIM and discharges
all three layer laws with no reproof. -/

/-- `lift` sends the empty context to the estate's syntactic identity. -/
theorem lift_injSvc : lift injSvc = idHandler (S := LayerSig) :=
  Handler.ext fun op => by cases op <;> rfl

/-- `lift` is a HOMOMORPHISM: layer composition becomes `Handler.through`. The
right-hand case is where scope pass-through pays for itself. -/
theorem lift_hom (outer inner : Svc) :
    lift (outer.andThen inner) = (lift outer).through (lift inner) :=
  Handler.ext fun op => by
    cases op with
    | inl o => rfl
    | inr o => exact (interpret_op (S := LayerSig) (lift inner) (Sum.inr o)).symm

/-- `lift` is INJECTIVE, so the laws transport back. -/
theorem lift_inj {a b : Svc} (h : lift a = lift b) : a = b :=
  Handler.ext fun op => congrArg (fun k => k.handle (Sum.inl op)) h

/-! ### §3.2 The layer laws, DISCHARGED by the existing theorem

Each of the three is `through_monoid`'s corresponding component, instantiated at
`lift a`, `lift b`, `lift c`. No new algebra: `lift_hom` and `lift_injSvc` are
the only new lemmas, one line each. -/

/-- **ASSOCIATIVE**, on the nose. `through_monoid`'s first component. -/
theorem andThen_assoc (a b c : Svc) :
    (a.andThen b).andThen c = a.andThen (b.andThen c) := by
  apply lift_inj
  simp only [lift_hom]
  exact (through_monoid (lift a) (lift b) (lift c)).1

/-- **RIGHT IDENTITY.** `through_monoid`'s second component. -/
theorem andThen_id_right (a : Svc) : a.andThen injSvc = a := by
  apply lift_inj
  simp only [lift_hom, lift_injSvc]
  exact (through_monoid (lift a) (lift a) (lift a)).2.1

/-- **LEFT IDENTITY.** `through_monoid`'s third component. -/
theorem andThen_id_left (a : Svc) : injSvc.andThen a = a := by
  apply lift_inj
  simp only [lift_hom, lift_injSvc]
  exact (through_monoid (lift a) (lift a) (lift a)).2.2

/-- The three at once, exhibited as ONE application of the estate's theorem —
this is the whole of the obligation, discharged by a declaration that was on
`main` before this design existed. -/
theorem layer_monoid_is_through_monoid (a b c : Svc) :
    (a.andThen b).andThen c = a.andThen (b.andThen c)
      ∧ a.andThen injSvc = a
      ∧ injSvc.andThen a = a :=
  ⟨andThen_assoc a b c, andThen_id_right a, andThen_id_left a⟩

/-! ### §3.3 The same laws WITH the build step

`Svc.andThen` is build-free. A `Layer` carries a `Prog LayerSig` prefix, so
composing two layers must build the inner one, build the outer one THROUGH it,
and then compose the results. The laws survive: `interpret_bind`
(`Cas/Lang/Handler.lean:53`) and `interpret_through` (`Cas/Lang/Tower.lean:71`)
carry the build past the composition, and `andThen_assoc` closes the residue. -/

/-- `interpret_bind` and `interpret_pure` restated at `>>=` and at the `Monad`
instance's `pure`, so `simp` can see them. Same proof terms; no new content.
(Position D flagged the same need; a shipped version would tag the library
lemmas instead.) -/
theorem interpret_bind' {S : Sig} {M : Type → Type} {A B : Type} [Monad M]
    [LawfulMonad M] (h : Handler S M) (p : Prog S A) (f : A → Prog S B) :
    interpret h (p >>= f) = interpret h p >>= fun a => interpret h (f a) :=
  interpret_bind h p f

theorem interpret_purep {S : Sig} {M : Type → Type} {A : Type} [Monad M]
    (h : Handler S M) (a : A) : interpret h (pure a : Prog S A) = pure a := rfl

/-- The empty layer: build nothing, forward everything. -/
def Layer.empty : Layer := pure injSvc

/-- **`provideMerge` at the layer plane.** Build `inner`; build `outer` in
`inner`'s language; compose the two contexts. -/
def Layer.provideMerge (inner outer : Layer) : Layer :=
  inner >>= fun hi => interpret (lift hi) outer >>= fun ho => pure (ho.andThen hi)

/-- Consuming a layer: build it, then interpret the program against it. Effect's
`Effect.provide`. -/
def Layer.run {A : Type} (l : Layer) (p : Prog LayerSig A) : Prog LayerSig A :=
  l >>= fun h => interpret (lift h) p

theorem Layer.provideMerge_empty_left (o : Layer) :
    Layer.provideMerge Layer.empty o = o := by
  simp only [Layer.provideMerge, Layer.empty, pure_bind, lift_injSvc, interpret_id,
    andThen_id_right, bind_pure]


theorem Layer.provideMerge_empty_right (i : Layer) :
    Layer.provideMerge i Layer.empty = i := by
  simp only [Layer.provideMerge, Layer.empty, interpret_purep, pure_bind,
    andThen_id_left, bind_pure]

/-- **ASSOCIATIVITY WITH THE BUILD.** The build order is the same on both sides;
the residue is `andThen_assoc`, i.e. `through_monoid`. -/
theorem Layer.provideMerge_assoc (a b c : Layer) :
    Layer.provideMerge (Layer.provideMerge c b) a
      = Layer.provideMerge c (Layer.provideMerge b a) := by
  simp only [Layer.provideMerge, bind_assoc, pure_bind, interpret_bind',
    interpret_purep, interpret_through, ← lift_hom, andThen_assoc]

/-- **R12's collapse at the layer plane.** Running a program against a composite
layer is running it against the outer, then against the inner: build-then-run
equals run-against-the-composite. Discharged by `interpret_bind` and
`interpret_through`. -/
theorem Layer.run_provideMerge {A : Type} (i o : Layer) (p : Prog LayerSig A) :
    Layer.run (Layer.provideMerge i o) p = Layer.run i (Layer.run o p) := by
  simp only [Layer.run, Layer.provideMerge, bind_assoc, pure_bind, interpret_bind',
    interpret_through, ← lift_hom]

theorem Layer.run_empty {A : Type} (p : Prog LayerSig A) :
    Layer.run Layer.empty p = p := by
  simp only [Layer.run, Layer.empty, pure_bind, lift_injSvc, interpret_id]

/-- `unwrap` / `flatMap` / `suspend` — a layer computed by a program — is `join`,
by `rfl`. REIFICATION C6 refused a node/edge Layer graph because these
combinators compute successors from runtime values; the objection does not reach
a carrier that is already the free monad. (It does still reach the CONTENT
plane: `LDesc` has no arm for them and would need `SystemNode`'s `opaque`.) -/
def Layer.unwrap (m : Prog LayerSig Layer) : Layer := m >>= id

theorem unwrap_is_join (m : Prog LayerSig Layer) : Layer.unwrap m = m >>= id := rfl

/-- Sharing is `bind`: build once, pass the built context to both consumers.
There is no memo map and no memo key in the carrier. -/
def Layer.shared (c : Layer) (k : Svc → Layer) : Layer := c >>= k

theorem shared_is_bind (c : Layer) (k : Svc → Layer) : Layer.shared c k = c >>= k := rfl

/-! ### §3.4 Receipts for §3 -/

#print axioms interpret_bind'
#print axioms interpret_purep
#print axioms lift_injSvc
#print axioms lift_hom
#print axioms lift_inj
#print axioms andThen_assoc
#print axioms andThen_id_right
#print axioms andThen_id_left
#print axioms layer_monoid_is_through_monoid
#print axioms Layer.provideMerge_empty_left
#print axioms Layer.provideMerge_empty_right
#print axioms Layer.provideMerge_assoc
#print axioms Layer.run_provideMerge
#print axioms Layer.run_empty
#print axioms unwrap_is_join
#print axioms shared_is_bind

/-! ## §4 PROVIDE / EXCLUDE — the residual row

The row is PURE first-order arithmetic on key lists, outside `Prog` (R14a/P1).
Under R7 that is forced: a type-indexed service set is not content, so
`provides`/`requires` cannot be `Sig` indices and no `sigOf : List ServiceRef →
Sig` is ever needed.

The section proves four things. (1) `provide` removes exactly what it supplies —
no more, no less. (2) `provideMerge`'s row is ASSOCIATIVE, as a literal list
equality. (3) `provide`'s row is NOT, and the counterexample is minimal. (4) The
row is SOUND against the builder, and the failure of its converse is exhibited. -/

/-- Row difference. -/
def without (xs ys : List SvcKey) : List SvcKey := xs.filter (fun k => !ys.contains k)

theorem mem_without (xs ys : List SvcKey) (k : SvcKey) :
    k ∈ without xs ys ↔ k ∈ xs ∧ k ∉ ys := by
  simp [without, List.mem_filter]

/-- The layer description: first-order content, `DecidableEq`, no functions. In
the shipped estate this is `Cas.Schema.SystemNode` (`Cas/Schema/System.lean:208`)
with addressed children; `acquires` is the one arm it lacks. -/
inductive LDesc where
  | empty
  | leaf         (key : SvcKey) (needs : List SvcKey) (body : BlockId)
  | acquires     (key : SvcKey) (needs : List SvcKey) (acq rel : BlockId)
  | merge        (l r : LDesc)
  | provideMerge (inner outer : LDesc)
  | provide      (inner outer : LDesc)
  deriving DecidableEq, Repr

/-- What a description advertises. `provide` HIDES the inner's services;
`provideMerge` keeps them. That single difference is the whole of §4.3. -/
def LDesc.provides : LDesc → List SvcKey
  | .empty => []
  | .leaf k _ _ => [k]
  | .acquires k _ _ _ => [k]
  | .merge l r => l.provides ++ r.provides
  | .provideMerge i o => i.provides ++ o.provides
  | .provide _ o => o.provides

/-- What a description still needs. THE EXCLUDE TRANSFORM is the `provide` and
`provideMerge` clauses: `i.requires ++ without o.requires i.provides` — exactly
rc.112's `RIn | Exclude<RIn2, ROut>`. -/
def LDesc.requires : LDesc → List SvcKey
  | .empty => []
  | .leaf _ n _ => n
  | .acquires _ n _ _ => n
  | .merge l r => l.requires ++ r.requires
  | .provideMerge i o => i.requires ++ without o.requires i.provides
  | .provide i o => i.requires ++ without o.requires i.provides

/-- Whether a description acquires — DECIDABLE ON CONTENT, where rc.112's
`Exclude<R, Scope.Scope>` makes it invisible in the type. -/
def LDesc.acquiring : LDesc → Bool
  | .empty => false
  | .leaf _ _ _ => false
  | .acquires _ _ _ _ => true
  | .merge l r => l.acquiring || r.acquiring
  | .provideMerge i o => i.acquiring || o.acquiring
  | .provide i o => i.acquiring || o.acquiring

/-! ### §4.1 The transform removes exactly what it supplies -/

/-- **THE CHARACTERIZATION.** A key survives `provide` iff the inner needed it,
or the outer needed it and the inner does not supply it. Everything in §4.1 is a
corollary. -/
theorem provide_requires_mem (i o : LDesc) (k : SvcKey) :
    k ∈ (LDesc.provide i o).requires
      ↔ k ∈ i.requires ∨ (k ∈ o.requires ∧ k ∉ i.provides) := by
  simp [LDesc.requires, mem_without]

/-- **NO LESS.** Everything the inner supplies IS removed from the outer's row.
(The side condition is that the inner does not itself require what it provides —
a description that needs its own service genuinely still needs it.) -/
theorem provide_removes_supplied (i o : LDesc) (k : SvcKey)
    (hp : k ∈ i.provides) (hr : k ∉ i.requires) :
    k ∉ (LDesc.provide i o).requires := by
  rw [provide_requires_mem]
  rintro (h | ⟨_, h⟩)
  · exact hr h
  · exact h hp

/-- **NO MORE.** Nothing the inner does NOT supply is removed. -/
theorem provide_keeps_unsupplied (i o : LDesc) (k : SvcKey)
    (ho : k ∈ o.requires) (hp : k ∉ i.provides) :
    k ∈ (LDesc.provide i o).requires := by
  rw [provide_requires_mem]; exact Or.inr ⟨ho, hp⟩

/-- **NO MORE, sharpened.** If a key of the outer's row is gone, the inner
supplied it — the transform removes nothing on any other ground. -/
theorem provide_removes_only_supplied (i o : LDesc) (k : SvcKey)
    (ho : k ∈ o.requires) (hgone : k ∉ (LDesc.provide i o).requires) :
    k ∈ i.provides :=
  Decidable.byContradiction fun hp => hgone (provide_keeps_unsupplied i o k ho hp)

/-- The inner's own row is never touched. -/
theorem provide_keeps_inner (i o : LDesc) (k : SvcKey) (h : k ∈ i.requires) :
    k ∈ (LDesc.provide i o).requires := by
  rw [provide_requires_mem]; exact Or.inl h

/-- And `provide` hides the inner's services, where `provideMerge` keeps them.
This is the ONLY difference between the two rows. -/
theorem provides_of_provide (i o : LDesc) :
    (LDesc.provide i o).provides = o.provides := rfl

theorem provides_of_provideMerge (i o : LDesc) :
    (LDesc.provideMerge i o).provides = i.provides ++ o.provides := rfl

/-! ### §4.2 `provideMerge`'s row is associative — as a literal list equality -/

/-- Excluding two rows in sequence is excluding their union. -/
theorem without_append (xs ys zs : List SvcKey) :
    without xs (ys ++ zs) = without (without xs zs) ys := by
  simp only [without, List.filter_filter]
  refine List.filter_congr fun k _ => ?_
  simp only [List.contains_append]
  cases ys.contains k <;> cases zs.contains k <;> rfl

/-- …and it distributes over row concatenation. -/
theorem without_distrib (xs ys zs : List SvcKey) :
    without (xs ++ ys) zs = without xs zs ++ without ys zs :=
  List.filter_append _ _

theorem provideMerge_provides_assoc (a b c : LDesc) :
    (LDesc.provideMerge (LDesc.provideMerge a b) c).provides
      = (LDesc.provideMerge a (LDesc.provideMerge b c)).provides := by
  simp only [LDesc.provides, List.append_assoc]

/-- **`provideMerge`'s ROW IS ASSOCIATIVE.** Not up to permutation, not up to
membership: the two lists are equal. This is the row half of `through_monoid`,
and it is why the estate's associativity theorem is the right anchor for
`provideMerge`. -/
theorem provideMerge_requires_assoc (a b c : LDesc) :
    (LDesc.provideMerge (LDesc.provideMerge a b) c).requires
      = (LDesc.provideMerge a (LDesc.provideMerge b c)).requires := by
  simp only [LDesc.requires, LDesc.provides, without_distrib, ← without_append,
    List.append_assoc]

/-! ### §4.3 `provide`'s row is NOT associative — and neither is its meaning

Four of the five proposals sold `provide_assoc` as a free consequence of
`through_assoc`. The estate's theorems are true and they are about
`Handler.through`, which is `provideMerge`. Effect's `provide` is `provideMerge`
followed by a MASK to the outer's services, and masking breaks the algebra —
which is exactly why rc.112 ships both operations. -/

def dA : LDesc := .leaf "A" [] 0
def dB : LDesc := .leaf "B" ["A"] 1
def dC : LDesc := .leaf "C" ["A"] 2

/-- **`provide` IS NOT ASSOCIATIVE ON THE ROW.** With `A` supplied at the
bottom, `B` and `C` both needing it: bracketed left the composite STILL requires
`A`, bracketed right it does not. The mask hides `A` from `C`. -/
theorem provide_requires_not_assoc :
    (LDesc.provide (LDesc.provide dA dB) dC).requires = ["A"]
      ∧ (LDesc.provide dA (LDesc.provide dB dC)).requires = []
      ∧ (LDesc.provide (LDesc.provide dA dB) dC).requires
          ≠ (LDesc.provide dA (LDesc.provide dB dC)).requires := by
  refine ⟨rfl, rfl, by decide⟩

/-- `provideMerge` on the SAME witness IS associative — so the failure is the
mask, not the row arithmetic. -/
theorem provideMerge_on_the_same_witness_is_assoc :
    (LDesc.provideMerge (LDesc.provideMerge dA dB) dC).requires
      = (LDesc.provideMerge dA (LDesc.provideMerge dB dC)).requires :=
  provideMerge_requires_assoc dA dB dC

/-! ### §4.4 The row against the builder

The denotation. `CodeEnv` is the R7 seam and the denotation's PARAMETER, exactly
as `Defun.embedFrom` takes its environment: block addresses are content, the
programs they name are code. -/

abbrev CodeEnv := BlockId → Prog LayerSig Addr32

/-- Answer one key; forward the rest. -/
def leafH (key : SvcKey) (body : Prog LayerSig Addr32) : Svc :=
  ⟨fun | .ask q => if q = key then body else fwd q⟩

/-- Service merge OVERLAPS on keys, so it takes the winning key set as DATA.
`Handler.sum` is the wrong operation here — `Sig.sum` is DISJOINT — and
`Handler.sum_unique` correspondingly does not reach it. `mergeOn_unique` below
is the analogue, and it is one application of `Handler.ext`. -/
def mergeOn (keys : List SvcKey) (l r : Svc) : Svc :=
  ⟨fun | .ask q => if keys.contains q then r.handle (.ask q) else l.handle (.ask q)⟩

/-- The MASK that distinguishes `provide` from `provideMerge`: keep only the
outer's services, forward everything else. -/
def restrictTo (keys : List SvcKey) (h : Svc) : Svc :=
  ⟨fun | .ask q => if keys.contains q then h.handle (.ask q) else fwd q⟩

/-- Merge's universal property at an OVERLAPPING merge. Discharged by
`Handler.ext` (`Cas/Backend/Universal.lean:128`), not by `Handler.sum_unique`. -/
theorem mergeOn_unique (keys : List SvcKey) (l r m : Svc)
    (hin : ∀ q, keys.contains q = true → m.handle (.ask q) = r.handle (.ask q))
    (hout : ∀ q, keys.contains q = false → m.handle (.ask q) = l.handle (.ask q)) :
    m = mergeOn keys l r :=
  Handler.ext fun op => by
    cases op with
    | ask q =>
      cases h : keys.contains q
      · show m.handle (.ask q) = _
        rw [hout q h]; simp only [mergeOn, h, Bool.false_eq_true, if_false]
      · show m.handle (.ask q) = _
        rw [hin q h]; simp only [mergeOn, h, if_true]

/-- THE DENOTATION. `provideMerge` is `Handler.through`; `provide` is
`Handler.through` MASKED. -/
def LDesc.build (ce : CodeEnv) : LDesc → Svc
  | .empty => injSvc
  | .leaf k _ b => leafH k (ce b)
  | .acquires k _ a r =>
      leafH k (Prog.op (S := LayerSig) (Sum.inr (ScopeE.acquire a r)))
  | .merge l r => mergeOn r.provides (l.build ce) (r.build ce)
  | .provideMerge i o => (o.build ce).andThen (i.build ce)
  | .provide i o => restrictTo o.provides ((o.build ce).andThen (i.build ce))

/-- The built context FORWARDS `q`: it does not answer the ask itself. -/
def Forwards (h : Svc) (q : SvcKey) : Prop := h.handle (.ask q) = fwd q

/-- `interpret_op` (`Cas/Lang/Representation.lean:115`) at the one shape every
proof below needs. `Sig.sum` is not reducible, so `rw` cannot unify `LayerSig.Op`
with `SvcSig.Op ⊕ ScopeSig.Op` on its own; stating the instance once fixes it. -/
theorem interpret_ask (h : Svc) (q : SvcKey) :
    interpret (lift h) (fwd q) = h.handle (.ask q) :=
  interpret_op (S := LayerSig) (lift h) (Sum.inl (SvcE.ask q))

/-- **THE BRIDGE — sound direction, UNCONDITIONAL.** Everything the row does not
claim to provide, the built context really does forward. So `provides` never
over-claims by omission and `requires` never under-claims: the emitted `RIn` is
honest in the direction that matters.

This is the theorem the whole field named as owed and nobody had. It is statable
at all only because §1 put keys at the VALUE level: the induction is over
first-order data, never over a `Sig` computed from content. -/
theorem build_forwards_of_not_provides (ce : CodeEnv) :
    ∀ (d : LDesc) (q : SvcKey), q ∉ d.provides → Forwards (d.build ce) q := by
  intro d
  induction d with
  | empty => intro q _; rfl
  | leaf key n b =>
    intro q hq
    have hne : q ≠ key := fun h => hq (by simp [LDesc.provides, h])
    exact if_neg hne
  | acquires key n a r =>
    intro q hq
    have hne : q ≠ key := fun h => hq (by simp [LDesc.provides, h])
    exact if_neg hne
  | merge l r ihl _ =>
    intro q hq
    simp only [LDesc.provides, List.mem_append, not_or] at hq
    have hc : ¬ (r.provides.contains q = true) := by simp [hq.2]
    exact (if_neg hc).trans (ihl q hq.1)
  | provideMerge i o ihi iho =>
    intro q hq
    simp only [LDesc.provides, List.mem_append, not_or] at hq
    exact (congrArg (fun p => interpret (lift (i.build ce)) p) (iho q hq.2)).trans
      ((interpret_ask (i.build ce) q).trans (ihi q hq.1))
  | provide i o _ _ =>
    intro q hq
    have hq' : q ∉ o.provides := hq
    have hc : ¬ (o.provides.contains q = true) := by simp [hq']
    exact if_neg hc

/-- **DISCHARGE.** An ask the OUTER does not provide is answered by the INNER —
that is what providing MEANS, and it is `interpret_op` plus the bridge. Together
with the line above it gives the exact statement at the composite:
`provideMerge` answers what either side provides and forwards the rest. -/
theorem provideMerge_discharges (ce : CodeEnv) (i o : LDesc) (q : SvcKey)
    (hq : q ∉ o.provides) :
    ((LDesc.provideMerge i o).build ce).handle (.ask q)
      = (i.build ce).handle (.ask q) := by
  exact (congrArg (fun p => interpret (lift (i.build ce)) p)
      (build_forwards_of_not_provides ce o q hq)).trans (interpret_ask (i.build ce) q)

/-- …and `provide` does NOT discharge it: the mask hides the inner's services,
matching `provides_of_provide`. This is the whole semantic difference between the
two operations, and §4.6 shows it is what breaks associativity. -/
theorem provide_hides_the_inner (ce : CodeEnv) (i o : LDesc) (q : SvcKey)
    (hq : q ∉ o.provides) : Forwards ((LDesc.provide i o).build ce) q :=
  if_neg (by simp [hq] : ¬ (o.provides.contains q = true))

/-! ### §4.5 The converse FAILS — the row can over-claim, and content cannot see it

The bridge's other direction — "everything the row claims to provide, the built
context answers" — is FALSE, and the counterexample is small. Two layers that
implement each other's service compose into a context that forwards a key both
of them advertise. No check on the DESCRIPTION can catch it, because the bodies
are opaque block references; it is a property of the code, not of the row. -/

def cycCE : CodeEnv
  | 0 => fwd "K"
  | _ => fwd "J"

/-- Provides `J`, implemented by asking for `K`. -/
def cycInner : LDesc := .leaf "J" ["K"] 0
/-- Provides `K`, implemented by asking for `J`. -/
def cycOuter : LDesc := .leaf "K" ["J"] 1

/-- **THE ROW OVER-CLAIMS.** `K` is in the composite's `provides` row, and the
composite forwards `K`. -/
theorem provides_can_overclaim :
    "K" ∈ (LDesc.provideMerge cycInner cycOuter).provides
      ∧ Forwards ((LDesc.provideMerge cycInner cycOuter).build cycCE) "K" :=
  ⟨by decide, rfl⟩

/-! ### §4.6 `provide` is non-associative IN THE MEANING TOO

§4.3 showed the row. Here is the same failure at the value plane, on the same
shape: the mask that makes `provide` differ from `provideMerge` also makes it
non-associative, so the row is not over-approximating — it is REPORTING a real
semantic difference. `A` is answered under one bracketing and escapes under the
other. -/

def eCE : CodeEnv
  | 1 => fwd "A"
  | _ => Prog.pure Falsifier.zeroAddr

def eA : LDesc := .leaf "A" [] 0
def eB : LDesc := .leaf "B" [] 0
def eC : LDesc := .leaf "C" ["A"] 1

/-- **`provide` IS NOT ASSOCIATIVE IN THE MEANING.** Bracketed left, `C`'s
implementation still escapes as an unanswered `ask "A"`; bracketed right, `A`
answers it. -/
theorem provide_is_not_associative_in_the_meaning :
    ((LDesc.provide (LDesc.provide eA eB) eC).build eCE).handle (.ask "C")
        = fwd "A"
      ∧ ((LDesc.provide eA (LDesc.provide eB eC)).build eCE).handle (.ask "C")
        = Prog.pure Falsifier.zeroAddr
      ∧ ((LDesc.provide (LDesc.provide eA eB) eC).build eCE).handle (.ask "C")
        ≠ ((LDesc.provide eA (LDesc.provide eB eC)).build eCE).handle (.ask "C") := by
  refine ⟨rfl, rfl, fun h => ?_⟩
  have h' : fwd "A" = (Prog.pure Falsifier.zeroAddr : Prog LayerSig Addr32) := h
  simp [fwd, Prog.op] at h'

/-- And `provideMerge` on the same witness agrees under both bracketings — the
`Handler.through` fragment keeps the algebra. -/
theorem provideMerge_agrees_on_the_same_witness :
    ((LDesc.provideMerge (LDesc.provideMerge eA eB) eC).build eCE).handle (.ask "C")
      = ((LDesc.provideMerge eA (LDesc.provideMerge eB eC)).build eCE).handle (.ask "C") :=
  rfl

/-! ### §4.7 Receipts for §4 -/

#print axioms mem_without
#print axioms provide_requires_mem
#print axioms provide_removes_supplied
#print axioms provide_keeps_unsupplied
#print axioms provide_removes_only_supplied
#print axioms provide_keeps_inner
#print axioms provides_of_provide
#print axioms provides_of_provideMerge
#print axioms without_append
#print axioms without_distrib
#print axioms provideMerge_provides_assoc
#print axioms provideMerge_requires_assoc
#print axioms provide_requires_not_assoc
#print axioms provideMerge_on_the_same_witness_is_assoc
#print axioms mergeOn_unique
#print axioms interpret_ask
#print axioms build_forwards_of_not_provides
#print axioms provideMerge_discharges
#print axioms provide_hides_the_inner
#print axioms provides_can_overclaim
#print axioms provide_is_not_associative_in_the_meaning
#print axioms provideMerge_agrees_on_the_same_witness

/-! ## §5 The floor, and the design running end to end

The tower leaves `Prog` EXACTLY ONCE, at one bottom handler. Scope is a
signature summand, so an acquiring layer is an ordinary layer and R18's "FORK A
must be restated per-layer" collapses to a single choice of target. -/

/-- R18's ruled target, at this design's state. -/
abbrev ScopeM := ExceptT Refusal (StateM ScopeState)

/-- The identification with §2's shape is definitional. -/
theorem ScopeM_is_Tgt (α : Type) : ScopeM α = Tgt ScopeState α := rfl

/-- The target is lawful, so every layer law of §3 instantiates here without
degradation. -/
example : LawfulMonad ScopeM := inferInstance

/-- Services nobody provides REFUSE. -/
def svcFloor : Handler SvcSig ScopeM :=
  ⟨fun | .ask _ => fun s => (.error (.failed "unmet service"), s)⟩

/-- Scope operations are §2's region machinery. -/
def scopeFloor (run : Blocks) : Handler ScopeSig ScopeM :=
  ⟨fun | .acquire a r => acquireT run a r
       | .scoped b => scopedT run (run b)⟩

/-- THE FLOOR — `Handler.sum`, the same operation that composes signatures. -/
def floorH (run : Blocks) : Handler LayerSig ScopeM :=
  Handler.sum svcFloor (scopeFloor run)

/-- Build the layer and run the program against it, at the floor. The `Monad`
instance comes from `ScopeM`; `Tgt ScopeState` is the same function type but is
not an instance target. -/
def launchM (run : Blocks) (l : Layer) (p : Prog LayerSig Addr32) : ScopeM Addr32 :=
  interpret (floorH run) (Layer.run l p)

/-- `launch`: build, run, ALL INSIDE ONE REGION. Derived — `Layer.run` and
`scopedT`, no new operation. -/
def launch (run : Blocks) (l : Layer) (p : Prog LayerSig Addr32) :
    Tgt ScopeState Addr32 :=
  scopedT run (launchM run l p)

/-- The same without the delimiter — the control for the leak theorem. -/
def unscopedLaunch (run : Blocks) (l : Layer) (p : Prog LayerSig Addr32) :
    Tgt ScopeState Addr32 :=
  launchM run l p

/-! ### §5.1 A worked system

`Db` is an ACQUIRING layer (acquire block 0, release block 1). `Pool` is an
ordinary layer that requires `Db` and acquires a resource of its own (blocks
2/3). The blocks are the §2.4 store programs, so the whole trace is readable off
the estate's own word. Note the two tables are disjoint by role: `CodeEnv` ids
name LAYER bodies (`Prog LayerSig`), `Blocks` ids name FLOOR blocks
(target computations). -/

def sysCE : CodeEnv
  | 7 => fwd "Db" >>= fun _ => Prog.op (S := LayerSig) (Sum.inr (ScopeE.acquire 2 3))
  | _ => Prog.pure Falsifier.zeroAddr

def dbDesc   : LDesc := .acquires "Db" [] 0 1
def poolDesc : LDesc := .leaf "Pool" ["Db"] 7
def sysDesc  : LDesc := .provideMerge dbDesc poolDesc

/-- The layer, built. `pure` because this system's build has no effect of its
own; a system whose build acquires is the §5.2 witness. -/
def sysLayer : Layer := pure (sysDesc.build sysCE)

def askPool : Prog LayerSig Addr32 := fwd "Pool"

def askPoolThenFail : Prog LayerSig Addr32 :=
  askPool >>= fun _ => Prog.op (S := LayerSig) (Sum.inr (ScopeE.scoped 4))

/-- The residual row of the composed system: `Db` is discharged by `provideMerge`,
both services are advertised, and the system is classified as ACQUIRING —
decidable on content, where rc.112's `Exclude<R, Scope.Scope>` hides it. -/
theorem sys_row :
    sysDesc.provides = ["Db", "Pool"]
      ∧ sysDesc.requires = []
      ∧ sysDesc.acquiring = true := ⟨rfl, rfl, rfl⟩

/-- **THE DESIGN, RUNNING.** Ask for `Pool`; the layer graph acquires `Db`
first, then `Pool`'s own resource; the region releases them LIFO. Every step is
a store admission in the estate's own word. -/
theorem launch_acquires_and_releases_LIFO :
    trace (launch demoBlocks sysLayer askPool ([], [])).2.1 = [0, 2, 3, 1] := by decide

/-- **THE SAME, ON THE FAILURE PATH.** The program refuses after both
acquisitions: both are still released, in the same LIFO order, and the refusal
is re-raised unchanged. This is the R18 law reaching all the way through a layer
composition. -/
theorem launch_releases_on_failure :
    (launch demoBlocks sysLayer askPoolThenFail ([], [])).1 = .error (.failed "boom")
      ∧ trace (launch demoBlocks sysLayer askPoolThenFail ([], [])).2.1
          = [0, 2, 3, 1] := ⟨rfl, by decide⟩

/-- **THE DELIMITER IS LOAD-BEARING.** Without the region the acquisitions
happen and NOTHING is released. A layer that acquires cannot be launched by
`build`-and-discard; `Layer.build : M (Handler S M)` hands back a handler with
no release site, which is why the delimiter is a separate operation and not a
bracket around the build. -/
theorem unscoped_launch_leaks :
    trace (unscopedLaunch demoBlocks sysLayer askPool ([], [])).2.1 = [0, 2] := by decide

/-! ### §5.2 The build step is real, and the honest observable is the stack

`Svc` alone — `Handler SvcSig (Prog LayerSig)`, the "layer is a handler" reading
— has no build. A layer whose `Prog LayerSig (·)` prefix is not `pure` acquires
ONCE however many times its service is used; the same service with the
acquisition inlined in the clause acquires PER USE, and owes a release per use. -/

/-- A layer whose BUILD acquires. The prefix is not `pure`. -/
def pooledLayer : Layer :=
  Prog.op (S := LayerSig) (Sum.inr (ScopeE.acquire 0 1)) >>= fun a =>
    pure (leafH "Db" (Prog.pure a))

/-- The same service with the acquisition INLINED in the clause — no build. -/
def inlinedLayer : Layer :=
  pure (leafH "Db" (Prog.op (S := LayerSig) (Sum.inr (ScopeE.acquire 0 1))))

def askDbTwice : Prog LayerSig Addr32 := fwd "Db" >>= fun _ => fwd "Db"

/-- Built once: ONE release owed. -/
theorem build_registers_one_finalizer :
    (unscopedLaunch demoBlocks pooledLayer askDbTwice ([], [])).2.2 = [1] := by decide

/-- Inlined: TWO releases owed, for two uses of one service. -/
theorem inlined_registers_two_finalizers :
    (unscopedLaunch demoBlocks inlinedLayer askDbTwice ([], [])).2.2 = [1, 1] := by decide

/-- **THE BUILD STEP IS OBSERVABLE**, and what it is observable IN is resource
lifetime: how many releases the region owes. -/
theorem build_step_is_observable :
    (unscopedLaunch demoBlocks pooledLayer askDbTwice ([], [])).2.2
      ≠ (unscopedLaunch demoBlocks inlinedLayer askDbTwice ([], [])).2.2 := by decide

/-- **AND THE STORE WORD ALONE CANNOT SEE IT.** `put` is word-idempotent, so the
two designs leave the SAME word: acquiring the same content twice is invisible
there. This is the requirements lane's "the memoization law is vacuous at
`ObsEq`" — a fact about ACQUISITION, not about sharing. The finalizer stack is
the observable that is not vacuous, because a release is owed per REGISTRATION.
Any future row that states a sharing or memoization law over the word alone is
stating a vacuity. -/
theorem the_word_alone_is_vacuous :
    trace (launch demoBlocks pooledLayer askDbTwice ([], [])).2.1
      = trace (launch demoBlocks inlinedLayer askDbTwice ([], [])).2.1 := by decide

/-! ### §5.3 Receipts for §5 -/

#print axioms ScopeM_is_Tgt
#print axioms sys_row
#print axioms launch_acquires_and_releases_LIFO
#print axioms launch_releases_on_failure
#print axioms unscoped_launch_leaks
#print axioms build_registers_one_finalizer
#print axioms inlined_registers_two_finalizers
#print axioms build_step_is_observable
#print axioms the_word_alone_is_vacuous

/-! ## §6 What is NOT modeled, and where the design fails

Stated as precisely as the checked part, because a hole named is worth more than
a hole hidden.

**1. `requires`-soundness against the builder — NOT PROVED, and it is the one
real gap in §4.** §4.4 proves the `provides` half (`build_forwards_of_not_provides`,
unconditional). The dual — `q ∉ d.requires` implies the built context never asks
`q` of the floor — is NOT here. It is not a type equation (that obstruction died
with the value-level keys); it is an induction over what an arbitrary block body
`ce b` may emit, so it needs a predicate `AsksOnly : List SvcKey → Prog LayerSig A
→ Prop` plus a well-formedness hypothesis tying each leaf's declared `needs` to
its body. Neither is written. Until it is, the emitted `RIn` rests on the row
alone in that direction.

**2. The bridge's converse is FALSE, not merely unproved.**
`provides_can_overclaim` exhibits two layers implementing each other's service
whose composite advertises `K` and forwards `K`. No check on the DESCRIPTION can
catch it: the bodies are opaque block references, so this is a property of the
code plane. A shipped `provides` row is therefore an ADVERTISEMENT, not a
guarantee — and that is a fact about content-addressed layer graphs in general,
not about this model.

**3. The floor is not stratified.** `scopeFloor` takes `run : Blocks`, i.e.
ALREADY-INTERPRETED blocks, so an acquisition block cannot itself ask for a
service — and most real acquiring layers depend on a config or a client. The
repair makes the floor self-referential and therefore fuel-bounded (the shape of
`EnsuringRepair.runBlocks`), and a fuel refusal is then indistinguishable from a
genuine refusal at the finalizer. Not built, not checked.

**4. No concurrency, no fibers, no interruption, no parallel scope.** Every
ordering theorem here is a theorem about a SEQUENTIAL fold. rc.112's
`Layer.mergeAll` opens a parallel scope, so `release_lifo` as the packet states
it carries a premise this model supplies silently. Declared, not discovered.

**5. `Layer.merge` with a build prefix is not lifted.** `mergeOn` and
`mergeOn_unique` are at the value plane and `LDesc.merge` is on content; the
layer-level `merge` and its (disjoint-key) laws are not stated. `Handler.sum` is
the WRONG operation for service merge — `Sig.sum` is disjoint where Effect's
merge overlaps last-wins — and `Handler.sum_unique` correspondingly does not
reach it, which is why `mergeOn_unique` is proved here from `Handler.ext`.
`Handler.sum` keeps its job composing LANGUAGES (`floorH`).

**6. The rows are pre-canonicalization.** The shipped `EmitLayer.residualOf`
runs `canonServices`, which ends in `List.mergeSort` and does not reduce in the
kernel. Every row theorem here is stated on plain `++`/`filter`, so restating
them under canonicalization turns list equalities into permutation-and-dedup
statements. Not attempted. The shadowing / commutation / idempotence /
address-stability facts are already proved in `Cas/Backend/Canon.lean` and are
not restated here.

**7. Nothing in `library/` was touched.** `LDesc` is a Lean-local model of
`Cas.Schema.SystemNode`; whether an added arm keeps
`#guard SystemNode.schemaCode.discriminated` (`Cas/Schema/System.lean:225`)
passing is untested, and the address-moving event an added arm costs is real.

**8. Finalizers here are total.** `scopedT_releases_on_success` carries the
premise that the drain succeeds — the one asymmetry the ruled repair also
carries (a REFUSING finalizer does replace a success). The witnesses in §2.4 and
§5 use finalizers that cannot fail, so the non-trivial half of
"runs-on-refusal-of-ANY-finalizer" is exercised only at the combinator level
(`ensuringExitT_runs_on_failure`, which has no premise on the finalizer's
outcome), never at a witness.

**9. The dynamic fragment is absent from the content plane.** `Layer.unwrap` is
`join` on the MEANING (`unwrap_is_join`, `rfl`), but `LDesc` has no `opaque` arm,
so `flatMap`/`suspend`/`catchCause` have no description here. `SystemNode`'s
`opaque` arm is the shipped answer and this model does not exercise it.

**10. `Layer.launch`'s laws.** `launch` is derived (`Layer.run` inside
`scopedT`) and no law is claimed for it beyond the region laws it inherits; its
real laws are blocked on the interruption bundle either way.
-/

/-! ## §7 Reuse ledger — which existing declaration carries which obligation

* `Prog`, `Handler`, `interpret`, `Sig`, `Sig.sum` — the carriers. UNCHANGED.
* `Handler.through` (`Cas/Lang/Tower.lean:65`) — IS `Svc.andThen`; no separate
  definition.
* `through_monoid` (`Cas/Backend/Universal.lean:785`) — DISCHARGES associativity
  and both identities, via the `lift` embedding into the endomorphism setting it
  is stated at. `andThen_assoc`, `andThen_id_right`, `andThen_id_left`.
* `interpret_through` (`Tower.lean:71`) — `Layer.provideMerge_assoc`,
  `Layer.run_provideMerge`.
* `interpret_bind` (`Cas/Lang/Handler.lean:53`) — carries the build past
  composition.
* `interpret_id` / `idHandler` (`Cas/Lang/Representation.lean:63,68`) —
  `lift_injSvc`, the unit laws, `Layer.run_empty`.
* `interpret_op` (`Representation.lean:115`) — `lift_hom`, `interpret_ask`, and
  through them the whole §4.4 bridge.
* `Handler.ext` (`Universal.lean:128`) — every uniqueness argument, including
  `mergeOn_unique`.
* `Handler.sum` (`Handler.lean:63`) — `lift` and the floor. Both are the SAME
  operation; nothing else composes languages here.
* `LawfulMonad (Prog S)` (`Representation.lean:54-58`) — `shared_is_bind`,
  `unwrap_is_join`, and every `bind_assoc`/`pure_bind` step.
* `referenceHandler` (`Handler.lean:75`) — the store blocks' meaning;
  `refHandlerW` is defined FROM it clause by clause.
* `Falsifier.lenAddr` / `zeroAddr` (`Cas/Lang/Wp.lean:747`) — the
  length-separating address function, so no digest is computed in the kernel.
* `Word`, `Binding`, `Node`, `Addr32`, `Refusal` — unchanged.
* `EnsuringRepair.ensuringT` and its four ruled laws — RE-DECLARED, not cited:
  staging is not importable. `ensuringExitT_diagonal` (`rfl`, axiom-free) makes
  the exit-indexed form conservative over the ruled one.

NEW LEMMAS, five, all short: `lift_injSvc`, `lift_hom`, `lift_inj`,
`interpret_ask`, `mergeOn_unique`. NEW ROW LEMMAS: `without_append`,
`without_distrib`. NOT MINTED: no `Layer` inductive, no `Scope` type, no
`MemoMap`, no `Runtime`, no `HHandler`, no `Sig.empty`, no `sigOf`, no change to
`Handler`/`Sig`/`Prog`.
-/

end Cas.Workshop.ScopeLayer
