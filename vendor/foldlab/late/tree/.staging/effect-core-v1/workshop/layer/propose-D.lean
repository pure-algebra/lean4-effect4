import Cas.Backend.Universal
import Cas.Backend.SumAlgebra

/-!
# Position D — `Layer` dissolved: the type is `Prog T (Handler S (Prog T))`

Scratch design probe for the Effect Core v1 layer pass. NOT a lake target,
adds nothing to `Cas`, edits nothing in `library/`.

Check: `cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/layer/propose-D.lean`
-/

namespace ProposeD

open Cas.Lang

/-! ## §0 — the type

No carrier is minted. `Layer` is an abbreviation over `Prog` and `Handler`,
both already in `library/cas`. It is `Prog` of `Handler` of `Prog`: a PROGRAM
in the lower language whose VALUE is a handler for the upper one.

The universes fit with nothing to arrange. `Handler : Sig → (Type → Type v) →
Type v`, so `Handler S (Prog T) : Type`, exactly where `interpret`'s
`{A : Type}` lives. -/

abbrev Layer (S T : Sig) : Type := Prog T (Handler S (Prog T))

/-- Interpretation of a pure program is `pure`. Definitional; named so `simp`
can use it. -/
@[simp] theorem interpret_pure [Monad M] (h : Handler S M) (a : A) :
    interpret h (pure a : Prog S A) = pure a := rfl

/-- `interpret_bind` (`Cas/Lang/Handler.lean:57`) restated at `>>=` rather than
`Prog.bind`, so `simp` can see it. Same proof term. -/
theorem interpret_bind' [Monad M] [LawfulMonad M] (h : Handler S M)
    (p : Prog S A) (f : A → Prog S B) :
    interpret h (p >>= f) = interpret h p >>= fun a => interpret h (f a) :=
  interpret_bind h p f

/-! ## §1 — every combinator, as a derived term

`build` is the identity function. That is the whole of position D: there is no
build STEP because a layer already IS the build. -/

/-- `build` — the identity. A layer is a program that returns an environment;
running it is running it. -/
def Layer.build (L : Layer S T) : Prog T (Handler S (Prog T)) := L

/-- `Layer.empty` — the syntactic identity handler, returned purely. -/
def Layer.empty : Layer S S := pure idHandler

/-- A non-acquiring layer: a handler, returned purely. This is the ONLY thing
`Handler S (Prog T)` can express, and §3 proves the gap. -/
def Layer.ofHandler (h : Handler S (Prog T)) : Layer S T := pure h

/-- `provide` — build once with `Prog.bind`, then `interpret`. The bind is
where the build happens; `interpret` dispatches every operation against the
handler the build produced. -/
def Layer.provide (L : Layer S T) (p : Prog S A) : Prog T A :=
  L >>= fun h => interpret h p

/-- `merge` — build both, then `Handler.sum`. The bind order IS the
acquisition order, so `merge` is sequential by construction. -/
def Layer.merge (L : Layer S T) (R : Layer U T) : Layer (S ⊕ₛ U) T :=
  L >>= fun h => R >>= fun g => pure (h.sum g)

/-- `andThen` / vertical composition — build the lower layer, transport the
upper layer's build through it (`interpret`), then transport its PAYLOAD
through it (`Handler.through`). `through` survives as the payload transport;
what it cannot do alone is the build, which is the outer `interpret`. -/
def Layer.andThen (L : Layer S T) (M : Layer T U) : Layer S U :=
  M >>= fun g => interpret g L >>= fun h => pure (h.through g)

/-! ## §2 — the category laws, discharged entirely by existing estate theorems

`Layer` with `andThen` and `empty` is a CATEGORY on signatures. Nothing below
is new mathematics: every step is `interpret_bind` (`Cas/Lang/Handler.lean:57`),
`interpret_through` (`Cas/Lang/Tower.lean:71`), `interpret_id`
(`Cas/Lang/Representation.lean:69`), `through_assoc`
(`Cas/Backend/Universal.lean:739`), `through_id_left` (`:765`),
`through_id_right` (`:757`), or `LawfulMonad (Prog S)`
(`Representation.lean:54`). -/

/-- `provide` through the empty layer is the program itself. -/
theorem provide_empty (p : Prog S A) : Layer.provide Layer.empty p = p :=
  interpret_id p

/-- **`build` is exactly what `through` erases.** Interpreting a `provide`
collapses to `Handler.through` precisely when the layer does not acquire.
Direct corollary of `interpret_through`. -/
theorem provide_ofHandler [Monad M] [LawfulMonad M]
    (h : Handler S (Prog T)) (g : Handler T M) (p : Prog S A) :
    interpret g (Layer.provide (Layer.ofHandler h) p)
      = interpret (h.through g) p :=
  interpret_through h g p

/-- On non-acquiring layers, `andThen` IS `Handler.through`, on the nose. -/
theorem andThen_ofHandler (h : Handler S (Prog T)) (g : Handler T (Prog U)) :
    Layer.andThen (Layer.ofHandler h) (Layer.ofHandler g)
      = Layer.ofHandler (h.through g) := rfl

/-- Right unit. -/
theorem andThen_empty_right (L : Layer S T) :
    Layer.andThen L (Layer.empty (S := T)) = L := by
  simp only [Layer.andThen, Layer.empty, pure_bind, interpret_id,
    through_id_right, bind_pure]


/-- Left unit. `through_id_left` at `M := Prog U`, whose right-unit equation
is free from `LawfulMonad (Prog U)`. -/
theorem andThen_empty_left (M : Layer S U) :
    Layer.andThen (Layer.empty (S := S)) M = M := by
  simp only [Layer.andThen, Layer.empty, interpret_pure, pure_bind,
    through_id_left rightUnit_of_lawful, bind_pure]

/-- **Associativity.** The build order comes out identical on both sides —
`N`, then `M` transported through `N`, then `L` transported through both — and
the residue is exactly `through_assoc`. Layer composition's associativity is a
theorem the estate ALREADY HAS; this proof adds no lemma of its own. -/
theorem andThen_assoc (L : Layer S T) (M : Layer T U) (N : Layer U V) :
    Layer.andThen (Layer.andThen L M) N
      = Layer.andThen L (Layer.andThen M N) := by
  simp only [Layer.andThen, interpret_bind', bind_assoc, interpret_pure,
    pure_bind, interpret_through]
  refine bind_congr fun n => ?_
  refine bind_congr fun g => ?_
  refine bind_congr fun h => ?_
  exact congrArg pure
    (through_assoc leftUnit_of_lawful bindAssoc_of_lawful h g n)

/-! ### merge's universal property, transported

`Handler.sum_unique` (`Cas/Backend/SumAlgebra.lean:212`) is merge's universal
property at the HANDLER. Under position D `merge` is `sum` under two binds, so
the property transports to the layer with no new content: two non-acquiring
layers merge to the unique handler agreeing with both. -/

theorem merge_ofHandler_unique
    (h : Handler S (Prog T)) (g : Handler U (Prog T))
    (k : Handler (S ⊕ₛ U) (Prog T))
    (hl : ∀ op, k.handle (Sum.inl op) = h.handle op)
    (hr : ∀ op, k.handle (Sum.inr op) = g.handle op) :
    Layer.merge (Layer.ofHandler h) (Layer.ofHandler g) = Layer.ofHandler k := by
  show (pure (h.sum g) : Layer (S ⊕ₛ U) T) = pure k
  exact congrArg pure (Handler.sum_unique h g k hl hr).symm

/-- Provision through a merged pair of non-acquiring layers projects to the
left component — `interpret_inl`, transported. -/
theorem provide_merge_inl
    (h : Handler S (Prog T)) (g : Handler U (Prog T)) (p : Prog S A) :
    Layer.provide (Layer.merge (Layer.ofHandler h) (Layer.ofHandler g))
        (Prog.inl (T := U) p)
      = Layer.provide (Layer.ofHandler h) p :=
  interpret_inl h g p

/-- …and to the right. -/
theorem provide_merge_inr
    (h : Handler S (Prog T)) (g : Handler U (Prog T)) (q : Prog U A) :
    Layer.provide (Layer.merge (Layer.ofHandler h) (Layer.ofHandler g))
        (Prog.inr (S := S) q)
      = Layer.provide (Layer.ofHandler g) q :=
  interpret_inr h g q

/-! ## §3 — `Handler S (Prog T)` is NOT a layer: the build falsifier

The estate ground report's objection, answered by exhibiting the gap as a
kernel-checked inequality rather than arguing it away. A layer whose
acquisition precedes its answers pays the acquisition ONCE under `provide` and
ONCE PER OPERATION under `through` — and `provide_ofHandler` says `through` is
precisely the build-erased case. -/

section Falsifier

/-- Upper signature: one operation, `use`. -/
inductive UpE where | use
  deriving DecidableEq
abbrev UpE.Ans : UpE → Type | .use => Unit
def UpSig : Sig := ⟨UpE, UpE.Ans⟩

/-- Lower signature: acquire a handle; touch one. -/
inductive LoE where | acq | touch (n : Nat)
  deriving DecidableEq
abbrev LoE.Ans : LoE → Type | .acq => Nat | .touch _ => Unit
def LoSig : Sig := ⟨LoE, LoE.Ans⟩

/-- The counting target: `(acquisitions, touches)`. -/
def counting : Handler LoSig (StateM (Nat × Nat)) where
  handle
    | .acq => fun s => (s.1, (s.1 + 1, s.2))
    | .touch _ => fun s => ((), (s.1, s.2 + 1))

/-- A pool layer: acquire ONE handle in the build, answer every `use` with it. -/
def poolL : Layer UpSig LoSig :=
  .vis .acq (fun n => .pure ⟨fun _ => .vis (.touch n) .pure⟩)

/-- The build-erased handler: the only `Handler UpSig (Prog LoSig)` doing the
same work. It has nowhere to put the acquisition but inside the clause. -/
def perOpH : Handler UpSig (Prog LoSig) where
  handle | .use => .vis .acq (fun n => .vis (.touch n) .pure)

/-- A consumer performing two operations. -/
def twoUses : Prog UpSig Unit := .vis .use (fun _ => .vis .use .pure)

/-- The layer acquires once and touches twice. -/
theorem pool_acquires_once :
    (interpret counting (Layer.provide poolL twoUses) (0, 0)).2 = (1, 2) := rfl

/-- The build-erased handler acquires twice. -/
theorem perOp_acquires_twice :
    (interpret counting (interpret perOpH twoUses) (0, 0)).2 = (2, 2) := rfl

/-- …and that second run IS `Handler.through`, by `interpret_through`. -/
theorem perOp_is_through :
    interpret counting (interpret perOpH twoUses)
      = interpret (perOpH.through counting) twoUses :=
  interpret_through perOpH counting twoUses

/-- **THE FALSIFIER.** `Handler S (Prog T)` cannot be `Layer`: composing with
`Handler.through` inlines the build, and the difference is observable in the
target. `Prog T (Handler S (Prog T))` is the smallest fix, and it mints no
carrier. -/
theorem through_erases_the_build :
    (interpret counting (Layer.provide poolL twoUses) (0, 0)).2
      ≠ (interpret (perOpH.through counting) twoUses (0, 0)).2 := by
  rw [← perOp_is_through]
  decide

end Falsifier

/-! ## §4 — sharing: `merge` duplicates the build, and content-addressing hides it

`Layer.memoize` is not a combinator here, and `MemoMap` is not a carrier. The
memo question is a QUOTIENT question: `merge L L` builds `L` twice, and that is
observable in a target that counts. It stops being observable exactly when the
acquisition is idempotent in the observation — which on the CAS plane is `put`'s
word-idempotence, not a fact about memoization. -/

section Sharing

open Falsifier

/-- Building the same layer twice acquires twice. Sharing is NOT free. -/
theorem merge_acquires_twice :
    (interpret counting (Layer.merge poolL poolL >>= fun _ => Prog.pure ())
      (0, 0)).2 = (2, 0) := rfl

/-- An idempotent acquisition: the second `acq` changes nothing observable —
the shape `put` has on a resident node. -/
def idemCounting : Handler LoSig (StateM (Nat × Nat)) where
  handle
    | .acq => fun s => ((0 : Nat), (min 1 (s.1 + 1), s.2))
    | .touch _ => fun s => ((), (s.1, s.2 + 1))

/-- **Sharing is a semantic equality exactly when acquisition is idempotent in
the observation.** Under `idemCounting` the duplicated build is invisible; no
memo map, no reference key, no `Layer.memoize`. -/
theorem sharing_is_free_under_idempotent_acquisition :
    (interpret idemCounting (Layer.merge poolL poolL >>= fun _ => Prog.pure ())
      (0, 0)).2
      = (interpret idemCounting (poolL >>= fun _ => Prog.pure ()) (0, 0)).2 := rfl

/-- And it is NOT free otherwise — the same expression separates under a
counting acquisition. So "memoize" names a quotient that holds on one plane and
fails on another; it is not a law of `Layer`. -/
theorem sharing_is_not_free_in_general :
    (interpret counting (Layer.merge poolL poolL >>= fun _ => Prog.pure ())
      (0, 0)).2
      ≠ (interpret counting (poolL >>= fun _ => Prog.pure ()) (0, 0)).2 := by
  decide

end Sharing

/-! ## §5 — Scope: the finalizer is a HANDLER CLAUSE, never a `Prog.bind`

R18 / `EC1-CE045` reach this design directly, and the reach is checked here at
the layer level rather than assumed. The two facts:

- **A.** `Layer.provide L p >>= fin` does not run `fin` when `p` refuses.
  `Prog.bind` is refusal-strict, so *no* layer combinator built from binds can
  finalize. Position D does not repair this and must not pretend to.
- **B.** The repair is `EnsuringRepair`'s `ensuringT`, transplanted: a
  combinator on TARGET values, installed as the clause of a scope operation.
  The target here has the R18 order — state OUTSIDE error — so the log survives
  the refusal.

The consequence for position D is exact and is stated as a limit, not a
feature: **`Layer` dissolves; `Scope` does not.** `Scope` stays a signature
whose operations are first-order and whose meaning is a handler clause. -/

section Scope

/-- The R18 target order, in miniature: `ExceptT` OUTSIDE `StateM`, so the log
survives the error branch. `ExceptT String (StateM (List String)) A` unfolds to
`List String → Except String A × List String`. -/
abbrev RM := ExceptT String (StateM (List String))

/-- Base signature: acquire (logged), work (logged), refuse. -/
inductive BE where | acquire | work (s : String) | fail
  deriving DecidableEq
abbrev BE.Ans : BE → Type | .acquire => Nat | .work _ => Unit | .fail => Empty
def BSig : Sig := ⟨BE, BE.Ans⟩

def baseH : Handler BSig RM where
  handle
    | .acquire => fun l => (.ok l.length, l ++ ["acquire"])
    | .work s => fun l => (.ok (), l ++ [s])
    | .fail => fun l => (.error "refused", l)

/-- The consumer's signature: one operation. -/
inductive CE where | step
  deriving DecidableEq
abbrev CE.Ans : CE → Type | .step => Unit
def CSig : Sig := ⟨CE, CE.Ans⟩

/-- A resource layer: acquire in the build, then serve. -/
def resourceL : Layer CSig BSig :=
  .vis .acquire (fun _ => .pure ⟨fun _ => .vis (.work "use") .pure⟩)

/-- A consumer that refuses partway. -/
def failing : Prog CSig Unit := .vis .step (fun _ => .vis .step .pure)

/-- The release program. -/
def release : Prog BSig Unit := .vis (.work "release") .pure

/-- A body that refuses: use the resource, then fail. -/
def bodyThatFails : Prog CSig Unit :=
  .vis .step (fun _ => .pure ())

def usingThenFail : Prog BSig Unit :=
  Layer.provide resourceL bodyThatFails >>= fun _ =>
    (.vis .fail (fun e => e.elim) : Prog BSig Unit)

/-- **FACT A — the layer-level restatement of `EC1-CE045`.** Sequencing the
release after a `provide` with `Prog.bind` loses it on the refusal path: the log
shows the acquire and the use, and NO release. -/
theorem provide_bind_release_skips_the_release :
    (interpret baseH (usingThenFail >>= fun _ => release) []).2
      = ["acquire", "use"] := rfl

/-- …and the refusal is reported, so the loss is not an artefact of the log. -/
theorem provide_bind_release_refuses :
    (interpret baseH (usingThenFail >>= fun _ => release) []).1
      = .error "refused" := rfl

/-- `ensuringT`, transplanted from
`workshop/counterexamples/EnsuringRepair.lean:547` and re-typed at this target.
It is a combinator on TARGET VALUES; `Handler` and `Sig` are untouched. -/
def ensT (body fin : RM A) : RM A := fun l =>
  match body l with
  | (.ok a, l₁) =>
    match fin l₁ with
    | (.ok _, l₂) => (.ok a, l₂)
    | (.error r, l₂) => (.error r, l₂)
  | (.error r, l₁) => (.error r, (fin l₁).2)

/-- **FACT B — the repair, at the layer.** With the release installed as a
target-level clause the log carries it on the refusal path, and the refusal is
preserved. -/
theorem ensT_release_runs_on_refusal :
    (ensT (interpret baseH usingThenFail) (interpret baseH release) []).2
      = ["acquire", "use", "release"] := rfl

theorem ensT_never_replaces_the_refusal :
    (ensT (interpret baseH usingThenFail) (interpret baseH release) []).1
      = .error "refused" := rfl

/-- And on the success path the release still runs, with the body's own value
preserved. -/
def usingOnly : Prog BSig Unit := Layer.provide resourceL bodyThatFails

theorem ensT_release_runs_on_success :
    (ensT (interpret baseH usingOnly) (interpret baseH release) []).2
      = ["acquire", "use", "release"] := rfl

/-- **The limit, stated as an inequality.** No `Prog.bind` sequencing agrees
with the scoped clause. The scope operation is therefore irreducible: it is not
sugar over `bind`, and position D does NOT dissolve it. -/
theorem scope_is_not_bind :
    (interpret baseH (usingThenFail >>= fun _ => release) []).2
      ≠ (ensT (interpret baseH usingThenFail) (interpret baseH release) []).2 := by
  decide

end Scope

/-! ## §6 — `launch`, derived

`launch` is `build` followed by suspension. It is one line over the type, it
mints nothing, and its LAWS are blocked on the interruption bundle (S10), so it
belongs in the derived surface, not beside `build`. `never` is a `vis` node
whose answer type is empty — `EC1-CE003`'s frontier arm, not a refusal. -/

section Launch

inductive SuspE where | forever
abbrev SuspE.Ans : SuspE → Type | .forever => Empty
def SuspSig : Sig := ⟨SuspE, SuspE.Ans⟩

def neverP : Prog SuspSig A := .vis .forever (fun e => e.elim)

/-- `launch` is `build >>= fun _ => never`, at the signature sum. One line, no
carrier, no law claimed. -/
def Layer.launch (L : Layer S T) : Prog (T ⊕ₛ SuspSig) A :=
  Prog.inl (L >>= fun _ => Prog.pure ()) >>= fun _ => Prog.inr neverP

end Launch

/-! ## §8 — R18's floor, moved: scope belongs in the SIGNATURE, not the target

R18's last paragraph is the packet's open seam: `Handler.through`'s middle must
be `Prog T`-valued, so a layer whose handler targets `ReaderT EnvR RefW` cannot
be a composition middle, and FORK A has to be restated per layer.

Position D's answer is R10 doing its job. Put the scope operations in the
SIGNATURE `T`, not in the target monad. Then a scoped layer is an ordinary
`Layer S T`, composes with `andThen` like any other, and the whole tower has ONE
floor: a single handler out of `... ⊕ₛ ScopeSig` into the R18 target. The scoped
layer stops being a special case and the per-layer FORK A restatement collapses
back to a single global choice.

What that needs is one lemma: an intermediate layer must pass scope operations
through untouched. It does, and the injection handler that does it is one line
over `Prog.vis`. -/

section Floor

/-- Re-emit every operation into the left of a sum. `idHandler` with an
injection; no carrier. -/
def injHandler : Handler S (Prog (S ⊕ₛ T)) where
  handle op := Prog.inl (Prog.op op)

/-- Interpreting through `injHandler` IS `Prog.inl` — the same proof shape as
`interpret_id` (`Cas/Lang/Representation.lean:69`). -/
theorem interpret_injHandler (p : Prog S A) :
    interpret (injHandler (S := S) (T := T)) p = Prog.inl p := by
  induction p with
  | pure a => rfl
  | vis op k ih =>
    show Prog.bind (Prog.inl (Prog.op op)) _ = _
    simp only [Prog.op, Prog.inl, Prog.bind]
    exact congrArg (Prog.vis (Sum.inl op)) (funext fun a => ih a)

/-- **The floor lemma.** An intermediate layer that handles its own operations
and injects the scope operations leaves every scope operation intact. So a
scoped layer composes through arbitrarily many `andThen`s, and the scope
operations reach the single bottom handler unchanged. -/
theorem scope_survives_composition
    (g : Handler B (Prog (Sc ⊕ₛ B'))) (p : Prog Sc A) :
    interpret (Handler.sum (injHandler (S := Sc) (T := B')) g) (Prog.inl p)
      = Prog.inl p := by
  rw [interpret_inl]
  exact interpret_injHandler p

/-- The layer form: a scoped layer, transported by `andThen` through a
passthrough layer, still emits its scope operations. -/
theorem scoped_layer_andThen_preserves_scope
    (L : Layer S (Sc ⊕ₛ B)) (g : Handler B (Prog (Sc ⊕ₛ B')))
    (h : Handler S (Prog (Sc ⊕ₛ B)))
    (hL : L = Layer.ofHandler h) :
    Layer.andThen L (Layer.ofHandler
        (Handler.sum (injHandler (S := Sc) (T := B')) g))
      = Layer.ofHandler
          (h.through (Handler.sum (injHandler (S := Sc) (T := B')) g)) := by
  subst hL; rfl

end Floor

end ProposeD


/-! ## §7 — receipts -/

section Receipts
open ProposeD
#print axioms provide_empty
#print axioms provide_ofHandler
#print axioms andThen_ofHandler
#print axioms andThen_empty_right
#print axioms andThen_empty_left
#print axioms andThen_assoc
#print axioms merge_ofHandler_unique
#print axioms provide_merge_inl
#print axioms provide_merge_inr
#print axioms pool_acquires_once
#print axioms perOp_acquires_twice
#print axioms perOp_is_through
#print axioms through_erases_the_build
#print axioms merge_acquires_twice
#print axioms sharing_is_free_under_idempotent_acquisition
#print axioms sharing_is_not_free_in_general
#print axioms provide_bind_release_skips_the_release
#print axioms provide_bind_release_refuses
#print axioms ensT_release_runs_on_refusal
#print axioms ensT_never_replaces_the_refusal
#print axioms ensT_release_runs_on_success
#print axioms scope_is_not_bind
#print axioms interpret_injHandler
#print axioms scope_survives_composition
#print axioms scoped_layer_andThen_preserves_scope
end Receipts
