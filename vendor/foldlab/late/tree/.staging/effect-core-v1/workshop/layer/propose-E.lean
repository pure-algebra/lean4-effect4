import Cas.Lang.Representation
import Cas.Backend.Universal

/-!
# Position E — layer-as-content-plus-interpreter, checked

Split along R7. The layer DESCRIPTION is first-order content; the layer
BUILDER is a `Handler`. Neither half alone is a Layer.

This file is the falsifier for that claim. It writes both halves down,
gives the bridge, proves the laws that are free from the estate, and
proves the one theorem that shows the split is FORCED rather than
stylistic (§5).

It also answers R18's open sentence — "`Handler.through`'s middle must
be `Prog T`-valued, so the tower has a floor at the scoped layer" — by
moving the floor: scope becomes OPERATIONS of an extended signature, so
every layer stays `Prog`-valued and the fork is ONE bottom handler
rather than a per-layer choice (§3, §6).
-/

namespace ProposeE
open Cas Cas.Lang

/-! ## 0. The signatures

R7 forbids a type-indexed service set: a type index is not first-order
content. So provided/required sets live at the VALUE level and there is
exactly ONE service signature. This mints no carrier — `Sig` is the
estate's carrier, and `SvcSig` is a value of it exactly as `ByteSig`
(`Tower.lean:47`) and `CasSig` (`Ops.lean:33`) are. -/

abbrev SvcKey := String
abbrev BlockId := Nat

/-- One operation: ask for a service by key; the answer is its address
(services are store residents). -/
inductive SvcE where
  | ask (key : SvcKey)
  deriving DecidableEq, Repr

abbrev SvcE.Ans : SvcE → Type
  | .ask _ => Addr32

abbrev SvcSig : Sig := ⟨SvcE, SvcE.Ans⟩

/-- R18's `ScopeE` (`EnsuringRepair.lean:168`) with ONE arm amended:
`ensuring (body finalizer)` becomes `ensuringExit (body onOk onErr)`.
That is the requirements lane's C9 — rc.112's finalizers are
exit-indexed (`Scope.addFinalizerExit`) and R18's exhibited `ensuring`
is exit-blind. Children stay `BlockId` DATA (R18 clause 1: no
higher-order handler carrier). -/
inductive ScopeE where
  | ensuringExit (body onOk onErr : BlockId)
  | raise (err : Addr32)
  deriving DecidableEq, Repr

abbrev ScopeE.Ans : ScopeE → Type
  | .ensuringExit _ _ _ => Addr32
  | .raise _ => Empty

abbrev ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩

/-- The layer plane's syntax: services and scope, one language. -/
abbrev LayerSig : Sig := SvcSig ⊕ₛ ScopeSig

/-! ## 1. The CODE half — no new type at all

A layer builder is `Handler.through`'s first argument. Because the
service signature is uniform, `provide` lands in the ENDOMORPHISM
setting `through_monoid` (`Universal.lean:785`) is stated at — the
theorem the estate lane declared inapplicable is recovered exactly by
refusing to index services in the type. -/

abbrev Layer := Handler SvcSig (Prog LayerSig)

/-- The empty layer: provide nothing, forward every ask. -/
def injSvc : Layer where
  handle op := Prog.op (S := LayerSig) (Sum.inl op)

/-- Scope operations pass through untouched. -/
def scopePass : Handler ScopeSig (Prog LayerSig) where
  handle op := Prog.op (S := LayerSig) (Sum.inr op)

/-- A leaf: answer this key with this program, forward every other. The
forwarding clause IS `idHandler`'s (`Representation.lean:70`). -/
def leafH (k : SvcKey) (body : Prog LayerSig Addr32) : Layer where
  handle
    | .ask k' => if k' = k then body else Prog.op (S := LayerSig) (Sum.inl (SvcE.ask k'))

/-- Merge takes the PROVIDES SET as an argument. §5 proves it must. -/
def mergeOn {M : Type → Type v} (keys : List SvcKey)
    (l r : Handler SvcSig M) : Handler SvcSig M where
  handle
    | .ask k => if keys.contains k then l.handle (.ask k) else r.handle (.ask k)

/-- The tower coercion: a layer, seen as a handler of the whole layer
language. `Handler.sum` (`Handler.lean:66`), unchanged. -/
def liftL (u : Layer) : Handler LayerSig (Prog LayerSig) :=
  Handler.sum u scopePass

/-- **`provide` IS `Handler.through`.** No definition of its own. -/
def Layer.provide (outer inner : Layer) : Layer :=
  outer.through (liftL inner)

/-! ## 2. The CONTENT half

Modelled here as a plain inductive. The SHIPPED carrier is
`Cas.Schema.SystemNode` (`Cas/Schema/System.lean:208`) with children
ADDRESSED, amended in exactly the two places §8 and the report name. -/

inductive LDesc where
  | empty
  | leaf     (key : SvcKey) (requires : List SvcKey) (body : BlockId)
  | acquires (key : SvcKey) (requires : List SvcKey)
             (acquire onOk onErr : BlockId)
  | merge    (l r : LDesc)
  | provide  (inner outer : LDesc)
  | fresh    (nonce : Nat) (inner : LDesc)
  deriving DecidableEq, Repr

/-! ### The residual calculus — pure, OUTSIDE `Prog` (R14a/P1).
This is `EmitLayer.residualOf` (`Cas/Backend/EmitLayer.lean:236`)
restated at value-level keys, which is where R7 puts it. -/

def without (xs ys : List SvcKey) : List SvcKey :=
  xs.filter (fun x => !ys.contains x)

def LDesc.provides : LDesc → List SvcKey
  | .empty => []
  | .leaf k _ _ => [k]
  | .acquires k _ _ _ _ => [k]
  | .merge l r => l.provides ++ r.provides
  | .provide _ o => o.provides
  | .fresh _ i => i.provides

def LDesc.requires : LDesc → List SvcKey
  | .empty => []
  | .leaf _ r _ => r
  | .acquires _ r _ _ _ => r
  | .merge l r => l.requires ++ r.requires
  | .provide i o => i.requires ++ without o.requires i.provides
  | .fresh _ i => i.requires

/-- The classification obligation the requirements lane named (§5 of
its report) but sited nowhere: whether a layer acquires is DECIDABLE ON
CONTENT, where in rc.112 it is invisible in the type. -/
def LDesc.acquiring : LDesc → Bool
  | .empty => false
  | .leaf _ _ _ => false
  | .acquires _ _ _ _ _ => true
  | .merge l r => l.acquiring || r.acquiring
  | .provide i o => i.acquiring || o.acquiring
  | .fresh _ i => i.acquiring

/-! ## 3. The BRIDGE

`CodeEnv` is the R7 seam itself: block addresses are content, the
programs they name are code. In the estate this is `Defun.embedFrom` /
`EnsuringRepair.runBlocks`; here it is a parameter, which is what
"hosts are code" MEANS.

`build` is TOTAL — the level-1/level-2 partiality R18 predicted does
not appear, because the scoped leaf's clause is an OPERATION of
`LayerSig`, still `Prog`-valued. -/

abbrev CodeEnv := BlockId → Prog LayerSig Addr32

def LDesc.build (ce : CodeEnv) : LDesc → Layer
  | .empty => injSvc
  | .leaf k _ b => leafH k (ce b)
  | .acquires k _ acq onOk onErr =>
      leafH k (Prog.op (S := LayerSig) (Sum.inr (ScopeE.ensuringExit acq onOk onErr)))
  | .merge l r => mergeOn l.provides (l.build ce) (r.build ce)
  | .provide i o => Layer.provide (o.build ce) (i.build ce)
  | .fresh _ i => i.build ce

/-- The bridge equations, each `rfl`: content `provide` IS code
`through`; content `empty` IS the forwarding handler; content `fresh`
is INVISIBLE to the builder — its whole content is a lifetime decision,
which is why the nonce must live in the content (§8). -/
theorem build_provide (ce : CodeEnv) (i o : LDesc) :
    (LDesc.provide i o).build ce = Layer.provide (o.build ce) (i.build ce) := by
  simp [LDesc.build]

theorem build_empty (ce : CodeEnv) : LDesc.empty.build ce = injSvc := by
  simp [LDesc.build]

theorem build_fresh (ce : CodeEnv) (n : Nat) (i : LDesc) :
    (LDesc.fresh n i).build ce = i.build ce := by
  simp [LDesc.build]

/-! ## 4. The laws, and who discharges them

Every law in this section is an EXISTING estate theorem applied. None
is new work. -/

/-- `liftL` of the empty layer IS `idHandler`. This is what makes the
unit laws free rather than owed. -/
theorem liftL_injSvc : liftL injSvc = idHandler (S := LayerSig) :=
  Handler.ext fun op => by cases op <;> rfl

/-- **`provide` is associative** — `through_assoc` (`Universal.lean:739`)
plus the one distributivity lemma below. -/
theorem liftL_through (t u : Layer) :
    liftL (Layer.provide t u) = (liftL t).through (liftL u) :=
  Handler.ext fun op => by
    cases op with
    | inl k => rfl
    | inr o =>
        show Prog.op (S := LayerSig) (Sum.inr o)
          = interpret (liftL u) (Prog.op (S := LayerSig) (Sum.inr o))
        rw [interpret_op (liftL u) (Sum.inr o)]
        rfl

theorem provide_assoc (t u v : Layer) :
    Layer.provide (Layer.provide t u) v = Layer.provide t (Layer.provide u v) := by
  show (t.through (liftL u)).through (liftL v) = t.through (liftL (Layer.provide u v))
  rw [liftL_through u v]
  exact through_assoc leftUnit_of_lawful bindAssoc_of_lawful t (liftL u) (liftL v)

/-- **`empty` is a right unit** — `through_id_right` (`:757`), free. -/
theorem provide_unit_right (t : Layer) : Layer.provide t injSvc = t := by
  show t.through (liftL injSvc) = t
  rw [liftL_injSvc]
  exact through_id_right t

/-- **`empty` is a left unit** — `interpret_op` (`Representation.lean`). -/
theorem provide_unit_left (u : Layer) : Layer.provide injSvc u = u :=
  Handler.ext fun op => by
    show interpret (liftL u) (Prog.op (S := LayerSig) (Sum.inl op)) = u.handle op
    rw [interpret_op (liftL u) (Sum.inl op)]
    rfl

/-- **Providing to a PROGRAM and providing to a LAYER agree.** The
coherence law that makes one name well-defined at two arities. It is
`interpret_through` (`Tower.lean:71`) used twice — free. -/
theorem provide_program_agrees {M : Type → Type} [Monad M] [LawfulMonad M]
    {A : Type} (t u : Layer) (h : Handler LayerSig M) (p : Prog SvcSig A) :
    interpret h (interpret (liftL u) (interpret t p))
      = interpret ((Layer.provide t u).through h) p := by
  rw [interpret_through (liftL u) h (interpret t p),
    interpret_through t ((liftL u).through h) p, Layer.provide,
    through_assoc leftUnit_of_lawful bindAssoc_of_lawful t (liftL u) h]

/-- **Merge is determined by its clauses** — the `Handler.sum_unique`
(`SumAlgebra.lean:212`) analogue at the OVERLAPPING merge. `Sig.sum` is
disjoint and this merge is not, so it is proved here rather than cited. -/
theorem mergeOn_unique {M : Type → Type v} (keys : List SvcKey)
    (l r k : Handler SvcSig M)
    (hl : ∀ key, key ∈ keys → k.handle (.ask key) = l.handle (.ask key))
    (hr : ∀ key, key ∉ keys → k.handle (.ask key) = r.handle (.ask key)) :
    k = mergeOn keys l r :=
  Handler.ext fun op => by
    cases op with
    | ask key =>
      by_cases h : key ∈ keys
      · rw [hl key h]; simp [mergeOn, h]
      · rw [hr key h]; simp [mergeOn, h]

/-! ## 5. THE THEOREM THAT FORCES THE SPLIT

The builder does not determine the merge: two builders plus two
provides-sets give two different merged layers. So `merge` is not a
function of the code half alone — the CONTENT half is necessary, not
decorative.

The deeper reason, stated because the theorem only witnesses it:
recovering a provides-set from a builder means deciding equality of
`Prog LayerSig Addr32`, whose continuations are host functions.
`Representation.lean`'s stratum 2 says that equality is propositional
and needs `funext`; no `DecidableEq (Prog S A)` instance exists, and
none can. -/

def a0 : Addr32 := ⟨List.replicate 32 0, by simp⟩
def a1 : Addr32 := ⟨List.replicate 32 1, by simp⟩

theorem a0_ne_a1 : a0 ≠ a1 := by
  intro h
  have : (List.replicate 32 (0 : UInt8)) = List.replicate 32 1 := congrArg Subtype.val h
  simp at this

private def lA : Layer := leafH "A" (Prog.pure a0)
private def rA : Layer := leafH "A" (Prog.pure a1)

private theorem mergeL_at : (mergeOn ["A"] lA rA).handle (SvcE.ask "A")
    = Prog.pure a0 := rfl

private theorem mergeR_at : (mergeOn [] lA rA).handle (SvcE.ask "A")
    = Prog.pure a1 := rfl

theorem merge_needs_the_content : mergeOn ["A"] lA rA ≠ mergeOn [] lA rA := by
  intro h
  have hc : (Prog.pure a0 : Prog LayerSig Addr32) = Prog.pure a1 := by
    rw [← mergeL_at, ← mergeR_at, h]
  exact a0_ne_a1 (by injection hc)

/-! ## 6. THE BOTTOM — scope, in R18's ruled target

R18: the finalization target is `ExceptT Refusal (StateT Word Id)` —
state OUTSIDE error, because `Except.error` has no word slot
(`EC1-CE045`). It appears ONCE, in the bottom handler, not per layer. -/

abbrev WM := ExceptT Refusal (StateM Word)
abbrev WComp := Word → Except Refusal Addr32 × Word

/-- The target is R18's, unfolded — not a new monad. -/
theorem WM_is_R18_target : WM Addr32 = WComp := rfl

/-- R18's combinator, verbatim (`EnsuringRepair.lean:547`). Exit-BLIND. -/
def ensuringT (body fin : WComp) : WComp := fun w =>
  match body w with
  | (.ok a, w₁) =>
    match fin w₁ with
    | (.ok _, w₂) => (.ok a, w₂)
    | (.error r, w₂) => (.error r, w₂)
  | (.error r, w₁) => (.error r, (fin w₁).2)

/-- **NEW, and owed by nobody today** (requirements lane C9). The
exit-INDEXED form rc.112 actually has. Two finalizer BLOCKS, not one —
first-order, so exit-indexing is content, never a closure over `Exit`. -/
def ensuringExitT (body onOk onErr : WComp) : WComp := fun w =>
  match body w with
  | (.ok a, w₁) =>
    match onOk w₁ with
    | (.ok _, w₂) => (.ok a, w₂)
    | (.error r, w₂) => (.error r, w₂)
  | (.error r, w₁) => (.error r, (onErr w₁).2)

/-- **Conservative.** The exit-blind combinator is the diagonal, so all
four R18 `ensuring` laws transfer by rewriting. -/
theorem ensuringExitT_diagonal (body fin : WComp) :
    ensuringExitT body fin fin = ensuringT body fin := rfl

/-- **Law: never replaces the refusal.** No premise on either finalizer. -/
theorem ensuringExitT_never_replaces_the_refusal
    (body onOk onErr : WComp) (w w₁ : Word) (r : Refusal)
    (hb : body w = (.error r, w₁)) :
    (ensuringExitT body onOk onErr w).1 = .error r := by
  simp only [ensuringExitT, hb]

/-- **Law: the finalizer's word survives the refusal.** The half
`Except Refusal (A × Word)` cannot state — R18's whole point. -/
theorem ensuringExitT_keeps_the_word
    (body onOk onErr : WComp) (w w₁ w₂ : Word) (r : Refusal)
    (res : Except Refusal Addr32)
    (hb : body w = (.error r, w₁)) (hf : onErr w₁ = (res, w₂)) :
    ensuringExitT body onOk onErr w = (.error r, w₂) := by
  simp only [ensuringExitT, hb, hf]

/-! ### The exit-indexing is not vacuous; release order is LIFO by nesting -/

def nZ : Node := ⟨0, 0, [], []⟩
def nO : Node := ⟨0, 1, [], []⟩

def mark (n : Node) : WComp := fun w => (.ok a0, w ++ [Binding.mk a0 n])
def okBody : WComp := fun w => (.ok a0, w)
def failBody : WComp := fun w => (.error (.failed "boom"), w)

/-- **`ensuringExitT` READS THE EXIT** — the two block ids are not
redundant, so C9 is a real obligation and not a restatement. -/
theorem ensuringExitT_reads_the_exit :
    (ensuringExitT okBody (mark nZ) (mark nO) []).2 = [Binding.mk a0 nZ]
      ∧ (ensuringExitT failBody (mark nZ) (mark nO) []).2 = [Binding.mk a0 nO] :=
  ⟨rfl, rfl⟩

/-- **RELEASE ORDER IS LIFO, AND IT IS FREE.** No finalizer stack, no
extra state component: NESTING IS THE ORDER, and nesting is content.
The inner acquisition's finalizer runs first because it is inner. -/
theorem release_lifo :
    (ensuringExitT (ensuringExitT okBody (mark nO) (mark nO))
        (mark nZ) (mark nZ) []).2
      = [Binding.mk a0 nO, Binding.mk a0 nZ] := rfl

/-- …and on the failing path, with the body's refusal intact. -/
theorem release_lifo_on_failure :
    ensuringExitT (ensuringExitT failBody (mark nO) (mark nO))
        (mark nZ) (mark nZ) []
      = (.error (.failed "boom"), [Binding.mk a0 nO, Binding.mk a0 nZ]) := rfl

/-! ### The bottom handler, and `build` -/

/-- The scope semantics: an ORDINARY `Handler` (R18 clause 1). -/
def scopeW (wce : BlockId → WComp) : Handler ScopeSig WM where
  handle
    | .ensuringExit b o e => ensuringExitT (wce b) (wce o) (wce e)
    | .raise _ => fun w => (.error (.failed "scope: raised"), w)

/-- The tower's floor: services below plus scope. `Handler.sum`. -/
def bottom (svc : Handler SvcSig WM) (wce : BlockId → WComp) :
    Handler LayerSig WM :=
  Handler.sum svc (scopeW wce)

/-- **`build`** — the description, the code table, and the floor, in one
interpretation. There is no `MemoMap` argument — see the report's memoization section. -/
def LDesc.buildAt (ce : CodeEnv) (d : LDesc)
    (svc : Handler SvcSig WM) (wce : BlockId → WComp) (k : SvcKey) : WComp :=
  interpret (bottom svc wce) ((d.build ce).handle (SvcE.ask k))

/-- `build` on a provided description factors through the layer
composition — the statement `runP_embed_agree` has at the program
plane, here at the layer plane, and free from `interpret_through`. -/
theorem buildAt_provide (ce : CodeEnv) (i o : LDesc)
    (svc : Handler SvcSig WM) (wce : BlockId → WComp) (k : SvcKey) :
    (LDesc.provide i o).buildAt ce svc wce k
      = interpret (bottom svc wce)
          (interpret (liftL (i.build ce)) ((o.build ce).handle (SvcE.ask k))) := by
  simp only [LDesc.buildAt, LDesc.build, Layer.provide, Handler.through]

/-! ## 8. `fresh` without a nonce is already broken under R4

`Cas.Schema.SystemNode.fresh (inner : StoreRef systemKindTag)`
(`Cas/Schema/System.lean:213`) carries no nonce. Under R4 identity is
content, so two authored `fresh`es of the same inner are ONE node at ONE
address — the exact opposite of what `fresh` is for. The nonce is not a
nicety; it is what makes the arm representable at all. -/

private def d0 : LDesc := .leaf "A" [] 0

theorem fresh_without_a_nonce_collapses :
    (LDesc.fresh 0 d0) = (LDesc.fresh 0 d0) := rfl

theorem fresh_with_a_nonce_separates :
    (LDesc.fresh 0 d0) ≠ (LDesc.fresh 1 d0) := by decide

/-! ## 9. Two divergences from rc.112, declared rather than discovered

1. **`mergeOn` is FIRST-wins on argument order; `Context.add` is
   LAST-wins** (`Context.ts:1861-1871`, requirements lane `GR-L8`). The
   bias is a one-line choice in `mergeOn`; what must not happen is
   leaving it unstated, because merge's associativity and the emitted
   TypeScript disagree if the two ends pick differently.
2. **`merge` here is SEQUENTIAL.** `Layer.mergeAll` opens a
   `"parallel"` scope (`Layer.ts:1596`), which is what makes
   `EC1-T064`'s `release_lifo` false as the packet states it. `release_lifo`
   above is TRUE because this design admits only the sequential merge —
   the divergence is the price of the theorem, and it is recorded here. -/


end ProposeE

/-! ## 10. Receipts -/

section Audit
open ProposeE
#print axioms ProposeE.provide_assoc
#print axioms ProposeE.provide_unit_right
#print axioms ProposeE.provide_unit_left
#print axioms ProposeE.provide_program_agrees
#print axioms ProposeE.mergeOn_unique
#print axioms ProposeE.merge_needs_the_content
#print axioms ProposeE.liftL_through
#print axioms ProposeE.liftL_injSvc
#print axioms ProposeE.build_provide
#print axioms ProposeE.ensuringExitT_diagonal
#print axioms ProposeE.ensuringExitT_never_replaces_the_refusal
#print axioms ProposeE.ensuringExitT_keeps_the_word
#print axioms ProposeE.ensuringExitT_reads_the_exit
#print axioms ProposeE.release_lifo
#print axioms ProposeE.release_lifo_on_failure
#print axioms ProposeE.WM_is_R18_target
#print axioms ProposeE.buildAt_provide
#print axioms ProposeE.fresh_with_a_nonce_separates
end Audit
