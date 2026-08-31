/-
  judge-position-B.lean — adversarial audit of position B ("layer-is-a-DAG").
  Writes nothing to library/.  Checked with:
    cd library/cas && lake env lean <this file>
  exit 0, no errors, no warnings, no sorry, no native_decide.
-/
import Cas.Lang.Tower
import Cas.Backend.Universal
import Cas.Backend.SumAlgebra
import Cas.Backend.Canon
import Cas.Backend.EmitLayer
import Cas.Lang.Defun

namespace JudgeB

open Cas Cas.Lang Cas.Schema Cas.Backend

/-! ## FINDING 1 (FOR B) — `sigOf` and the DEPENDENT memo DO elaborate.

B flagged resolution (a) as "the single place where claiming a type
works when it does not is most likely" and did not check it.  I checked
it.  It works.  This risk resolves in B's favour. -/

abbrev SigEnv := String → Option Sig

/-- And "there is no `Sig.empty`" is NOT the obstruction: one is three
tokens.  Every position in this packet asserts its absence as if it
were a structural fact; it is only an absence from `library/`. -/
def SigNil : Sig := ⟨Empty, fun e => e.elim⟩

def sigOf (E : SigEnv) : List ServiceRef → Sig
  | [] => SigNil
  | s :: rest => (E s.key |>.getD SigNil) ⊕ₛ sigOf E rest

abbrev CtxAt (E : SigEnv) (provides : Cas.Addr32 → List ServiceRef)
    (M : Type → Type) (a : Cas.Addr32) : Type :=
  Handler (sigOf E (provides a)) M

/-- B's ruled resolution (a): the dependent memo.  ELABORATES. -/
abbrev DepMemo (E : SigEnv) (p : Cas.Addr32 → List ServiceRef)
    (M : Type → Type) : Type := (a : Cas.Addr32) → Option (CtxAt E p M a)

/-- …and is UPDATABLE, with the transport `subst` supplies.  No sigma,
no universe bump, no `Handler.sum_unique` lost. -/
def depMemoInsert {E : SigEnv} {p : Cas.Addr32 → List ServiceRef}
    {M : Type → Type} (m : DepMemo E p M) (a : Cas.Addr32)
    (v : CtxAt E p M a) : DepMemo E p M := fun a' =>
  if h : a' = a then some (h ▸ v) else m a'

/-! ## FINDING 2 (AGAINST B) — the bridge is not "unwritten", it is
UNSTATABLE at the `merge` and `provideMerge` arms.

B owes `residual_agrees_with_the_denotation`:
    sigOf E (residualOf t n).provides  =  ROut (denote t n)
`Sig.Op : Type`, so this is an equation between TYPES.

`residualOf` (`EmitLayer.lean:243`) puts `canonServices` on BOTH fields
of every arm, and B's own `mergeL`/`provideMergeL` give
`ROut (merge x y) = ROut x ⊕ₛ ROut y`.  So at the merge arm the bridge
IS:
    sigOf E (canonServices (px ++ py))  =  sigOf E px ⊕ₛ sigOf E py
Three independent obstructions, each a type equation Lean cannot prove.
-/

def kA : ServiceRef := { key := "A", name := "A", path := "p" }
def kB : ServiceRef := { key := "B", name := "B", path := "p" }
def unitSig : Sig := ⟨Unit, fun _ => Nat⟩
def E0 : SigEnv := fun _ => some unitSig

/-- OBSTRUCTION A — no unit.  The nil case of any fold needs
`SigNil ⊕ₛ S = S`, i.e. `Empty ⊕ S.Op = S.Op` in `Type`. -/
example : (SigNil ⊕ₛ SigNil).Op = (Empty ⊕ Empty) := rfl
example : SigNil.Op = Empty := rfl
-- REFUTED AS `rfl`, and unprovable without univalence:
--   example (S : Sig) : SigNil ⊕ₛ S = S := rfl
--   error: type mismatch … but is expected to have type SigNil ⊕ₛ S = S

/-- OBSTRUCTION B — the concatenation law fails on SHAPE.  A right fold
gives a right-nested sum; the denotation gives a balanced one. -/
example : (sigOf E0 [kA, kB]).Op = (Unit ⊕ (Unit ⊕ Empty)) := rfl
example : ((sigOf E0 [kA]) ⊕ₛ (sigOf E0 [kB])).Op
        = ((Unit ⊕ Empty) ⊕ (Unit ⊕ Empty)) := rfl
-- `Unit ⊕ (Unit ⊕ Empty)` vs `(Unit ⊕ Empty) ⊕ (Unit ⊕ Empty)`:
-- distinct types.  Rebalancing needs associativity, which is:
--   example (A B C : Sig) : (A ⊕ₛ B) ⊕ₛ C = A ⊕ₛ (B ⊕ₛ C) := rfl
--   error: type mismatch … A ⊕ₛ B ⊕ₛ C = A ⊕ₛ (B ⊕ₛ C)
-- B's own compositionLaws bullet concedes exactly this and calls it a
-- TYPE FACT no design on this carrier can state.  It then owes a
-- theorem that needs it.

-- OBSTRUCTION C — and it is not a fold-shape artefact a smarter
-- `sigOf` could dodge.  `canonServices` SORTS BY KEY and DEDUPS, while
-- `Sig.sum` is neither commutative nor idempotent.  So a merge authored
-- out of key order has its summands REORDERED on the content plane and
-- not on the value plane.  Exhibited on the real function:
#guard (canonServices [kB, kA]).map (·.key) == ["A", "B"]
#guard ([kB, kA]).map (·.key) == ["B", "A"]
-- …and dedup collapses a repeat that `⊕ₛ` keeps as two summands —
-- which is precisely `canonServices_last_wins` (`Canon.lean:278`), the
-- theorem B cites in its own favour, working against the bridge.
#guard (canonServices [kA, kA]).length == 1

/-! So the missing piece is not the one definition B budgets for
(`sigOf`).  It is a SIGNATURE-NORMALIZATION / SUBSUMPTION apparatus:
a relation `S ≤ₛ T` with a coercion on handlers, plus the theorems that
`canonServices` and `⊕ₛ`-folding agree up to it.  That apparatus is a
new carrier, it is nowhere in `library/`, and it appears in NO field of
B's `newCarriersMinted`. -/

/-! ## FINDING 2b (AGAINST B) — `Defun.lean` is NOT the precedent.

B's `layerModel` opens: "Two planes, one bridge — `Cas/Lang/Defun.lean`'s
shape exactly (`PProg` content, `Prog` meaning, `embed`,
`runP_embed_agree :362`)".  The precedent does not have the feature that
blocks B.  `embed` lands at a FIXED signature and a FIXED answer type: -/

example : Cas.Lang.PProg → Prog CasSig Cas.Addr32 := Cas.Lang.embed

example (H : Bytes → Cas.Addr32) (p : Cas.Lang.PProg) (w : Word) :
    run H (p.length + 1) (Cas.Lang.embed p) w = Cas.Lang.runP H p w :=
  Cas.Lang.runP_embed_agree H p w

/-! `runP_embed_agree` equates two VALUES at one fixed type.  B's
`denote : (t : Table) → (a : Addr32) → LayerH (sigOf E (provides a))
(sigOf E (requires a))` computes its TYPE INDEX from the content, so its
agreement theorem is an equation between COMPUTED TYPES.  That is a
different and much harder shape, and it is exactly where FINDING 2
bites.  The estate has no worked precedent for it. -/

/-! ## FINDING 3 (AGAINST B) — `acquires` is degraded exactly where
cost #3 bites.

`acquires` returns `true` on `opaque` (conservative, unknown body), and
B routes the ENTIRE dynamic fragment — `flatMap`, `unwrap`, `suspend`,
`catchCause` — to `opaque`.  So on any topology containing one
config-driven layer, the classifier B sells as buy #4 answers `true`
and decides nothing.  The probe cannot show this: its `LNode` mirror
DROPS the `opaque` and `backing` arms, so `acquires_decided` is checked
on a shape from which the contested case has been removed. -/

example (c : CodeRef) (n : String) (ps rs : List ServiceRef) : SystemNode :=
  .«opaque» c n ps rs        -- the arm the probe's mirror omits

/-! ## FINDING 4 (NEUTRAL) — `through_monoid` is correctly declined.
B says it quantifies over endomorphisms at ONE signature and never
applies to a layer that provides what it does not require.  Verified
against `Universal.lean:776-790`: the estate's own docstring says the
same, and the theorem's type confirms it. -/

example {S : Sig} (t u v : Handler S (Prog S)) :
    (t.through u).through v = t.through (u.through v)
      ∧ t.through (idHandler (S := S)) = t
      ∧ (idHandler (S := S)).through t = t := through_monoid t u v

/-! ## FINDING 5 (FOR B) — the anchors are real and say what B says.
Every citation in B's `compositionLaws` re-run here at B's own use. -/

example {S T U V : Sig} (a : Handler S (Prog T)) (b : Handler T (Prog U))
    (c : Handler U (Prog V)) :
    (a.through b).through c = a.through (b.through c) :=
  through_assoc leftUnit_of_lawful bindAssoc_of_lawful a b c

example {S T : Sig} (a : Handler S (Prog T)) : a.through idHandler = a :=
  through_id_right a

example {S T : Sig} (a : Handler S (Prog T)) : (idHandler (S := S)).through a = a :=
  through_id_left rightUnit_of_lawful a

example {S T : Sig} {M : Type → Type} [Monad M] [LawfulMonad M] {A : Type}
    (t : Handler S (Prog T)) (h : Handler T M) (p : Prog S A) :
    interpret h (interpret t p) = interpret (t.through h) p :=
  interpret_through t h p

example {S T : Sig} {M : Type → Type v} (h : Handler S M) (g : Handler T M)
    (k : Handler (S ⊕ₛ T) M)
    (hl : ∀ op, k.handle (Sum.inl op) = h.handle op)
    (hr : ∀ op, k.handle (Sum.inr op) = g.handle op) : k = h.sum g :=
  Handler.sum_unique h g k hl hr

example {xs : List ServiceRef} {s : ServiceRef} (h : s ∈ canonServices xs) :
    ∃ pre post, xs = pre ++ s :: post ∧ s.key ∉ post.map (·.key) :=
  canonServices_last_wins h

example {xs ys : List ServiceRef} (hnd : (xs.map (·.key)).Nodup) (hp : xs.Perm ys) :
    canonServices xs = canonServices ys := canonServices_perm hnd hp

end JudgeB


/-! ## FINDING 6 (AGAINST B) — the probe's `build` is not a build.

B declares the `Ctx` monomorphization ("here it is the acquisition
ordinal so sharing is observable").  It does NOT declare the further
step: the fold never reads any node's `requires` (`.service _ prov _`),
and the `provide` arm DISCARDS the inner's context (`ri.2` is bound and
unused; only `ri.1`, the memo, is threaded).  So `build` performs no
dependency discharge whatsoever.  Verbatim replay of §3, with the
wiring broken, axiom-free. -/

namespace WiringAudit
open Cas Cas.Lang

open Cas Cas.Lang
abbrev Key := String
abbrev Code := Nat
abbrev NodeAddr := Nat
inductive LNode where
  | service (ctor : Code) (provides : Key) (requires : List Key)
  | scoped (acquire release : Code) (provides : Key) (requires : List Key)
  | stub
  | merge (parts : List NodeAddr)
  | provide (inner outer : NodeAddr)
  | provideMerge (inner outer : NodeAddr)
  | fresh (inner : NodeAddr)
abbrev Table := List (NodeAddr × LNode)
def find? (t : Table) (a : NodeAddr) : Option LNode :=
  (t.find? fun row => row.1 == a).map (·.2)
abbrev Inst := Nat
abbrev Ctx := List (Key × Inst)
abbrev BState := List Nat × List Code × Nat
abbrev BuildM := ExceptT Refusal (StateM BState)
abbrev Memo := List (NodeAddr × Ctx)
def memoFind? (m : Memo) (a : NodeAddr) : Option Ctx :=
  (m.find? fun row => row.1 == a).map (·.2)
def emit (x : Nat) : BuildM Unit := fun s => (.ok (), (s.1 ++ [x], s.2.1, s.2.2))
def newInst : BuildM Inst := fun s => (.ok s.2.2, (s.1, s.2.1, s.2.2 + 1))
def pushFin (c : Code) : BuildM Unit := fun s => (.ok (), (s.1, c :: s.2.1, s.2.2))
def refuse (r : Refusal) : BuildM A := fun s => (.error r, s)
-- VERBATIM from propose-B.lean §3
def build : Nat → Table → Memo → NodeAddr → BuildM (Memo × Ctx)
  | 0, _, _, _ => refuse (.failed "layer build: out of fuel")
  | f + 1, t, m, a =>
    match memoFind? m a with
    | some c => pure (m, c)
    | none =>
      match find? t a with
      | none => refuse (.failed "layer build: unresolved node")
      | some node =>
        match node with
        | .stub => refuse (.failed "layer build: constructor refused")
        | .service _ prov _ => do
            let i ← newInst; emit i; let c : Ctx := [(prov, i)]; pure ((a, c) :: m, c)
        | .scoped _ rel prov _ => do
            let i ← newInst; emit i; pushFin rel
            let c : Ctx := [(prov, i)]; pure ((a, c) :: m, c)
        | .fresh inner => do let r ← build f t [] inner; pure (m, r.2)
        | .provide inner outer => do
            let ri ← build f t m inner
            let ro ← build f t ri.1 outer
            pure ((a, ro.2) :: ro.1, ro.2)
        | .provideMerge inner outer => do
            let ri ← build f t m inner
            let ro ← build f t ri.1 outer
            let c : Ctx := ri.2 ++ ro.2
            pure ((a, c) :: ro.1, c)
        | .merge parts => do
            let r ← parts.foldlM (fun (acc : Memo × Ctx) (p : NodeAddr) => do
                let r ← build f t acc.1 p
                pure (r.1, acc.2 ++ r.2)) ((m, ([] : Ctx)) : Memo × Ctx)
            pure ((a, r.2) :: r.1, r.2)
def s0 : BState := ([], [], 0)

-- B's own witness table
def good : Table :=
  [ (0, .service 0 "Db" []), (1, .service 1 "A" ["Db"]), (2, .provide 0 1) ]

-- The SAME table with the wiring BROKEN: the outer demands "Cache",
-- which the inner does not provide.  `build` cannot tell.
def broken : Table :=
  [ (0, .service 0 "Db" []), (1, .service 1 "A" ["Cache"]), (2, .provide 0 1) ]

-- And with the inner providing something ELSE entirely.
def alsoBroken : Table :=
  [ (0, .service 0 "Zzz" []), (1, .service 1 "A" ["Db"]), (2, .provide 0 1) ]

theorem build_ignores_requires_1 :
    (build 8 good [] 2 s0).2.1 = (build 8 broken [] 2 s0).2.1 := rfl
theorem build_ignores_requires_2 :
    (build 8 good [] 2 s0).1.toOption.map (·.2)
      = (build 8 broken [] 2 s0).1.toOption.map (·.2) := rfl
theorem build_accepts_unsatisfied_wiring :
    (build 8 broken [] 2 s0).1.toOption.map (·.2) = some [("A", 1)] := rfl
theorem build_ignores_what_the_inner_provides :
    (build 8 alsoBroken [] 2 s0).1.toOption.map (·.2) = some [("A", 1)] := rfl

#print axioms build_ignores_requires_1
#print axioms build_accepts_unsatisfied_wiring
#print axioms build_ignores_what_the_inner_provides

end WiringAudit
