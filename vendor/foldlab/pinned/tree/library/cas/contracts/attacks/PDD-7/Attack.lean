import Cas.Backend.SumAlgebra

/-!
# PDD-7 — the breaker's adversarial record

## Subject

```
CASTLE   agent/opus-cc-mac/pdd-7 @ d714ef14
           module  library/cas/Cas/Backend/SumAlgebra.lean  @ 03ca1435
           packet  library/cas/contracts/PDD-7.contract.md  @ 8e7fe66a
                     ledger row c2686dc6, non-vacuity pin 24b6fe30,
                     exhibits correction d714ef14
           merge   7a3d558d (main into the branch)
BREAKER  independent; did not build this castle
BRANCH   attack/opus-cc-mac/pdd-7
```

## What this file IS

An ADVERSARIAL RECORD. Every declaration is an attack on the packet or
the module: a witness that a claim is weaker or stronger than
advertised, a fresh wrong-but-passing candidate, or a break attempt
that FAILED and is kept because a failed break is earned confidence and
earned confidence is record (BREAKER.md, "attack artifacts are record").

The verdict it backs is `RESULTS.md` beside it: **STANDS**. No theorem
in `SumAlgebra.lean` is false; the axiom census reproduces; the
ledger's break row is CONFIRMED in both directions. What this file adds
is where the packet's PROSE overreaches its theorems, three fresh
adversaries with the law that kills each, and four results the packet
could have had and does not.

## What this file is NOT

NOT part of any Lake target and it must not become one. It adds nothing
to `Cas`, moves no bytes, touches no ledger, and lives in a directory
whose name (`PDD-7`) is not a legal Lean module component, so it cannot
be `import`ed even by accident. It is not a battery for the castle.

## How to elaborate it

From `library/cas`:

```
lake env lean contracts/attacks/PDD-7/Attack.lean
```

Expected: elaborates clean, no `sorry`. §7's `#check` block and §8's
`#print axioms` block are read off the run, not asserted.

## The map

- **§1** — ADQ-INL is not vacuous: the premise is inhabited, elaborated.
- **§2** — the quantifier. `syntactic_hyp_iff` and
  `inl_unique_one_target`: the hypothesis at the ONE instance the proof
  consumes IS the conclusion, so the target quantifier can be narrowed
  to a single monad. `inl_unique_via_initiality`: a second route, which
  bottoms out at the same instance. `narrowing_to_Id_fails`: it cannot
  be narrowed to `Id`. `sum_unique_iff` and the two
  `sum_unique_needs_*_premise` theorems: ADQ-SUM's premises are exactly
  L21+L22 and neither is spare.
- **§3** — the ledger row, re-elaborated by a different route:
  `doubleInl` FACTORS as `Prog.inl ∘ dup`, which is the structural
  reason L25 and L26 cannot see it, and `doubleInl_fails_L23_premise`
  is the other half stated as a theorem.
- **§4** — three fresh adversaries: reordering, eliding, and doubling
  on one operation tag only, the last at `CasSig` itself. With
  `no_Id_counter_for_CasSig`: the castle's advertised counting target
  does not exist at the store language.
- **§5** — `handleLlm`. `badHandleLlm` satisfies L31 and is killed by
  L30. `askTwice_answers_agree`: the oracle quantifier is over total
  deterministic functions and nothing else. `llmOracleHandler_unique`:
  L30's right summand is forced. `handleLlm_bind`: L32, which the
  packet leaves OWED, in two lines.
- **§6** — failed break attempts.
- **§7** — the universe scope of the categoricity, read off signatures.
- **§8** — this record's own axiom census.
-/

namespace PDD7Attack
open Cas Cas.Lang

universe u v

/-! ## own extensionality helper (the castle's is private) -/
theorem handlerExt {S : Sig} {M : Type → Type v} {h g : Handler S M}
    (hyp : ∀ op, h.handle op = g.handle op) : h = g := by
  cases h; cases g; exact congrArg Handler.mk (funext hyp)

/-! ## §1 non-vacuity of ADQ-INL, elaborated rather than argued -/

example {S T : Sig} {A : Type} (p : Prog S A) :
    Prog.inl (T := T) p = Prog.inl p :=
  Prog.inl_unique (fun {_} q => Prog.inl q)
    (fun _ _ _ h g {_} q => interpret_inl h g q) p

/-! ## §2 the quantifier -/

/-- The hypothesis of ADQ-INL, taken at the ONE instance its proof
consumes, is the conclusion up to two rewrites. -/
theorem syntactic_hyp_iff {S T : Sig}
    (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A) {A : Type} (p : Prog S A) :
    (interpret ((inlHandler S T).sum (inrHandler S T)) (ι p)
        = interpret (inlHandler S T) p)
      ↔ ι p = Prog.inl p := by
  rw [sum_inlHandler_inrHandler, interpret_id, interpret_inlHandler]

/-- ADQ-INL with the target quantifier NARROWED to one monad and one
handler pair. Strictly stronger than the castle's. -/
theorem inl_unique_one_target {S T : Sig}
    (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A)
    (hι : ∀ {A : Type} (p : Prog S A),
        interpret ((inlHandler S T).sum (inrHandler S T)) (ι p)
          = interpret (inlHandler S T) p)
    {A : Type} (p : Prog S A) : ι p = Prog.inl p :=
  (syntactic_hyp_iff ι p).mp (hι p)

/-- A second, genuinely different route: initiality plus ADQ-SUM. -/
theorem inl_unique_via_initiality {S T : Sig}
    (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A)
    (hι : ∀ (M : Type → Type) [Monad M] [LawfulMonad M]
            (h : Handler S M) (g : Handler T M) {A : Type} (p : Prog S A),
            interpret (h.sum g) (ι p) = interpret h p)
    {A : Type} (p : Prog S A) : ι p = Prog.inl p := by
  refine eq_of_forall_interpret (fun M _ _ d => ?_)
  have hd : d = (Handler.mk (fun op => d.handle (Sum.inl op))).sum
                (Handler.mk (fun op => d.handle (Sum.inr op))) :=
    Handler.sum_unique _ _ d (fun _ => rfl) (fun _ => rfl)
  rw [hd, hι, interpret_inl]

/-! ### Id is not a separating target -/

theorem doubleInl_interpret_inl_Id {S T : Sig}
    (h : Handler S Id) (g : Handler T Id) {A : Type} (p : Prog S A) :
    interpret (h.sum g) (Adversary.doubleInl (T := T) p) = interpret h p := by
  induction p with
  | pure a => rfl
  | vis e k ih => exact ih (h.handle e)

/-- Narrowing ADQ-INL's target quantifier to `Id` makes it FALSE:
`doubleInl` satisfies the Id-restricted hypothesis at every handler
pair and is not `Prog.inl`. -/
theorem narrowing_to_Id_fails :
    ¬ (∀ (S T : Sig) (ι : {A : Type} → Prog S A → Prog (S ⊕ₛ T) A),
        (∀ (h : Handler S Id) (g : Handler T Id) {A : Type} (p : Prog S A),
           interpret (h.sum g) (ι p) = interpret h p) →
        ∀ {A : Type} (p : Prog S A), ι p = Prog.inl p) := by
  intro hyp
  have hEq := hyp Adversary.TickSig Adversary.TickSig
    (fun {_} p => Adversary.doubleInl p)
    (fun h g {_} p => doubleInl_interpret_inl_Id h g p) Adversary.tick
  have hc := congrArg
    (fun x => (interpret (Adversary.tickHandler.sum Adversary.tickHandler) x) 0) hEq
  rw [Adversary.doubleInl_tick_count, Adversary.inl_tick_count] at hc
  have h2 : (2 : Nat) = 1 := congrArg Prod.snd hc
  omega

/-! ### ADQ-SUM's premises are exactly L21+L22, and both are needed -/

theorem sum_unique_iff {S T : Sig} {M : Type → Type v}
    (h : Handler S M) (g : Handler T M) (k : Handler (S ⊕ₛ T) M) :
    ((∀ op, k.handle (Sum.inl op) = h.handle op)
       ∧ (∀ op, k.handle (Sum.inr op) = g.handle op))
      ↔ k = h.sum g := by
  constructor
  · exact fun hlr => Handler.sum_unique h g k hlr.1 hlr.2
  · rintro rfl; exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- Dropping the right-hand premise breaks ADQ-SUM. -/
theorem sum_unique_needs_right_premise :
    ¬ (∀ (S : Sig) (M : Type → Type) (h g : Handler S M) (k : Handler (S ⊕ₛ S) M),
         (∀ op, k.handle (Sum.inl op) = h.handle op) → k = h.sum g) := by
  intro hyp
  have hEq := hyp Adversary.TickSig Adversary.Counter
    Adversary.tickHandler Adversary.tickHandler2
    (Adversary.tickHandler.sum Adversary.tickHandler) (fun _ => rfl)
  have hc := congrArg (fun (x : Handler _ Adversary.Counter) => (x.handle (Sum.inr ())) 0) hEq
  have h2 : (1 : Nat) = 2 := congrArg Prod.snd hc
  omega

/-- …and dropping the left-hand premise breaks it the other way. -/
theorem sum_unique_needs_left_premise :
    ¬ (∀ (S : Sig) (M : Type → Type) (h g : Handler S M) (k : Handler (S ⊕ₛ S) M),
         (∀ op, k.handle (Sum.inr op) = g.handle op) → k = h.sum g) := by
  intro hyp
  have hEq := hyp Adversary.TickSig Adversary.Counter
    Adversary.tickHandler Adversary.tickHandler2
    (Adversary.tickHandler2.sum Adversary.tickHandler2) (fun _ => rfl)
  have hc := congrArg
    (fun (x : Handler _ Adversary.Counter) => (x.handle (Sum.inl ())) 0) hEq
  have h2 : (2 : Nat) = 1 := congrArg Prod.snd hc
  omega

/-! ## §3 the ledger row, re-elaborated

Not by copying the castle's inductions: the route here is a
FACTORIZATION. `doubleInl` is `Prog.inl` after a doubling endomorphism
of `Prog S`, and every one of L25/L26 for the adversary then falls out
of the same law for `Prog.inl` composed with the same law for `dup`.
That is why those laws cannot see it. -/

/-- The doubling endomorphism, inside one signature. -/
def dup {S : Sig} {A : Type u} : Prog S A → Prog S A
  | .pure a => .pure a
  | .vis e k => .vis e fun r => .vis e fun _ => dup (k r)

theorem dup_pure {S : Sig} {A : Type u} (a : A) :
    dup (S := S) (Prog.pure a) = Prog.pure a := rfl

theorem dup_bind {S : Sig} {A B : Type u} (p : Prog S A) (f : A → Prog S B) :
    dup (p.bind f) = (dup p).bind (fun a => dup (f a)) := by
  induction p with
  | pure a => rfl
  | vis e k ih =>
    exact congrArg (Prog.vis (S := S) (A := B) e) (funext fun r =>
      congrArg (Prog.vis (S := S) (A := B) e) (funext fun _ => ih r))

theorem dup_injective {S : Sig} {A : Type u} :
    ∀ (p q : Prog S A), dup p = dup q → p = q := by
  intro p
  induction p with
  | pure a =>
    intro q hq
    cases q with
    | pure b => simpa [dup] using hq
    | vis e' k' => simp [dup] at hq
  | vis e k ih =>
    intro q hq
    cases q with
    | pure b => simp [dup] at hq
    | vis e' k' =>
      have hq' : Prog.vis (S := S) e (fun r => Prog.vis (S := S) e (fun _ => dup (k r)))
               = Prog.vis (S := S) e' (fun r => Prog.vis (S := S) e' (fun _ => dup (k' r))) := hq
      injection hq' with he hk
      subst he
      refine congrArg (Prog.vis e) (funext fun r => ih r (k' r) ?_)
      injection congrFun (eq_of_heq hk) r with _ h2
      exact congrFun h2 r

/-- **The structural explanation of the break.** The doubling injection
is the real injection precomposed with an endomorphism of `Prog S`. -/
theorem doubleInl_factors {S T : Sig} {A : Type u} (p : Prog S A) :
    Adversary.doubleInl (T := T) p = Prog.inl (dup p) := by
  induction p with
  | pure a => rfl
  | vis e k ih =>
    exact congrArg (Prog.vis (S := S ⊕ₛ T) (A := A) (Sum.inl e)) (funext fun r =>
      congrArg (Prog.vis (S := S ⊕ₛ T) (A := A) (Sum.inl e)) (funext fun _ => ih r))

theorem doubleInl_pure' {S T : Sig} {A : Type u} (a : A) :
    Adversary.doubleInl (S := S) (T := T) (Prog.pure a) = Prog.pure a := rfl

/-- L25 for the adversary, re-derived: factorization, `dup_bind`,
`Prog.inl_bind`. -/
theorem doubleInl_bind' {S T : Sig} {A B : Type u}
    (p : Prog S A) (f : A → Prog S B) :
    Adversary.doubleInl (T := T) (p.bind f)
      = (Adversary.doubleInl (T := T) p).bind
          (fun a => Adversary.doubleInl (T := T) (f a)) := by
  simp only [doubleInl_factors, dup_bind, Prog.inl_bind]

/-- L26 for the adversary, re-derived from the two injectivities. -/
theorem doubleInl_injective' {S T : Sig} {A : Type u} (p q : Prog S A)
    (h : Adversary.doubleInl (T := T) p = Adversary.doubleInl (T := T) q) :
    p = q :=
  dup_injective p q (Prog.inl_injective (T := T) _ _
    (by rw [← doubleInl_factors, ← doubleInl_factors]; exact h))

/-- The doubling injection is not the real one, at a witness. -/
theorem doubleInl_tick_ne :
    Adversary.doubleInl (T := Adversary.TickSig) Adversary.tick
      ≠ Prog.inl Adversary.tick := by
  intro hEq
  have hc := congrArg
    (fun x => (interpret (Adversary.tickHandler.sum Adversary.tickHandler) x) 0) hEq
  rw [Adversary.doubleInl_tick_count, Adversary.inl_tick_count] at hc
  have h2 : (2 : Nat) = 1 := congrArg Prod.snd hc
  omega

/-- **L23 alone kills the doubling injection** — through ADQ-INL, with
no appeal to L25 or L26. The castle's break-ledger claim, restated as a
theorem rather than as prose. -/
theorem doubleInl_fails_L23_premise :
    ¬ (∀ (M : Type → Type) [Monad M] [LawfulMonad M]
         (h : Handler Adversary.TickSig M) (g : Handler Adversary.TickSig M)
         {A : Type} (p : Prog Adversary.TickSig A),
         interpret (h.sum g) (Adversary.doubleInl (T := Adversary.TickSig) p)
           = interpret h p) := fun hyp =>
  doubleInl_tick_ne
    (Prog.inl_unique (fun {_} q => Adversary.doubleInl q) hyp Adversary.tick)

/-! ## §4 fresh adversaries -/

abbrev Sig2 : Sig := ⟨Bool, fun _ => Unit⟩
abbrev Trace := StateT (List Bool) Id

def traceHandler : Handler Sig2 Trace where
  handle b := fun l => ((), l ++ [b])

def opT (b : Bool) : Prog Sig2 Unit := .vis b .pure
def pgmAB : Prog Sig2 Unit := .vis true (fun _ => .vis false (fun _ => .pure ()))

/-! ### A1 — the reordering injection -/

def swapTwoInl {T : Sig} {A : Type} : Prog Sig2 A → Prog (Sig2 ⊕ₛ T) A
  | .pure a => .pure a
  | .vis e k =>
    match k () with
    | .pure a => .vis (Sum.inl e) (fun _ => .pure a)
    | .vis e' k' =>
        .vis (Sum.inl e') (fun _ => .vis (Sum.inl e) (fun _ => Prog.inl (k' ())))

theorem swapTwoInl_trace :
    (interpret (traceHandler.sum traceHandler) (swapTwoInl (T := Sig2) pgmAB)) []
      = ((), [false, true]) := rfl

theorem pgmAB_trace : (interpret traceHandler pgmAB) [] = ((), [true, false]) := rfl

theorem swapTwoInl_not_interpret_inl :
    ¬ (∀ (T : Sig) (M : Type → Type) [Monad M] (h : Handler Sig2 M) (g : Handler T M)
         (A : Type) (p : Prog Sig2 A),
         interpret (h.sum g) (swapTwoInl (T := T) p) = interpret h p) := by
  intro hyp
  have h1 := congrFun (hyp Sig2 Trace traceHandler traceHandler Unit pgmAB) []
  rw [swapTwoInl_trace, pgmAB_trace] at h1
  have h2 : [false, true] = [true, false] := congrArg Prod.snd h1
  simp at h2

theorem swapTwoInl_bind_lhs :
    (interpret (traceHandler.sum traceHandler)
      (swapTwoInl (T := Sig2) ((opT true).bind (fun _ => opT false)))) []
      = ((), [false, true]) := rfl

theorem swapTwoInl_bind_rhs :
    (interpret (traceHandler.sum traceHandler)
      ((swapTwoInl (T := Sig2) (opT true)).bind
        (fun _ => swapTwoInl (T := Sig2) (opT false)))) []
      = ((), [true, false]) := rfl

/-- Unlike the doubling injection, the reordering one FAILS L25. -/
theorem swapTwoInl_not_monad_morphism :
    ¬ (∀ (A B : Type) (p : Prog Sig2 A) (f : A → Prog Sig2 B),
         swapTwoInl (T := Sig2) (p.bind f)
           = (swapTwoInl (T := Sig2) p).bind
               (fun a => swapTwoInl (T := Sig2) (f a))) := by
  intro hyp
  have h1 := congrArg
    (fun x => (interpret (traceHandler.sum traceHandler) x) [])
    (hyp Unit Unit (opT true) (fun _ => opT false))
  rw [swapTwoInl_bind_lhs, swapTwoInl_bind_rhs] at h1
  have h2 : [false, true] = [true, false] := congrArg Prod.snd h1
  simp at h2

/-! ### A2 — the eliding injection -/

def dropInl {T : Sig} {A : Type} : Prog Sig2 A → Prog (Sig2 ⊕ₛ T) A
  | .pure a => .pure a
  | .vis _ k => Prog.inl (k ())

theorem dropInl_trace :
    (interpret (traceHandler.sum traceHandler) (dropInl (T := Sig2) pgmAB)) []
      = ((), [false]) := rfl

theorem dropInl_not_interpret_inl :
    ¬ (∀ (T : Sig) (M : Type → Type) [Monad M] (h : Handler Sig2 M) (g : Handler T M)
         (A : Type) (p : Prog Sig2 A),
         interpret (h.sum g) (dropInl (T := T) p) = interpret h p) := by
  intro hyp
  have h1 := congrFun (hyp Sig2 Trace traceHandler traceHandler Unit pgmAB) []
  rw [dropInl_trace, pgmAB_trace] at h1
  have h2 : [false] = [true, false] := congrArg Prod.snd h1
  simp at h2

theorem dropInl_collapses :
    dropInl (T := Sig2) (opT true) = dropInl (T := Sig2) (opT false) := rfl

theorem opT_distinct : opT true ≠ opT false := by
  intro h
  simp only [opT, Prog.vis.injEq] at h
  exact Bool.noConfusion h.1

/-- The eliding injection also fails L26 — it is not injective. -/
theorem dropInl_not_injective :
    ¬ (∀ (A : Type) (p q : Prog Sig2 A),
         dropInl (T := Sig2) p = dropInl (T := Sig2) q → p = q) :=
  fun hyp => opT_distinct (hyp Unit _ _ dropInl_collapses)

/-! ### A3 — the tag-selective doubling injection, at the store language -/

def zeroAddr : Addr32 := ⟨List.replicate 32 0, by simp⟩
def zeroNode : Node := ⟨0, 0, [], []⟩

abbrev CCounter := StateT Nat (Except Unit)

def countCas : Handler CasSig CCounter where
  handle
    | .put _ => fun n => .ok (zeroAddr, n + 1)
    | .load _ => fun n => .ok (zeroNode, n + 1)
    | .fail _ => fun _ => .error ()

/-- `StateT Nat Id` — the castle's advertised counting target — has NO
handler at `CasSig`: `fail` answers `Empty` and `Id` has no error
branch to put it in. -/
theorem no_Id_counter_for_CasSig (h : Handler CasSig (StateT Nat Id)) : False :=
  ((h.handle (CasE.fail "x")) 0).1.elim

def putDoubleInl {T : Sig} {A : Type} : Prog CasSig A → Prog (CasSig ⊕ₛ T) A
  | .pure a => .pure a
  | .vis (CasE.put n) k =>
      .vis (Sum.inl (CasE.put n)) fun r =>
        .vis (Sum.inl (CasE.put n)) fun _ => putDoubleInl (k r)
  | .vis (CasE.load a) k =>
      .vis (Sum.inl (CasE.load a)) fun r => putDoubleInl (k r)
  | .vis (CasE.fail s) k =>
      .vis (Sum.inl (CasE.fail s)) fun r => putDoubleInl (k r)

def putP : Prog CasSig Unit := .vis (CasE.put zeroNode) (fun _ => .pure ())
def loadP : Prog CasSig Unit := .vis (CasE.load zeroAddr) (fun _ => .pure ())

theorem putDoubleInl_put_count :
    (interpret (countCas.sum countCas) (putDoubleInl (T := CasSig) putP)) 0
      = .ok ((), 2) := rfl

theorem inl_put_count :
    (interpret (countCas.sum countCas) (Prog.inl (T := CasSig) putP)) 0
      = .ok ((), 1) := rfl

theorem countCas_putP : (interpret countCas putP) 0 = .ok ((), 1) := rfl

/-- Tag-selectivity: on a `load` the adversary is indistinguishable
from the real injection, at the very handler that separates them on a
`put`. -/
theorem putDoubleInl_load_agrees :
    (interpret (countCas.sum countCas) (putDoubleInl (T := CasSig) loadP)) 0
      = (interpret (countCas.sum countCas) (Prog.inl (T := CasSig) loadP)) 0 := rfl

theorem putDoubleInl_not_interpret_inl :
    ¬ (∀ (T : Sig) (M : Type → Type) [Monad M] (h : Handler CasSig M) (g : Handler T M)
         (A : Type) (p : Prog CasSig A),
         interpret (h.sum g) (putDoubleInl (T := T) p) = interpret h p) := by
  intro hyp
  have h1 := congrFun (hyp CasSig CCounter countCas countCas Unit putP) 0
  rw [putDoubleInl_put_count, countCas_putP] at h1
  injection h1 with h2
  have h3 : (2 : Nat) = 1 := congrArg Prod.snd h2
  omega

/-! ## §5 `handleLlm` — the oracle quantifier and L31's reach -/

/-- An adversarial `handleLlm` that IGNORES the oracle and answers every
inference with the empty string. -/
def badHandleLlm (oracle : String → String) : Prog AgentSig A → Prog CasSig A
  | .pure a => .pure a
  | .vis (Sum.inl e) k => .vis e (fun r => badHandleLlm oracle (k r))
  | .vis (Sum.inr (LlmE.infer _)) k => badHandleLlm oracle (k "")

/-- The adversary satisfies **L31 in full** — L31 pins nothing on a
program that is not of the `liftCas` form. -/
theorem badHandleLlm_liftCas (oracle : String → String) {A : Type u}
    (p : Prog CasSig A) : badHandleLlm oracle (liftCas p) = p := by
  induction p with
  | pure a => rfl
  | vis e k ih => exact congrArg (Prog.vis e) (funext ih)

def wildOracle : String → String := fun s => s ++ "!"

theorem badHandleLlm_differs :
    badHandleLlm wildOracle (infer "x") ≠ Prog.handleLlm wildOracle (infer "x") := by
  intro h
  have h1 : (Prog.pure "" : Prog CasSig String) = Prog.pure "x!" := h
  injection h1 with h2
  exact absurd h2 (by decide)

/-- …and L30 is what kills it. -/
theorem badHandleLlm_not_interpret :
    badHandleLlm wildOracle (infer "x")
      ≠ interpret (idHandler.sum (llmOracleHandler wildOracle)) (infer "x") := by
  rw [← handleLlm_eq_interpret]
  exact badHandleLlm_differs

/-! ### the oracle quantifier is over TOTAL DETERMINISTIC FUNCTIONS -/

def askTwice : Prog AgentSig (String × String) :=
  .vis (Sum.inr (LlmE.infer "x")) (fun a =>
    .vis (Sum.inr (LlmE.infer "x")) (fun b => .pure (a, b)))

theorem askTwice_handled (oracle : String → String) :
    askTwice.handleLlm oracle = Prog.pure (oracle "x", oracle "x") := rfl

/-- Two identical prompts in one program ALWAYS get the same answer.
No oracle in L30/L31's quantifier can answer otherwise. -/
theorem askTwice_answers_agree (oracle : String → String) (a b : String)
    (h : askTwice.handleLlm oracle = Prog.pure (a, b)) : a = b := by
  rw [askTwice_handled] at h
  injection h with h1
  exact (congrArg Prod.fst h1).symm.trans (congrArg Prod.snd h1)

/-! ### L30's right summand is FORCED (a categoricity the packet omits) -/

theorem llmOracleHandler_unique (oracle : String → String)
    (g : Handler LlmSig (Prog CasSig))
    (hg : ∀ (A : Type) (p : Prog AgentSig A),
        p.handleLlm oracle = interpret (idHandler.sum g) p) :
    g = llmOracleHandler oracle := by
  refine handlerExt (fun op => ?_)
  match op with
  | LlmE.infer q =>
    have h := hg String (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure)
    have hl : Prog.handleLlm oracle
          (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure)
        = Prog.pure (oracle q) := rfl
    have hr : interpret (idHandler.sum g)
          (Prog.vis (S := AgentSig) (Sum.inr (LlmE.infer q)) Prog.pure)
        = (g.handle (LlmE.infer q)).bind Prog.pure := rfl
    exact (Prog.bind_pure_right (g.handle (LlmE.infer q))).symm.trans
      (hr.symm.trans (h.symm.trans hl))

/-! ### L32, the row the packet leaves OWED, in two lines from L30 -/

theorem handleLlm_bind (oracle : String → String) {A B : Type}
    (p : Prog AgentSig A) (f : A → Prog AgentSig B) :
    (p.bind f).handleLlm oracle
      = (p.handleLlm oracle).bind (fun a => (f a).handleLlm oracle) := by
  simp only [handleLlm_eq_interpret]
  exact interpret_bind (idHandler.sum (llmOracleHandler oracle)) p f

/-! ## §6 failed break attempts, kept as record -/

/-- FAILED: the escape route "the `LawfulMonad` premise of ADQ-INL rules
out the counting target, so the refutation is outside the law". It does
not — both counting targets are lawful. -/
example : LawfulMonad Adversary.Counter := inferInstance
example : LawfulMonad CCounter := inferInstance
example : LawfulMonad (Prog CasSig) := inferInstance

/-- FAILED: "ADQ-INL is vacuous". `interpret_inl` inhabits the premise
at a BARE `Monad`, weaker than the premise asks. -/
example {S T : Sig} {A : Type} (p : Prog S A) :
    Prog.inl (T := T) p = Prog.inl p :=
  Prog.inl_unique (fun {_} q => Prog.inl q)
    (fun _ _ _ h g {_} q => interpret_inl h g q) p

/-! ## §7 the universe scope of the categoricity, read off the signatures -/

#check @liftCas
#check @Prog.handleLlm
#check @Prog.inl
#check @Prog.inl_unique
#check @handleLlm_eq_interpret
#check @handleLlm_liftCas

/-! ## §8 axiom census of this attack record -/

#print axioms inl_unique_one_target
#print axioms inl_unique_via_initiality
#print axioms narrowing_to_Id_fails
#print axioms sum_unique_iff
#print axioms sum_unique_needs_right_premise
#print axioms sum_unique_needs_left_premise
#print axioms doubleInl_fails_L23_premise
#print axioms doubleInl_factors
#print axioms doubleInl_bind'
#print axioms doubleInl_injective'
#print axioms swapTwoInl_not_interpret_inl
#print axioms swapTwoInl_not_monad_morphism
#print axioms dropInl_not_interpret_inl
#print axioms dropInl_not_injective
#print axioms putDoubleInl_not_interpret_inl
#print axioms no_Id_counter_for_CasSig
#print axioms badHandleLlm_liftCas
#print axioms badHandleLlm_not_interpret
#print axioms askTwice_answers_agree
#print axioms llmOracleHandler_unique
#print axioms handleLlm_bind

end PDD7Attack
