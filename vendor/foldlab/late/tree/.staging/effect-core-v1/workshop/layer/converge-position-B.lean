/-
  converge-position-B.lean — CONVERGENCE probe for position B.

  Checked with:  cd library/cas && lake env lean <this file>
  Outside every lake target; modifies nothing in library/.

  WHAT THIS FILE IS FOR.

  Position B was killed on ONE thing: the content->type bridge
  `sigOf : List ServiceRef -> Sig` and the theorem
  `sigOf E (canonServices (px ++ py)) = sigOf E px ⊕ₛ sigOf E py`.
  That is an equation between TYPES: `Sig.Op : Type`, `canonServices`
  SORTS and DEDUPS, and `⊕ₛ` is neither commutative nor idempotent nor
  associative on the nose.  The judge is right.  It is not "unwritten
  work"; it is unstatable without a signature-normalization apparatus
  that nothing in the estate has and that nobody budgeted.

  THIS FILE TESTS THE REPAIR, AND THE REPAIR COMES FROM A RIVAL.
  Position E's move — forced by R7, not chosen — is that a
  type-indexed service set is not first-order content, so there is ONE
  service signature and provides/requires are VALUE-level keys.  Take
  that, and `sigOf` DOES NOT EXIST.  There is nothing to bridge, because
  the type index never varied.

  E was killed for having no build step (its `LDesc.build` is a pure
  function, so its `.acquires` arm compiles to a handler clause that
  re-enters per dispatch).  B's memo fold is exactly the missing piece,
  and under a uniform signature the memo is HOMOGENEOUS — no dependent
  type, no sigma, no universe bump, no `DecidableEq Sig`.

  So the two fatal flaws are complementary.  This file checks that
  taking both repairs at once actually elaborates and actually
  separates the facts each position was sold on.
-/
import Cas.Lang.Tower
import Cas.Backend.Universal
import Cas.Backend.SumAlgebra

namespace ConvergeB

open Cas Cas.Lang

/-! ## §1  THE UNIFORM SERVICE SIGNATURE (position E's move, R7-forced)

One signature.  Provides/requires are VALUE-level key lists, never type
indices.  This is the whole repair: with `Sig` fixed there is no
`sigOf`, hence no type-level bridge to prove. -/

abbrev SvcKey := String

inductive SvcE where
  | ask (key : SvcKey)
  deriving DecidableEq, Repr

abbrev SvcE.Ans : SvcE → Type | _ => Nat        -- an instance handle

abbrev SvcSig : Sig := ⟨SvcE, SvcE.Ans⟩

/-! ## §2  THE BUILD TARGET (R18's forced order: state OUTSIDE error) -/

abbrev Trace    := List Nat
abbrev FinStack := List Nat
abbrev BState   := Trace × FinStack
abbrev Tgt      := ExceptT Refusal (StateM BState)

/-- The built context, as a HANDLER.  Homogeneous: one signature. -/
abbrev Ctx := Handler SvcSig Tgt

def emitT (n : Nat) : Tgt Unit := fun s => (.ok (), (s.1 ++ [n], s.2))
/-- Acquire: record the code, return a FRESH instance handle. -/
def acquire (code : Nat) : Tgt Nat := fun s => (.ok s.1.length, (s.1 ++ [code], s.2))
def pushFin (rel : Nat) : Tgt Unit := fun s => (.ok (), (s.1, rel :: s.2))
def closeScope : Tgt Unit := fun s => (.ok (), (s.1 ++ s.2, []))
def refuseT (r : Refusal) : Tgt A := fun s => (Except.error r, s)

/-! ## §3  THE BUILT CONTEXT IS FIRST-ORDER DATA

Effect's `Context<R>` is `ReadonlyMap<string, any>`.  Under a uniform
signature the estate's answer is the same shape and it is CONTENT: an
association list of key to instance handle.  `Handler` is its
DENOTATION, not its carrier.  This is what makes the memo hashable. -/

abbrev Assoc := List (SvcKey × Nat)

def look? : Assoc → SvcKey → Option Nat
  | [], _ => none
  | (k, i) :: r, q => if q = k then some i else look? r q

/-- The denotation of a built context: answer from the assoc, else
forward to what is below.  No `Sig.sum`, no type index. -/
def ctxOf (c : Assoc) (below : Ctx) : Ctx where
  handle | .ask k => match look? c k with
    | some i => pure i
    | none   => below.handle (.ask k)

def emptyCtx : Ctx where
  handle | .ask _ => refuseT (.failed "unresolved service")

/-! ## §4  THE BRIDGE — the theorem position B was killed for not having.

Under a uniform signature it is statable AND provable, because it is an
equation between HANDLER VALUES at ONE signature, not between types. -/

theorem look_append (c d : Assoc) (k : SvcKey) :
    look? (c ++ d) k = ((look? c k).orElse (fun _ => look? d k)) := by
  induction c with
  | nil => cases h : look? d k <;> simp [look?, Option.orElse, h]
  | cons hd tl ih =>
    obtain ⟨k', i⟩ := hd
    by_cases hk : k = k' <;> simp [look?, hk, ih]

/-- **THE BRIDGE.**  Content-plane merge (list append) agrees with
value-plane composition (context stacking).  This is the
`residual_agrees_with_the_denotation` obligation, discharged. -/
theorem ctxOf_append (c d : Assoc) (below : Ctx) :
    ctxOf (c ++ d) below = ctxOf c (ctxOf d below) := by
  apply Handler.ext
  intro op
  cases op with
  | ask k =>
    show (match look? (c ++ d) k with | some i => pure i | none => below.handle (.ask k))
       = (match look? c k with
          | some i => pure i
          | none => (ctxOf d below).handle (.ask k))
    rw [look_append]
    cases h : look? c k <;> simp [Option.orElse, ctxOf]

/-- **THE UNIVERSAL PROPERTY** — the `Handler.sum_unique` analogue for
service merge, which `sum_unique` provably cannot reach (`Sig.sum` is
disjoint; this merge OVERLAPS).  Cheap here because the signature is
uniform: any handler answering from the assoc where it is defined and
deferring below where it is not IS `ctxOf`.  So merge is DETERMINED,
not merely defined. -/
theorem ctxOf_unique (c : Assoc) (below k : Ctx)
    (hin  : ∀ q i, look? c q = some i → k.handle (.ask q) = pure i)
    (hout : ∀ q, look? c q = none → k.handle (.ask q) = below.handle (.ask q)) :
    k = ctxOf c below := by
  apply Handler.ext; intro op; cases op with
  | ask q =>
    cases h : look? c q with
    | none   => rw [hout q h]; simp [ctxOf, h]
    | some i => rw [hin q i h]; simp [ctxOf, h]

/-- Its unit half: the empty context contributes nothing. -/
theorem ctxOf_nil (below : Ctx) : ctxOf [] below = below := by
  apply Handler.ext; intro op; cases op; rfl

/-! ## §5  THE NODE TABLE — position B's DAG, unchanged in shape.

Shape mirror of `Cas.Schema.SystemNode` with `Nat` addresses so the
fold reduces.  Arms match the shipped union plus B's proposed `scoped`. -/

abbrev Addr := Nat

inductive LNode where
  | service (code : Nat) (provides : SvcKey) (requires : List SvcKey)
  | scoped  (acq rel : Nat) (provides : SvcKey) (requires : List SvcKey)
  | merge   (parts : List Addr)
  | provide (inner outer : Addr)
  | fresh   (inner : Addr)
  deriving Repr

abbrev Table := List (Addr × LNode)
abbrev Memo  := List (Addr × Assoc)          -- HOMOGENEOUS.  First-order.

def findN? : Table → Addr → Option LNode
  | [], _ => none
  | (a, n) :: r, q => if q = a then some n else findN? r q

def findM? : Memo → Addr → Option Assoc
  | [], _ => none
  | (a, c) :: r, q => if q = a then some c else findM? r q

/-! ## §6  BUILD — the step E lacks and B supplies.

Acquisition happens HERE, in `Tgt`, once per address.  The clause the
built context hands out is `pure handle`, so a second USE does not
re-acquire.  That is the entire content of "there is a build step". -/

def build : Nat → Table → Memo → Addr → Tgt (Memo × Assoc)
  | 0, _, _, _ => refuseT (.failed "build: out of fuel")
  | f + 1, t, m, a =>
    match findM? m a with
    | some c => pure (m, c)                        -- SHARING: one visit per address
    | none =>
      match findN? t a with
      | none => refuseT (.failed "build: unresolved node")
      | some node =>
        match node with
        | .service code prov _ => do
            let i ← acquire code
            let c : Assoc := [(prov, i)]
            pure ((a, c) :: m, c)
        | .scoped acq rel prov _ => do
            let i ← acquire acq
            pushFin rel                            -- REGISTRATION, at first visit
            let c : Assoc := [(prov, i)]
            pure ((a, c) :: m, c)
        | .fresh inner => do
            let r ← build f t [] inner             -- EMPTY memo, not recorded
            pure (m, r.2)
        | .provide inner outer => do
            let ri ← build f t m inner
            let ro ← build f t ri.1 outer
            pure ((a, ro.2) :: ro.1, ro.2)
        | .merge parts => do
            let r ← parts.foldlM (fun acc p => do
                      let r ← build f t acc.1 p
                      pure (r.1, acc.2 ++ r.2)) ((m, []) : Memo × Assoc)
            pure ((a, r.2) :: r.1, r.2)

/-- The TREE fold — same clauses, memo never consulted.  Used only to
show memoization is observable, i.e. SEMANTICS not optimization. -/
def buildNoMemo : Nat → Table → Addr → Tgt Assoc
  | 0, _, _ => refuseT (.failed "build: out of fuel")
  | f + 1, t, a =>
    match findN? t a with
    | none => refuseT (.failed "build: unresolved node")
    | some node =>
      match node with
      | .service code prov _ => do let i ← acquire code; pure [(prov, i)]
      | .scoped acq rel prov _ => do
          let i ← acquire acq; pushFin rel; pure [(prov, i)]
      | .fresh inner => buildNoMemo f t inner
      | .provide inner outer => do
          let _ ← buildNoMemo f t inner
          buildNoMemo f t outer
      | .merge parts => parts.foldlM (fun acc p => do
          let r ← buildNoMemo f t p; pure (acc ++ r)) ([] : Assoc)

def run (p : Tgt A) : Except Refusal A × BState := p ([], [])

/-! ## §7  THE BUILD STEP, KERNEL-CHECKED.

This is the falsifier that killed position E, run against the
convergence design.  A consumer that uses one service TWICE. -/

def useTwice (k : SvcKey) : Prog SvcSig (Nat × Nat) :=
  .vis (.ask k) (fun i => .vis (.ask k) (fun j => .pure (i, j)))

/-- Position E's shape: acquisition is a HANDLER CLAUSE, re-entered per
dispatch.  Two uses, two acquisitions. -/
def perUseCtx (k : SvcKey) (code : Nat) : Ctx where
  handle | .ask k' => if k' = k then acquire code else refuseT (.failed "no")

theorem clause_acquisition_pays_per_use :
    (run (interpret (perUseCtx "Db" 100) (useTwice "Db"))).2.1 = [100, 100] := rfl

/-- The convergence design: acquisition happens in the BUILD.  One
node, one acquisition, and BOTH uses get the SAME handle. -/
def tOne : Table := [(0, .service 100 "Db" [])]

theorem build_acquisition_pays_per_build :
    (run (do let r ← build 8 tOne [] 0
             interpret (ctxOf r.2 emptyCtx) (useTwice "Db"))).2.1 = [100] := rfl

theorem build_hands_out_one_instance :
    (run (do let r ← build 8 tOne [] 0
             interpret (ctxOf r.2 emptyCtx) (useTwice "Db"))).1 = .ok (0, 0) := rfl

/-- Non-vacuity: the two really differ. -/
theorem build_step_is_observable :
    (run (interpret (perUseCtx "Db" 100) (useTwice "Db"))).2.1
      ≠ (run (do let r ← build 8 tOne [] 0
                 interpret (ctxOf r.2 emptyCtx) (useTwice "Db"))).2.1 := by decide

/-! ## §8  SHARING — position B's surviving buys, re-checked here.

The diamond: two consumers of one `Db` address. -/

def tDiamond : Table :=
  [ (0, .merge [1, 2])
  , (1, .provide 3 4)
  , (2, .provide 3 5)
  , (3, .service 100 "Db" [])
  , (4, .service 101 "A" ["Db"])
  , (5, .service 102 "B" ["Db"]) ]

theorem diamond_shares : (run (build 12 tDiamond [] 0)).2.1 = [100, 101, 102] := rfl

theorem diamond_unshared_pays_twice :
    (run (buildNoMemo 12 tDiamond 0)).2.1 = [100, 101, 100, 102] := rfl

theorem memo_is_observable :
    (run (build 12 tDiamond [] 0)).2.1 ≠ (run (buildNoMemo 12 tDiamond 0)).2.1 := by decide

/-! ## §9  FRESH needs no nonce (B's refutation of GR-L6, re-checked).

`fresh` neither reads nor writes the memo at its own address and builds
its child against an EMPTY memo.  Freshness is a property of the
TRAVERSAL, not of the key — so two occurrences of ONE address give two
instances, with no nonce and no carrier change. -/

def tFresh  : Table := [(0, .merge [1, 1]), (1, .fresh 2), (2, .service 100 "Db" [])]
def tShared : Table := [(0, .merge [2, 2]), (2, .service 100 "Db" [])]

theorem fresh_does_not_share  : (run (build 12 tFresh  [] 0)).2.1 = [100, 100] := rfl
theorem shared_address_shares : (run (build 12 tShared [] 0)).2.1 = [100] := rfl
theorem fresh_is_not_share :
    (run (build 12 tFresh [] 0)).2.1 ≠ (run (build 12 tShared [] 0)).2.1 := by decide

/-! ## §10  LIFETIME — the one fact no rival can state.

The memo entry owns the resource: the finalizer is pushed at the
moment the node is FIRST VISITED, and there is exactly one such moment
per address.  This is `EC1-T062` / collision C4, settled by
construction rather than by redefining "registered". -/

def tScopedDiamond : Table :=
  [ (0, .merge [1, 2])
  , (1, .provide 3 4)
  , (2, .provide 3 5)
  , (3, .scoped 100 200 "Db" [])
  , (4, .service 101 "A" ["Db"])
  , (5, .service 102 "B" ["Db"]) ]

def buildScoped (f : Nat) (t : Table) (a : Addr) : Tgt Assoc := fun s =>
  match (do let r ← build f t [] a; pure r.2 : Tgt Assoc) s with
  | (.ok x, s₁) => match closeScope s₁ with
      | (.ok _, s₂)   => (.ok x, s₂)
      | (.error r, s₂) => (.error r, s₂)
  | (.error r, s₁) => (.error r, (closeScope s₁).2)   -- word SURVIVES the error branch

theorem shared_scoped_releases_once :
    (run (buildScoped 12 tScopedDiamond 0)).2.1 = [100, 101, 102, 200] := rfl

/-- Same DAG, tree fold: the finalizer runs TWICE.  So the memo key
decides how many times a finalizer runs — memoization is a LIFETIME
decision, not a cost model. -/
def buildScopedNoMemo (f : Nat) (t : Table) (a : Addr) : Tgt Assoc := fun s =>
  match (buildNoMemo f t a) s with
  | (.ok x, s₁) => match closeScope s₁ with
      | (.ok _, s₂) => (.ok x, s₂)
      | (.error r, s₂) => (.error r, s₂)
  | (.error r, s₁) => (.error r, (closeScope s₁).2)

theorem unshared_scoped_releases_twice :
    (run (buildScopedNoMemo 12 tScopedDiamond 0)).2.1 = [100, 101, 100, 102, 200, 200] := rfl

/-! ## §11  R18 — finalizers observe failure AND retain state. -/

def tFails : Table :=
  [ (0, .merge [1, 2])
  , (1, .scoped 100 200 "R1" [])
  , (2, .provide 3 4)
  , (3, .scoped 101 201 "R2" [])
  , (4, .service 999 "A" ["R2"]) ]

def tRefuses : Table :=
  [ (0, .merge [1, 2])
  , (1, .scoped 100 200 "R1" [])
  , (2, .scoped 101 201 "R2" [])
  , (3, .merge [0, 77]) ]        -- 77 is unresolved

theorem build_releases_on_refusal :
    (run (buildScoped 12 tRefuses 3)).2.1 = [100, 101, 201, 200] := rfl

theorem refusal_survives_the_finalizers :
    (run (buildScoped 12 tRefuses 3)).1 = .error (.failed "build: unresolved node") := rfl

theorem release_is_lifo : (run (buildScoped 12 tFails 0)).2.1 = [100, 101, 999, 201, 200] := rfl

/-! ## §12  WHAT `Sig.sum` IS STILL FOR.

The uniform-signature move does NOT delete `Handler.sum` — it corrects
what it was being used for.  `Sig.sum` composes LANGUAGES (services,
scope, store); service MERGE is `Assoc` append on content.  These were
being conflated, which is why `Handler.sum_unique` kept being cited for
a merge it cannot reach. -/

inductive ScopeE where
  | ensuringExit (body onOk onErr : Nat)      -- E's exit-indexed form, first-order
  deriving DecidableEq, Repr
abbrev ScopeE.Ans : ScopeE → Type | _ => Nat
abbrev ScopeSig : Sig := ⟨ScopeE, ScopeE.Ans⟩

abbrev LayerSig : Sig := SvcSig ⊕ₛ ScopeSig

/-- `Handler.sum` keeps its job at the LANGUAGE level, with
`Handler.sum_unique` (SumAlgebra.lean:212) still its universal
property — it just is not the service merge. -/
def layerFloor (svc : Ctx) (scp : Handler ScopeSig Tgt) : Handler LayerSig Tgt :=
  svc.sum scp

example (svc : Ctx) (scp : Handler ScopeSig Tgt)
    (k : Handler LayerSig Tgt)
    (hl : ∀ op, k.handle (Sum.inl op) = svc.handle op)
    (hr : ∀ op, k.handle (Sum.inr op) = scp.handle op) :
    k = layerFloor svc scp := Handler.sum_unique svc scp k hl hr

/-! ## §13  THE PURE FRAGMENT — and `through_monoid` IS RECOVERED.

Position E claimed the uniform-signature move recovers `through_monoid`
(Universal.lean:785) and was refuted, correctly, because E's own carrier
is `Handler SvcSig (Prog LayerSig)` — two DIFFERENT signatures, so not
endomorphisms.  But the claim is right about the PURE FRAGMENT, whose
target is `Prog SvcSig`: there the estate's own monoid statement applies
VERBATIM, with no `liftL` and no new lemma.  Checked. -/

abbrev LayerH := Handler SvcSig (Prog SvcSig)

def provideL (o i : LayerH) : LayerH := o.through i
def emptyL : LayerH := idHandler

/-- All three laws at once, from the estate theorem the other four
positions each declared inapplicable. -/
example (t u v : LayerH) :
    (t.through u).through v = t.through (u.through v)
      ∧ t.through emptyL = t
      ∧ emptyL.through t = t :=
  through_monoid t u v

/-! ## §14  RECEIPTS -/

#print axioms ctxOf_append
#print axioms ctxOf_nil
#print axioms clause_acquisition_pays_per_use
#print axioms build_acquisition_pays_per_build
#print axioms build_hands_out_one_instance
#print axioms build_step_is_observable
#print axioms diamond_shares
#print axioms diamond_unshared_pays_twice
#print axioms memo_is_observable
#print axioms fresh_does_not_share
#print axioms shared_address_shares
#print axioms fresh_is_not_share
#print axioms shared_scoped_releases_once
#print axioms unshared_scoped_releases_twice
#print axioms build_releases_on_refusal
#print axioms refusal_survives_the_finalizers
#print axioms release_is_lifo
#print axioms look_append
#print axioms ctxOf_unique

end ConvergeB
