/-
  propose-B.lean — design probe for position B ("layer-is-a-DAG").

  Checked with:  cd library/cas && lake env lean <this file>
  This file is OUTSIDE every lake target and modifies nothing in library/.

  WHAT THIS FILE CLAIMS, AND WHAT IT DOES NOT.

  It does NOT re-declare a Layer carrier. `Cas.Schema.SystemNode`
  (`Cas/Schema/System.lean:208`) is already the R7-side layer DAG: a
  `cas_union` whose children are `StoreRef systemKindTag`, with
  `service` / `backing` / `opaque` / `merge` / `provide` / `provideMerge` /
  `fresh` arms.  The design proposes exactly ONE added arm (`scoped`) and
  a `build` fold; everything else is reuse.

  Because `SystemNode` lives in `library/cas` and this pass may not modify
  it, the probe carries a SHAPE MIRROR (`LNode`) with `Nat` addresses and
  `Nat` code references so the fold reduces and the facts below close by
  `rfl`.  Every arm of `LNode` except `scoped` and `stub` is an arm of
  `SystemNode` today; §0 pins that correspondence by construction so the
  mirror cannot silently drift.
-/
import Cas.Lang.Tower
import Cas.Backend.Universal
import Cas.Backend.Canon

namespace ProposeB

open Cas Cas.Lang Cas.Schema Cas.Backend

/-! ## 0. The datum — `SystemNode` plus one arm

The real carrier, unchanged, with the proposed arm written beside it so
the difference is exactly one constructor. -/

/-- The proposed added arm, as a standalone record so it can be exhibited
without editing `Cas.Schema.SystemNode`.  In the shipped design this is
`| scoped (acquire release : CodeRef) (provides : ServiceRef)
   (requires : List ServiceRef)` on the existing union — the growth path
`Cas/Schema/System.lean:105-107` sanctions ("By an ARM, on the Exchange
precedent — never by a sibling carrier"). -/
structure ScopedArm where
  acquire : CodeRef
  release : CodeRef
  provides : ServiceRef
  requires : List ServiceRef

/-- The existing arms are real: this pins that the mirror's arm list is
the union's arm list, by naming each constructor. -/
example (c : CodeRef) (p : ServiceRef) (ps rs : List ServiceRef)
    (i o : StoreRef systemKindTag) : List SystemNode :=
  [ .service c p rs, .backing c ps rs, .«opaque» c "note" ps rs
  , .merge [i], .provide i o, .provideMerge i o, .fresh i ]

/-! ## 1. The probe mirror -/

abbrev Key := String
abbrev Code := Nat
abbrev NodeAddr := Nat

/-- `SystemNode`'s arms with `Nat` addresses, plus the proposed `scoped`
arm and a `stub` leaf that stands for any leaf whose constructor refuses
(a `CodeRef` that throws).  `backing` / `opaque` are omitted: they are
`service` with a list of provided keys and nothing in this file
distinguishes them. -/
inductive LNode where
  | service (ctor : Code) (provides : Key) (requires : List Key)
  | scoped (acquire release : Code) (provides : Key) (requires : List Key)
  | stub
  | merge (parts : List NodeAddr)
  | provide (inner outer : NodeAddr)
  | provideMerge (inner outer : NodeAddr)
  | fresh (inner : NodeAddr)

/-- A resolution table, children-first — `EmitLayer.Resolved`'s own
discipline (`Cas/Backend/EmitLayer.lean:236`). -/
abbrev Table := List (NodeAddr × LNode)

def find? (t : Table) (a : NodeAddr) : Option LNode :=
  (t.find? fun row => row.1 == a).map (·.2)

/-! ## 2. The built environment, and the build's state

`Ctx` is `Context<R>`: an ORDERED association list from service key to the
built instance.  In the shipped design the value is the target-monad
handler the leaf's `CodeRef` denotes and the key index is recovered by
`EmitLayer.residualOf`; here it is the acquisition ordinal so sharing is
observable.

`BState` is a bare product of existing types — no structure is minted:
  * the acquisition/release TRACE (stands for `Word`);
  * the finalizer stack, innermost first (stands for
    `List (ScopeId × Addr32)`);
  * the instance counter.

`BuildM` is R18's forced transformer ORDER — state OUTSIDE error, so the
trace survives the error branch (`EC1-CE045`,
`reraise_is_finalizer_blind`). -/

abbrev Inst := Nat
abbrev Ctx := List (Key × Inst)
abbrev BState := List Nat × List Code × Nat
abbrev BuildM := ExceptT Refusal (StateM BState)

/-- The memo map.  THE MEMO KEY IS THE CONTENT ADDRESS (R4) — not JS
reference identity (`Layer.ts:432`). -/
abbrev Memo := List (NodeAddr × Ctx)

def memoFind? (m : Memo) (a : NodeAddr) : Option Ctx :=
  (m.find? fun row => row.1 == a).map (·.2)

def emit (x : Nat) : BuildM Unit :=
  fun s => (.ok (), (s.1 ++ [x], s.2.1, s.2.2))

def newInst : BuildM Inst :=
  fun s => (.ok s.2.2, (s.1, s.2.1, s.2.2 + 1))

def pushFin (c : Code) : BuildM Unit :=
  fun s => (.ok (), (s.1, c :: s.2.1, s.2.2))

def refuse (r : Refusal) : BuildM A := fun s => (.error r, s)

/-- Run every registered finalizer, innermost first, and clear the stack.
This is the `sequential` strategy — `internal/effect.ts:3817-3821`.  The
`parallel` strategy is a DIFFERENT clause and is not modelled
(`GR-S4`; packet collision C2). -/
def closeScope : BuildM Unit :=
  fun s => (.ok (), (s.1 ++ s.2.1, [], s.2.2))

/-- `ensuring` at the build's target — `EnsuringRepair.ensuringT`
(`workshop/counterexamples/EnsuringRepair.lean:547`) with the answer type
generalized.  Finalizer runs on both paths; the body's refusal is never
replaced. -/
def ensuringB (body : BuildM A) (fin : BuildM Unit) : BuildM A := fun s =>
  match body s with
  | (.ok x, s₁) =>
    match fin s₁ with
    | (.ok _, s₂) => (.ok x, s₂)
    | (.error r, s₂) => (.error r, s₂)
  | (.error r, s₁) => (.error r, (fin s₁).2)

/-! ## 3. `build` — the fold that `Handler.through` does not have

`Handler.through` inlines a service implementation at every call site, so
two uses pay two acquisitions (the estate scout's `through_has_no_build`,
axiom-free).  A DAG has a build MOMENT: one visit per address, recorded in
the memo map.  `fresh` is the one arm that does not memoize — it builds
its child against an EMPTY memo and discards the result, which is exactly
`Layer.fresh`'s `makeMemoMapUnsafe()` (`Layer.ts:3850`, read off in
`Cas/Schema/System.lean:59-68`).

Fuel is the table's size; the DAG is acyclic by construction because a
`StoreRef` can only name content that already exists
(`System.lean:139-143`). -/
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
            let i ← newInst
            emit i
            let c : Ctx := [(prov, i)]
            pure ((a, c) :: m, c)
        | .scoped _ rel prov _ => do
            let i ← newInst
            emit i
            pushFin rel
            let c : Ctx := [(prov, i)]
            pure ((a, c) :: m, c)
        | .fresh inner => do
            let r ← build f t [] inner
            pure (m, r.2)
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
            let r ← parts.foldlM
              (fun (acc : Memo × Ctx) (p : NodeAddr) => do
                let r ← build f t acc.1 p
                pure (r.1, acc.2 ++ r.2))
              ((m, ([] : Ctx)) : Memo × Ctx)
            pure ((a, r.2) :: r.1, r.2)

/-- The public destructor: build a topology in its own scope, closing it
whatever happens.  `Layer.build` (`Layer.ts:800`) with the scope explicit. -/
def buildScoped (f : Nat) (t : Table) (a : NodeAddr) : BuildM Ctx :=
  ensuringB (do let r ← build f t [] a; pure r.2) closeScope

def s0 : BState := ([], [], 0)

/-! ## 4. `acquires` — the classification the requirements scout says
nobody owns

Whether a layer registers a finalizer is invisible in the pin's TYPE
(`effectContext` always yields `Exclude<R, Scope.Scope>`,
`Layer.ts:1479-1481`).  On a first-order DAG it is a DECIDABLE PREDICATE
OVER CONTENT — one table walk, no proof obligation.  This is the whole
argument for the data representation. -/
def acquires : Nat → Table → NodeAddr → Bool
  | 0, _, _ => true
  | f + 1, t, a =>
    match find? t a with
    | none => false
    | some node =>
      match node with
      | .scoped _ _ _ _ => true
      | .service _ _ _ => false
      | .stub => false
      | .fresh i => acquires f t i
      | .provide i o => acquires f t i || acquires f t o
      | .provideMerge i o => acquires f t i || acquires f t o
      | .merge ps => ps.any (acquires f t)

/-! ## 5. The tables under test -/

/-- A diamond: one shared `Db`, two dependents, merged. -/
def diamond : Table :=
  [ (0, .service 0 "Db" [])
  , (1, .service 1 "A" ["Db"])
  , (2, .service 2 "B" ["Db"])
  , (3, .provide 0 1)
  , (4, .provide 0 2)
  , (5, .merge [3, 4])
  , (6, .fresh 0)
  , (7, .merge [6, 6])
  , (8, .merge [0, 0]) ]

/-- Two scoped acquisitions and then an unresolved node — a build that
fails AFTER acquiring. -/
def failing : Table :=
  [ (0, .scoped 10 100 "R1" [])
  , (1, .scoped 11 101 "R2" [])
  , (2, .merge [0, 1])
  , (3, .provide 2 99)          -- 99 is not in the table: the build refuses
  , (4, .merge [0, 1]) ]

/-! ## 6. What the fold proves

Every fact below is `rfl` on the closed term — no axioms beyond those the
kernel needs to reduce it. -/

/-- **L-B1 — sharing is a fold property, not a policy.**  The diamond
acquires `Db` ONCE: three instances total, not four, and the trace is
`[0,1,2]`.  This is `GR-L5` discharged by the representation itself.
`Handler.through` cannot state it (`through_has_no_build`). -/
theorem diamond_shares : (build 8 diamond [] 5 s0).2.1 = [0, 1, 2] := rfl

/-- **L-B2 — `fresh` needs NO nonce.**  `GR-L6` claims that under content
addressing `fresh l = fresh l` collapses and `fresh` becomes
unrepresentable.  That is false for a fold whose memo is threaded: the
`fresh` arm neither reads nor writes the memo at its own address, so TWO
OCCURRENCES of one address build TWO instances. -/
theorem fresh_does_not_share : (build 8 diamond [] 7 s0).2.1 = [0, 1] := rfl

/-- And the contrast that makes L-B2 non-vacuous: the same shape without
`fresh` shares, so the two arms are observably different at one address. -/
theorem merge_of_one_address_shares : (build 8 diamond [] 8 s0).2.1 = [0] := rfl

theorem fresh_is_not_share : (build 8 diamond [] 7 s0).2.1 ≠ (build 8 diamond [] 8 s0).2.1 := by
  decide

/-- **L-B3 — R18 conformance.**  The build acquires two resources, then
refuses; the finalizers still run, LIFO, and the trace SURVIVES the error
branch.  `[0,1,101,100]`: acquire R1, acquire R2, release R2, release R1. -/
theorem build_releases_on_refusal :
    (buildScoped 8 failing 3 s0).2.1 = [0, 1, 101, 100] := rfl

/-- The refusal itself is re-raised unchanged — the finalizer does not
replace it (`ensuring_never_replaces_the_refusal`, R18 law 3). -/
theorem refusal_survives_the_finalizers :
    (buildScoped 8 failing 3 s0).1 = .error (.failed "layer build: unresolved node") := rfl

/-- **L-B4 — release is LIFO under the sequential strategy**, on the
success path too. -/
theorem release_lifo_sequential :
    (buildScoped 8 failing 4 s0).2.1 = [0, 1, 101, 100] := rfl

/-- **L-B5 — `acquires` is decided on content.**  The classification the
requirements scout (§5) says "the S17 note implies but does not name" is a
table walk. -/
theorem acquires_decided :
    acquires 8 diamond 5 = false ∧ acquires 8 failing 3 = true := by decide

/-- **L-B6 — the pure fragment leaves the scope alone.**  When `acquires`
is false the finalizer stack is untouched, so `buildScoped` and `build`
agree; when it is true they do not.  (Stated here at the two witnesses;
the general implication is NEW WORK — see the report.) -/
theorem pure_build_registers_nothing :
    (build 8 diamond [] 5 s0).2.2.1 = [] := rfl

/-! ## 7. The other half — the pure fragment's denotation is the estate's
own handler algebra, and its laws are already discharged

`build`'s `provide` arm denotes `Handler.through`; on the acquisition-free
fragment nothing else is happening, so composition's identity and
associativity come from `Cas/Backend/Universal.lean` verbatim at
`M := Prog U`.  These are the estate scout's `LayerProbe` claims, restated
here so this file carries both halves of the design. -/

section PureDenotation

variable {ROut RMid RIn : Sig}

/-- The pure fragment's denotation: `Layer ROut RIn := Handler ROut (Prog RIn)`. -/
abbrev LayerH (ROut RIn : Sig) := Handler ROut (Prog RIn)

def provideL (outer : LayerH ROut RMid) (inner : LayerH RMid RIn) : LayerH ROut RIn :=
  outer.through inner

def emptyL : LayerH ROut ROut := idHandler

def mergeL {M : Type → Type v} (l : Handler ROut M) (r : Handler RMid M) :
    Handler (ROut ⊕ₛ RMid) M := l.sum r

theorem provideL_assoc {S T U V : Sig}
    (a : LayerH S T) (b : LayerH T U) (c : LayerH U V) :
    provideL (provideL a b) c = provideL a (provideL b c) :=
  through_assoc leftUnit_of_lawful bindAssoc_of_lawful a b c

theorem provideL_id_right (a : LayerH ROut RIn) : provideL a emptyL = a :=
  through_id_right a

theorem provideL_id_left (a : LayerH ROut RIn) : provideL emptyL a = a :=
  through_id_left rightUnit_of_lawful a

/-- Launch: the same operation at a non-`Prog` target.  `interpret_through`
(`Tower.lean:71`) IS build-then-run = run-against-the-composite. -/
theorem launch_through {M : Type → Type v} [Monad M] [LawfulMonad M]
    (l : LayerH ROut RIn) (h : Handler RIn M) (p : Prog ROut A) :
    interpret h (interpret l p) = interpret (l.through h) p :=
  interpret_through l h p

/-- `provideMerge` is DERIVED, not primitive. -/
def provideMergeL (outer : LayerH ROut RIn) (inner : LayerH RIn RIn) :
    Handler (ROut ⊕ₛ RIn) (Prog RIn) :=
  (provideL outer inner).sum inner

end PureDenotation

/-! ## 8. The content plane's algebra is ALREADY PROVED

`Cas/Backend/Canon.lean` carries 18 theorems about service SETS on the
first-order side.  Three of them are ledger rows the requirements scout
graded MUST/SHOULD with no owner. -/

/-- `GR-E5` — last-wins shadowing, on content. -/
example {xs : List ServiceRef} {s : ServiceRef} (h : s ∈ canonServices xs) :
    ∃ pre post, xs = pre ++ s :: post ∧ s.key ∉ post.map (·.key) :=
  canonServices_last_wins h

/-- `GR-E7` — unrelated-service commutation, with the disjointness premise
the scout says the law needs, and it is exactly the premise on main. -/
example {xs ys : List ServiceRef} (hnd : (xs.map (·.key)).Nodup) (hp : xs.Perm ys) :
    canonServices xs = canonServices ys :=
  canonServices_perm hnd hp

/-- Idempotence of context combination. -/
example (xs : List ServiceRef) : canonServices (canonServices xs) = canonServices xs :=
  canonServices_idem xs

end ProposeB

/-! ## 9. Memoization is SEMANTICS, not an optimization

The same fold with the memo removed — the tree fold, which is what
`Handler.through` does when it inlines. -/

namespace ProposeB

def buildNoMemo : Nat → Table → NodeAddr → BuildM Ctx
  | 0, _, _ => refuse (.failed "layer build: out of fuel")
  | f + 1, t, a =>
    match find? t a with
    | none => refuse (.failed "layer build: unresolved node")
    | some node =>
      match node with
      | .stub => refuse (.failed "layer build: constructor refused")
      | .service _ prov _ => do
          let i ← newInst; emit i; pure [(prov, i)]
      | .scoped _ rel prov _ => do
          let i ← newInst; emit i; pushFin rel; pure [(prov, i)]
      | .fresh inner => buildNoMemo f t inner
      | .provide inner outer => do
          let _ ← buildNoMemo f t inner
          buildNoMemo f t outer
      | .provideMerge inner outer => do
          let ci ← buildNoMemo f t inner
          let co ← buildNoMemo f t outer
          pure (ci ++ co)
      | .merge parts => do
          parts.foldlM (fun (acc : Ctx) (p : NodeAddr) => do
            let c ← buildNoMemo f t p
            pure (acc ++ c)) ([] : Ctx)

/-- **L-B7 — the memo is observable.**  Without it the diamond acquires
`Db` TWICE.  So one-instance-per-address is a SEMANTIC claim about the
fold, not a cost model: the two folds disagree on the trace. -/
theorem no_memo_builds_the_diamond_twice :
    (buildNoMemo 8 diamond 5 s0).2.1 = [0, 1, 2, 3] := rfl

theorem memo_is_observable :
    (build 8 diamond [] 5 s0).2.1 ≠ (buildNoMemo 8 diamond 5 s0).2.1 := by decide

/-! ### A shared SCOPED service: the release count is what memoization
decides.  `GR-L5`(c) and packet collision C4 (`EC1-T062` presumes one
owner per resource). -/

def sharedScoped : Table :=
  [ (0, .scoped 10 100 "Db" [])
  , (1, .service 1 "A" ["Db"])
  , (2, .service 2 "B" ["Db"])
  , (3, .provide 0 1)
  , (4, .provide 0 2)
  , (5, .merge [3, 4]) ]

/-- **L-B8 — memoized: acquired once, RELEASED ONCE.**  The finalizer
`100` appears exactly once in the trace. -/
theorem shared_scoped_releases_once :
    (buildScoped 8 sharedScoped 5 s0).2.1 = [0, 1, 2, 100] := rfl

/-- **L-B8′ — unmemoized: acquired twice, RELEASED TWICE.**  So the memo
key decides how many times a finalizer runs, which is `EC1-T062`'s
subject.  `Handler.through`'s carrier cannot state either side. -/
theorem shared_scoped_unmemoized_releases_twice :
    (ensuringB (buildNoMemo 8 sharedScoped 5) closeScope s0).2.1
      = [0, 1, 2, 3, 100, 100] := rfl

/-! ## 10. The residual: `provide` keeps the outer's keys, `provideMerge`
keeps both — the fold agrees with `EmitLayer.residualOf`
(`Cas/Backend/EmitLayer.lean:243-259`). -/

def resid : Table :=
  [ (0, .service 0 "Db" [])
  , (1, .service 1 "A" ["Db"])
  , (2, .provide 0 1)
  , (3, .provideMerge 0 1) ]

theorem provide_keeps_the_outer :
    (build 8 resid [] 2 s0).1 = .ok ([(2, [("A", 1)]), (1, [("A", 1)]), (0, [("Db", 0)])],
      [("A", 1)]) := rfl

theorem provideMerge_keeps_both :
    ((build 8 resid [] 3 s0).1.toOption.map (·.2)) = some [("Db", 0), ("A", 1)] := rfl

/-! ## 11. Receipts -/

#print axioms diamond_shares
#print axioms fresh_does_not_share
#print axioms fresh_is_not_share
#print axioms build_releases_on_refusal
#print axioms refusal_survives_the_finalizers
#print axioms release_lifo_sequential
#print axioms acquires_decided
#print axioms memo_is_observable
#print axioms shared_scoped_releases_once
#print axioms shared_scoped_unmemoized_releases_twice
#print axioms provide_keeps_the_outer
#print axioms provideMerge_keeps_both
#print axioms provideL_assoc
#print axioms provideL_id_left
#print axioms launch_through

end ProposeB

/-! ## 12. The residual fold is not a proposal — it is on main

`EmitLayer.residualOf` (`Cas/Backend/EmitLayer.lean:243`) already computes
`provide`'s dependency discharge over the REAL `SystemNode`, in Effect's
own algebra: the composite requires the inner's requirements plus the
outer's requirements MINUS what the inner provides.  Run here on real
values, with real addresses, so the claim is checked and not merely cited. -/

namespace ProposeB

open Cas Cas.Schema Cas.Backend

private def aI : Cas.Addr32 := Subtype.mk (List.replicate 32 (1 : UInt8)) (by simp)
private def aO : Cas.Addr32 := Subtype.mk (List.replicate 32 (2 : UInt8)) (by simp)

private def svcDb : ServiceRef := { key := "Db", name := "Db", path := "p" }
private def svcA : ServiceRef := { key := "A", name := "A", path := "p" }

private def resolved : Resolved :=
  [ (aI, "db", { provides := [svcDb], requires := [] })
  , (aO, "a", { provides := [svcA], requires := [svcDb] }) ]

/-! ### L-B9 — dependency discharge, on main, over the real carrier
`provide inner outer` provides only the outer's keys and requires
NOTHING: the inner discharged `Db`.  `provideMerge` keeps both sides'
keys with the same discharge.

These are `#guard`s, not theorems: `canonServices` ends in
`List.mergeSort`, which is well-founded and does not reduce in the
kernel, so `decide`/`rfl` cannot close them.  `Cas/Schema/System.lean`
uses the same instrument for the same reason.  A kernel theorem here
would need the `mergeSort` normalization `Cas/Backend/Canon.lean` proves
about — that is real work and it is NOT done. -/

#guard (residualOf resolved (.provide (StoreRef.mk aI) (StoreRef.mk aO))).map
        (fun r => (r.provides.map (·.key), r.requires.map (·.key)))
      == some (["A"], [])

#guard (residualOf resolved (.provideMerge (StoreRef.mk aI) (StoreRef.mk aO))).map
        (fun r => (r.provides.map (·.key), r.requires.map (·.key)))
      == some (["A", "Db"], [])

end ProposeB
