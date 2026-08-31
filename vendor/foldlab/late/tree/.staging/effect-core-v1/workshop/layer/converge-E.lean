import Cas.Lang.Representation
import Cas.Backend.Universal

/-!
# Convergence probe — author of position E

The common core I believe all five could sign, CHECKED.  Nothing below is
argued; every claim is a receipt in this file.

`cd library/cas && lake env lean <this file>`
-/

namespace ConvergeE
open Cas Cas.Lang

/-! ## 1. The content plane.  ONE signature; services are value-level KEYS.

This is the erasure move from position E, kept.  Position B's judge proved
its bridge theorem UNSTATABLE because `sigOf : List ServiceRef → Sig` must
satisfy `sigOf (canon (px ++ py)) = sigOf px ⊕ₛ sigOf py`, an equation
between TYPES needing signature normalisation that does not exist.  With
keys at the value level there is no `sigOf`, and §4 goes through. -/

abbrev SvcKey := String
abbrev CodeId := Nat          -- shipped form: `Cas.Schema.CodeRef`

/-- `Cas.Schema.SystemNode` (Schema/System.lean:208) at value-level keys,
with `acquires` added and `fresh` UNCHANGED (no nonce). -/
inductive LDesc where
  | empty
  | leaf     (key : SvcKey) (requires : List SvcKey) (ctor : CodeId)
  | acquires (key : SvcKey) (requires : List SvcKey) (acq rel : CodeId)
  | merge    (l r : LDesc)
  | provide  (inner outer : LDesc)
  | fresh    (inner : LDesc)
  deriving DecidableEq, Repr

def without (xs ys : List SvcKey) : List SvcKey := xs.filter (fun x => decide (x ∉ ys))

/-- `EmitLayer.residualOf` (Backend/EmitLayer.lean:243) at value-level keys. -/
def LDesc.provides : LDesc → List SvcKey
  | .empty => []
  | .leaf k _ _ => [k]
  | .acquires k _ _ _ => [k]
  | .merge l r => l.provides ++ r.provides
  | .provide _ o => o.provides
  | .fresh i => i.provides

def LDesc.requires : LDesc → List SvcKey
  | .empty => []
  | .leaf _ r _ => r
  | .acquires _ r _ _ => r
  | .merge l r => l.requires ++ r.requires
  | .provide i o => i.requires ++ without o.requires i.provides
  | .fresh i => i.requires

/-- Decidable ON CONTENT, where rc.112's `Exclude<R, Scope>` hides it. -/
def LDesc.acquiring : LDesc → Bool
  | .empty => false
  | .leaf _ _ _ => false
  | .acquires _ _ _ _ => true
  | .merge l r => l.acquiring || r.acquiring
  | .provide i o => i.acquiring || o.acquiring
  | .fresh i => i.acquiring

/-! ## 2. `provide` IS NOT ASSOCIATIVE — at the estate's OWN residual formula.

Four of five positions sold `provide_assoc` as free from `through_assoc`
(Universal.lean:739).  That theorem is about `Handler.through`.  It is not
the associativity of the `provide` whose requirement discharge
`EmitLayer.residualOf` already computes, and that one is FALSE. -/

def dA : LDesc := .leaf "A" [] 0
def dB : LDesc := .leaf "B" ["A"] 1
def dC : LDesc := .leaf "C" ["A"] 2

theorem provide_is_not_associative :
    (LDesc.provide (LDesc.provide dA dB) dC).requires
      ≠ (LDesc.provide dA (LDesc.provide dB dC)).requires := by decide

theorem provide_assoc_left_still_requires_A :
    (LDesc.provide (LDesc.provide dA dB) dC).requires = ["A"] := by decide

theorem provide_assoc_right_requires_nothing :
    (LDesc.provide dA (LDesc.provide dB dC)).requires = [] := by decide

/-! ## 3. The build.  An EFFECT, with a memo keyed on CONTENT.

Field fact, proved independently by A (`build_step_is_observable`),
C (`through_pays_twice`/`layer_pays_once`), D (`through_erases_the_build`)
and by my own judge against me (`position_E_reacquires_per_use`):
`Layer := Handler ROut (Prog RIn)` has no build step.  Conceded; repaired. -/

abbrev Inst := Nat
abbrev Ctx  := List (SvcKey × Inst)      -- rc.112's `Context<R>`: a key map
abbrev Memo := List (LDesc × Ctx)        -- key = content (shipped: its address)

structure St where
  next  : Inst
  trace : List Nat
  fins  : List Nat                       -- pending finalizers, innermost first
  deriving DecidableEq, Repr

/-- R18's ruled ORDER: state OUTSIDE error, so state survives the error
branch.  `EnsuringRepair.lean:361` is this shape at `Refusal`/`Word`. -/
def BuildM (A : Type) := St → Except String A × St

theorem BuildM_is_R18_order (A : Type) :
    BuildM A = ExceptT String (StateM St) A := rfl

instance : Monad BuildM where
  pure a := fun s => (.ok a, s)
  bind x f := fun s => match x s with
    | (.ok a, s') => f a s'
    | (.error e, s') => (.error e, s')

theorem pure_run (a : α) (s : St) : (pure a : BuildM α) s = (.ok a, s) := rfl
theorem bind_run (x : BuildM α) (f : α → BuildM β) (s : St) :
    (x >>= f) s = (match x s with
      | (.ok a, s') => f a s'
      | (.error e, s') => (.error e, s')) := rfl

def keys (c : Ctx) : List SvcKey := c.map Prod.fst

def newInst : BuildM Inst := fun s => (.ok s.next, { s with next := s.next + 1 })
def mark (n : Nat) : BuildM Unit := fun s => (.ok (), { s with trace := s.trace ++ [n] })
def pushFin (n : Nat) : BuildM Unit := fun s => (.ok (), { s with fins := n :: s.fins })
def refuse (msg : String) : BuildM α := fun _s => (.error msg, _s)

def needAll (env : Ctx) : List SvcKey → BuildM Unit
  | [] => pure ()
  | q :: rest => if q ∈ keys env then needAll env rest else refuse "missing service"

def memoFind? (m : Memo) (d : LDesc) : Option Ctx :=
  match m.find? (fun p => p.1 == d) with
  | some p => some p.2
  | none => none

/-- The memo check, isolated so the arms below have clean equations. -/
def memoized (m : Memo) (d : LDesc) (miss : BuildM (Memo × Ctx)) : BuildM (Memo × Ctx) :=
  match memoFind? m d with
  | some c => fun s => (.ok (m, c), s)
  | none => miss

def build (env : Ctx) : Memo → LDesc → BuildM (Memo × Ctx)
  | m, .empty => pure (m, [])
  | m, .leaf k rq c =>
      memoized m (.leaf k rq c) (do
        needAll env rq
        let i ← newInst
        mark c
        pure (((.leaf k rq c), [(k, i)]) :: m, [(k, i)]))
  | m, .acquires k rq a r =>
      memoized m (.acquires k rq a r) (do
        needAll env rq
        let i ← newInst
        mark a
        pushFin r                       -- REGISTERED ONCE, at the build
        pure (((.acquires k rq a r), [(k, i)]) :: m, [(k, i)]))
  | m, .merge l r => do
      let x ← build env m l
      let y ← build env x.1 r
      pure (((.merge l r), x.2 ++ y.2) :: y.1, x.2 ++ y.2)
  | m, .provide i o => do
      let x ← build env m i
      let y ← build (env ++ x.2) x.1 o
      pure (((.provide i o), y.2) :: y.1, y.2)
  | m, .fresh i => do
      let x ← build env [] i            -- EMPTY memo, and NOT recorded
      pure (m, x.2)

def st0 : St := { next := 0, trace := [], fins := [] }
def run (d : LDesc) : Except String (Memo × Ctx) × St := build [] [] d st0

/-! ### 3a. The build step exists: ONE acquisition, TWO uses. -/

def db      : LDesc := .acquires "Db" [] 100 900
def useL    : LDesc := .leaf "L" ["Db"] 1
def useR    : LDesc := .leaf "R" ["Db"] 2
def diamond : LDesc := .provide db (.merge useL useR)

theorem diamond_acquires_once : (run diamond).2.trace = [100, 1, 2] := by rfl
theorem diamond_registers_one_finalizer : (run diamond).2.fins = [900] := by rfl
theorem diamond_serves_both : (run diamond).1.map (fun r => keys r.2) = .ok ["L", "R"] := by rfl

/-! ### 3b. `fresh` needs NO nonce.  (Conceding to position B.) -/

theorem shared_builds_one : (run (.merge db db)).2.trace = [100] := by rfl
theorem fresh_builds_two :
    (run (.merge (.fresh db) (.fresh db))).2.trace = [100, 100] := by rfl
theorem fresh_is_not_share :
    (run (.merge (.fresh db) (.fresh db))).2.trace ≠ (run (.merge db db)).2.trace := by decide

/-! ### 3c. Ownership: the memo entry owns the resource (position B's C4). -/

theorem shared_registers_one_finalizer : (run (.merge db db)).2.fins = [900] := by rfl
theorem fresh_registers_two : (run (.merge (.fresh db) (.fresh db))).2.fins = [900, 900] := by rfl

/-! ### 3d. Release order is LIFO, by the fold's own push order. -/

def db2  : LDesc := .acquires "Db2" ["Db"] 101 901
def nest : LDesc := .provide db (.provide db2 (.leaf "U" ["Db2"] 3))

theorem nested_acquires_in_order : (run nest).2.trace = [100, 101, 3] := by rfl
theorem release_is_lifo : (run nest).2.fins = [901, 900] := by rfl

/-! ### 3e. R12 IS PRESERVED.  The built context IS a `Handler`.

`Handler`, `interpret`, `Handler.through`, `interpret_through`,
`through_assoc` all keep their jobs — at the TOWER axis (a service
implemented as a program over a lower signature, Tower.lean:65/71).
That axis is NOT layer `provide`; §2 shows why conflating them was the
field's shared error. -/

inductive SvcE where
  | ask (key : SvcKey)
  deriving DecidableEq, Repr
abbrev SvcE.Ans : SvcE → Type | .ask _ => Inst      -- shipped: `Addr32`
abbrev SvcSig : Sig := ⟨SvcE, SvcE.Ans⟩

def lookup? : Ctx → SvcKey → Option Inst
  | [], _ => none
  | (a, i) :: rest, k => if a = k then some i else lookup? rest k

/-- The built context, read as a semantics.  ONE signature, so no `sigOf`. -/
def ctxHandler (c : Ctx) : Handler SvcSig (Except String) where
  handle | .ask k => match lookup? c k with
                     | some i => .ok i
                     | none => .error "unbound service"

theorem lookup_of_mem_keys : ∀ (c : Ctx) (k : SvcKey),
    k ∈ keys c → (lookup? c k).isSome = true
  | [], _, h => by simp [keys] at h
  | (a, i) :: rest, k, h => by
      by_cases hk : a = k
      · simp [lookup?, hk]
      · have hr : k ∈ keys rest := by
          simp only [keys, List.map_cons, List.mem_cons] at h
          rcases h with h | h
          · exact absurd h.symm hk
          · simpa [keys] using h
        simp [lookup?, hk]
        exact lookup_of_mem_keys rest k hr

/-! ## 4. THE BRIDGE.  `residualOf` is SOUND against the builder.

The theorem the whole field owes and nobody has.  Position B's judge proved
it UNSTATABLE on a type-indexed carrier.  At one signature it is an
induction over `List String`. -/

def MemoOk (m : Memo) : Prop := ∀ p ∈ m, keys p.2 = p.1.provides

theorem keys_append (a b : Ctx) : keys (a ++ b) = keys a ++ keys b := by
  simp [keys]

theorem mem_without {q : SvcKey} {xs ys : List SvcKey}
    (h : q ∈ xs) (hn : q ∉ ys) : q ∈ without xs ys := by
  simp [without, List.mem_filter, h, hn]

theorem memoized_hit {m : Memo} {d : LDesc} {c : Ctx}
    {miss : BuildM (Memo × Ctx)} {s : St}
    (h : memoFind? m d = some c) : memoized m d miss s = (.ok (m, c), s) := by
  simp [memoized, h]

theorem memoized_miss {m : Memo} {d : LDesc} {miss : BuildM (Memo × Ctx)}
    (h : memoFind? m d = none) : memoized m d miss = miss := by
  simp [memoized, h]

theorem needAll_ok (env : Ctx) : ∀ (rq : List SvcKey) (s : St),
    (∀ q ∈ rq, q ∈ keys env) → needAll env rq s = (.ok (), s)
  | [], _, _ => rfl
  | q :: rest, s, h => by
      have hq : q ∈ keys env := h q (by simp)
      simp only [needAll, if_pos hq]
      exact needAll_ok env rest s (fun x hx => h x (by simp [hx]))

theorem memoFind_sound {m : Memo} {d : LDesc} {c : Ctx}
    (hm : MemoOk m) (h : memoFind? m d = some c) : keys c = d.provides := by
  unfold memoFind? at h
  cases hp : m.find? (fun p => p.1 == d) with
  | none => rw [hp] at h; exact absurd h (by simp)
  | some p =>
    rw [hp] at h
    have hc : p.2 = c := by simpa using h
    have hmem : p ∈ m := List.mem_of_find?_eq_some hp
    have hkey : p.1 = d := by simpa using List.find?_some hp
    have hk := hm p hmem
    rw [hc, hkey] at hk
    exact hk

theorem memoOk_cons {m : Memo} {d : LDesc} {c : Ctx}
    (hm : MemoOk m) (h : keys c = d.provides) : MemoOk ((d, c) :: m) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hrest
  · exact h
  · exact hm p hrest

/-- THE SANDWICH.  `requires` is SUFFICIENT (a description whose demands
the environment meets does not refuse) and `provides` is EXACT (the built
context's key set is the residual, on the nose). -/
theorem build_sound (d : LDesc) : ∀ (env : Ctx) (m : Memo) (s : St),
    MemoOk m → (∀ q ∈ d.requires, q ∈ keys env) →
    ∃ m' c s', build env m d s = (.ok (m', c), s') ∧ keys c = d.provides ∧ MemoOk m' := by
  induction d with
  | empty => intro env m s hm _; exact ⟨m, [], s, rfl, rfl, hm⟩
  | leaf k rq ct =>
    intro env m s hm hr
    cases hf : memoFind? m (LDesc.leaf k rq ct) with
    | some c => exact ⟨m, c, s, by simp [build, memoized_hit hf], memoFind_sound hm hf, hm⟩
    | none =>
      refine ⟨((LDesc.leaf k rq ct), [(k, s.next)]) :: m, [(k, s.next)],
              { next := s.next + 1, trace := s.trace ++ [ct], fins := s.fins },
              ?_, rfl, memoOk_cons hm rfl⟩
      simp [build, memoized_miss hf, bind_run, needAll_ok env rq s hr, newInst, mark, pure_run]
  | acquires k rq a r =>
    intro env m s hm hr
    cases hf : memoFind? m (LDesc.acquires k rq a r) with
    | some c => exact ⟨m, c, s, by simp [build, memoized_hit hf], memoFind_sound hm hf, hm⟩
    | none =>
      refine ⟨((LDesc.acquires k rq a r), [(k, s.next)]) :: m, [(k, s.next)],
              { next := s.next + 1, trace := s.trace ++ [a], fins := r :: s.fins },
              ?_, rfl, memoOk_cons hm rfl⟩
      simp [build, memoized_miss hf, bind_run, needAll_ok env rq s hr, newInst, mark, pushFin, pure_run]
  | merge l r ihl ihr =>
    intro env m s hm hr
    have hrl : ∀ q ∈ l.requires, q ∈ keys env := fun q hq =>
      hr q (by simp [LDesc.requires, hq])
    obtain ⟨m1, cl, s1, e1, k1, hm1⟩ := ihl env m s hm hrl
    have hrr : ∀ q ∈ r.requires, q ∈ keys env := fun q hq =>
      hr q (by simp [LDesc.requires, hq])
    obtain ⟨m2, cr, s2, e2, k2, hm2⟩ := ihr env m1 s1 hm1 hrr
    have hk : keys (cl ++ cr) = (LDesc.merge l r).provides := by
      rw [keys_append, k1, k2]; rfl
    exact ⟨_, cl ++ cr, s2, by simp [build, bind_run, e1, e2, pure_run], hk, memoOk_cons hm2 hk⟩
  | provide i o ihi iho =>
    intro env m s hm hr
    have hri : ∀ q ∈ i.requires, q ∈ keys env := fun q hq =>
      hr q (by simp [LDesc.requires, hq])
    obtain ⟨m1, ci, s1, e1, k1, hm1⟩ := ihi env m s hm hri
    have hro : ∀ q ∈ o.requires, q ∈ keys (env ++ ci) := by
      intro q hq
      rw [keys_append]
      by_cases hc : q ∈ i.provides
      · exact List.mem_append_right _ (by rw [k1]; exact hc)
      · refine List.mem_append_left _ (hr q ?_)
        simp only [LDesc.requires, List.mem_append]
        exact Or.inr (mem_without hq hc)
    obtain ⟨m2, co, s2, e2, k2, hm2⟩ := iho (env ++ ci) m1 s1 hm1 hro
    have hk : keys co = (LDesc.provide i o).provides := k2
    exact ⟨_, co, s2, by simp [build, bind_run, e1, e2, pure_run], hk, memoOk_cons hm2 hk⟩
  | fresh i ih =>
    intro env m s hm hr
    obtain ⟨m1, ci, s1, e1, k1, _⟩ := ih env [] s (by intro p hp; cases hp) hr
    exact ⟨m, ci, s1, by simp [build, bind_run, e1, pure_run], k1, hm⟩

/-- The corollary the emitted TypeScript's `RIn` needs and does not have
today: a CLOSED description builds without asking anybody for anything,
and answers exactly the services its residual advertises. -/
theorem closed_builds (d : LDesc) (h : d.requires = []) :
    ∃ m c s, build [] [] d st0 = (.ok (m, c), s) ∧ keys c = d.provides := by
  obtain ⟨m, c, s, e, k, _⟩ :=
    build_sound d [] [] st0 (by intro p hp; cases hp) (by simp [h])
  exact ⟨m, c, s, e, k⟩

/-- Non-vacuity: `requires` is not an over-approximation that never bites.
An OPEN description refuses, at exactly the key the residual names. -/
theorem open_description_refuses :
    (build [] [] dB st0).1 = .error "missing service" := by rfl

/-- The payoff of the bridge, stated where a consumer feels it: a closed
description builds, and the built context ANSWERS every service its
residual advertises.  This is what the emitted `ROut` currently asserts
with no theorem under it. -/
theorem built_answers_its_provides (d : LDesc) (h : d.requires = []) :
    ∃ m c s, build [] [] d st0 = (.ok (m, c), s)
      ∧ ∀ k ∈ d.provides, ((ctxHandler c).handle (.ask k)).isOk = true := by
  obtain ⟨m, c, s, e, k⟩ := closed_builds d h
  refine ⟨m, c, s, e, fun q hq => ?_⟩
  have : q ∈ keys c := by rw [k]; exact hq
  have hs := lookup_of_mem_keys c q this
  cases hl : lookup? c q with
  | none => rw [hl] at hs; simp at hs
  | some i => simp [ctxHandler, hl, Except.isOk, Except.toBool]

/-! ## 5. Exit-indexed finalization — position E's one keeper, portable.

Requirements-lane C9: rc.112's finalizers are exit-indexed
(`Scope.addFinalizerExit`), the ruled `ensuring` is exit-blind, and nobody
owned the gap.  Two finalizer BLOCK IDS keep it first-order (R7); the
diagonal proves it conservative over R18's ruled repair. -/

abbrev Tgt (σ α : Type) := σ → Except String α × σ

def ensuringT (body fin : Tgt σ α) : Tgt σ α := fun w =>
  match body w with
  | (.ok a, w1) => match fin w1 with
      | (.ok _, w2) => (.ok a, w2)
      | (.error r, w2) => (.error r, w2)
  | (.error r, w1) => (.error r, (fin w1).2)

def ensuringExitT (body onOk onErr : Tgt σ α) : Tgt σ α := fun w =>
  match body w with
  | (.ok a, w1) => match onOk w1 with
      | (.ok _, w2) => (.ok a, w2)
      | (.error r, w2) => (.error r, w2)
  | (.error r, w1) => (.error r, (onErr w1).2)

/-- CONSERVATIVE over the ruled repair: all four `ensuring` laws transfer. -/
theorem ensuringExitT_diagonal (body fin : Tgt σ α) :
    ensuringExitT body fin fin = ensuringT body fin := rfl

theorem ensuringExitT_never_replaces_the_refusal
    {body onOk onErr : Tgt σ α} {w w1 : σ} {r : String}
    (hb : body w = (.error r, w1)) :
    (ensuringExitT body onOk onErr w).1 = .error r := by
  simp [ensuringExitT, hb]

/-- The half `Except String (α × σ)` structurally cannot state. -/
theorem ensuringExitT_keeps_the_state
    {body onOk onErr : Tgt σ α} {w w1 w2 : σ} {r : String} {res : Except String α}
    (hb : body w = (.error r, w1)) (hf : onErr w1 = (res, w2)) :
    ensuringExitT body onOk onErr w = (.error r, w2) := by
  simp [ensuringExitT, hb, hf]

/-! ## 6. Receipts -/

#print axioms provide_is_not_associative
#print axioms provide_assoc_left_still_requires_A
#print axioms provide_assoc_right_requires_nothing
#print axioms BuildM_is_R18_order
#print axioms diamond_acquires_once
#print axioms diamond_registers_one_finalizer
#print axioms diamond_serves_both
#print axioms shared_builds_one
#print axioms fresh_builds_two
#print axioms fresh_is_not_share
#print axioms shared_registers_one_finalizer
#print axioms fresh_registers_two
#print axioms nested_acquires_in_order
#print axioms release_is_lifo
#print axioms needAll_ok
#print axioms memoFind_sound
#print axioms build_sound
#print axioms closed_builds
#print axioms open_description_refuses
#print axioms lookup_of_mem_keys
#print axioms built_answers_its_provides
#print axioms ensuringExitT_diagonal
#print axioms ensuringExitT_never_replaces_the_refusal
#print axioms ensuringExitT_keeps_the_state

end ConvergeE
