import Test.Dogfood.Scenario.Atomic.Model
import Test.Dogfood.Scenario.Frame
import Effect4.Laws.Program.HeapSites
import Effect4.Laws.Api.AuthorBuild

/-!
# Atomic write sites and request-stage accounting

Placement: store-typing, R4, steps of the scenario claim `atomic`.
Consumers: `Atomic.bounded`, `Atomic.counted` and `Atomic.committed`.
Reach: the built shop and every session-admitted script at the original budgets.
The write-site proof serves the cell-invariant law. The observation algebra serves the stage law.
Neither proves progress, a host transaction or a lowered run.
The two remaining planned obligations retain their assumptions explicitly.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.Atomic.Store

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Run (ControlHistory history_control)
open Effect4.Program.HeapSites
open Test.Dogfood.Scenario (Move)

/-- A successful shop build retains its empty row table. Consumer: `scenario_control`. -/
theorem shop_table (b : Api.Built) (hb : Api.Author.build (shop .none) = .ok b) : b.table = [] :=
  (Api.Author.build_retains hb).2.1

/-- The script's history admits controls only, since the shop declares no host row. -/
theorem scenario_control (b : Api.Built) (hb : Api.Author.build (shop .none) = .ok b)
    (moves : List Move) : ControlHistory b budget.compileFuel
      (Scenario.play (opened b) moves).machine :=
  history_control (shop_table b hb) (Scenario.history b "atomic" budget "" moves)

/-- The scenario's observation, read off a machine. `observe` reads a run only through its
machine (`observe_eq`). -/
def observeM (m : NativeMachine) : Observation :=
  let decisions := requestFibers.map fun fiber => outcomeOf ((m.fiber? fiber).bind RunFiber.exit)
  { decisions := decisions
    window := m.state.refs[0]?
    account := m.state.refs[1]?
    completed := (decisions.filter fun outcome => outcome.isAdmitted || outcome == .rejected).length
    cleanups := entries (m.state.refs[2]?) }

theorem observe_eq (s : Run) : observe s = observeM s.machine := rfl

def UsedOk (v : Val) : Prop := natField (some v) "used" ≤ 3

/-! ## 5. The stages of the requests, `counted` and `committed`

`counted` and `committed` relate the window, the account, the cleanup log and the requests'
exits. One cell's predicate cannot carry them: the window counts decisions with no identity, so
"each request decides once" is a fact of each request fiber's position in its code. The
relational invariant gives each request a stage (a ghost: an interrupted request's stage is not
readable from the machine once its code is gone) and says what the stores and the exits say of
the stages (`StagesFit`). The algebra from `StagesFit` to the two goals is proved here outright;
the existence of the stages is the program-specific planned goal `shop_stages`. -/

/-- A request's stage: waiting for its decision, admitted with no deposit yet, deposited, or
rejected. -/
inductive Stage
  | waiting
  | admitted
  | deposited
  | rejected
deriving DecidableEq

/-- Whether a stage is one that the window's `admitted` field counts. -/
def Stage.counts : Stage → Bool
  | .admitted | .deposited => true
  | _ => false

/-- **What a stage assignment says of an observation**: `g id` is request `id`'s stage. The
window's counts are the stages' counts; a request's deposit stands once when it deposited and
not otherwise; an admitted exit follows a deposit and a rejected exit a rejection; request 2's
planted failure follows a cleanup entry that saw a decided request. -/
structure StagesFit (g : Nat → Stage) (o : Observation) : Prop where
  admitted : o.admitted = (requests.filter fun id => (g id).counts).length
  rejected : o.rejected = (requests.filter fun id => decide (g id = .rejected)).length
  deposit : ∀ id ∈ requests, o.deposits.count id = if g id = .deposited then 1 else 0
  length : o.deposits.length = (requests.filter fun id => decide (g id = .deposited)).length
  owned : o.deposits.all requests.contains = true
  exits : ∀ x ∈ o.decisions.zip requests, (x.1.isAdmitted = true → g x.2 = .deposited) ∧
    (x.1 = .rejected → g x.2 = .rejected)
  six : o.decisions.length = 6
  completed : o.completed =
    (o.decisions.filter fun outcome => outcome.isAdmitted || outcome == .rejected).length
  cleaned : o.decisions[1]? = some .failedBehind →
    (o.sawAt 2).any (fun seen => decide (1 ≤ seen)) = true

/-- **The stages exist** (program-specific; new). Every machine of every history of the shop
admits a stage assignment that fits its observation.

Placement. Concept `store-typing`, requirement R4. Question: the scenario clauses `counted` and
`committed`, whose step this is. Consumers: `Atomic.counted`, `Atomic.committed`; with a
`cleaned` stage per request it also serves `cleans_once` (R11, another seat's). Reach: the
built shop, every compile budget, every control history. Not established: that a request
decides (progress), anything of a lowered run. Route (`README.md`, section S2): the shop's
per-fiber positions, by the fiber-local residual law (G2), and one check per write site and per
interruption. -/
@[semantics "store-typing" (requirement := R4)]
proof_goal shop_stages (b : Api.Built) (hb : Effect4.Api.Author.build (shop .none) = .ok b)
    (compileFuel : Nat) :
    ∀ m, ControlHistory b compileFuel m → ∃ g, StagesFit g (observeM m)

/-! ### The observation algebra (proved) -/

theorem length_filter_zip_fst {α β : Type} (p : α → Bool) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      ((xs.zip ys).filter fun x => p x.1).length = (xs.filter p).length
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have ih := length_filter_zip_fst p xs ys (Nat.succ.inj h)
    simp only [List.zip_cons_cons, List.filter_cons]
    cases p x
    · exact ih
    · simp only [if_true, List.length_cons, ih]
  | [], _ :: _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)

/-- Filters of a zip by the right component count as filters of the right list. -/
theorem length_filter_zip_snd {α β : Type} (q : β → Bool) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      ((xs.zip ys).filter fun x => q x.2).length = (ys.filter q).length
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have ih := length_filter_zip_snd q xs ys (Nat.succ.inj h)
    simp only [List.zip_cons_cons, List.filter_cons]
    cases q y
    · exact ih
    · simp only [if_true, List.length_cons, ih]
  | [], _ :: _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], h => absurd h (Nat.succ_ne_zero _)

/-- A filter by a stronger test is no longer. -/
theorem length_filter_le_of_imp {γ : Type} (p q : γ → Bool) :
    ∀ l : List γ, (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl 0
  | x :: l, h => by
    have ih := length_filter_le_of_imp p q l fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.filter_cons]
    cases hp : p x with
    | true =>
      rw [h x List.mem_cons_self hp]
      simp only [if_true, List.length_cons]
      exact Nat.succ_le_succ ih
    | false =>
      cases q x
      · exact ih
      · simp only [if_true, List.length_cons]
        exact Nat.le_succ_of_le ih

/-- Two disjoint filters together are no longer than the list. -/
theorem length_filter_add_le {γ : Type} (p q : γ → Bool) :
    ∀ l : List γ, (∀ x ∈ l, p x = true → q x = false) →
      (l.filter p).length + (l.filter q).length ≤ l.length
  | [], _ => Nat.le_refl 0
  | x :: l, h => by
    have ih := length_filter_add_le p q l fun y hy => h y (List.mem_cons_of_mem x hy)
    cases hp : p x with
    | true =>
      have hq := h x List.mem_cons_self hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by rw [hq]; exact Bool.false_ne_true),
        List.length_cons, List.length_cons]
      omega
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true), List.length_cons]
      cases hq : q x with
      | true =>
        rw [List.filter_cons_of_pos hq, List.length_cons]
        omega
      | false =>
        rw [List.filter_cons_of_neg (by rw [hq]; exact Bool.false_ne_true)]
        omega

/-- A filter that keeps the length keeps every element. -/
theorem all_of_length_filter {γ : Type} (p : γ → Bool) :
    ∀ l : List γ, (l.filter p).length = l.length → ∀ x ∈ l, p x = true
  | [], _, _, hx => absurd hx List.not_mem_nil
  | x :: l, h, y, hy => by
    cases hp : p x with
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true), List.length_cons] at h
      have bound := List.length_filter_le p l
      omega
    | true =>
      rw [List.filter_cons_of_pos hp, List.length_cons, List.length_cons] at h
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hp
      · exact all_of_length_filter p l (Nat.succ.inj h) y hy

/-- The six request numbers. -/
theorem requests_length : requests.length = 6 := rfl

theorem mem_of_mem_zip_right {α β : Type} {x : α × β} :
    ∀ {xs : List α} {ys : List β}, x ∈ xs.zip ys → x.2 ∈ ys
  | [], _, h => absurd h List.not_mem_nil
  | _ :: _, [], h => absurd h List.not_mem_nil
  | a :: xs, b :: ys, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem b (mem_of_mem_zip_right h)

theorem mem_of_mem_zip_left {α β : Type} {x : α × β} :
    ∀ {xs : List α} {ys : List β}, x ∈ xs.zip ys → x.1 ∈ xs
  | [], _, h => absurd h List.not_mem_nil
  | _ :: _, [], h => absurd h List.not_mem_nil
  | a :: xs, b :: ys, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_of_mem_zip_left h)

/-- An admitted outcome is not the rejected one. -/
theorem not_rejected_of_admitted : ∀ outcome : RequestOutcome, outcome.isAdmitted = true →
    (outcome == .rejected) = false
  | .admitted, _ => rfl
  | .failedBehind, _ => rfl
  | .pending, h => absurd h Bool.false_ne_true
  | .rejected, h => absurd h Bool.false_ne_true
  | .interrupted _, h => absurd h Bool.false_ne_true
  | .other, h => absurd h Bool.false_ne_true

/-- **`counted` from the stages** (the algebra; proved). -/
theorem counted_of_fit {g : Nat → Stage} {o : Observation} (h : StagesFit g o) :
    o.counted = true := by
  have lengths : o.decisions.length = requests.length := h.six
  -- the outcome tests read through the stages, at every request
  have admittedLe : (o.decisions.filter RequestOutcome.isAdmitted).length ≤ o.admitted := by
    rw [h.admitted, ← length_filter_zip_fst _ _ _ lengths,
      ← length_filter_zip_snd (fun id => (g id).counts) _ _ lengths]
    refine length_filter_le_of_imp _ _ _ fun x hx hadm => ?_
    rw [(h.exits x hx).1 hadm]
    rfl
  have rejectedLe : (o.decisions.filter (· == .rejected)).length ≤ o.rejected := by
    rw [h.rejected, ← length_filter_zip_fst _ _ _ lengths,
      ← length_filter_zip_snd (fun id => decide (g id = .rejected)) _ _ lengths]
    refine length_filter_le_of_imp _ _ _ fun x hx hrej => ?_
    rw [(h.exits x hx).2 (beq_iff_eq.mp hrej)]
    rfl
  have sumLe : o.admitted + o.rejected ≤ 6 := by
    rw [h.admitted, h.rejected]
    refine length_filter_add_le _ _ requests fun id _ hc => ?_
    cases hg : g id <;> rw [hg] at hc
    · cases hc
    · rfl
    · rfl
    · cases hc
  have lengthLe : o.deposits.length ≤ o.admitted := by
    rw [h.length, h.admitted]
    refine length_filter_le_of_imp _ _ requests fun id _ hd => ?_
    rw [of_decide_eq_true hd]
    rfl
  have perRequest : ((o.decisions.zip requests).all fun (outcome, id) =>
      if outcome.isAdmitted then o.deposits.count id == 1
      else if outcome == .rejected then o.deposits.count id == 0
      else decide (o.deposits.count id ≤ 1)) = true := by
    refine List.all_eq_true.mpr fun x hx => ?_
    obtain ⟨outcome, id⟩ := x
    dsimp only
    have hid : id ∈ requests := mem_of_mem_zip_right hx
    have hcount := h.deposit id hid
    obtain ⟨hadm, hrej⟩ := h.exits (outcome, id) hx
    cases hA : outcome.isAdmitted with
    | true =>
      rw [hcount, hadm hA]
      rfl
    | false =>
      cases hR : outcome == .rejected with
      | true =>
        have hg : g id = .rejected := hrej (beq_iff_eq.mp hR)
        rw [hcount, hg]
        rfl
      | false =>
        show decide (o.deposits.count id ≤ 1) = true
        rw [hcount]
        cases g id <;> rfl
  have complete : (o.completed != 6 ||
      (o.admitted == (o.decisions.filter RequestOutcome.isAdmitted).length &&
        o.rejected == (o.decisions.filter (· == .rejected)).length &&
        o.deposits.length == o.admitted)) = true := by
    cases hne : (o.completed != 6) with
    | true => rfl
    | false =>
      have hsix : o.completed = 6 := bne_eq_false_iff_eq.mp hne
      have every : ∀ x ∈ o.decisions, (x.isAdmitted || x == .rejected) = true := by
        refine all_of_length_filter _ o.decisions ?_
        rw [← h.completed, hsix, h.six]
      -- at a completed request, each outcome test is a stage test
      have stage : ∀ x ∈ o.decisions.zip requests,
          x.1.isAdmitted = (g x.2).counts ∧ (x.1 == .rejected) = decide (g x.2 = .rejected) ∧
            decide (g x.2 = .deposited) = (g x.2).counts := by
        intro x hx
        have hor := every x.1 (mem_of_mem_zip_left hx)
        obtain ⟨hadm, hrej⟩ := h.exits x hx
        cases hA : x.1.isAdmitted with
        | true =>
          rw [hadm hA, not_rejected_of_admitted x.1 hA]
          exact ⟨rfl, rfl, rfl⟩
        | false =>
          rw [hA, Bool.false_or] at hor
          rw [hrej (beq_iff_eq.mp hor), hor]
          exact ⟨rfl, rfl, rfl⟩
      have admittedEq : o.admitted = (o.decisions.filter RequestOutcome.isAdmitted).length := by
        rw [h.admitted, ← length_filter_zip_fst _ _ _ lengths,
          ← length_filter_zip_snd (fun id => (g id).counts) _ _ lengths]
        exact congrArg List.length (List.filter_congr fun x hx => (stage x hx).1.symm)
      have rejectedEq : o.rejected = (o.decisions.filter (· == .rejected)).length := by
        rw [h.rejected, ← length_filter_zip_fst _ _ _ lengths,
          ← length_filter_zip_snd (fun id => decide (g id = .rejected)) _ _ lengths]
        exact congrArg List.length (List.filter_congr fun x hx => (stage x hx).2.1.symm)
      have depositsEq : o.deposits.length = o.admitted := by
        rw [h.length, h.admitted, ← length_filter_zip_snd (fun id => decide (g id = .deposited)) _ _
          lengths, ← length_filter_zip_snd (fun id => (g id).counts) _ _ lengths]
        exact congrArg List.length (List.filter_congr fun x hx => (stage x hx).2.2)
      rw [Bool.false_or, beq_iff_eq.mpr admittedEq, beq_iff_eq.mpr rejectedEq,
        beq_iff_eq.mpr depositsEq]
      rfl
  unfold Observation.counted
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨perRequest, admittedLe⟩, rejectedLe⟩, sumLe⟩, lengthLe⟩, h.owned⟩, complete⟩

/-- **`committed` from the stages** (the algebra; proved). -/
theorem committed_of_fit {g : Nat → Stage} {o : Observation} (h : StagesFit g o)
    (hfail : o.decisions[1]? = some .failedBehind) : o.committed = true := by
  have hzip : ((RequestOutcome.failedBehind, 2) : RequestOutcome × Nat) ∈
      o.decisions.zip requests := by
    apply List.mem_of_getElem? (i := 1)
    rw [List.getElem?_zip_eq_some]
    exact ⟨hfail, rfl⟩
  have hg : g 2 = .deposited := (h.exits _ hzip).1 rfl
  have hcount : o.deposits.count 2 = 1 := by
    rw [h.deposit 2 (by decide), hg]
    rfl
  have hadm : 1 ≤ o.admitted := by
    rw [h.admitted]
    exact List.length_pos_of_mem (a := 2) (List.mem_filter.mpr ⟨by decide, by rw [hg]; rfl⟩)
  show ((o.deposits.count 2 == 1) && decide (1 ≤ o.admitted) &&
    (o.sawAt 2).any fun seen => decide (1 ≤ seen)) = true
  rw [hcount, decide_eq_true hadm, h.cleaned hfail]
  rfl
/-- A record read after a set: the set field reads the new value, every other field what it read. -/
theorem read_after_set {v v' x : Val} {name : String} (h : Record.set v name x = some v')
    (n : String) :
    Record.read false v' n = if name = n then some x else Record.read false v n := by
  unfold Record.set at h
  cases he : Record.entries v with
  | none =>
    rw [he] at h
    cases h
  | some fields =>
    rw [he] at h
    have hv' : Record.frame (Field.canonBy Field.bytesKey ((name, x) :: fields)) = v' :=
      Option.some.inj h
    subst hv'
    have hnd := Field.canonBy_names_nodup (key := Field.bytesKey)
      ((name, x) :: fields)
    have hentries : Record.entries (Record.frame (Field.canonBy Field.bytesKey ((name, x) :: fields))) =
        some (Field.canonBy Field.bytesKey ((name, x) :: fields)) := by
      simp only [Record.entries, Record.frame, Program.recordParts?, Option.bind_eq_bind,
        Option.bind_some, Typed.readColumns_frame, if_pos hnd]
    unfold Record.read Record.lookup
    rw [hentries, he]
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true, if_false,
      Field.firstOf_canonBy Field.bytesKey_injective, Field.firstOf]

def tfield (d : Nat) (name : String) : Term := .field .required (.var d) name
def tsucc (t : Term) : Term := .app "succ" (.cons t .nil)
def tpair (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

def decisionAt (d : Nat) : Term :=
  .app "ite" (.cons (.app "lt" (.cons (tfield d "used") (.cons (.lit (.nat 3)) .nil)))
    (.cons (tpair (.lit (.bool true))
        (.recordSet (.recordSet (.var d) "used" (tsucc (tfield d "used")))
          "admitted" (tsucc (tfield d "admitted"))))
    (.cons (tpair (.lit (.bool false)) (.recordSet (.var d) "rejected" (tsucc (tfield d "rejected"))))
    .nil)))

theorem heapOk_poke {P : Val → Prop} {refs : RefHeap} (q : RefKey) {v : Val}
    (h : HeapOk P refs) (hv : P v) : HeapOk P (refPoke refs q v) := by
  intro i w hw
  unfold refPoke at hw
  rw [List.getElem?_set] at hw
  split at hw
  · split at hw
    · cases hw
      exact hv
    · cases hw
  · exact h i w hw

theorem read_required (a : Val) (n : String) :
    Record.read (decide (FieldReadMode.required = FieldReadMode.optional)) a n =
      Record.read false a n := rfl
theorem toVal_nat (n : Nat) : (Lit.nat n).toVal = some (.nat n) := rfl
theorem toVal_bool (b : Bool) : (Lit.bool b).toVal = some (.bool b) := rfl
theorem atom_lt (u n : Nat) : nativeAtom "lt" [.nat u, .nat n] = some (.bool (decide (u < n))) := rfl
theorem atom_pair (x y : Val) : nativeAtom "pair" [x, y] = some (.list [x, y]) := rfl
theorem atom_ite (c : Bool) (x y : Val) :
    nativeAtom "ite" [.bool c, x, y] = some (if c then x else y) := rfl
theorem atom_succ (u : Nat) : nativeAtom "succ" [.nat u] = some (.nat (u + 1)) := rfl

theorem atom_succ_inv {v w : Val} (h : nativeAtom "succ" [v] = some w) :
    ∃ u, v = .nat u ∧ w = .nat (u + 1) := by
  cases v with
  | nat u => exact ⟨u, rfl, (Option.some.inj h).symm⟩
  | unit => cases h
  | bool _ => cases h
  | str _ => cases h
  | bytes _ => cases h
  | list _ => cases h
  | pair _ _ => cases h
  | none => cases h
  | some _ => cases h
  | ctor _ _ => cases h
  | ref _ _ => cases h
  | handle _ _ => cases h
  | negInt _ => cases h
  | float _ => cases h

/-- `natField` of a value whose `used` field reads a natural. -/
theorem natField_used {v : Val} {n : Nat} (h : Record.read false v "used" = some (.nat n)) :
    natField (some v) "used" = n := by
  unfold natField
  show (match Record.read false v "used" with
    | some (.nat n) => n
    | _ => 0) = n
  rw [h]

/-- **The decision keeps the used bound**: its answer is a pair whose window satisfies `UsedOk`,
from a window that does. -/
theorem decision_used {env : List Val} {a x : Val}
    (hx : evalTerm (env ++ [a]) (decisionAt env.length) = some x) (ha : UsedOk a) :
    ∃ b v, x = .list [.bool b, v] ∧ UsedOk v := by
  simp only [decisionAt, tfield, tsucc, tpair, evalTerm, evalTerms, List.getElem?_concat_length,
    Option.bind_eq_bind, Option.bind_some, read_required, toVal_nat, toVal_bool] at hx
  cases hu : Record.read false a "used" with
  | none =>
    rw [hu] at hx
    cases hx
  | some vu =>
    rw [hu] at hx
    simp only [Option.bind_some] at hx
    cases hs : nativeAtom "succ" [vu] with
    | none =>
      rw [hs] at hx
      simp only [Option.bind_none] at hx
      cases hl : nativeAtom "lt" [vu, Val.nat 3] <;> rw [hl] at hx <;> cases hx
    | some su =>
      obtain ⟨u, rfl, rfl⟩ := atom_succ_inv hs
      simp only [atom_lt, Option.bind_some, atom_succ] at hx
      cases ht1 : Record.set a "used" (Val.nat (u + 1)) with
      | none =>
        rw [ht1] at hx
        cases hx
      | some t1 =>
        rw [ht1] at hx
        simp only [Option.bind_some] at hx
        cases had : Record.read false a "admitted" with
        | none =>
          rw [had] at hx
          cases hx
        | some vad =>
          rw [had] at hx
          simp only [Option.bind_some] at hx
          cases hsa : nativeAtom "succ" [vad] with
          | none =>
            rw [hsa] at hx
            cases hx
          | some sa =>
            rw [hsa] at hx
            simp only [Option.bind_some] at hx
            cases ht2 : Record.set t1 "admitted" sa with
            | none =>
              rw [ht2] at hx
              cases hx
            | some t2 =>
              rw [ht2] at hx
              simp only [Option.bind_some, atom_pair] at hx
              cases hrj : Record.read false a "rejected" with
              | none =>
                rw [hrj] at hx
                cases hx
              | some vrj =>
                rw [hrj] at hx
                simp only [Option.bind_some] at hx
                cases hsr : nativeAtom "succ" [vrj] with
                | none =>
                  rw [hsr] at hx
                  cases hx
                | some sr =>
                  rw [hsr] at hx
                  simp only [Option.bind_some] at hx
                  cases hf1 : Record.set a "rejected" sr with
                  | none =>
                    rw [hf1] at hx
                    cases hx
                  | some f1 =>
                    rw [hf1] at hx
                    simp only [Option.bind_some, atom_pair, atom_ite] at hx
                    cases hlt : decide (u < 3) with
                    | true =>
                      rw [hlt] at hx
                      refine ⟨true, t2, (Option.some.inj hx).symm, ?_⟩
                      have hread : Record.read false t2 "used" = some (.nat (u + 1)) := by
                        rw [read_after_set ht2 "used", if_neg (by decide),
                          read_after_set ht1 "used", if_pos rfl]
                      unfold UsedOk
                      rw [natField_used hread]
                      have := of_decide_eq_true hlt
                      omega
                    | false =>
                      rw [hlt] at hx
                      refine ⟨false, f1, (Option.some.inj hx).symm, ?_⟩
                      have hread : Record.read false f1 "used" = some (.nat u) := by
                        rw [read_after_set hf1 "used", if_neg (by decide), hu]
                      unfold UsedOk
                      rw [natField_used hread]
                      have bound : natField (some a) "used" ≤ 3 := ha
                      rw [natField_used hu] at bound
                      exact bound

/-- A `Ref.modify` step reads the cell once, evaluates the term once, and writes the pair's
second item. -/
theorem refModify_step {q : RefKey} {f : Term} {env : List Val} {s s' : Stores} {ans : Val}
    (h : syncOpStep (.refModify q f env) s = some (s', ans)) :
    ∃ a x r, refPeek s.refs q = some a ∧ evalTerm (env ++ [a]) f = some x ∧
      Store.Image.ofTuple2 Store.Image.ident Store.Image.ident x = some r ∧
      s'.refs = refPoke s.refs q r.2 := by
  have h' : (refStep (.refModify q f env) s.refs).map
      (fun step => ({ s with refs := step.2 }, step.1)) = some (s', ans) := h
  cases hp : refPeek s.refs q with
  | none =>
    simp only [refStep, hp, Option.bind_none, Option.map_none] at h'
    cases h'
  | some a =>
    cases hx : evalTerm (env ++ [a]) f with
    | none =>
      simp only [refStep, hp, hx, Option.bind_some, Option.bind_none, Option.map_none] at h'
      cases h'
    | some x =>
      cases hr : Store.Image.ofTuple2 Store.Image.ident Store.Image.ident x with
      | none =>
        simp only [refStep, hp, hx, hr, Option.bind_some, Option.map_none] at h'
        cases h'
      | some r =>
        simp only [refStep, hp, hx, hr, Option.bind_some, Option.map_some] at h'
        exact ⟨a, x, r, rfl, hx, hr,
          (congrArg (fun p : Stores × Val => p.1.refs) (Option.some.inj h')).symm⟩

/-- **The decision's write site keeps the used bound**, at every cell and every environment of
its level: the atomic check-and-increment of p4. -/
theorem decision_keeps_used (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refModify q (decisionAt env.length) env) := by
  intro s s' ans h hok
  obtain ⟨a, x, r, ha, hx, hr, hs'⟩ := refModify_step h
  obtain ⟨b, v, rfl, hv⟩ := decision_used hx (hok q.index a ha)
  have hr' : r = (.bool b, v) := (Option.some.inj hr).symm
  rw [hs', hr']
  exact heapOk_poke q hok hv

/-- The racy write of the red control: a blind increment of the window it reads. -/
def racyAt (d : Nat) : Term :=
  .recordSet (.recordSet (.var d) "used" (tsucc (tfield d "used")))
    "admitted" (tsucc (tfield d "admitted"))

/-- **Red control: the racy write site does not keep the used bound.** On a window with
`used = 3`, the blind increment writes `used = 4`. This is why atomicity is the premise:
the check and the write in one store step. -/
theorem racy_breaks_used : ¬ OpKeeps UsedOk (.refUpdate ⟨0⟩ (racyAt 0) []) := by
  intro keeps
  have hstep : syncOpStep (.refUpdate ⟨0⟩ (racyAt 0) [])
      { Stores.empty with refs := [Test.Dogfood.P4RateLimiter.windowVal 3 3 0] } =
      some ({ Stores.empty with refs := [Test.Dogfood.P4RateLimiter.windowVal 4 4 0] }, Val.unit) :=
    rfl
  have before : HeapOk UsedOk [Test.Dogfood.P4RateLimiter.windowVal 3 3 0] := by
    intro i v hv
    match i, hv with
    | 0, hv =>
      cases hv
      show natField (some (Test.Dogfood.P4RateLimiter.windowVal 3 3 0)) "used" ≤ 3
      decide
  have after := keeps _ _ _ hstep before 0 _ rfl
  have broken : ¬ natField (some (Test.Dogfood.P4RateLimiter.windowVal 4 4 0)) "used" ≤ 3 := by
    decide
  exact broken after



/-! ### The decision's coherence: what `counted` needs of the write site

`bounded` needs atomicity (`racy_breaks_used`). `counted` needs a different property of the
decision's write site: its answer agrees with its write. An admitted answer counts one more
admission and no rejection; a rejected answer the converse. The fault `erased` answers the test
and leaves the window, so it is incoherent: the red control of `counted` (`shopControls`). The
racy write keeps coherence (it counts on the branch it answers), which is why `counted`'s red
control is `erased` and not `racy`. This is the decision's step of `shop_stages`. -/

/-- `natField` of a value whose field reads a natural. -/
theorem natField_of_read {v : Val} {name : String} {n : Nat}
    (h : Record.read false v name = some (.nat n)) : natField (some v) name = n := by
  unfold natField
  show (match Record.read false v name with
    | some (.nat n) => n
    | _ => 0) = n
  rw [h]

/-- **The decision's evaluation**: the window's three counts read as naturals, both branches are
built, and the pair answers the branch that the `used` count selects. -/
theorem decision_eval {env : List Val} {a x : Val}
    (hx : evalTerm (env ++ [a]) (decisionAt env.length) = some x) :
    ∃ (u ad rj : Nat) (t1 t2 f1 : Val),
      Record.read false a "used" = some (.nat u) ∧
      Record.read false a "admitted" = some (.nat ad) ∧
      Record.read false a "rejected" = some (.nat rj) ∧
      Record.set a "used" (.nat (u + 1)) = some t1 ∧
      Record.set t1 "admitted" (.nat (ad + 1)) = some t2 ∧
      Record.set a "rejected" (.nat (rj + 1)) = some f1 ∧
      x = (if decide (u < 3) then .list [.bool true, t2] else .list [.bool false, f1]) := by
  simp only [decisionAt, tfield, tsucc, tpair, evalTerm, evalTerms, List.getElem?_concat_length,
    Option.bind_eq_bind, Option.bind_some, read_required, toVal_nat, toVal_bool] at hx
  cases hu : Record.read false a "used" with
  | none =>
    rw [hu] at hx
    cases hx
  | some vu =>
    rw [hu] at hx
    simp only [Option.bind_some] at hx
    cases hs : nativeAtom "succ" [vu] with
    | none =>
      rw [hs] at hx
      simp only [Option.bind_none] at hx
      cases hl : nativeAtom "lt" [vu, Val.nat 3] <;> rw [hl] at hx <;> cases hx
    | some su =>
      obtain ⟨u, rfl, rfl⟩ := atom_succ_inv hs
      simp only [atom_lt, Option.bind_some, atom_succ] at hx
      cases ht1 : Record.set a "used" (Val.nat (u + 1)) with
      | none =>
        rw [ht1] at hx
        cases hx
      | some t1 =>
        rw [ht1] at hx
        simp only [Option.bind_some] at hx
        cases had : Record.read false a "admitted" with
        | none =>
          rw [had] at hx
          cases hx
        | some vad =>
          rw [had] at hx
          simp only [Option.bind_some] at hx
          cases hsa : nativeAtom "succ" [vad] with
          | none =>
            rw [hsa] at hx
            cases hx
          | some sa =>
            obtain ⟨ad, rfl, rfl⟩ := atom_succ_inv hsa
            rw [atom_succ] at hx
            simp only [Option.bind_some] at hx
            cases ht2 : Record.set t1 "admitted" (Val.nat (ad + 1)) with
            | none =>
              rw [ht2] at hx
              cases hx
            | some t2 =>
              rw [ht2] at hx
              simp only [Option.bind_some, atom_pair] at hx
              cases hrj : Record.read false a "rejected" with
              | none =>
                rw [hrj] at hx
                cases hx
              | some vrj =>
                rw [hrj] at hx
                simp only [Option.bind_some] at hx
                cases hsr : nativeAtom "succ" [vrj] with
                | none =>
                  rw [hsr] at hx
                  cases hx
                | some sr =>
                  obtain ⟨rj, rfl, rfl⟩ := atom_succ_inv hsr
                  rw [atom_succ] at hx
                  simp only [Option.bind_some] at hx
                  cases hf1 : Record.set a "rejected" (Val.nat (rj + 1)) with
                  | none =>
                    rw [hf1] at hx
                    cases hx
                  | some f1 =>
                    rw [hf1] at hx
                    simp only [Option.bind_some, atom_pair, atom_ite] at hx
                    exact ⟨u, ad, rj, t1, t2, f1, rfl, rfl, rfl, ht1, ht2, hf1,
                      (Option.some.inj hx).symm⟩

/-- **Coherence of a read-modify-write term at a level**: from every window, its answer is a
Boolean paired with a window whose counts move by its answer. -/
def Coherent (f : Term) (d : Nat) : Prop :=
  ∀ (env : List Val) (a x : Val), env.length = d → evalTerm (env ++ [a]) f = some x →
    ∃ b v, x = .list [.bool b, v] ∧
      (b = true → natField (some v) "admitted" = natField (some a) "admitted" + 1 ∧
        natField (some v) "rejected" = natField (some a) "rejected") ∧
      (b = false → natField (some v) "rejected" = natField (some a) "rejected" + 1 ∧
        natField (some v) "admitted" = natField (some a) "admitted")

/-- **The decision is coherent** at every level: the decision's step of `shop_stages`. -/
theorem decision_coherent (d : Nat) : Coherent (decisionAt d) d := by
  intro env a x hlen hx
  subst hlen
  obtain ⟨u, ad, rj, t1, t2, f1, _, had, hrj, ht1, ht2, hf1, rfl⟩ := decision_eval hx
  have hA := natField_of_read had
  have hR := natField_of_read hrj
  cases hlt : decide (u < 3) with
  | true =>
    refine ⟨true, t2, rfl, ⟨fun _ => ⟨?_, ?_⟩, fun h => nomatch h⟩⟩
    · have hread : Record.read false t2 "admitted" = some (.nat (ad + 1)) := by
        rw [read_after_set ht2 "admitted", if_pos rfl]
      rw [natField_of_read hread, hA]
    · have hread : Record.read false t2 "rejected" = some (.nat rj) := by
        rw [read_after_set ht2 "rejected", if_neg (by decide), read_after_set ht1 "rejected",
          if_neg (by decide), hrj]
      rw [natField_of_read hread, hR]
  | false =>
    refine ⟨false, f1, rfl, ⟨(fun h => nomatch h), fun _ => ⟨?_, ?_⟩⟩⟩
    · have hread : Record.read false f1 "rejected" = some (.nat (rj + 1)) := by
        rw [read_after_set hf1 "rejected", if_pos rfl]
      rw [natField_of_read hread, hR]
    · have hread : Record.read false f1 "admitted" = some (.nat ad) := by
        rw [read_after_set hf1 "admitted", if_neg (by decide), had]
      rw [natField_of_read hread, hA]

/-- The erased decision of the red control: it answers the test and leaves the window. -/
def erasedAt (d : Nat) : Term :=
  tpair (.app "lt" (.cons (tfield d "used") (.cons (.lit (.nat 3)) .nil))) (.var d)

/-- **Red control: the erased decision is incoherent.** On the empty window it answers an
admission and counts none. -/
theorem erased_incoherent : ¬ Coherent (erasedAt 0) 0 := by
  intro coherent
  have heval : evalTerm ([] ++ [Test.Dogfood.P4RateLimiter.windowVal 0 0 0]) (erasedAt 0) =
      some (.list [.bool true, Test.Dogfood.P4RateLimiter.windowVal 0 0 0]) := rfl
  obtain ⟨b, v, hx, htrue, _⟩ := coherent [] _ _ rfl heval
  have hb : b = true ∧ v = Test.Dogfood.P4RateLimiter.windowVal 0 0 0 := by
    have := (Store.Val.list.inj hx)
    obtain ⟨hb, hv⟩ := List.cons.inj this
    obtain ⟨hv, -⟩ := List.cons.inj hv
    exact ⟨(Store.Val.bool.inj hb).symm, hv.symm⟩
  obtain ⟨rfl, rfl⟩ := hb
  have hcount := (htrue rfl).1
  have hzero : natField (some (Test.Dogfood.P4RateLimiter.windowVal 0 0 0)) "admitted" = 0 := by
    decide
  rw [hzero] at hcount
  exact absurd hcount (by decide)


/-! ## 7. The census of the shop's write sites, and `shop_sites_used` decomposed

`shop_sites_used` (section 4) is decomposed here into a census, decided by the kernel on the
elaborated program, and one lemma per family of sites. The decision's family is proved
(section 6); the allocations and the reads are proved here; the deposit, the refill and the
note are planned goals of the same shape as `decision_used`. -/

/-- The shop's elaborated program. -/
def shopProgram : Option NativeEff := (Authoring.elaborateModule (shop .none)).toOption

/-- p5's deposit of `id` at level `d`, as the elaborator wrote it for the shop. -/
def depositAt (id d : Nat) : Term :=
  tpair (.app "add" (.cons (tfield d "balance") (.cons (.lit (.nat id)) .nil)))
    (.recordSet (.recordSet (.var d) "balance"
        (.app "add" (.cons (tfield d "balance") (.cons (.lit (.nat id)) .nil))))
      "history" (.app "append" (.cons (tfield d "history") (.cons (.app "cons"
        (.cons (.record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)] ["_tag", "amount"]
            (.cons (.lit (.str "Deposit")) (.cons (.lit (.nat id)) .nil)))
          (.cons (.app "nil" .nil) .nil))) .nil))))

/-- p4's refill at level `d`: the window with `used = 0`. -/
def refillAt (d : Nat) : Term := .recordSet (.var d) "used" (.lit (.nat 0))

/-- The finalizer's note of `id` at level `d`: the log with `[id, admitted + rejected]` appended,
the window read one level below. -/
def noteAt (id d : Nat) : Term :=
  .app "append" (.cons (.var d) (.cons (.app "cons" (.cons
    (tpair (.lit (.nat id)) (.app "add" (.cons (tfield (d - 1) "admitted")
      (.cons (tfield (d - 1) "rejected") .nil))))
    (.cons (.app "nil" .nil) .nil))) .nil))

/-- The window's allocation request. -/
def window0T : Term :=
  .record [("used", false, .nat), ("admitted", false, .nat), ("rejected", false, .nat)]
    ["used", "admitted", "rejected"]
    (.cons (.lit (.nat 0)) (.cons (.lit (.nat 0)) (.cons (.lit (.nat 0)) .nil)))

/-- The account's allocation request. -/
def account0T : Term :=
  .record [("id", false, .string), ("balance", false, .nat),
      ("history", false, .list (.union
        (.record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)])
        (.record [("_tag", false, .lit "Withdraw"), ("amount", false, .nat)])))]
    ["id", "balance", "history"]
    (.cons (.lit (.str "acc-1")) (.cons (.lit (.nat 0)) (.cons (.app "nil" .nil) .nil)))

/-- The cleanup log's allocation request. -/
def logT : Term :=
  .field .required (.record [("v", false, .list (.prod .nat .nat))] ["v"]
    (.cons (.app "nil" .nil) .nil)) "v"

/-- **The families of the shop's sites**, as a test: each site's row and term. -/
def siteOk : NativeOp → Term → Option Nat → Bool
  | .refMake, request, _ => request == window0T || request == account0T || request == logT
  | .refGet, _, _ => true
  | .sleep, _, _ => true
  | .refModifyWith f, _, some l =>
    f == decisionAt l || (List.range 7).any fun id => f == depositAt id l
  | .refUpdateWith f, _, some l =>
    f == refillAt l || (List.range 7).any fun id => f == noteAt id l
  | _, _, _ => false

/-- **The census** (kernel evaluation of the elaborated shop, about three seconds): every one
of the shop's `perform` sites is in a family. -/
theorem shop_census :
    (shopProgram.map fun p => (performSites p).all fun site =>
      siteOk site.2.1 site.2.2.1 site.2.2.2) = some true := by
  decide

/-- An allocation of a value that satisfies a cell predicate keeps it. -/
theorem make_keeps {P : Val → Prop} (v : Val) (hv : P v) : OpKeeps P (.refMake v) := by
  intro s s' ans h hok
  have h' : (refStep (.refMake v) s.refs).map
      (fun step => ({ s with refs := step.2 }, step.1)) = some (s', ans) := h
  simp only [refStep, Option.map_some] at h'
  have hs : s.refs ++ [v] = s'.refs :=
    congrArg (fun p : Stores × Val => p.1.refs) (Option.some.inj h')
  rw [← hs]
  intro i w hw
  rw [List.getElem?_append] at hw
  split at hw
  · exact hok i w hw
  · cases hi : i - s.refs.length with
    | zero =>
      rw [hi] at hw
      cases hw
      exact hv
    | succ k =>
      rw [hi] at hw
      cases hw

/-- A read keeps every cell predicate. -/
theorem get_keeps {P : Val → Prop} (q : RefKey) : OpKeeps P (.refGet q) := by
  intro before after answer step held
  rw [syncOpStep_refGet_refs step]
  exact held

/-- A record set's evaluation: the target and the value evaluate, and the set answers. -/
theorem eval_recordSet {env : List Val} {target value : Term} {name : String} {v : Val}
    (h : evalTerm env (.recordSet target name value) = some v) :
    ∃ t x, evalTerm env target = some t ∧ evalTerm env value = some x ∧
      Record.set t name x = some v := by
  simp only [evalTerm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, x, hx, hs⟩ := h
  exact ⟨t, x, ht, hx, hs⟩

/-- A pair's evaluation: both items evaluate, and the pair is their list. -/
theorem eval_pair {env : List Val} {a b : Term} {v : Val} (h : evalTerm env (tpair a b) = some v) :
    ∃ va vb, evalTerm env a = some va ∧ evalTerm env b = some vb ∧ v = .list [va, vb] := by
  simp only [tpair, evalTerm, evalTerms, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vals, ⟨va, ha, rest, ⟨vb, hb, tail, htail, hrest⟩, hvals⟩, hatom⟩ := h
  cases htail
  cases hrest
  cases hvals
  exact ⟨va, vb, ha, hb, (Option.some.inj (hatom : some (Val.list [va, vb]) = some v)).symm⟩

/-- `append` answers a list. -/
theorem atom_append_inv {vals : List Val} {v : Val} (h : nativeAtom "append" vals = some v) :
    ∃ xs, v = .list xs := by
  match vals, h with
  | [xs, ys], h =>
    have h' : ((Val.asList? xs).bind fun front =>
        (Val.asList? ys).map fun back => Val.list (front ++ back)) = some v := h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
    obtain ⟨front, _, back, _, rfl⟩ := h'
    exact ⟨front ++ back, rfl⟩
  | [], h => cases h
  | [_], h => cases h
  | _ :: _ :: _ :: _, h => cases h

/-- An `append` term answers a list. -/
theorem eval_append {env : List Val} {args : Terms} {v : Val}
    (h : evalTerm env (.app "append" args) = some v) : ∃ xs, v = .list xs := by
  simp only [evalTerm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vals, _, hatom⟩ := h
  exact atom_append_inv hatom

/-- A list has no `used` field: `natField` reads `0`. -/
theorem natField_list (xs : List Val) : natField (some (.list xs)) "used" = 0 := rfl

/-- The variable at the environment's length reads the value appended last. -/
theorem eval_var_last (env : List Val) (a : Val) :
    evalTerm (env ++ [a]) (.var env.length) = some a := by
  simp only [evalTerm, List.getElem?_concat_length]

/-- A `Ref.update` step reads the cell once, evaluates the term once, and writes its value. -/
theorem refUpdate_step {q : RefKey} {f : Term} {env : List Val} {s s' : Stores} {ans : Val}
    (h : syncOpStep (.refUpdate q f env) s = some (s', ans)) :
    ∃ a a', refPeek s.refs q = some a ∧ evalTerm (env ++ [a]) f = some a' ∧
      s'.refs = refPoke s.refs q a' := by
  have h' : (refStep (.refUpdate q f env) s.refs).map
      (fun step => ({ s with refs := step.2 }, step.1)) = some (s', ans) := h
  cases hp : refPeek s.refs q with
  | none =>
    simp only [refStep, hp, Option.bind_none, Option.map_none] at h'
    cases h'
  | some a =>
    cases hx : evalTerm (env ++ [a]) f with
    | none =>
      simp only [refStep, hp, hx, Option.bind_some, Option.map_none] at h'
      cases h'
    | some a' =>
      simp only [refStep, hp, hx, Option.bind_some, Option.map_some] at h'
      exact ⟨a, a', rfl, hx,
        (congrArg (fun p : Stores × Val => p.1.refs) (Option.some.inj h')).symm⟩

/-- **The refill's write site keeps the used bound**: it writes `used = 0`. A step of
`shop_sites_used`. -/
theorem refill_keeps_used (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refUpdate q (refillAt env.length) env) := by
  intro s s' ans h hok
  obtain ⟨a, a', _, hx, hs'⟩ := refUpdate_step h
  obtain ⟨t, x, ht, hxv, hset⟩ := eval_recordSet hx
  rw [eval_var_last] at ht
  cases ht
  have hx0 : x = .nat 0 := (Option.some.inj (hxv : some (Val.nat 0) = some x)).symm
  subst hx0
  have hread : Record.read false a' "used" = some (.nat 0) := by
    rw [read_after_set hset "used", if_pos rfl]
  rw [hs']
  refine heapOk_poke q hok ?_
  unfold UsedOk
  rw [natField_used hread]
  decide

/-- **The note's write site keeps the used bound**: it writes a list. A step of
`shop_sites_used`. -/
theorem note_keeps_used (id : Nat) (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refUpdate q (noteAt id env.length) env) := by
  intro s s' ans h hok
  obtain ⟨a, a', _, hx, hs'⟩ := refUpdate_step h
  obtain ⟨xs, rfl⟩ := eval_append hx
  rw [hs']
  refine heapOk_poke q hok ?_
  unfold UsedOk
  rw [natField_list]
  decide

/-- **The deposit's write site keeps the used bound**: it sets `balance` and `history` and
leaves `used`. A step of `shop_sites_used`. -/
theorem deposit_keeps_used (id : Nat) (q : RefKey) (env : List Val) :
    OpKeeps UsedOk (.refModify q (depositAt id env.length) env) := by
  intro s s' ans h hok
  obtain ⟨a, x, r, ha, hx, hr, hs'⟩ := refModify_step h
  obtain ⟨va, vb, _, hb, rfl⟩ := eval_pair hx
  have hr' : r = (va, vb) := (Option.some.inj hr).symm
  obtain ⟨t1, y, ht1, _, hset2⟩ := eval_recordSet hb
  obtain ⟨t0, z, ht0, _, hset1⟩ := eval_recordSet ht1
  rw [eval_var_last] at ht0
  cases ht0
  have hread : Record.read false vb "used" = Record.read false a "used" := by
    rw [read_after_set hset2 "used", if_neg (by decide), read_after_set hset1 "used",
      if_neg (by decide)]
  have hfield : natField (some vb) "used" = natField (some a) "used" := by
    unfold natField
    show (match Record.read false vb "used" with
      | some (.nat n) => n
      | _ => 0) = (match Record.read false a "used" with
      | some (.nat n) => n
      | _ => 0)
    rw [hread]
  rw [hs', hr']
  refine heapOk_poke q hok ?_
  unfold UsedOk
  rw [hfield]
  exact hok q.index a ha

/-- One closed allocation request: its value satisfies `UsedOk` at every environment. -/
theorem closed_used (request : Term) (env : List Val)
    (hclosed : evalTerm env request = evalTerm [] request)
    (hcheck : (evalTerm [] request).all (fun v => decide (natField (some v) "used" ≤ 3)) = true)
    (v : Val) (hv : evalTerm env request = some v) : UsedOk v := by
  rw [hclosed] at hv
  rw [hv] at hcheck
  exact (of_decide_eq_true hcheck : natField (some v) "used" ≤ 3)

/-- The three allocations write values whose `used` field is at most three. -/
theorem allocations_used (env : List Val) (request : Term)
    (h : (request == window0T || request == account0T || request == logT) = true) (v : Val)
    (hv : evalTerm env request = some v) : UsedOk v := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl
  · exact closed_used window0T env rfl (by decide) v hv
  · exact closed_used account0T env rfl (by decide) v hv
  · exact closed_used logT env rfl (by decide) v hv

/-- The families of the shop's sites, as a predicate. -/
inductive Family : NativeOp → Term → Option Nat → Prop
  | make {request : Term} {lvl : Option Nat} :
      (request == window0T || request == account0T || request == logT) = true →
      Family .refMake request lvl
  | get {request : Term} {lvl : Option Nat} : Family .refGet request lvl
  | sleep {request : Term} {lvl : Option Nat} : Family .sleep request lvl
  | decision {request : Term} {l : Nat} : Family (.refModifyWith (decisionAt l)) request (some l)
  | deposit {request : Term} {l : Nat} (id : Nat) :
      Family (.refModifyWith (depositAt id l)) request (some l)
  | refill {request : Term} {l : Nat} : Family (.refUpdateWith (refillAt l)) request (some l)
  | note {request : Term} {l : Nat} (id : Nat) :
      Family (.refUpdateWith (noteAt id l)) request (some l)

/-- The test reads as the predicate. -/
theorem family_of_siteOk {op : NativeOp} {request : Term} {lvl : Option Nat}
    (h : siteOk op request lvl = true) : Family op request lvl := by
  unfold siteOk at h
  split at h
  · exact .make h
  · exact .get
  · exact .sleep
  · simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h with rfl | ⟨id, _, rfl⟩
    · exact .decision
    · exact .deposit id
  · simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h with rfl | ⟨id, _, rfl⟩
    · exact .refill
    · exact .note id
  · cases h

/-- A `Ref.modify` row makes a modify of a cell, with its term and the environment. -/
theorem modify_inv {f : Term} {env : List Val} {val : Val} {o : SyncOp}
    (h : NativeOp.syncOpOf (.refModifyWith f) env val = some o) :
    ∃ k, o = .refModify ⟨k⟩ f env := by
  cases val with
  | handle kind key =>
    cases hk : (kind == 2) with
    | true =>
      have : kind = 2 := beq_iff_eq.mp hk
      subst this
      exact ⟨key, (Option.some.inj h).symm⟩
    | false =>
      have hne : kind ≠ 2 := fun he => by
        rw [he] at hk
        exact Bool.false_ne_true (hk.symm.trans rfl)
      unfold NativeOp.syncOpOf at h
      split at h
      all_goals simp only [reduceCtorEq, NativeOp.refModifyWith.injEq, Store.Val.handle.injEq] at *
      exact absurd (‹kind = 2 ∧ _›).1 hne
  | unit => cases h
  | bool _ => cases h
  | nat _ => cases h
  | str _ => cases h
  | bytes _ => cases h
  | list _ => cases h
  | pair _ _ => cases h
  | none => cases h
  | some _ => cases h
  | ctor _ _ => cases h
  | ref _ _ => cases h
  | negInt _ => cases h
  | float _ => cases h

/-- A `Ref.update` row makes an update of a cell, with its term and the environment. -/
theorem update_inv {f : Term} {env : List Val} {val : Val} {o : SyncOp}
    (h : NativeOp.syncOpOf (.refUpdateWith f) env val = some o) :
    ∃ k, o = .refUpdate ⟨k⟩ f env := by
  cases val with
  | handle kind key =>
    cases hk : (kind == 2) with
    | true =>
      have : kind = 2 := beq_iff_eq.mp hk
      subst this
      exact ⟨key, (Option.some.inj h).symm⟩
    | false =>
      have hne : kind ≠ 2 := fun he => by
        rw [he] at hk
        exact Bool.false_ne_true (hk.symm.trans rfl)
      unfold NativeOp.syncOpOf at h
      split at h
      all_goals simp only [reduceCtorEq, NativeOp.refUpdateWith.injEq, Store.Val.handle.injEq] at *
      exact absurd (‹kind = 2 ∧ _›).1 hne
  | unit => cases h
  | bool _ => cases h
  | nat _ => cases h
  | str _ => cases h
  | bytes _ => cases h
  | list _ => cases h
  | pair _ _ => cases h
  | none => cases h
  | some _ => cases h
  | ctor _ _ => cases h
  | ref _ _ => cases h
  | negInt _ => cases h
  | float _ => cases h

/-- A `Ref.get` row makes a read of a cell. -/
theorem get_inv {env : List Val} {val : Val} {o : SyncOp}
    (h : NativeOp.syncOpOf .refGet env val = some o) : ∃ k, o = .refGet ⟨k⟩ := by
  cases val with
  | handle kind key =>
    cases hk : (kind == 2) with
    | true =>
      have : kind = 2 := beq_iff_eq.mp hk
      subst this
      exact ⟨key, (Option.some.inj h).symm⟩
    | false =>
      have hne : kind ≠ 2 := fun he => by
        rw [he] at hk
        exact Bool.false_ne_true (hk.symm.trans rfl)
      unfold NativeOp.syncOpOf at h
      split at h
      all_goals simp only [reduceCtorEq, Store.Val.handle.injEq] at *
      exact absurd (‹kind = 2 ∧ _›).1 hne
  | unit => cases h
  | bool _ => cases h
  | nat _ => cases h
  | str _ => cases h
  | bytes _ => cases h
  | list _ => cases h
  | pair _ _ => cases h
  | none => cases h
  | some _ => cases h
  | ctor _ _ => cases h
  | ref _ _ => cases h
  | negInt _ => cases h
  | float _ => cases h

/-- **The shop's write sites keep the used bound** (program-specific; proved). Each of the shop's
31 `perform` sites keeps `UsedOk` at its level: the census (`shop_census`) puts each in a family,
and each family keeps the bound. Placement: concept `store-typing`, requirement R4; a step of the
scenario clause `bounded`; consumer `Atomic.bounded`. -/
theorem shop_sites_used (b : Api.Built)
    (hb : Effect4.Api.Author.build (shop .none) = .ok b) : SitesKeep b.program UsedOk := by
  intro path op request env val o hnode hlevel hval hop
  have hprog : shopProgram = some b.program := by
    unfold shopProgram
    rw [(Api.Author.build_retains hb).1]
    rfl
  have hmem := performSites_complete hnode
  rw [hlevel] at hmem
  have hall : (performSites b.program).all
      (fun site => siteOk site.2.1 site.2.2.1 site.2.2.2) = true := by
    have h := shop_census
    rw [hprog] at h
    exact Option.some.inj h
  have hok : siteOk op request (some env.length) = true := List.all_eq_true.mp hall _ hmem
  cases family_of_siteOk hok with
  | make hm =>
    have ho : o = .refMake val := (Option.some.inj hop).symm
    rw [ho]
    exact make_keeps val (allocations_used env request hm val hval)
  | get =>
    obtain ⟨k, rfl⟩ := get_inv hop
    exact get_keeps _
  | sleep => cases hop
  | decision =>
    obtain ⟨k, rfl⟩ := modify_inv hop
    exact decision_keeps_used _ env
  | deposit id =>
    obtain ⟨k, rfl⟩ := modify_inv hop
    exact deposit_keeps_used id _ env
  | refill =>
    obtain ⟨k, rfl⟩ := update_inv hop
    exact refill_keeps_used _ env
  | note id =>
    obtain ⟨k, rfl⟩ := update_inv hop
    exact note_keeps_used id _ env

end Test.Dogfood.Scenario.Atomic.Store
