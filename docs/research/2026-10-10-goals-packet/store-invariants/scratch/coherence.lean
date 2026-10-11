
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
    refine ⟨true, t2, by rw [hlt]; rfl, fun _ => ⟨?_, ?_⟩, fun h => absurd h Bool.true_ne_false⟩
    · have hread : Record.read false t2 "admitted" = some (.nat (ad + 1)) := by
        rw [read_after_set ht2 "admitted", if_pos rfl]
      rw [natField_of_read hread, hA]
    · have hread : Record.read false t2 "rejected" = some (.nat rj) := by
        rw [read_after_set ht2 "rejected", if_neg (by decide), read_after_set ht1 "rejected",
          if_neg (by decide), hrj]
      rw [natField_of_read hread, hR]
  | false =>
    refine ⟨false, f1, by rw [hlt]; rfl, fun h => absurd h Bool.false_ne_true, fun _ => ⟨?_, ?_⟩⟩
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

