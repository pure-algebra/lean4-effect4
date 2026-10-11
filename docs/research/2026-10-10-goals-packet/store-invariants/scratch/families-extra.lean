
def HeapOk (P : Val → Prop) (refs : RefHeap) : Prop := ∀ (i : Nat) (v : Val), refs[i]? = some v → P v
def OpKeeps (P : Val → Prop) (o : SyncOp) : Prop :=
  ∀ (s s' : Stores) (ans : Val), syncOpStep o s = some (s', ans) → HeapOk P s.refs →
    HeapOk P s'.refs

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
    have hnd := Field.canonBy_names_nodup (key := Field.bytesKey) ((name, x) :: fields)
    have hentries : Record.entries (Record.frame (Field.canonBy Field.bytesKey ((name, x) :: fields))) =
        some (Field.canonBy Field.bytesKey ((name, x) :: fields)) := by
      simp only [Record.entries, Record.frame, Program.recordParts?, Option.bind_eq_bind,
        Option.bind_some, Typed.readColumns_frame, if_pos hnd]
    unfold Record.read Record.lookup
    rw [hentries, he]
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true, if_false,
      Field.firstOf_canonBy Field.bytesKey_injective, Field.firstOf]

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

theorem natField_used {v : Val} {n : Nat} (h : Record.read false v "used" = some (.nat n)) :
    natField (some v) "used" = n := by
  unfold natField
  show (match Record.read false v "used" with
    | some (.nat n) => n
    | _ => 0) = n
  rw [h]

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

def tfield (d : Nat) (name : String) : Term := .field .required (.var d) name

def depositAt (id d : Nat) : Term :=
  tpair (.app "add" (.cons (tfield d "balance") (.cons (.lit (.nat id)) .nil)))
    (.recordSet (.recordSet (.var d) "balance"
        (.app "add" (.cons (tfield d "balance") (.cons (.lit (.nat id)) .nil))))
      "history" (.app "append" (.cons (tfield d "history") (.cons (.app "cons"
        (.cons (.record [("_tag", false, .lit "Deposit"), ("amount", false, .nat)] ["_tag", "amount"]
            (.cons (.lit (.str "Deposit")) (.cons (.lit (.nat id)) .nil)))
          (.cons (.app "nil" .nil) .nil))) .nil))))

def refillAt (d : Nat) : Term := .recordSet (.var d) "used" (.lit (.nat 0))

def noteAt (id d : Nat) : Term :=
  .app "append" (.cons (.var d) (.cons (.app "cons" (.cons
    (tpair (.lit (.nat id)) (.app "add" (.cons (tfield (d - 1) "admitted")
      (.cons (tfield (d - 1) "rejected") .nil))))
    (.cons (.app "nil" .nil) .nil))) .nil))

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
