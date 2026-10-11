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

