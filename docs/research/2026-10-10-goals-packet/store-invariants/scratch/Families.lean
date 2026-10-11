import Test.Dogfood.Scenario.Atomic

set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program Test.Dogfood.Scenario.Atomic

namespace ScratchF

def UsedOk (v : Val) : Prop := natField (some v) "used" ≤ 3
def tpair (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

theorem eval_recordSet {env : List Val} {target value : Term} {name : String} {v : Val}
    (h : evalTerm env (.recordSet target name value) = some v) :
    ∃ t x, evalTerm env target = some t ∧ evalTerm env value = some x ∧
      Record.set t name x = some v := by
  simp only [evalTerm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, x, hx, hs⟩ := h
  exact ⟨t, x, ht, hx, hs⟩

theorem eval_pair {env : List Val} {a b : Term} {v : Val} (h : evalTerm env (tpair a b) = some v) :
    ∃ va vb, evalTerm env a = some va ∧ evalTerm env b = some vb ∧ v = .list [va, vb] := by
  simp only [tpair, evalTerm, evalTerms, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vals, ⟨va, ha, rest, ⟨vb, hb, nil, hnil, hrest⟩, hvals⟩, hatom⟩ := h
  cases hnil
  cases hrest
  cases hvals
  exact ⟨va, vb, ha, hb, (Option.some.inj (hatom : some (Val.list [va, vb]) = some v)).symm⟩

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

theorem eval_append {env : List Val} {args : Terms} {v : Val}
    (h : evalTerm env (.app "append" args) = some v) : ∃ xs, v = .list xs := by
  simp only [evalTerm, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨vals, _, hatom⟩ := h
  exact atom_append_inv hatom

theorem natField_list (xs : List Val) : natField (some (.list xs)) "used" = 0 := rfl

theorem eval_var_last (env : List Val) (a : Val) : evalTerm (env ++ [a]) (.var env.length) = some a := by
  simp only [evalTerm, List.getElem?_concat_length]

end ScratchF
