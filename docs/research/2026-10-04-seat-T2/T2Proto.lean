import Effect4.Laws.Program.Typed.Adequacy

/-! Seat T2's phase-1 prototype (scratch; not committed). It states the connector and the
semantic premise against the tree at `69686dd6`, without editing it: the lowering of each function
name to a binder term per read-modify-write shape, the four shape agreements on numbers, the
decoders, the premise `TermMaps` with its monotonicity, the four discharges at a cell declared
equivalent to `nat`, one generic lemma for every term kernel, and the red controls (a non-number
cell). -/

set_option autoImplicit false

namespace T2Proto
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed

/-! ## The lowering: one binder term per shape, over the cell's value at level 0 -/

def app1 (atom : String) (a : Term) : Term := .app atom (.cons a .nil)
def app2 (atom : String) (a b : Term) : Term := .app atom (.cons a (.cons b .nil))
def cur : Term := .var 0

def updateTerm : FnName → Term
  | .incr | .takeAndBump => app1 "succ" cur
  | .double => app2 "mul" cur (.lit (.nat 2))
  | .zeroWhenPositive | .noChange => cur

def updateSomeTerm : FnName → Term
  | .noChange => .app "none" .nil
  | .zeroWhenPositive =>
    .app "ite" (.cons (app2 "lt" (.lit (.nat 0)) cur)
      (.cons (app1 "some" (.lit (.nat 0))) (.cons (.app "none" .nil) .nil)))
  | f => app1 "some" (updateTerm f)

def modifyTerm (f : FnName) : Term := app2 "pair" cur (updateTerm f)

def modifySomeTerm : FnName → Term
  | .noChange => app2 "pair" cur (.app "none" .nil)
  | f => app2 "pair" cur (app1 "some" (updateTerm f))

/-! ## The decoders: the carrier's option frames and the data wave's tuple image -/

def toOpt : Option Val → Val
  | some a => Store.Val.some a
  | none => Store.Val.none

def option? : Val → Option (Option Val)
  | Store.Val.some a => some (some a)
  | Store.Val.none => some none
  | _ => none

theorem option?_toOpt (o : Option Val) : option? (toOpt o) = some o := by
  cases o <;> rfl

def modify? (r : Val) : Option (Val × Val) :=
  match Program.Val.tuple? r with
  | some [b, a'] => some (b, a')
  | _ => none

def modifySome? (r : Val) : Option (Val × Option Val) :=
  match Program.Val.tuple? r with
  | some [b, o] => (option? o).map (b, ·)
  | _ => none

/-! ## The value-level agreements: on every number, the term evaluates to the name's answer -/

theorem updateTerm_agrees (f : FnName) (n : Nat) :
    evalTerm [.nat n] (updateTerm f) = some (f.total (.nat n)) := by
  cases f <;> rfl

theorem updateSomeTerm_agrees (f : FnName) (n : Nat) :
    evalTerm [.nat n] (updateSomeTerm f) = some (toOpt (f.partialUpdate (.nat n))) := by
  cases f
  case zeroWhenPositive => cases n <;> rfl
  all_goals rfl

theorem modifyTerm_agrees (f : FnName) (n : Nat) :
    evalTerm [.nat n] (modifyTerm f) =
      some (Program.Val.tuple [(f.modify (.nat n)).1, (f.modify (.nat n)).2]) := by
  cases f <;> rfl

theorem modifySomeTerm_agrees (f : FnName) (n : Nat) :
    evalTerm [.nat n] (modifySomeTerm f) =
      some (Program.Val.tuple [(f.modifySome (.nat n)).1, toOpt (f.modifySome (.nat n)).2]) := by
  cases f <;> rfl

/-! ## The red control: a non-number cell. The old name answered the value unchanged; the term is a
frontier. -/

example : FnName.total .incr (.bool true) = .bool true := rfl
example : evalTerm [.bool true] (updateTerm .incr) = none := rfl
example : FnName.modify .incr (.bool true) = (.bool true, .bool true) := rfl
example : evalTerm [.bool true] (modifyTerm .incr) = none := rfl
example : FnName.partialUpdate .zeroWhenPositive (.bool true) = none := rfl
example : evalTerm [.bool true] (updateSomeTerm .zeroWhenPositive) = none := rfl
-- the identity names agree everywhere
example : evalTerm [.bool true] (updateTerm .noChange) = some (FnName.total .noChange (.bool true)) :=
  rfl

/-! ## The semantic premise: the unary Kripke relation at a function type -/

def TermMaps (w : Typed.World) (f : Term) (env : List Val) (A R : Ty) : Prop :=
  ∀ w', w.leHost w' → ∀ a, Fits w' a A → ∃ r, evalTerm (env ++ [a]) f = some r ∧ Fits w' r R

theorem TermMaps.mono {w w' : Typed.World} {f : Term} {env : List Val} {A R : Ty}
    (ord : w.leHost w') (h : TermMaps w f env A R) : TermMaps w' f env A R :=
  fun w'' o a ha => h w'' (leHost_trans _ _ _ ord o) a ha

/-! ## The discharges at a cell declared equivalent to `nat` -/

theorem nat_of_equiv {w : Typed.World} {t : Ty} (equiv : Equiv t .nat) {a : Val}
    (h : Fits w a t) : ∃ n, a = .nat n :=
  fits_nat_inv (fits_subN w equiv.1 a h)

theorem fits_toOpt {w : Typed.World} {t : Ty} {o : Option Val} (h : ∀ a, o = some a → Fits w a t) :
    Fits w (toOpt o) (.option t) := by
  cases o with
  | none => exact trivial
  | some a => exact h a rfl

theorem updateTerm_maps {w : Typed.World} {t : Ty} (equiv : Equiv t .nat) (f : FnName) :
    TermMaps w (updateTerm f) [] t t := by
  intro w' _ a ha
  obtain ⟨n, rfl⟩ := nat_of_equiv equiv ha
  exact ⟨_, updateTerm_agrees f n, fits_total f ha⟩

theorem updateSomeTerm_maps {w : Typed.World} {t : Ty} (equiv : Equiv t .nat) (f : FnName) :
    TermMaps w (updateSomeTerm f) [] t (.option t) := by
  intro w' _ a ha
  obtain ⟨n, rfl⟩ := nat_of_equiv equiv ha
  exact ⟨_, updateSomeTerm_agrees f n, fits_toOpt fun a' h => fits_partialUpdate f ha h⟩

theorem modifyTerm_maps {w : Typed.World} {t : Ty} (equiv : Equiv t .nat) (f : FnName) :
    TermMaps w (modifyTerm f) [] t (.prod .nat t) := by
  intro w' _ a ha
  obtain ⟨n, rfl⟩ := nat_of_equiv equiv ha
  obtain ⟨answer, m, written⟩ := modify_nat f n
  refine ⟨_, modifyTerm_agrees f n, (fits_prod_iff _ _ _ _).mpr ⟨_, _, rfl, ?_, ?_⟩⟩
  · rw [answer]; exact trivial
  · rw [written]; exact fits_nat_irrel w' n m t ha

theorem modifySomeTerm_maps {w : Typed.World} {t : Ty} (equiv : Equiv t .nat) (f : FnName) :
    TermMaps w (modifySomeTerm f) [] t (.prod .nat (.option t)) := by
  intro w' _ a ha
  obtain ⟨n, rfl⟩ := nat_of_equiv equiv ha
  refine ⟨_, modifySomeTerm_agrees f n, (fits_prod_iff _ _ _ _).mpr ⟨_, _, rfl, ?_, ?_⟩⟩
  · cases f <;> exact trivial
  · refine fits_toOpt fun a' h => ?_
    obtain ⟨_, m, written⟩ := modifySome_nat f n
    rw [h] at written
    cases written
    exact fits_nat_irrel w' n m t ha

#print axioms updateTerm_agrees
#print axioms updateSomeTerm_agrees
#print axioms modifyTerm_agrees
#print axioms modifySomeTerm_agrees
#print axioms updateTerm_maps
#print axioms updateSomeTerm_maps
#print axioms modifyTerm_maps
#print axioms modifySomeTerm_maps

/-! ## One lemma for every term kernel -/

def termKernel {D : Type} (decode : Val → Option D) (arrange : Val → D → Val × Option Val)
    (f : Term) (env : List Val) : RefKernel :=
  fun a => ((evalTerm (env ++ [a]) f).bind decode).map (arrange a)

theorem termKernel_keeps {D : Type} {decode : Val → Option D}
    {arrange : Val → D → Val × Option Val} {w : Typed.World} {f : Term} {env : List Val}
    {t R : Ty} {Good : D → Prop} {Q : Val → Prop} (maps : TermMaps w f env t R)
    (hdecode : ∀ r, Fits w r R → ∃ d, decode r = some d ∧ Good d)
    (harrange : ∀ a d, Fits w a t → Good d →
      Q (arrange a d).1 ∧ ∀ next, (arrange a d).2 = some next → Fits w next t) :
    (∀ c, Fits w c t → (termKernel decode arrange f env c).isSome = true) ∧
      RefKernel.Keeps (Fits w · t) Q (termKernel decode arrange f env) := by
  have run : ∀ c, Fits w c t →
      ∃ d, termKernel decode arrange f env c = some (arrange c d) ∧ Good d := by
    intro c hc
    obtain ⟨r, hr, hfit⟩ := maps w (leHost_refl w) c hc
    obtain ⟨d, hd, good⟩ := hdecode r hfit
    exact ⟨d, by simp only [termKernel, hr, Option.bind_some, hd, Option.map_some], good⟩
  refine ⟨fun c hc => ?_, fun c p hc hp => ?_⟩
  · obtain ⟨d, hk, _⟩ := run c hc
    rw [hk]
    rfl
  · obtain ⟨d, hk, good⟩ := run c hc
    rw [hk] at hp
    cases hp
    exact harrange c d hc good

/-! ## The shape facts the eight rows read -/

theorem decode_option {w : Typed.World} {t : Ty} (r : Val) (h : Fits w r (.option t)) :
    ∃ o, option? r = some o ∧ ∀ a, o = some a → Fits w a t := by
  rcases fits_option_inv h with rfl | ⟨x, rfl, hx⟩
  · exact ⟨none, rfl, fun _ h => nomatch h⟩
  · exact ⟨some x, rfl, fun a h => by cases h; exact hx⟩

theorem decode_modify {w : Typed.World} {b t : Ty} (r : Val) (h : Fits w r (.prod b t)) :
    ∃ p, modify? r = some p ∧ Fits w p.1 b ∧ Fits w p.2 t := by
  obtain ⟨x, y, rfl, hx, hy⟩ := (fits_prod_iff _ _ _ _).mp h
  exact ⟨(x, y), rfl, hx, hy⟩

end T2Proto

#print axioms T2Proto.termKernel_keeps
#print axioms T2Proto.decode_option
#print axioms T2Proto.decode_modify
#print axioms T2Proto.TermMaps.mono
