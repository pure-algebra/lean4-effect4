import P2Ty
import Aesop

/-!
# Seat P: the copied relational view with a head of variable arity (type-language probe, 2026-10-01)

Research probe. A copy of the generated `src/Effect4/Laws/Program/TyView.lean` at `bff50631`
over the copied `ProbeP.Ty`, answering question 3's shape question: what must
`TyView.sub_eq_args` look like when a head has variable arity?

**Answer (proved below).** `sub_eq_args` keeps its statement exactly. A record's children are
its canonical field types, each at variance `co` (readonly properties); its head is the
canonical list of names with their optional flags, compared by `sameHead`; a map is a
fixed-arity head `[(inv, key), (co, value)]` and needs nothing new. The one law whose statement
changes is `eq_of_sameHead` ("a node is its head and its children"): two raw records with the
same canonical head and children are equal only up to the field order, so its conclusion is
`canonHead a = canonHead b`, where `canonHead` orders a record's fields and is the identity on
every other head. `argsBelow_antisymm` inherits that conclusion; `eq_of_sameHead_nil` keeps its
statement (an empty canonical field list is an empty written one).

The variance table's row for a head of variable arity is one variance applied to every element
of the list position (`record: co*`), not a fixed list; the generator needs that row shape and
the head's normaliser (`canonF`) to emit `args`, `sameHead` and `canonHead`.
-/

set_option autoImplicit false

namespace ProbeP

namespace Ty

open ProbeP.Field

/-- copied. -/
inductive Variance where
  | co
  | contra
  | inv
deriving DecidableEq, Repr

/-- copied. -/
def Variance.holds (r : Ty → Ty → Bool) : Variance → Ty → Ty → Bool
  | .co,     x, y => r x y
  | .contra, x, y => r y x
  | .inv,    x, y => r x y && r y x

/-- arm: two. A record's children are its canonical field types, covariant (readonly); a map is
exact in its key (`inv`) and covariant in its value. -/
def args : Ty → List (Variance × Ty)
  | .never => []
  | .unit => []
  | .nat => []
  | .int => []
  | .string => []
  | .bool => []
  | .handle _ => []
  | .option inner => [(.co, inner)]
  | .list inner => [(.co, inner)]
  | .prod left right => [(.co, left), (.co, right)]
  | .except error value => [(.co, error), (.co, value)]
  | .exitOf value error => [(.co, value), (.co, error)]
  | .causeOf error => [(.co, error)]
  | .fiberOf value error => [(.co, value), (.co, error)]
  | .union left right => [(.co, left), (.co, right)]
  | .lit _ => []
  | .refOf value => [(.inv, value)]
  | .deferredOf value error => [(.inv, value), (.inv, error)]
  | .var _ => []
  | .unknown => []
  | .record fields => (canonF fields).map fun p => (.co, p.2.2)
  | .map key value => [(.inv, key), (.co, value)]
  | .tuple items => items.map fun t => (.co, t)
  | .app _ args => args.map fun t => (.inv, t)
  | .null => []
  | .undefined => []
  | .number => []
  | .bytes => []

/-- arm: two. A record's head is its canonical names with their flags. -/
def sameHead : Ty → Ty → Bool
  | .never, .never => true
  | .unit, .unit => true
  | .nat, .nat => true
  | .int, .int => true
  | .string, .string => true
  | .bool, .bool => true
  | .handle target1, .handle target2 => decide (target1 = target2)
  | .option _, .option _ => true
  | .list _, .list _ => true
  | .prod _ _, .prod _ _ => true
  | .except _ _, .except _ _ => true
  | .exitOf _ _, .exitOf _ _ => true
  | .causeOf _, .causeOf _ => true
  | .fiberOf _ _, .fiberOf _ _ => true
  | .lit value1, .lit value2 => decide (value1 = value2)
  | .refOf _, .refOf _ => true
  | .deferredOf _ _, .deferredOf _ _ => true
  | .var index1, .var index2 => decide (index1 = index2)
  | .unknown, .unknown => true
  | .record fs, .record gs => decide (heads (canonF fs) = heads (canonF gs))
  | .map _ _, .map _ _ => true
  | .tuple ts, .tuple us => decide (ts.length = us.length)
  | .app n ts, .app m us => decide (n = m ∧ ts.length = us.length)
  | .null, .null => true
  | .undefined, .undefined => true
  | .number, .number => true
  | .bytes, .bytes => true
  | _, _ => false

/-- The head's normaliser: a record's fields in canonical order; every other head unchanged. -/
def canonHead : Ty → Ty
  | .record fs => .record (canonF fs)
  | t => t

/-- copied. -/
def topRule : Ty → Ty → Bool
  | _, .unknown => true
  | _, _        => false

/-- copied. -/
def argsBelow (r : Ty → Ty → Bool) (a b : Ty) : Bool :=
  (a.args.zip b.args).all fun p => p.1.1.holds r p.1.2 p.2.2

/-! ### The head relation -/

/-- case: two (copied text with the two cases). -/
theorem sameHead_refl (t : Ty) (h : isMember t = true) : sameHead t t = true := by
  cases t
  case union => exact Bool.noConfusion h
  case never => exact Bool.noConfusion h
  all_goals simp only [sameHead, decide_true, and_self]

theorem sameHead_symm {a b : Ty} (h : sameHead a b = true) : sameHead b a = true := by
  cases a <;> cases b <;> aesop (add norm simp [sameHead])

theorem sameHead_trans {a b c : Ty} (hab : sameHead a b = true)
    (hbc : sameHead b c = true) : sameHead a c = true := by
  fun_cases Ty.sameHead a b <;> cases c <;> aesop (add norm simp [sameHead])

/-- A list compared with itself position by position. -/
theorem zip_self_all {r : Ty → Ty → Bool} (hr : ∀ x, r x x = true) :
    ∀ (l : List (Variance × Ty)), (l.zip l).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true
  | [] => rfl
  | (v, x) :: rest => by
    rw [List.zip_cons_cons, List.all_cons, zip_self_all hr rest, Bool.and_true]
    cases v <;> simp only [Variance.holds, hr, Bool.and_self]

/-- case: two. -/
theorem argsBelow_refl (t : Ty) : argsBelow sub t t = true :=
  zip_self_all sub_refl t.args

/-- Corresponding arguments correspond: same length, same variances. case: two (the record
case reads the equal canonical heads' lengths). -/
theorem args_congr {a b : Ty} (h : sameHead a b = true) :
    a.args.length = b.args.length ∧ a.args.map Prod.fst = b.args.map Prod.fst := by
  cases a <;> cases b
  case record.record fs gs =>
    have hh : heads (canonF fs) = heads (canonF gs) := of_decide_eq_true h
    have hlen : (canonF fs).length = (canonF gs).length := by
      have := congrArg List.length hh
      simp only [heads, List.length_map] at this
      exact this
    simp only [args, List.length_map, List.map_map]
    refine ⟨hlen, ?_⟩
    rw [show (Prod.fst ∘ fun p : String × Bool × Ty => (Variance.co, p.2.2)) = fun _ => Variance.co from rfl,
      List.map_const', List.map_const', hlen]
  case tuple.tuple ts us =>
    have hlen : ts.length = us.length := of_decide_eq_true h
    simp only [args, List.length_map, List.map_map]
    refine ⟨hlen, ?_⟩
    rw [show (Prod.fst ∘ fun t : Ty => (Variance.co, t)) = fun _ => Variance.co from rfl,
      List.map_const', List.map_const', hlen]
  case app.app n ts m us =>
    have hlen : ts.length = us.length := (of_decide_eq_true h).2
    simp only [args, List.length_map, List.map_map]
    refine ⟨hlen, ?_⟩
    rw [show (Prod.fst ∘ fun t : Ty => (Variance.inv, t)) = fun _ => Variance.inv from rfl,
      List.map_const', List.map_const', hlen]
  all_goals aesop (add norm simp [sameHead, args])

/-- **The law that changes.** A node is its head and its children, up to the head's normaliser:
two records with one canonical head and one list of canonical children have one canonical form.
(Two raw records that differ only in field order satisfy the premises and are different raw
terms; `eq_of_sameHead_raw_false` below.) -/
theorem eq_of_sameHead {a b : Ty} (h : sameHead a b = true)
    (hx : a.args.map Prod.snd = b.args.map Prod.snd) : canonHead a = canonHead b := by
  cases a <;> cases b
  case record.record fs gs =>
    have hh : heads (canonF fs) = heads (canonF gs) := of_decide_eq_true h
    simp only [args, List.map_map] at hx
    simp only [canonHead, Ty.record.injEq]
    exact fields_ext (canonF fs) (canonF gs) hh hx
  case tuple.tuple ts us =>
    simp only [args, List.map_map] at hx
    simp only [canonHead, Ty.tuple.injEq]
    rw [show (Prod.snd ∘ fun t : Ty => (Variance.co, t)) = id from rfl, List.map_id, List.map_id] at hx
    exact hx
  case app.app n ts m us =>
    have hn : n = m := (of_decide_eq_true h).1
    simp only [args, List.map_map] at hx
    simp only [canonHead, Ty.app.injEq]
    rw [show (Prod.snd ∘ fun t : Ty => (Variance.inv, t)) = id from rfl, List.map_id, List.map_id] at hx
    exact ⟨hn, hx⟩
  all_goals aesop (add norm simp [sameHead, args, canonHead, Ty.handle.injEq, Ty.option.injEq,
    Ty.list.injEq, Ty.prod.injEq, Ty.except.injEq, Ty.exitOf.injEq, Ty.causeOf.injEq,
    Ty.fiberOf.injEq, Ty.union.injEq, Ty.lit.injEq, Ty.refOf.injEq, Ty.deferredOf.injEq,
    Ty.var.injEq, Ty.map.injEq])
where
  /-- Two field lists with the same heads and the same types are equal. -/
  fields_ext : ∀ (l m : List (String × Bool × Ty)), heads l = heads m →
      l.map (Prod.snd ∘ fun p : String × Bool × Ty => (Variance.co, p.2.2)) =
        m.map (Prod.snd ∘ fun p : String × Bool × Ty => (Variance.co, p.2.2)) → l = m
    | [], [], _, _ => rfl
    | [], _ :: _, hh, _ => nomatch hh
    | _ :: _, [], hh, _ => nomatch hh
    | (n, o, s) :: l, (k, q, t) :: m, hh, ht => by
      simp only [heads, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hh
      simp only [List.map_cons, List.cons.injEq, Function.comp_apply] at ht
      obtain ⟨⟨hn, ho⟩, hrest⟩ := hh
      rw [hn, ho, ht.1, fields_ext l m hrest ht.2]

/-- RED CONTROL (proved): the old statement of `eq_of_sameHead`, `a = b`, is false at a raw
record written out of order. -/
theorem eq_of_sameHead_raw_false :
    ¬ (∀ a b : Ty, sameHead a b = true → a.args.map Prod.snd = b.args.map Prod.snd → a = b) := by
  intro hall
  have := hall (.record [("b", false, .nat), ("a", false, .string)])
    (.record [("a", false, .string), ("b", false, .nat)]) (by decide) (by decide)
  exact absurd this (by decide)

/-- copied. -/
theorem Variance.holds_trans {r : Ty → Ty → Bool} (v : Variance)
    (htrans : ∀ x y z, r x y = true → r y z = true → r x z = true) {x y z : Ty}
    (h : v.holds r x y = true) (h' : v.holds r y z = true) : v.holds r x z = true := by
  cases v <;> aesop (add norm simp [Variance.holds])

/-- copied. -/
theorem Variance.holds_antisymm {r : Ty → Ty → Bool} (v : Variance) {x y : Ty}
    (h : v.holds r x y = true) (h' : v.holds r y x = true) :
    r x y = true ∧ r y x = true := by
  cases v <;> aesop (add norm simp [Variance.holds])

/-! ### The congruence arms, one lemma each -/

theorem sub_args_option (x0 y0 : Ty) :
    sub (.option x0) (.option y0) = argsBelow sub (.option x0) (.option y0) := by
  by_cases h : Ty.option x0 = Ty.option y0
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.option x0) (.option y0) rfl)]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true]

theorem sub_args_list (x0 y0 : Ty) :
    sub (.list x0) (.list y0) = argsBelow sub (.list x0) (.list y0) := by
  by_cases h : Ty.list x0 = Ty.list y0
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.list x0) (.list y0) rfl)]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true]

theorem sub_args_prod (x0 x1 y0 y1 : Ty) :
    sub (.prod x0 x1) (.prod y0 y1) = argsBelow sub (.prod x0 x1) (.prod y0 y1) := by
  by_cases h : Ty.prod x0 x1 = Ty.prod y0 y1
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.prod x0 x1) (.prod y0 y1) rfl)]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true]

theorem sub_args_except (x0 x1 y0 y1 : Ty) :
    sub (.except x0 x1) (.except y0 y1) = argsBelow sub (.except x0 x1) (.except y0 y1) := by
  by_cases h : Ty.except x0 x1 = Ty.except y0 y1
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.except x0 x1) (.except y0 y1) rfl)]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true]

theorem sub_args_exitOf (x0 x1 y0 y1 : Ty) :
    sub (.exitOf x0 x1) (.exitOf y0 y1) = argsBelow sub (.exitOf x0 x1) (.exitOf y0 y1) := by
  by_cases h : Ty.exitOf x0 x1 = Ty.exitOf y0 y1
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.exitOf x0 x1) (.exitOf y0 y1) rfl)]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true]

theorem sub_args_causeOf (x0 y0 : Ty) :
    sub (.causeOf x0) (.causeOf y0) = argsBelow sub (.causeOf x0) (.causeOf y0) := by
  by_cases h : Ty.causeOf x0 = Ty.causeOf y0
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.causeOf x0) (.causeOf y0) rfl)]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true]

theorem sub_args_fiberOf (x0 x1 y0 y1 : Ty) :
    sub (.fiberOf x0 x1) (.fiberOf y0 y1) = argsBelow sub (.fiberOf x0 x1) (.fiberOf y0 y1) := by
  by_cases h : Ty.fiberOf x0 x1 = Ty.fiberOf y0 y1
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.fiberOf x0 x1) (.fiberOf y0 y1) rfl)]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true]

theorem sub_args_refOf (x0 y0 : Ty) :
    sub (.refOf x0) (.refOf y0) = argsBelow sub (.refOf x0) (.refOf y0) := by
  by_cases h : Ty.refOf x0 = Ty.refOf y0
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.refOf x0) (.refOf y0) rfl)]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true]

theorem sub_args_deferredOf (x0 x1 y0 y1 : Ty) :
    sub (.deferredOf x0 x1) (.deferredOf y0 y1) = argsBelow sub (.deferredOf x0 x1) (.deferredOf y0 y1) := by
  by_cases h : Ty.deferredOf x0 x1 = Ty.deferredOf y0 y1
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.deferredOf x0 x1) (.deferredOf y0 y1) rfl)]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

/-- new: the map head is a fixed-arity congruence (`inv` key, `co` value). -/
theorem sub_args_map (x0 x1 y0 y1 : Ty) :
    sub (.map x0 x1) (.map y0 y1) = argsBelow sub (.map x0 x1) (.map y0 y1) := by
  by_cases h : Ty.map x0 x1 = Ty.map y0 y1
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.map x0 x1) (.map y0 y1) rfl)]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true]

/-- Attaching does not change a position-wise comparison. -/
theorem all_zip_attach {α : Type} (f : α → α → Bool) :
    ∀ (l m : List α), ((l.attach.zip m.attach).all fun pq => f pq.1.1 pq.2.1) =
      (l.zip m).all fun pq => f pq.1 pq.2
  | [], _ => by simp only [List.attach_nil, List.zip_nil_left, List.all_nil]
  | _ :: _, [] => by simp only [List.attach_nil, List.zip_nil_right, List.all_nil]
  | a :: l, b :: m => by
    rw [List.attach_cons, List.attach_cons, List.zip_cons_cons, List.zip_cons_cons, List.all_cons,
      List.all_cons]
    congr 1
    have ih := all_zip_attach f l m
    rw [← ih, List.zip_map, List.all_map]
    rfl

/-- new: the record head. Under one canonical head, `sub` is the field-wise comparison. -/
theorem sub_args_record (fs gs : List (String × Bool × Ty))
    (hh : heads (canonF fs) = heads (canonF gs)) :
    sub (.record fs) (.record gs) = argsBelow sub (.record fs) (.record gs) := by
  by_cases h : Ty.record fs = Ty.record gs
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.record fs) (.record gs) rfl)]
    show (decide (heads (canonF fs) = heads (canonF gs)) &&
      ((canonF fs).attach.zip (canonF gs).attach).all fun pq => sub pq.1.1.2.2 pq.2.1.2.2) =
        (((canonF fs).map fun p => (Variance.co, p.2.2)).zip
          ((canonF gs).map fun p => (Variance.co, p.2.2))).all
            fun p => p.1.1.holds sub p.1.2 p.2.2
    rw [decide_eq_true hh, Bool.true_and,
      all_zip_attach (fun p q : String × Bool × Ty => sub p.2.2 q.2.2), List.zip_map, List.all_map]
    rfl

/-- new: the tuple head, given equal arity. -/
theorem sub_args_tuple (ts us : List Ty) (hlen : ts.length = us.length) :
    sub (.tuple ts) (.tuple us) = argsBelow sub (.tuple ts) (.tuple us) := by
  by_cases h : Ty.tuple ts = Ty.tuple us
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.tuple ts) (.tuple us) rfl)]
    show (decide (ts.length = us.length) &&
      (ts.attach.zip us.attach).all fun pq => sub pq.1.1 pq.2.1) =
        ((ts.map fun t => (Variance.co, t)).zip (us.map fun t => (Variance.co, t))).all
          fun p => p.1.1.holds sub p.1.2 p.2.2
    rw [decide_eq_true hlen, Bool.true_and, all_zip_attach (fun p q : Ty => sub p q), List.zip_map,
      List.all_map]
    rfl

/-- new: the reference head (invariant arguments), given the name and the arity. -/
theorem sub_args_app (n m : String) (ts us : List Ty) (hh : n = m ∧ ts.length = us.length) :
    sub (.app n ts) (.app m us) = argsBelow sub (.app n ts) (.app m us) := by
  by_cases h : Ty.app n ts = Ty.app m us
  · rw [h, sub_refl, argsBelow_refl]
  · conv => lhs; unfold sub
    rw [if_neg h, ite_leafRule_false (leafRule_of_left_none (.app n ts) (.app m us) rfl)]
    show (decide (n = m ∧ ts.length = us.length) &&
      (ts.attach.zip us.attach).all fun pq => sub pq.1.1 pq.2.1 && sub pq.2.1 pq.1.1) =
        ((ts.map fun t => (Variance.inv, t)).zip (us.map fun t => (Variance.inv, t))).all
          fun p => p.1.1.holds sub p.1.2 p.2.2
    rw [decide_eq_true hh, Bool.true_and,
      all_zip_attach (fun p q : Ty => sub p q && sub q p), List.zip_map, List.all_map]
    rfl

/-- Different heads: the order answers `false`. The hypothesis `hleaf` is the table's
(`leafRule`, was `litRule`). case: the table's line is `case2` (production's `.lit _, .string` arm
is gone from the rows, so the congruence arms keep their numbers); the record, tuple and reference
arms' `decide` is false at different heads. -/
theorem sub_eq_false_of_not_sameHead (a b : Ty) (ha : isMember a = true)
    (hb : isMember b = true) (hleaf : leafRule a b = false) (htop : topRule a b = false)
    (hh : sameHead a b = false) : sub a b = false := by
  fun_cases Ty.sub a b
  case case1 => rw [sameHead_refl _ ha] at hh; exact Bool.noConfusion hh
  case case2 _ hl => rw [hleaf] at hl; exact Bool.noConfusion hl
  case case3 => exact Bool.noConfusion ha
  case case4 => exact Bool.noConfusion ha
  case case5 => exact Bool.noConfusion hb
  case case6 => exact Bool.noConfusion htop
  case case16 fs gs _ _ =>
    simp only [sameHead, decide_eq_false_iff_not] at hh
    rw [decide_eq_false hh, Bool.false_and]
  case case18 ts us _ _ =>
    simp only [sameHead, decide_eq_false_iff_not] at hh
    rw [decide_eq_false hh, Bool.false_and]
  case case19 n ts m us _ _ =>
    simp only [sameHead, decide_eq_false_iff_not] at hh
    rw [decide_eq_false hh, Bool.false_and]
  case case20 => rfl
  all_goals simp only [sameHead, Bool.true_eq_false] at hh

/-- Same head: the order IS the variance-wise comparison. case: two. -/
theorem sub_eq_argsBelow_of_sameHead (a b : Ty) (hh : sameHead a b = true) :
    sub a b = argsBelow sub a b := by
  revert hh
  fun_cases Ty.sameHead a b
  case case1 => intro _; rw [sub_refl, argsBelow_refl]
  case case2 => intro _; rw [sub_refl, argsBelow_refl]
  case case3 => intro _; rw [sub_refl, argsBelow_refl]
  case case4 => intro _; rw [sub_refl, argsBelow_refl]
  case case5 => intro _; rw [sub_refl, argsBelow_refl]
  case case6 => intro _; rw [sub_refl, argsBelow_refl]
  case case7 =>
    intro hh
    have hp := of_decide_eq_true hh
    subst hp
    rw [sub_refl, argsBelow_refl]
  case case8 => intro _; exact sub_args_option _ _
  case case9 => intro _; exact sub_args_list _ _
  case case10 => intro _; exact sub_args_prod _ _ _ _
  case case11 => intro _; exact sub_args_except _ _ _ _
  case case12 => intro _; exact sub_args_exitOf _ _ _ _
  case case13 => intro _; exact sub_args_causeOf _ _
  case case14 => intro _; exact sub_args_fiberOf _ _ _ _
  case case15 =>
    intro hh
    have hp := of_decide_eq_true hh
    subst hp
    rw [sub_refl, argsBelow_refl]
  case case16 => intro _; exact sub_args_refOf _ _
  case case17 => intro _; exact sub_args_deferredOf _ _ _ _
  case case18 =>
    intro hh
    have hp := of_decide_eq_true hh
    subst hp
    rw [sub_refl, argsBelow_refl]
  case case19 => intro _; rw [sub_refl, argsBelow_refl]
  case case20 fs gs => intro hh; exact sub_args_record fs gs (of_decide_eq_true hh)
  case case21 => intro _; exact sub_args_map _ _ _ _
  case case22 ts us => intro hh; exact sub_args_tuple ts us (of_decide_eq_true hh)
  case case23 n ts m us => intro hh; exact sub_args_app n m ts us (of_decide_eq_true hh)
  case case24 => intro _; rw [sub_refl, argsBelow_refl]
  case case25 => intro _; rw [sub_refl, argsBelow_refl]
  case case26 => intro _; rw [sub_refl, argsBelow_refl]
  case case27 => intro _; rw [sub_refl, argsBelow_refl]
  case case28 => intro hh; exact Bool.noConfusion hh

/-- **`sub` between union members is the variance-wise comparison of corresponding
arguments.** Statement unchanged but for the leaf hypothesis's name: `hleaf : leafRule a b = false`,
the table's rule, where production reads `hlit : litRule a b = false`. -/
theorem sub_eq_args (a b : Ty) (ha : isMember a = true) (hb : isMember b = true)
    (hleaf : leafRule a b = false) (htop : topRule a b = false) :
    sub a b = (sameHead a b && argsBelow sub a b) := by
  cases hh : sameHead a b
  · rw [Bool.false_and]
    exact sub_eq_false_of_not_sameHead a b ha hb hleaf htop hh
  · rw [Bool.true_and]
    exact sub_eq_argsBelow_of_sameHead a b hh

/-- A child is smaller. case: two. -/
theorem sizeOf_args {t : Ty} {v : Variance} {x : Ty} (h : (v, x) ∈ t.args) :
    sizeOf x < sizeOf t := by
  cases t
  case record fs =>
    simp only [args, List.mem_map, Prod.mk.injEq] at h
    obtain ⟨p, hp, -, rfl⟩ := h
    have := sizeOf_field_lt (mem_canonBy hp)
    simp only [Ty.record.sizeOf_spec]
    omega
  case map k v =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp only [Ty.map.sizeOf_spec] <;> omega
  case tuple ts =>
    simp only [args, List.mem_map, Prod.mk.injEq] at h
    obtain ⟨t, ht, -, rfl⟩ := h
    have := sizeOf_item_lt ht
    simp only [Ty.tuple.sizeOf_spec]
    omega
  case app n ts =>
    simp only [args, List.mem_map, Prod.mk.injEq] at h
    obtain ⟨t, ht, -, rfl⟩ := h
    have := sizeOf_item_lt ht
    simp only [Ty.app.sizeOf_spec]
    omega
  case option inner =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩; simp only [Ty.option.sizeOf_spec]; omega
  case list inner =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩; simp only [Ty.list.sizeOf_spec]; omega
  case prod left right =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp only [Ty.prod.sizeOf_spec] <;> omega
  case except error value =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp only [Ty.except.sizeOf_spec] <;> omega
  case exitOf value error =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp only [Ty.exitOf.sizeOf_spec] <;> omega
  case causeOf error =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩; simp only [Ty.causeOf.sizeOf_spec]; omega
  case fiberOf value error =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp only [Ty.fiberOf.sizeOf_spec] <;> omega
  case union left right =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp only [Ty.union.sizeOf_spec] <;> omega
  case refOf value =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩; simp only [Ty.refOf.sizeOf_spec]; omega
  case deferredOf value error =>
    simp only [args, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp only [Ty.deferredOf.sizeOf_spec] <;> omega
  all_goals simp only [args, List.not_mem_nil] at h

/-! ### The order's two generic steps (copied; no head is named) -/

theorem Variance.holds_trans_of {r : Ty → Ty → Bool} (v : Variance) {x y z : Ty} {m : Nat}
    (hm : sizeOf x + sizeOf y + sizeOf z < m)
    (htrans : ∀ p q s, sizeOf p + sizeOf q + sizeOf s < m →
      r p q = true → r q s = true → r p s = true)
    (h : v.holds r x y = true) (h' : v.holds r y z = true) : v.holds r x z = true := by
  cases v
  case co => exact htrans x y z hm h h'
  case contra => exact htrans z y x (by omega) h' h
  case inv =>
    simp only [Variance.holds, Bool.and_eq_true_iff] at h h' ⊢
    exact ⟨htrans x y z hm h.1 h'.1, htrans z y x (by omega) h'.2 h.2⟩

private theorem zipAll_trans {r : Ty → Ty → Bool} :
    ∀ (xs ys zs : List (Variance × Ty)),
      xs.map Prod.fst = ys.map Prod.fst → ys.map Prod.fst = zs.map Prod.fst →
      (∀ x ∈ xs, ∀ y ∈ ys, ∀ z ∈ zs, ∀ v : Variance,
        v.holds r x.2 y.2 = true → v.holds r y.2 z.2 = true → v.holds r x.2 z.2 = true) →
      (xs.zip ys).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true →
      (ys.zip zs).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true →
      (xs.zip zs).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: _, [], _, h1, _, _, _, _ => by
    simp only [List.map_cons, List.map_nil] at h1
    exact absurd h1 (List.cons_ne_nil _ _)
  | _ :: _, _ :: _, [], _, h2, _, _, _ => by
    simp only [List.map_cons, List.map_nil] at h2
    exact absurd h2 (List.cons_ne_nil _ _)
  | x :: xs, y :: ys, z :: zs, h1, h2, hstep, hxy, hyz => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true_iff] at hxy hyz ⊢
    refine ⟨?_, ?_⟩
    · refine hstep x List.mem_cons_self y List.mem_cons_self z List.mem_cons_self x.1 hxy.1 ?_
      rw [h1.1]
      exact hyz.1
    · exact zipAll_trans xs ys zs h1.2 h2.2
        (fun a ha b hb c hc => hstep a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
          c (List.mem_cons_of_mem _ hc))
        hxy.2 hyz.2

/-- copied. -/
theorem argsBelow_trans {r : Ty → Ty → Bool} {a b c : Ty}
    (hab : sameHead a b = true) (hbc : sameHead b c = true)
    (htrans : ∀ x y z, sizeOf x + sizeOf y + sizeOf z < sizeOf a + sizeOf b + sizeOf c →
      r x y = true → r y z = true → r x z = true)
    (h1 : argsBelow r a b = true) (h2 : argsBelow r b c = true) :
    argsBelow r a c = true := by
  refine zipAll_trans a.args b.args c.args (args_congr hab).2 (args_congr hbc).2 ?_ h1 h2
  intro x hx y hy z hz v
  refine Variance.holds_trans_of v ?_ htrans
  have hxa : sizeOf x.2 < sizeOf a := sizeOf_args hx
  have hyb : sizeOf y.2 < sizeOf b := sizeOf_args hy
  have hzc : sizeOf z.2 < sizeOf c := sizeOf_args hz
  omega

private theorem zipAll_antisymm {r : Ty → Ty → Bool} :
    ∀ (xs ys : List (Variance × Ty)),
      xs.map Prod.fst = ys.map Prod.fst →
      (∀ x ∈ xs, ∀ y ∈ ys, r x.2 y.2 = true → r y.2 x.2 = true → x.2 = y.2) →
      (xs.zip ys).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true →
      (ys.zip xs).all (fun p => p.1.1.holds r p.1.2 p.2.2) = true →
      xs.map Prod.snd = ys.map Prod.snd
  | [], [], _, _, _, _ => rfl
  | _ :: _, [], h, _, _, _ => by
    simp only [List.map_cons, List.map_nil] at h
    exact absurd h (List.cons_ne_nil _ _)
  | [], _ :: _, h, _, _, _ => by
    simp only [List.map_cons, List.map_nil] at h
    exact absurd h.symm (List.cons_ne_nil _ _)
  | x :: xs, y :: ys, h, hstep, hxy, hyx => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true_iff] at hxy hyx
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, zipAll_antisymm xs ys h.2
      (fun a ha b hb => hstep a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      hxy.2 hyx.2⟩
    have hback : x.1.holds r y.2 x.2 = true := by rw [h.1]; exact hyx.1
    obtain ⟨hf, hb⟩ := Variance.holds_antisymm x.1 hxy.1 hback
    exact hstep x List.mem_cons_self y List.mem_cons_self hf hb

/-- copied. -/
theorem sizeOf_args_mem {t x : Ty} (h : x ∈ t.args.map Prod.snd) : sizeOf x < sizeOf t := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  exact sizeOf_args hp

/-- **The order's antisymmetric step.** statement: its conclusion is `canonHead a = canonHead b`
(it was `a = b`), inherited from `eq_of_sameHead`. -/
theorem argsBelow_antisymm {r : Ty → Ty → Bool} {a b : Ty} (hab : sameHead a b = true)
    (heq : ∀ x ∈ a.args.map Prod.snd, ∀ y ∈ b.args.map Prod.snd,
      r x y = true → r y x = true → x = y)
    (h1 : argsBelow r a b = true) (h2 : argsBelow r b a = true) : canonHead a = canonHead b := by
  refine eq_of_sameHead hab (zipAll_antisymm a.args b.args (args_congr hab).2 ?_ h1 h2)
  intro x hx y hy hxy hyx
  exact heq x.2 (List.mem_map_of_mem hx) y.2 (List.mem_map_of_mem hy) hxy hyx

/-! ### The two rules beside the congruences, as inversions (copied) -/

theorem topRule_eq_false {a b : Ty} (h : b ≠ .unknown) : topRule a b = false := by
  cases b
  case unknown => exact absurd rfl h
  all_goals rfl

/-- With no children, the head's normaliser does nothing (no written field). -/
theorem canonHead_of_args_nil {t : Ty} (hx : t.args = []) : canonHead t = t := by
  cases t
  case record fs =>
    simp only [args, List.map_eq_nil_iff, canonBy_eq_nil_iff] at hx
    rw [hx]
    rfl
  all_goals rfl

/-- At a head with no children, `sameHead` is equality. Statement unchanged; the record case
reads `canonBy_eq_nil_iff` (no canonical children means no written fields). -/
theorem eq_of_sameHead_nil {a b : Ty} (h : sameHead a b = true) (hx : a.args = []) : a = b := by
  have hlen := (args_congr h).1
  rw [hx, List.length_nil] at hlen
  have hb : b.args = [] := List.eq_nil_of_length_eq_zero hlen.symm
  have hc := eq_of_sameHead h (by rw [hx, hb])
  rw [canonHead_of_args_nil hx, canonHead_of_args_nil hb] at hc
  exact hc

/-! ### The leaf table's laws

The closure's laws are checked over the finite head domain (`LeafHead.all`) by `decide`, so they
are regenerated with the table; a type's leaf head carries the facts the order's proofs read
(childless, a member, its own normal form). Nothing below names an edge. -/

theorem LeafHead.mem_all (x : LeafHead) : x ∈ LeafHead.all := by
  cases x <;> decide

/-- The closure's specification: a path of declared edges. -/
inductive LeafPath (edges : List (LeafHead × LeafHead)) : LeafHead → LeafHead → Prop
  | refl (x : LeafHead) : LeafPath edges x x
  | step {x y z : LeafHead} : (x, y) ∈ edges → LeafPath edges y z → LeafPath edges x z

/-- The search finds only paths (any table, any fuel). -/
theorem leafReach_sound (edges : List (LeafHead × LeafHead)) :
    ∀ (n : Nat) (x y : LeafHead), leafReach edges n x y = true → LeafPath edges x y
  | 0, x, y, h => by
    rw [leafReach] at h
    rw [of_decide_eq_true h]
    exact .refl y
  | n + 1, x, y, h => by
    rw [leafReach, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with h | ⟨e, he, hstep⟩
    · rw [of_decide_eq_true h]
      exact .refl y
    · rw [Bool.and_eq_true] at hstep
      have hx : e.1 = x := of_decide_eq_true hstep.1
      subst hx
      exact .step he (leafReach_sound edges n e.2 y hstep.2)

theorem leafLe_refl (x : LeafHead) : leafLe x x = true := by
  cases x <;> rfl

/-- **Transitivity of the leaf order** (checked over the finite domain). -/
theorem leafLe_trans {x y z : LeafHead} (hxy : leafLe x y = true) (hyz : leafLe y z = true) :
    leafLe x z = true := by
  have h : ∀ x ∈ LeafHead.all, ∀ y ∈ LeafHead.all, ∀ z ∈ LeafHead.all,
      leafLe x y = true → leafLe y z = true → leafLe x z = true := by decide
  exact h x (LeafHead.mem_all x) y (LeafHead.mem_all y) z (LeafHead.mem_all z) hxy hyz

/-- **The table is acyclic**, stated as the closure's antisymmetry (checked over the finite
domain). `sub`'s antisymmetry reads it through `leafRule_asymm`, and transitivity reads it through
`leafRule_trans` (a composite of two rules must relate different heads, which fails for a payload
head on a cycle: `lit "a" < y < lit "b"`). A cyclic table fails it: the red control in
`P2Ty.lean`. -/
theorem leafLe_antisymm {x y : LeafHead} (hxy : leafLe x y = true) (hyx : leafLe y x = true) :
    x = y := by
  have h : ∀ x ∈ LeafHead.all, ∀ y ∈ LeafHead.all,
      leafLe x y = true → leafLe y x = true → x = y := by decide
  exact h x (LeafHead.mem_all x) y (LeafHead.mem_all y) hxy hyx

/-- Every declared edge is in the closure, and none is a loop. -/
theorem leafLe_of_edge {x y : LeafHead} (h : (x, y) ∈ leafEdges) : leafLe x y = true := by
  have hall : ∀ e ∈ leafEdges, leafLe e.1 e.2 = true := by decide
  exact hall (x, y) h

theorem leafEdge_ne {x y : LeafHead} (h : (x, y) ∈ leafEdges) : x ≠ y := by
  have hall : ∀ e ∈ leafEdges, e.1 ≠ e.2 := by decide
  exact hall (x, y) h

/-- **The leaf order is the table's reflexive-transitive closure.** -/
theorem leafLe_iff_path {x y : LeafHead} : leafLe x y = true ↔ LeafPath leafEdges x y := by
  constructor
  · exact leafReach_sound leafEdges _ x y
  · intro h
    induction h with
    | refl x => exact leafLe_refl x
    | step he _ ih => exact leafLe_trans (leafLe_of_edge he) ih

/-- The acyclicity in path form: two paths that close a loop are both empty. -/
theorem leafEdges_acyclic {x y : LeafHead} (hxy : LeafPath leafEdges x y)
    (hyx : LeafPath leafEdges y x) : x = y :=
  leafLe_antisymm (leafLe_iff_path.mpr hxy) (leafLe_iff_path.mpr hyx)

/-- A leaf head's type is a childless member and its own normal form. -/
theorem leafHead_facts {t : Ty} {x : LeafHead} (h : leafHead t = some x) :
    t.args = [] ∧ isMember t = true ∧ normalize t = t := by
  cases t
  case lit | string | nat | int | number | undefined | unit => exact ⟨rfl, rfl, rfl⟩
  all_goals cases h

/-- The table's rule, unpacked. -/
theorem leafRule_eq_true {a b : Ty} (h : leafRule a b = true) :
    ∃ x y, leafHead a = some x ∧ leafHead b = some y ∧ x ≠ y ∧ leafLe x y = true := by
  unfold leafRule at h
  split at h
  · rename_i x y hx hy
    rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    exact ⟨x, y, hx, hy, h.1, h.2⟩
  · exact Bool.noConfusion h

/-- The table's rule, packed. -/
theorem leafRule_of_heads {a b : Ty} {x y : LeafHead} (ha : leafHead a = some x)
    (hb : leafHead b = some y) (hne : x ≠ y) (hle : leafLe x y = true) : leafRule a b = true := by
  unfold leafRule
  rw [ha, hb]
  show (!decide (x = y) && leafLe x y) = true
  rw [decide_eq_false hne, hle]
  rfl

/-- A declared edge between two types' leaf heads is a rule of the order. -/
theorem leafRule_of_edge {a b : Ty} {x y : LeafHead} (he : (x, y) ∈ leafEdges)
    (ha : leafHead a = some x) (hb : leafHead b = some y) : leafRule a b = true :=
  leafRule_of_heads ha hb (leafEdge_ne he) (leafLe_of_edge he)

/-- The table's rule is between childless members (`litRule_args`'s statement). -/
theorem leafRule_args {a b : Ty} (h : leafRule a b = true) :
    a.args = [] ∧ b.args = [] ∧ isMember a = true ∧ isMember b = true := by
  obtain ⟨x, y, hx, hy, -, -⟩ := leafRule_eq_true h
  exact ⟨(leafHead_facts hx).1, (leafHead_facts hy).1, (leafHead_facts hx).2.1,
    (leafHead_facts hy).2.1⟩

/-- **The rule composes**: the closure is transitive, and the composite relates different heads
because the table is acyclic. -/
theorem leafRule_trans {a b c : Ty} (hab : leafRule a b = true) (hbc : leafRule b c = true) :
    leafRule a c = true := by
  obtain ⟨x, y, hx, hy, hxy, hlxy⟩ := leafRule_eq_true hab
  obtain ⟨y', z, hy', hz, -, hlyz⟩ := leafRule_eq_true hbc
  rw [hy] at hy'
  cases hy'
  refine leafRule_of_heads hx hz ?_ (leafLe_trans hlxy hlyz)
  intro hxz
  subst hxz
  exact hxy (leafLe_antisymm hlxy hlyz)

/-- The rule is asymmetric (the table is acyclic). -/
theorem leafRule_asymm {a b : Ty} (h : leafRule a b = true) : leafRule b a = false := by
  cases hba : leafRule b a with
  | false => rfl
  | true =>
    obtain ⟨x, y, hx, hy, hxy, hlxy⟩ := leafRule_eq_true h
    obtain ⟨y', x', hy', hx', -, hlyx⟩ := leafRule_eq_true hba
    rw [hx] at hx'
    rw [hy] at hy'
    cases hx'
    cases hy'
    exact absurd (leafLe_antisymm hlxy hlyx) hxy

/-- Neither side of a rule is the top. -/
theorem leafRule_ne_unknown {a b : Ty} (h : leafRule a b = true) :
    a ≠ .unknown ∧ b ≠ .unknown := by
  obtain ⟨x, y, hx, hy, -, -⟩ := leafRule_eq_true h
  refine ⟨?_, ?_⟩
  · rintro rfl
    cases hx
  · rintro rfl
    cases hy

/-- A rule relates two different heads. -/
theorem leafRule_sameHead {a b : Ty} (h : leafRule a b = true) : sameHead a b = false := by
  cases hs : sameHead a b with
  | false => rfl
  | true =>
    obtain ⟨x, y, hx, hy, hxy, -⟩ := leafRule_eq_true h
    have hab : a = b := eq_of_sameHead_nil hs (leafHead_facts hx).1
    subst hab
    rw [hx] at hy
    cases hy
    exact absurd rfl hxy

/-- Both sides of a rule are their own normal forms. -/
theorem leafRule_normalize {a b : Ty} (h : leafRule a b = true) :
    normalize a = a ∧ normalize b = b := by
  obtain ⟨x, y, hx, hy, -, -⟩ := leafRule_eq_true h
  exact ⟨(leafHead_facts hx).2.2, (leafHead_facts hy).2.2⟩

/-- A normal type is its own canonical head. -/
theorem Normal.canonHead {t : Ty} (h : Normal t) : canonHead t = t := by
  induction h
  case record fs _ hasc _ => exact congrArg Ty.record (canonBy_of_ascending fs hasc)
  case row r _ _ _ ih =>
    cases hr : r.elems with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => exact ih x (by rw [hr]; exact List.mem_singleton_self x)
      | cons y ys => rfl
  all_goals rfl

end Ty

/-! ## Acceptance guards (the view's contract, copied and extended) -/

private def lhs (a b : Ty) : Bool := Ty.sub a b
private def rhs (a b : Ty) : Bool := Ty.sameHead a b && Ty.argsBelow Ty.sub a b

#guard lhs (.option (.lit "a")) (.option .string) = rhs (.option (.lit "a")) (.option .string)
#guard lhs (.refOf (.lit "a")) (.refOf .string) = rhs (.refOf (.lit "a")) (.refOf .string)
-- the record head: permuted, depth, a missing field, a flag
#guard lhs (.record [("b", false, .nat), ("a", false, .lit "x")]) (.record [("a", false, .string), ("b", false, .nat)])
  = rhs (.record [("b", false, .nat), ("a", false, .lit "x")]) (.record [("a", false, .string), ("b", false, .nat)])
#guard lhs (.record [("a", false, .nat)]) (.record [("a", false, .nat), ("b", false, .nat)])
  = rhs (.record [("a", false, .nat)]) (.record [("a", false, .nat), ("b", false, .nat)])
#guard lhs (.record [("a", true, .nat)]) (.record [("a", false, .nat)])
  = rhs (.record [("a", true, .nat)]) (.record [("a", false, .nat)])
#guard lhs (.map .string (.lit "a")) (.map .string .string) = rhs (.map .string (.lit "a")) (.map .string .string)
#guard (Ty.record [("b", false, .nat), ("a", false, .string)]).args.map Prod.snd = [.string, .nat]
#guard (Ty.map .string .nat).args = [(.inv, .string), (.co, .nat)]
#guard Ty.sameHead (.record [("b", false, .nat), ("a", true, .string)]) (.record [("a", true, .bool), ("b", false, .nat)])
#guard !Ty.sameHead (.record [("a", true, .nat)]) (.record [("a", false, .nat)])
-- the leaf table's rule: different heads only; a literal relates to its own value by reflexivity
#guard Ty.leafRule .nat .number && Ty.leafRule (.lit "a") .string && !Ty.leafRule (.lit "a") (.lit "b")
#guard !Ty.leafRule .nat .nat && !Ty.leafRule .number .nat && !Ty.leafRule .null .unit

end ProbeP

#print axioms ProbeP.Ty.sameHead_refl
#print axioms ProbeP.Ty.sameHead_symm
#print axioms ProbeP.Ty.sameHead_trans
#print axioms ProbeP.Ty.argsBelow_refl
#print axioms ProbeP.Ty.args_congr
#print axioms ProbeP.Ty.eq_of_sameHead
#print axioms ProbeP.Ty.eq_of_sameHead_raw_false
#print axioms ProbeP.Ty.sub_args_record
#print axioms ProbeP.Ty.sub_args_map
#print axioms ProbeP.Ty.sub_args_tuple
#print axioms ProbeP.Ty.sub_args_app
#print axioms ProbeP.Ty.leafReach_sound
#print axioms ProbeP.Ty.leafLe_trans
#print axioms ProbeP.Ty.leafLe_antisymm
#print axioms ProbeP.Ty.leafLe_iff_path
#print axioms ProbeP.Ty.leafEdges_acyclic
#print axioms ProbeP.Ty.leafRule_trans
#print axioms ProbeP.Ty.leafRule_asymm
#print axioms ProbeP.Ty.leafRule_sameHead
#print axioms ProbeP.Ty.leafRule_of_edge
#print axioms ProbeP.Ty.sub_eq_false_of_not_sameHead
#print axioms ProbeP.Ty.sub_eq_argsBelow_of_sameHead
#print axioms ProbeP.Ty.sub_eq_args
#print axioms ProbeP.Ty.sizeOf_args
#print axioms ProbeP.Ty.argsBelow_trans
#print axioms ProbeP.Ty.argsBelow_antisymm
#print axioms ProbeP.Ty.eq_of_sameHead_nil
#print axioms ProbeP.Ty.Normal.canonHead
