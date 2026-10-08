import Effect4.Modules.Step
import Effect4.Laws.Schema.FieldRef
import Effect4.Laws.Program.TyNormal
import Effect4.Laws.Modules.Reading
import Effect4.Laws.Modules.Checking
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Modules.Step — the step language's laws, proved once

A step written as data (`src/Effect4/Modules/Step.lean`) inherits three laws, with no proof of
its own (decisions row 330, slice L2):

- **Reading** (`Step.sound`; claim `step-language-sound`, concept `translation-simulation`,
  requirement R10): at every scope, for every caller's terms that read the inputs' encodings, a
  step that passes its reading check (`Step.canonical`) has a term that reads the encoding of its
  value (`Step.eval`). It holds at every identity context, the opaque one included.
- **Typing** (`Step.typed`; claim `step-language-typed`, concept `store-typing`, requirement
  R4): at every scope, for every caller's terms typed at the inputs' types, a step that passes
  its typing check (`Step.normal`) has a term that types at the step's type. The check certifies
  normal forms by a fold of `Ty` (`Ty.certNormal`), so it closes by `rfl` on a concrete step.
- **Framing** (`Step.frame`, `Step.frame_read`; claim `step-frame`, concept
  `translation-simulation`, requirement R10): on an update spine, a field that no overwrite names
  keeps its value. On carriers this needs no premise on the record's names, and on the machine's
  record frame it needs ascending names.

The typing check implies the reading check (`Step.canonical_of_normal`), so one check gives
both laws. The proofs reuse the builders' lemmas (`src/Effect4/Laws/Modules/Reading.lean`,
`src/Effect4/Laws/Modules/Checking.lean`) and the field laws
(`src/Effect4/Laws/Schema/FieldRef.lean`). The consumers are each module's step statements:
a module's `*_agrees` and `*_types` become corollaries (slice L3 for Semaphore's
`takeIfAvailable`).

What the laws do not establish: nothing of a fold (the language has none yet), of an optional
field, of a step's specification, or of a run. A step's value is a function of its inputs'
values; that it is the module's model is each module's statement.
-/

set_option autoImplicit false

namespace Effect4.Modules
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Store Effect4.Schema
open Effect4.Schema.Model

/-! ## Booleans of a check -/

theorem and_true : ∀ {a b : Bool}, (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => nomatch h
  | false, _, h => nomatch h

theorem and_intro : ∀ {a b : Bool}, a = true → b = true → (a && b) = true
  | true, true, _, _ => rfl
  | true, false, _, h => nomatch h
  | false, _, h, _ => nomatch h

/-! ## Encodings of a selection, a list and an option -/

theorem toVal_ite {α : Type} (I : Image α) (c : Bool) (x y : α) :
    (if c = true then I.toVal x else I.toVal y) = I.toVal (if c = true then x else y) := by
  cases c <;> rfl

theorem toVal_head {α : Type} (I : Image α) : ∀ xs : List α,
    (match (xs.map I.toVal)[0]? with
      | Option.some v => Store.Val.some v
      | none => Store.Val.none) = (Image.option I).toVal xs.head?
  | [] => rfl
  | _ :: _ => rfl

theorem nat_length_map {α : Type} (f : α → Val) (xs : List α) :
    Val.nat (xs.map f).length = Val.nat xs.length := by
  rw [List.length_map]

theorem list_snoc_map {α : Type} (f : α → Val) (xs : List α) (x : α) :
    Val.list (xs.map f ++ [f x]) = Val.list ((xs ++ [x]).map f) := by
  rw [List.map_append]
  rfl

theorem list_append_map {α : Type} (f : α → Val) (xs ys : List α) :
    Val.list (xs.map f ++ ys.map f) = Val.list ((xs ++ ys).map f) := by
  rw [List.map_append]

theorem list_take_map {α : Type} (f : α → Val) (xs : List α) (n : Nat) :
    Val.list ((xs.map f).take n) = Val.list ((xs.take n).map f) := by
  rw [List.map_take]

theorem list_drop_map {α : Type} (f : α → Val) (xs : List α) (n : Nat) :
    Val.list ((xs.map f).drop n) = Val.list ((xs.drop n).map f) := by
  rw [List.map_drop]

/-- Two inputs at one position of one type are one input. -/
theorem Input.index_inj : ∀ {Γ : List Ty} {t : Ty} (x y : Input Γ t), x.index = y.index → x = y
  | _, _, .here _ _, .here _ _, _ => rfl
  | _, _, .here _ _, .there _ _, h => nomatch h
  | _, _, .there _ _, .here _ _, h => nomatch h
  | _, _, .there _ x, .there _ y, h => by rw [Input.index_inj x y (Nat.succ.inj h)]

namespace Step

variable {Γ : List Ty}

/-! ## The order of the checks -/

/-- A check implies a weaker check, node by node. -/
theorem check_mono {r₁ r₂ : List (String × Bool × Ty) → Bool} {a₁ a₂ : Ty → Bool}
    (hr : ∀ fs, r₁ fs = true → r₂ fs = true) (ha : ∀ t, a₁ t = true → a₂ t = true) :
    ∀ {s : Ty} (e : Step Γ s), cata (checkAlg r₁ a₁) e = true → cata (checkAlg r₂ a₂) e = true
  | _, .var _, _ => rfl
  | _, .bool _, _ => rfl
  | _, .nat _, _ => rfl
  | _, .unit, _ => rfl
  | _, .not a, h => check_mono hr ha a h
  | _, .and a b, h => and_intro (check_mono hr ha a (and_true h).1) (check_mono hr ha b (and_true h).2)
  | _, .or a b, h => and_intro (check_mono hr ha a (and_true h).1) (check_mono hr ha b (and_true h).2)
  | _, .ite c a b, h => by
    obtain ⟨ht, rest⟩ := and_true h
    obtain ⟨hc, hab⟩ := and_true rest
    exact and_intro (ha _ ht) (and_intro (check_mono hr ha c hc)
      (and_intro (check_mono hr ha a (and_true hab).1) (check_mono hr ha b (and_true hab).2)))
  | _, .add a b, h => and_intro (check_mono hr ha a (and_true h).1) (check_mono hr ha b (and_true h).2)
  | _, .sub a b, h => and_intro (check_mono hr ha a (and_true h).1) (check_mono hr ha b (and_true h).2)
  | _, .lt a b, h => and_intro (check_mono hr ha a (and_true h).1) (check_mono hr ha b (and_true h).2)
  | _, .eq a b, h => and_intro (check_mono hr ha a (and_true h).1) (check_mono hr ha b (and_true h).2)
  | _, .isZero a, h => check_mono hr ha a h
  | _, .pair a b, h => and_intro (check_mono hr ha a (and_true h).1) (check_mono hr ha b (and_true h).2)
  | _, .tuple2 a b, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact and_intro (ha _ ht)
      (and_intro (check_mono hr ha a (and_true rest).1) (check_mono hr ha b (and_true rest).2))
  | _, .fst p, h => check_mono hr ha p h
  | _, .snd p, h => check_mono hr ha p h
  | _, .some a, h => check_mono hr ha a h
  | _, .get r _, h => and_intro (hr _ (and_true h).1) (check_mono hr ha r (and_true h).2)
  | _, .set r _ v, h => by
    obtain ⟨hf, rest⟩ := and_true h
    exact and_intro (hr _ hf)
      (and_intro (check_mono hr ha r (and_true rest).1) (check_mono hr ha v (and_true rest).2))
  | _, .emptyLike xs, h => check_mono hr ha xs h
  | _, .len xs, h => check_mono hr ha xs h
  | _, .snoc xs x, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact and_intro (ha _ ht)
      (and_intro (check_mono hr ha xs (and_true rest).1) (check_mono hr ha x (and_true rest).2))
  | _, .append xs ys, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact and_intro (ha _ ht)
      (and_intro (check_mono hr ha xs (and_true rest).1) (check_mono hr ha ys (and_true rest).2))
  | _, .take xs n, h => and_intro (check_mono hr ha xs (and_true h).1) (check_mono hr ha n (and_true h).2)
  | _, .drop xs n, h => and_intro (check_mono hr ha xs (and_true h).1) (check_mono hr ha n (and_true h).2)
  | _, .head xs, h => check_mono hr ha xs h

/-- **The typing check implies the reading check**: a record in normal form has ascending
names. -/
theorem canonical_of_normal {s : Ty} (e : Step Γ s) (h : e.normal = true) : e.canonical = true :=
  check_mono (fun _ hn => decide_eq_true (ascending_of_normal (Ty.normalize_of_certNormal _ hn)))
    (fun _ _ => rfl) e h

/-! ## Reading -/

section Reading

variable (L : Leaves) (vs : Inputs L Γ) {src : {t : Ty} → Input Γ t → TermSrc} {env : Env}
  {path : List Nat} {vals : List Val}

/-- **A step's term reads its value** (claim `step-language-sound`): at every scope, when the
caller's terms read the encodings of the inputs' values, a step that passes the reading check
has a term that reads the encoding of its value. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem sound
    (hin : ∀ {t : Ty} (x : Input Γ t), Reads (src x) env path vals ((imageAt L t).toVal (x.get vs))) :
    ∀ {s : Ty} (e : Step Γ s), e.canonical = true →
      Reads (e.term src) env path vals ((imageAt L s).toVal (e.eval L vs))
  | _, .var x, _ => hin x
  | _, .bool b, _ => reads_bool b env path vals
  | _, .nat n, _ => reads_nat n env path vals
  | _, .unit, _ => reads_unit
  | _, .not a, h => reads_notT (sound hin a h)
  | _, .and a b, h => reads_andT (sound hin a (and_true h).1) (sound hin b (and_true h).2)
  | _, .or a b, h => reads_orT (sound hin a (and_true h).1) (sound hin b (and_true h).2)
  | _, .ite c a b, h => by
    obtain ⟨hc, hab⟩ := and_true h
    exact (reads_ifT (sound hin c hc) (sound hin a (and_true hab).1)
      (sound hin b (and_true hab).2)).to (toVal_ite _ _ _ _)
  | _, .add a b, h => reads_add (sound hin a (and_true h).1) (sound hin b (and_true h).2)
  | _, .sub a b, h => reads_sub (sound hin a (and_true h).1) (sound hin b (and_true h).2)
  | _, .lt a b, h => reads_lt (sound hin a (and_true h).1) (sound hin b (and_true h).2)
  | _, .eq a b, h => reads_eq (sound hin a (and_true h).1) (sound hin b (and_true h).2)
  | _, .isZero a, h => reads_isZero (sound hin a h)
  | _, .pair a b, h => reads_pair (sound hin a (and_true h).1) (sound hin b (and_true h).2)
  | _, .tuple2 a b, h => reads_tuple2 (sound hin a (and_true h).1) (sound hin b (and_true h).2)
  | _, .fst p, h => reads_app (.cons (sound hin p h) .nil) rfl
  | _, .snd p, h => reads_app (.cons (sound hin p h) .nil) rfl
  | _, .some a, h => reads_some (sound hin a h)
  | _, .get r f, h =>
    reads_field (sound hin r (and_true h).2)
      (FieldRef.read_law (of_decide_eq_true (and_true h).1) f (r.eval L vs))
  | _, .set r f v, h => by
    obtain ⟨hf, rest⟩ := and_true h
    exact reads_recordSet (sound hin r (and_true rest).1) (sound hin v (and_true rest).2)
      (FieldRef.write_law (of_decide_eq_true hf) f (r.eval L vs) (v.eval L vs))
  | _, .emptyLike xs, h => reads_noneOf (sound hin xs h)
  | _, .len xs, h => (reads_len (sound hin xs h)).to (nat_length_map _ _)
  | _, .snoc xs x, h =>
    (reads_snoc (sound hin xs (and_true h).1) (sound hin x (and_true h).2)).to
      (list_snoc_map _ _ _)
  | _, .append xs ys, h =>
    (reads_append (sound hin xs (and_true h).1) (sound hin ys (and_true h).2)).to
      (list_append_map _ _ _)
  | _, .take xs n, h =>
    (reads_take (sound hin xs (and_true h).1) (sound hin n (and_true h).2)).to
      (list_take_map _ _ _)
  | _, .drop xs n, h =>
    (reads_drop (sound hin xs (and_true h).1) (sound hin n (and_true h).2)).to
      (list_drop_map _ _ _)
  | _, .head xs, h => (reads_head (sound hin xs h)).to (toVal_head _ _)

end Reading

/-! ## Typing -/

section Typing

/-- **The typing check gives the typing facts**: each certified type is its own normal form
(`Ty.normalize_of_certNormal`), and a certified product's items are normal factors. -/
theorem facts_of_normal : ∀ {s : Ty} (e : Step Γ s), e.normal = true → e.Facts
  | _, .var _, _ => trivial
  | _, .bool _, _ => trivial
  | _, .nat _, _ => trivial
  | _, .unit, _ => trivial
  | _, .not a, h => facts_of_normal a h
  | _, .and a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, .or a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, .ite c a b, h => by
    obtain ⟨ht, rest⟩ := and_true h
    obtain ⟨hc, hab⟩ := and_true rest
    exact ⟨Ty.normalize_of_certNormal _ ht, facts_of_normal c hc,
      facts_of_normal a (and_true hab).1, facts_of_normal b (and_true hab).2⟩
  | _, .add a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, .sub a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, .lt a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, .eq a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, .isZero a, h => facts_of_normal a h
  | _, .pair a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, .tuple2 a b, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact ⟨certNormal_prod_facts ht, facts_of_normal a (and_true rest).1,
      facts_of_normal b (and_true rest).2⟩
  | _, .fst p, h => facts_of_normal p h
  | _, .snd p, h => facts_of_normal p h
  | _, .some a, h => facts_of_normal a h
  | _, .get r _, h => ⟨Ty.normalize_of_certNormal _ (and_true h).1, facts_of_normal r (and_true h).2⟩
  | _, .set r _ v, h => by
    obtain ⟨hf, rest⟩ := and_true h
    exact ⟨Ty.normalize_of_certNormal _ hf, facts_of_normal r (and_true rest).1,
      facts_of_normal v (and_true rest).2⟩
  | _, .emptyLike xs, h => facts_of_normal xs h
  | _, .len xs, h => facts_of_normal xs h
  | _, .snoc xs x, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact ⟨Ty.normalize_of_certNormal _ ht, facts_of_normal xs (and_true rest).1,
      facts_of_normal x (and_true rest).2⟩
  | _, .append xs ys, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact ⟨Ty.normalize_of_certNormal _ ht, facts_of_normal xs (and_true rest).1,
      facts_of_normal ys (and_true rest).2⟩
  | _, .take xs n, h => ⟨facts_of_normal xs (and_true h).1, facts_of_normal n (and_true h).2⟩
  | _, .drop xs n, h => ⟨facts_of_normal xs (and_true h).1, facts_of_normal n (and_true h).2⟩
  | _, .head xs, h => facts_of_normal xs h

variable {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
  {src : {t : Ty} → Input Γ t → TermSrc} {env : Env} {path : List Nat} {types : List Ty}
include atoms

/-- **A step's term types at the step's type** (claim `step-language-typed`): at every scope,
when the caller's terms type at the inputs' types, a step whose typing facts hold has a term
that types at its type, under each literal flag. A caller proves the facts from premises where a
type is a parameter, or by the typing check (`typed_of_normal`). -/
@[semantics "store-typing" (requirement := R4)]
theorem typed (hin : ∀ {t : Ty} (x : Input Γ t), TypesEach sig (src x) env path types t) :
    ∀ {s : Ty} (e : Step Γ s), e.Facts → TypesEach sig (e.term src) env path types s
  | _, .var x, _ => hin x
  | _, .bool b, _ => types_bool b
  | _, .nat n, _ => types_nat n
  | _, .unit, _ => types_unit
  | _, .not a, h => types_notT atoms (typed hin a h)
  | _, .and a b, h => types_andT atoms (typed hin a h.1) (typed hin b h.2)
  | _, .or a b, h => types_orT atoms (typed hin a h.1) (typed hin b h.2)
  | _, .ite c a b, h =>
    types_ifT atoms (typed hin c h.2.1) (typed hin a h.2.2.1) (typed hin b h.2.2.2) h.1
  | _, .add a b, h => types_add atoms (typed hin a h.1) (typed hin b h.2)
  | _, .sub a b, h => types_sub atoms (typed hin a h.1) (typed hin b h.2)
  | _, .lt a b, h => types_lt atoms (typed hin a h.1) (typed hin b h.2)
  | _, .eq a b, h => types_eq atoms (typed hin a h.1) (typed hin b h.2)
  | _, .isZero a, h => types_isZero atoms (typed hin a h)
  | _, .pair a b, h => types_pair atoms (typed hin a h.1) (typed hin b h.2)
  | _, .tuple2 a b, h =>
    types_tuple2 atoms (typed hin a h.2.1) (typed hin b h.2.2) h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2
  | _, .fst p, h => fun _ => types_app (.cons (typed hin p h _) .nil) (atomOf_native atoms rfl)
  | _, .snd p, h => fun _ => types_app (.cons (typed hin p h _) .nil) (atomOf_native atoms rfl)
  | _, .some a, h => types_some atoms (typed hin a h)
  | _, .get r f, h => fun _ => types_field (typed hin r h.2 false) (fieldType_ref h.1 f)
  | _, .set r f v, h => fun _ =>
    types_recordSet (typed hin r h.2.1 false) (typed hin v h.2.2 true) (setType_ref h.1 f)
  | _, .emptyLike xs, h => types_noneOf atoms (typed hin xs h)
  | _, .len xs, h => types_len atoms (typed hin xs h)
  | _, .snoc xs x, h => types_snoc atoms h.1 (typed hin xs h.2.1) (typed hin x h.2.2)
  | _, .append xs ys, h => types_append atoms (typed hin xs h.2.1) (typed hin ys h.2.2) h.1
  | _, .take xs n, h => types_take atoms (typed hin xs h.1) (typed hin n h.2)
  | _, .drop xs n, h => types_drop atoms (typed hin xs h.1) (typed hin n h.2)
  | _, .head xs, h => types_head atoms (typed hin xs h)

/-- The typing law by the typing check: it closes by `rfl` on a concrete step. -/
theorem typed_of_normal (hin : ∀ {t : Ty} (x : Input Γ t), TypesEach sig (src x) env path types t)
    {s : Ty} (e : Step Γ s) (h : e.normal = true) : TypesEach sig (e.term src) env path types s :=
  typed sig atoms hin e (facts_of_normal e h)

end Typing

/-! ## Framing -/

section Frame

variable (L : Leaves) (vs : Inputs L Γ)

/-- **The frame law on carriers** (claim `step-frame`): on an update spine of an input, a field
that no overwrite names reads as it does in the input. No premise on the record's names. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem frame {fs : List (String × Bool × Ty)} (x : Input Γ (.record fs)) {t : Ty}
    (g : FieldRef fs t) :
    ∀ (e : Step Γ (.record fs)), e.spine = Option.some x.index → g.name ∉ e.writes →
      g.get (e.eval L vs) = g.get (x.get vs)
  | .var y, hs, _ => by
    have same : y = x := Input.index_inj y x (Option.some.inj hs)
    rw [same]
    rfl
  | .ite c a b, hs, hw => by
    have spine : (if a.spine = b.spine then a.spine else none) = Option.some x.index := hs
    by_cases equal : a.spine = b.spine
    · rw [if_pos equal] at spine
      have outside : g.name ∉ c.writes ++ a.writes ++ b.writes := hw
      rw [List.mem_append, List.mem_append, not_or, not_or] at outside
      have ha := frame x g a spine outside.1.2
      have hb := frame x g b (equal ▸ spine) outside.2
      have chosen : ∀ test : Bool,
          g.get ((evalAlg L vs).ite (t := .record fs) test (a.eval L vs) (b.eval L vs)) =
            g.get (x.get vs) := by
        intro test
        cases test
        · exact hb
        · exact ha
      exact chosen (c.eval L vs)
    · rw [if_neg equal] at spine
      exact nomatch spine
  | .set r f v, hs, hw => by
    have outside : g.name ∉ r.writes ++ v.writes ++ [f.name] := hw
    rw [List.mem_append, List.mem_append, not_or, not_or, List.mem_singleton] at outside
    show g.get (f.set (r.eval L vs) (v.eval L vs)) = _
    rw [FieldRef.get_set_other f g (r.eval L vs) (v.eval L vs)
      (fun same => outside.2 (FieldRef.name_of_index f g same).symm)]
    exact frame x g r hs outside.1.1
  | .get _ _, hs, _ => nomatch hs
  | .fst _, hs, _ => nomatch hs
  | .snd _, hs, _ => nomatch hs

/-- **The frame law on the machine's record frame**: for a record with ascending names, the
machine's read of a field that no overwrite names is the same before and after the step. -/
theorem frame_read {fs : List (String × Bool × Ty)} (h : Field.Ascending Field.bytesKey fs)
    (x : Input Γ (.record fs)) {t : Ty} (g : FieldRef fs t) (e : Step Γ (.record fs))
    (hs : e.spine = Option.some x.index) (hw : g.name ∉ e.writes) :
    Machine.Record.read false ((imageAt L (.record fs)).toVal (e.eval L vs)) g.name =
      Machine.Record.read false ((imageAt L (.record fs)).toVal (x.get vs)) g.name := by
  rw [FieldRef.read_law h g, FieldRef.read_law h g, frame L vs x g e hs hw]

end Frame

/-! ## Evaluating a selection -/

/-- A selection's value is the chosen branch's, by the test's value. -/
theorem eval_ite (L : Leaves) (vs : Inputs L Γ) {t : Ty} (c : Step Γ .bool) (a b : Step Γ t) :
    (Step.ite c a b).eval L vs = cond (c.eval L vs) (a.eval L vs) (b.eval L vs) := by
  have chosen : ∀ test : Bool,
      (evalAlg L vs).ite test (a.eval L vs) (b.eval L vs) = cond test (a.eval L vs) (b.eval L vs) := by
    intro test
    cases test <;> rfl
  exact chosen (c.eval L vs)

/-! ## A caller's terms, input by input -/

section Inputs

variable {L : Leaves} {env : Env} {path : List Nat} {vals : List Val}

/-- No input: nothing to read. -/
theorem _root_.Effect4.Modules.Input.reads_nil :
    ∀ {t : Ty} (x : Input [] t),
      Reads (Input.source [] x) env path vals ((imageAt L t).toVal (x.get (L := L) ())) :=
  fun x => nomatch x

/-- The inputs' reading, one input more: the first term reads the first value. -/
theorem _root_.Effect4.Modules.Input.reads_cons {u : Ty} {Γ : List Ty} {src0 : TermSrc}
    {srcs : List TermSrc} {v0 : CarrierAt L u} {vs : Inputs L Γ}
    (h0 : Reads src0 env path vals ((imageAt L u).toVal v0))
    (hrest : ∀ {t : Ty} (x : Input Γ t),
      Reads (Input.source srcs x) env path vals ((imageAt L t).toVal (x.get vs))) :
    ∀ {t : Ty} (x : Input (u :: Γ) t),
      Reads (Input.source (src0 :: srcs) x) env path vals
        ((imageAt L t).toVal (x.get (L := L) ((v0, vs) : Inputs L (u :: Γ))))
  | _, .here _ _ => h0
  | _, .there _ x => hrest x

variable {Op : Type} {sig : Signature Op} {types : List Ty}

/-- No input: nothing to type. -/
theorem _root_.Effect4.Modules.Input.types_nil :
    ∀ {t : Ty} (x : Input [] t), TypesEach sig (Input.source [] x) env path types t :=
  fun x => nomatch x

/-- The inputs' typing, one input more. -/
theorem _root_.Effect4.Modules.Input.types_cons {u : Ty} {Γ : List Ty} {src0 : TermSrc}
    {srcs : List TermSrc} (h0 : TypesEach sig src0 env path types u)
    (hrest : ∀ {t : Ty} (x : Input Γ t), TypesEach sig (Input.source srcs x) env path types t) :
    ∀ {t : Ty} (x : Input (u :: Γ) t), TypesEach sig (Input.source (src0 :: srcs) x) env path types t
  | _, .here _ _ => h0
  | _, .there _ x => hrest x

end Inputs

end Step
end Effect4.Modules
