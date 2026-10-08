import Effect4.Modules.Step
import Effect4.Laws.Schema.FieldRef
import Effect4.Laws.Program.TyNormal
import Effect4.Laws.Modules.Reading
import Effect4.Laws.Modules.Checking
import Effect4.Laws.Modules.Construction
import Effect4.Laws.Modules.Cons
import Effect4.Laws.Modules.Tuple3
import Effect4.Laws.Schema.Identity
import Effect4.Laws.Auto.Semantics
import Effect4.Laws.Program.Typed.ListFold
import Aesop

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

What the laws do not establish: nothing of an optional
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

mutual
/-- A check implies a weaker check, node by node. -/
theorem check_mono {r₁ r₂ : List (String × Bool × Ty) → Bool} {a₁ a₂ : Ty → Bool}
    {f₁ f₂ : Ty → Bool} {s₁ s₂ : Ty → Ty → Bool}
    (hf : ∀ t, f₁ t = true → f₂ t = true)
    (hs : ∀ a b, s₁ a b = true → s₂ a b = true)
    (hr : ∀ fs, r₁ fs = true → r₂ fs = true) (ha : ∀ t, a₁ t = true → a₂ t = true) :
    ∀ {Γ : List Ty} {s : Ty} (e : Step Γ s), cata (checkAlg r₁ a₁ f₁ s₁) e = true → cata (checkAlg r₂ a₂ f₂ s₂) e = true
  | _, _, .var _, _ => rfl
  | _, _, .bool _, _ => rfl
  | _, _, .nat _, _ => rfl
  | _, _, .unit, _ => rfl
  | _, _, .not a, h => check_mono hf hs hr ha a h
  | _, _, .and a b, h => and_intro (check_mono hf hs hr ha a (and_true h).1) (check_mono hf hs hr ha b (and_true h).2)
  | _, _, .or a b, h => and_intro (check_mono hf hs hr ha a (and_true h).1) (check_mono hf hs hr ha b (and_true h).2)
  | _, _, .ite c a b, h => by
    obtain ⟨ht, rest⟩ := and_true h
    obtain ⟨hc, hab⟩ := and_true rest
    exact and_intro (ha _ ht) (and_intro (check_mono hf hs hr ha c hc)
      (and_intro (check_mono hf hs hr ha a (and_true hab).1) (check_mono hf hs hr ha b (and_true hab).2)))
  | _, _, .add a b, h => and_intro (check_mono hf hs hr ha a (and_true h).1) (check_mono hf hs hr ha b (and_true h).2)
  | _, _, .sub a b, h => and_intro (check_mono hf hs hr ha a (and_true h).1) (check_mono hf hs hr ha b (and_true h).2)
  | _, _, .lt a b, h => and_intro (check_mono hf hs hr ha a (and_true h).1) (check_mono hf hs hr ha b (and_true h).2)
  | _, _, .eq a b, h => and_intro (check_mono hf hs hr ha a (and_true h).1) (check_mono hf hs hr ha b (and_true h).2)
  | _, _, .isZero a, h => check_mono hf hs hr ha a h
  | _, _, .pair a b, h => and_intro (check_mono hf hs hr ha a (and_true h).1) (check_mono hf hs hr ha b (and_true h).2)
  | _, _, .tuple2 a b, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact and_intro (ha _ ht)
      (and_intro (check_mono hf hs hr ha a (and_true rest).1) (check_mono hf hs hr ha b (and_true rest).2))
  | _, _, .tuple3 x y z, h =>
    and_intro (and_intro (ha _ (and_true (and_true h).1).1)
      (and_intro (ha _ (and_true (and_true (and_true h).1).2).1)
        (ha _ (and_true (and_true (and_true h).1).2).2)))
      (and_intro (check_mono hf hs hr ha x (and_true (and_true h).2).1)
        (and_intro (check_mono hf hs hr ha y (and_true (and_true (and_true h).2).2).1)
          (check_mono hf hs hr ha z (and_true (and_true (and_true h).2).2).2)))
  | _, _, .fst p, h => check_mono hf hs hr ha p h
  | _, _, .snd p, h => check_mono hf hs hr ha p h
  | _, _, .some a, h => check_mono hf hs hr ha a h
  | _, _, .get r _, h => and_intro (hr _ (and_true h).1) (check_mono hf hs hr ha r (and_true h).2)
  | _, _, .set r _ v, h => by
    obtain ⟨hfields, rest⟩ := and_true h
    exact and_intro (hr _ hfields)
      (and_intro (check_mono hf hs hr ha r (and_true rest).1) (check_mono hf hs hr ha v (and_true rest).2))
  | _, _, .emptyLike xs, h => check_mono hf hs hr ha xs h
  | _, _, .len xs, h => check_mono hf hs hr ha xs h
  | _, _, .snoc xs x, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact and_intro (ha _ ht)
      (and_intro (check_mono hf hs hr ha xs (and_true rest).1) (check_mono hf hs hr ha x (and_true rest).2))
  | _, _, .append xs ys, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact and_intro (ha _ ht)
      (and_intro (check_mono hf hs hr ha xs (and_true rest).1) (check_mono hf hs hr ha ys (and_true rest).2))
  | _, _, .take xs n, h => and_intro (check_mono hf hs hr ha xs (and_true h).1) (check_mono hf hs hr ha n (and_true h).2)
  | _, _, .drop xs n, h => and_intro (check_mono hf hs hr ha xs (and_true h).1) (check_mono hf hs hr ha n (and_true h).2)
  | _, _, .head xs, h => check_mono hf hs hr ha xs h
  | _, _, .fold xs init body, h =>
    and_intro (and_intro (check_mono hf hs hr ha xs (and_true (and_true h).1).1)
      (check_mono hf hs hr ha init (and_true (and_true h).1).2)) (check_mono hf hs hr ha body (and_true h).2)

  | _, _, .record fields, h =>
    and_intro (hr _ (and_true h).1) (and_intro (hf _ (and_true (and_true h).2).1)
      (check_fields_mono hf hs hr ha fields (and_true (and_true h).2).2))
  | _, _, .nil, h => and_intro (ha _ (and_true h).1)
    (and_intro (hf _ (and_true (and_true h).2).1) (hs _ _ (and_true (and_true h).2).2))
  | _, _, .none, h => and_intro (ha _ (and_true h).1)
    (and_intro (hf _ (and_true (and_true h).2).1) (hs _ _ (and_true (and_true h).2).2))
  | _, _, .cons x xs, h => and_intro (ha _ (and_true h).1)
    (and_intro (check_mono hf hs hr ha x (and_true (and_true h).2).1)
      (check_mono hf hs hr ha xs (and_true (and_true h).2).2))
  | _, _, .sameDeferred a b, h =>
    and_intro (check_mono hf hs hr ha a (and_true h).1) (check_mono hf hs hr ha b (and_true h).2)

/-- The required-field half of check monotonicity, consumed by the record arm. -/
theorem check_fields_mono {r₁ r₂ : List (String × Bool × Ty) → Bool} {a₁ a₂ : Ty → Bool}
    {f₁ f₂ : Ty → Bool} {s₁ s₂ : Ty → Ty → Bool}
    (hf : ∀ t, f₁ t = true → f₂ t = true) (hs : ∀ a b, s₁ a b = true → s₂ a b = true)
    (hr : ∀ fs, r₁ fs = true → r₂ fs = true) (ha : ∀ t, a₁ t = true → a₂ t = true) :
    ∀ {Γ : List Ty} {fs : List (String × Bool × Ty)} (fields : StepFields Γ fs),
    (FieldResults.map (fun _ {_} x => x) fs (cataFields (checkAlg r₁ a₁ f₁ s₁) fields)).all id = true →
    (FieldResults.map (fun _ {_} x => x) fs (cataFields (checkAlg r₂ a₂ f₂ s₂) fields)).all id = true
  | _, _, .nil, _ => rfl
  | _, _, .cons _ value rest, h =>
    and_intro (check_mono hf hs hr ha value (and_true h).1)
      (check_fields_mono hf hs hr ha rest (and_true h).2)
end

/-- **The typing check implies the reading check**: a record in normal form has ascending
names. -/
theorem canonical_of_normal {s : Ty} (e : Step Γ s) (h : e.normal = true) : e.canonical = true :=
  check_mono (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ hn => decide_eq_true (ascending_of_normal (Ty.normalize_of_certNormal _ hn)))
    (fun _ _ => rfl) e h

mutual
/-- Successful input resolution gives a body tree without any carrier inhabitant.
A helper of step-language-sound's fold arm. -/
theorem tree_exists : ∀ {Γ : List Ty} {t : Ty} (e : Step Γ t)
    {src : {u : Ty} → Input Γ u → TermSrc} {env : Env} {path : List Nat},
    (∀ {u : Ty} (x : Input Γ u), ∃ tree, src x env path = .ok tree) →
    ∃ tree, e.term src env path = .ok tree
  | _, _, .var x, src, env, path, hin => hin x
  | _, _, .bool b, _, _, _, _ => ⟨_, rfl⟩
  | _, _, .nat n, _, _, _, _ => ⟨_, rfl⟩
  | _, _, .unit, _, _, _, _ => ⟨_, rfl⟩
  | _, _, .not a, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    refine ⟨.app "not" (termsOfList [tree_a]), ?_⟩
    change (notT (a.term src)) env path = _
    simp only [ notT, app, List.mapM_cons, List.mapM_nil, ha]
    rfl
  | _, _, .and a b, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    obtain ⟨tree_b, hb⟩ := tree_exists b hin
    refine ⟨.app "and" (termsOfList [tree_a, tree_b]), ?_⟩
    change (andT (a.term src) (b.term src)) env path = _
    simp only [ andT, app, List.mapM_cons, List.mapM_nil, ha, hb]
    rfl
  | _, _, .or a b, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    obtain ⟨tree_b, hb⟩ := tree_exists b hin
    refine ⟨.app "or" (termsOfList [tree_a, tree_b]), ?_⟩
    change (orT (a.term src) (b.term src)) env path = _
    simp only [ orT, app, List.mapM_cons, List.mapM_nil, ha, hb]
    rfl
  | _, _, .ite c a b, src, env, path, hin => by
    obtain ⟨tree_c, hc⟩ := tree_exists c hin
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    obtain ⟨tree_b, hb⟩ := tree_exists b hin
    refine ⟨.app "ite" (termsOfList [tree_c, tree_a, tree_b]), ?_⟩
    change (ifT (c.term src) (a.term src) (b.term src)) env path = _
    simp only [ ifT, app, List.mapM_cons, List.mapM_nil, hc, ha, hb]
    rfl
  | _, _, .add a b, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    obtain ⟨tree_b, hb⟩ := tree_exists b hin
    refine ⟨.app "add" (termsOfList [tree_a, tree_b]), ?_⟩
    change (app "add" [(a.term src), (b.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, ha, hb]
    rfl
  | _, _, .sub a b, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    obtain ⟨tree_b, hb⟩ := tree_exists b hin
    refine ⟨.app "sub" (termsOfList [tree_a, tree_b]), ?_⟩
    change (app "sub" [(a.term src), (b.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, ha, hb]
    rfl
  | _, _, .lt a b, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    obtain ⟨tree_b, hb⟩ := tree_exists b hin
    refine ⟨.app "lt" (termsOfList [tree_a, tree_b]), ?_⟩
    change (app "lt" [(a.term src), (b.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, ha, hb]
    rfl
  | _, _, .eq a b, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    obtain ⟨tree_b, hb⟩ := tree_exists b hin
    refine ⟨.app "eq" (termsOfList [tree_a, tree_b]), ?_⟩
    change (app "eq" [(a.term src), (b.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, ha, hb]
    rfl
  | _, _, .isZero a, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    refine ⟨.app "isZero" (termsOfList [tree_a]), ?_⟩
    change (app "isZero" [(a.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, ha]
    rfl
  | _, _, .pair a b, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    obtain ⟨tree_b, hb⟩ := tree_exists b hin
    refine ⟨.app "pair" (termsOfList [tree_a, tree_b]), ?_⟩
    change (app "pair" [(a.term src), (b.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, ha, hb]
    rfl
  | _, _, .tuple2 a b, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    obtain ⟨tree_b, hb⟩ := tree_exists b hin
    refine ⟨.app "tuple" (termsOfList [tree_a, tree_b]), ?_⟩
    change (Authoring.tuple [(a.term src), (b.term src)]) env path = _
    simp only [ Authoring.tuple, app, List.mapM_cons, List.mapM_nil, ha, hb]
    rfl
  | _, _, .fst p, src, env, path, hin => by
    obtain ⟨tree_p, hp⟩ := tree_exists p hin
    refine ⟨.app "fst" (termsOfList [tree_p]), ?_⟩
    change (app "fst" [(p.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, hp]
    rfl
  | _, _, .snd p, src, env, path, hin => by
    obtain ⟨tree_p, hp⟩ := tree_exists p hin
    refine ⟨.app "snd" (termsOfList [tree_p]), ?_⟩
    change (app "snd" [(p.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, hp]
    rfl
  | _, _, .some a, src, env, path, hin => by
    obtain ⟨tree_a, ha⟩ := tree_exists a hin
    refine ⟨.app "some" (termsOfList [tree_a]), ?_⟩
    change (app "some" [(a.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, ha]
    rfl
  | _, _, .get r f, src, env, path, hin => by
    obtain ⟨tree_r, hr⟩ := tree_exists r hin
    refine ⟨.field .required tree_r f.name, ?_⟩
    change (field (r.term src) f.name) env path = _
    simp only [ field, hr]
    rfl
  | _, _, .set r f v, src, env, path, hin => by
    obtain ⟨tree_r, hr⟩ := tree_exists r hin
    obtain ⟨tree_v, hv⟩ := tree_exists v hin
    refine ⟨.recordSet tree_r f.name tree_v, ?_⟩
    change (recordSet (r.term src) f.name (v.term src)) env path = _
    simp only [ recordSet, hr, hv]
    rfl
  | _, _, .emptyLike xs, src, env, path, hin => by
    obtain ⟨tree_xs, hxs⟩ := tree_exists xs hin
    refine ⟨.app "take" (termsOfList [tree_xs, .lit (.nat 0)]), ?_⟩
    change (noneOf (xs.term src)) env path = _
    simp only [ noneOf, app, Authoring.nat, lit, List.mapM_cons, List.mapM_nil, hxs]
    rfl
  | _, _, .len xs, src, env, path, hin => by
    obtain ⟨tree_xs, hxs⟩ := tree_exists xs hin
    refine ⟨.app "length" (termsOfList [tree_xs]), ?_⟩
    change (Modules.len (xs.term src)) env path = _
    simp only [ Modules.len, app, List.mapM_cons, List.mapM_nil, hxs]
    rfl
  | _, _, .snoc xs x, src, env, path, hin => by
    obtain ⟨tree_xs, hxs⟩ := tree_exists xs hin
    obtain ⟨tree_x, hx⟩ := tree_exists x hin
    refine ⟨.app "append" (termsOfList [tree_xs, .app "cons" (termsOfList [tree_x, .app "nil" .nil])]), ?_⟩
    change (Modules.snoc (xs.term src) (x.term src)) env path = _
    simp only [ Modules.snoc, app, nilT, List.mapM_cons, List.mapM_nil, hxs, hx]
    rfl
  | _, _, .append xs ys, src, env, path, hin => by
    obtain ⟨tree_xs, hxs⟩ := tree_exists xs hin
    obtain ⟨tree_ys, hys⟩ := tree_exists ys hin
    refine ⟨.app "append" (termsOfList [tree_xs, tree_ys]), ?_⟩
    change (app "append" [(xs.term src), (ys.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, hxs, hys]
    rfl
  | _, _, .take xs n, src, env, path, hin => by
    obtain ⟨tree_xs, hxs⟩ := tree_exists xs hin
    obtain ⟨tree_n, hn⟩ := tree_exists n hin
    refine ⟨.app "take" (termsOfList [tree_xs, tree_n]), ?_⟩
    change (app "take" [(xs.term src), (n.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, hxs, hn]
    rfl
  | _, _, .drop xs n, src, env, path, hin => by
    obtain ⟨tree_xs, hxs⟩ := tree_exists xs hin
    obtain ⟨tree_n, hn⟩ := tree_exists n hin
    refine ⟨.app "drop" (termsOfList [tree_xs, tree_n]), ?_⟩
    change (app "drop" [(xs.term src), (n.term src)]) env path = _
    simp only [ app, List.mapM_cons, List.mapM_nil, hxs, hn]
    rfl
  | _, _, .head xs, src, env, path, hin => by
    obtain ⟨tree_xs, hxs⟩ := tree_exists xs hin
    refine ⟨.app "get" (termsOfList [tree_xs, .lit (.nat 0)]), ?_⟩
    change (app "get" [(xs.term src), Authoring.nat 0]) env path = _
    simp only [ app, Authoring.nat, lit, List.mapM_cons, List.mapM_nil, hxs]
    rfl
  | _, _, .fold (acc := acc) (item := item) xs init body, src, env, path, hin => by
    obtain ⟨lt, hl⟩ := tree_exists xs hin
    obtain ⟨it, hi⟩ := tree_exists init hin
    have inputs : ∀ {u : Ty} (x : Input (acc :: item :: _) u),
        ∃ tree, foldSources (acc := acc) (item := item) src env path x (env.push [env.mint "acc", env.mint "item"]) path =
          .ok tree := by
      intro u x
      cases x with
      | here => exact ⟨_, rfl⟩
      | there _ x =>
        cases x with
        | here => exact ⟨_, rfl⟩
        | there _ x =>
          obtain ⟨t, ht⟩ := hin x
          exact ⟨_, by simp only [foldSources, capturedSource, ht]; rfl⟩
    obtain ⟨tree_b, hb⟩ := tree_exists body inputs
    refine ⟨.fold Option.none lt it tree_b, ?_⟩
    change (xs.term src env path >>= fun l => init.term src env path >>= fun i =>
      body.term (foldSources src env path) (env.push [env.mint "acc", env.mint "item"]) path >>=
        fun b => Except.ok (Term.fold Option.none l i b)) = _
    rw [hl, hi, hb]
    rfl

  | _, _, .tuple3 x y z, src, env, path, hin => by
    obtain ⟨tx, hx⟩ := tree_exists x hin
    obtain ⟨ty, hy⟩ := tree_exists y hin
    obtain ⟨tz, hz⟩ := tree_exists z hin
    refine ⟨.app "tuple" (termsOfList [tx, ty, tz]), ?_⟩
    change (tuple [x.term src, y.term src, z.term src]) env path = _
    simp only [Authoring.tuple, app, List.mapM_cons, List.mapM_nil, hx, hy, hz]
    rfl
  | _, _, .record (fs := fs) fields, src, env, path, hin => by
    obtain ⟨trees, htrees⟩ := trees_exist fields hin
    refine ⟨.record fs ((FieldResults.map (fun name {_} value => (name, value src)) fs
      (cataFields termAlg fields)).map Prod.fst) (termsOfList trees), ?_⟩
    change (Authoring.record fs _) env path = _
    unfold Authoring.record
    rw [htrees]
    rfl
  | _, _, .nil, _, _, _, _ => ⟨_, rfl⟩
  | _, _, .none, _, _, _, _ => ⟨_, rfl⟩
  | _, _, .cons x xs, src, env, path, hin => by
    obtain ⟨tx, hx⟩ := tree_exists x hin
    obtain ⟨txs, hxs⟩ := tree_exists xs hin
    refine ⟨.app "cons" (termsOfList [tx, txs]), ?_⟩
    change (app "cons" [x.term src, xs.term src]) env path = _
    simp only [app, List.mapM_cons, List.mapM_nil, hx, hxs]
    rfl
  | _, _, .sameDeferred a b, src, env, path, hin => by
    obtain ⟨ta, ha⟩ := tree_exists a hin
    obtain ⟨tb, hb⟩ := tree_exists b hin
    refine ⟨.app "sameHandle" (termsOfList [ta, tb]), ?_⟩
    change (Modules.same (a.term src) (b.term src)) env path = _
    simp only [Modules.same, app, List.mapM_cons, List.mapM_nil, ha, hb]
    rfl

/-- Record child sources resolve without requiring inhabitants of their carriers. -/
theorem trees_exist : ∀ {Γ : List Ty} {fs : List (String × Bool × Ty)} (fields : StepFields Γ fs)
    {src : {u : Ty} → Input Γ u → TermSrc} {env : Env} {path : List Nat},
    (∀ {u : Ty} (x : Input Γ u), ∃ tree, src x env path = .ok tree) →
    ∃ trees, (FieldResults.map (fun name {_} value => (name, value src)) fs
      (cataFields termAlg fields)).mapM (fun entry => entry.2 env path) = .ok trees
  | _, _, .nil, _, _, _, _ => ⟨[], rfl⟩
  | _, _, .cons name value rest, src, env, path, hin => by
    obtain ⟨tree, ht⟩ := tree_exists value hin
    obtain ⟨trees, hts⟩ := trees_exist rest hin
    refine ⟨tree :: trees, ?_⟩
    change ((name, value.term src) :: _).mapM (fun entry => entry.2 env path) = _
    simp only [List.mapM_cons, cataFields, ht, hts]
    rfl
end

/-- Field sources retain the schema names, independent of every child result. -/
theorem fields_names : ∀ {Γ : List Ty} {fs : List (String × Bool × Ty)}
    (fields : StepFields Γ fs) (src : {t : Ty} → Input Γ t → TermSrc),
    (FieldResults.map (fun name {_} value => (name, value src)) fs
      (cataFields termAlg fields)).map Prod.fst = fs.map Prod.fst
  | _, _, .nil, _ => rfl
  | _, _, .cons name _ rest, src => congrArg (name :: ·) (fields_names rest src)

/-- Scope alignment passes to a child whose binder occurrence implies the parent's.
A helper of step-language-sound and step-language-typed. -/
theorem scope_mono {Γ Δ : List Ty} {s t : Ty} {parent : Step Γ s} {child : Step Δ t}
    {env : Env} {length : Nat} (h : parent.ScopeFacts env length)
    (occurs : child.binds = true → parent.binds = true) : child.ScopeFacts env length := by
  unfold ScopeFacts at h ⊢
  cases hb : child.binds
  · trivial
  · rw [occurs hb] at h
    exact h

/-- An identity requirement passes to a child that compares deferred handles.
The comparison arm of the reading law consumes this capability. -/
theorem identity_mono {Γ Δ : List Ty} {s t : Ty} {parent : Step Γ s} {child : Step Δ t}
    {L : Leaves} (h : parent.IdentityFacts L)
    (occurs : child.compares = true → parent.compares = true) : child.IdentityFacts L := by
  unfold IdentityFacts at h ⊢
  cases hb : child.compares
  · trivial
  · rw [occurs hb] at h
    exact h

/-- Alignment suffices for the per-step scope contract. A helper of both step laws. -/
theorem scope_of_alignment {Γ : List Ty} {t : Ty} (e : Step Γ t) {env : Env} {length : Nat}
    (h : length = env.names.length) : e.ScopeFacts env length := by
  unfold ScopeFacts
  split
  · exact h
  · trivial

/-- Freezing a tree and lifting its slots preserves its reading.
A helper of step-language-sound's fold arm. -/
theorem captured_reads {src : TermSrc} {env : Env} {path : List Nat} {vals : List Val} {v : Val}
    (depth : vals.length = env.names.length) (h : Reads src env path vals v) (acc item : Val) :
    Reads (capturedSource src env path) (env.push [env.mint "acc", env.mint "item"])
      path (vals ++ [acc, item]) v := by
  obtain ⟨t, ht, hv⟩ := h
  refine ⟨Term.weaken (env.names.length + 1) (Term.weaken env.names.length t), ?_, ?_⟩
  · simp only [capturedSource, ht]
    rfl
  · rw [← depth]
    have first := evalTerm_weaken vals [] acc t
    have second := evalTerm_weaken (vals ++ [acc]) [] item (Term.weaken vals.length t)
    simp only [List.append_nil] at first second
    simp only [List.length_append, List.length_cons, List.length_nil] at second
    change evalTerm (vals ++ [acc, item])
      (Term.weaken (vals.length + 1) (Term.weaken vals.length t)) = _
    rw [List.append_assoc] at second
    simp only [List.cons_append, List.nil_append, Nat.zero_add] at second
    rw [second, first]
    exact hv

/-- The fold inputs read the binder values and the frozen outer values.
A helper of step-language-sound's fold arm. -/
theorem fold_inputs_reads {L : Leaves} {Γ : List Ty} {acc item : Ty} {vs : Inputs L Γ}
    {src : {t : Ty} → Input Γ t → TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (hin : ∀ {t : Ty} (x : Input Γ t), Reads (src x) env path vals ((imageAt L t).toVal (x.get vs)))
    (a : CarrierAt L acc) (i : CarrierAt L item) :
    ∀ {t : Ty} (x : Input (acc :: item :: Γ) t),
      Reads (foldSources src env path x) (env.push [env.mint "acc", env.mint "item"]) path
        (vals ++ [(imageAt L acc).toVal a, (imageAt L item).toVal i])
        ((imageAt L t).toVal (x.get (a, (i, vs))))
  | _, .here _ _ => ⟨_, rfl, (reads_minted_acc depth path _ _).eval (minted_acc_tree env path)⟩
  | _, .there _ (.here _ _) =>
    ⟨_, rfl, (reads_minted_item depth path _ _).eval (minted_item_tree env path)⟩
  | _, .there _ (.there _ x) => captured_reads depth (hin x) _ _

/-- The model fold has the encoded term fold's result, including an empty carrier.
A helper of step-language-sound's fold arm. -/
theorem fold_eval_image {α β : Type} (I : Image α) (A : Image β) (f : β → α → β)
    (vals : List Val) (body : Term)
    (hbody : ∀ a i, evalTerm (vals ++ [A.toVal a, I.toVal i]) body = Option.some (A.toVal (f a i))) :
    ∀ (xs : List α) (start : β),
      (xs.map I.toVal).foldlM (fun a i => evalTerm (vals ++ [a, i]) body) (A.toVal start) =
        Option.some (A.toVal (xs.foldl f start))
  | [], _ => rfl
  | x :: xs, start => by
    show (evalTerm (vals ++ [A.toVal start, I.toVal x]) body).bind
      (fun next => (xs.map I.toVal).foldlM (fun a i => evalTerm (vals ++ [a, i]) body) next) = _
    rw [hbody, Option.bind_some]
    exact fold_eval_image I A f vals body hbody xs (f start x)

/-- Frozen inputs retain their types across the two inserted slots.
A helper of step-language-typed's fold arm. -/
theorem captured_types {Op : Type} {sig : Signature Op} {src : TermSrc} {env : Env}
    {path : List Nat} {types : List Ty} {T : Ty} (depth : types.length = env.names.length)
    (h : TypesEach sig src env path types T) (acc item : Ty) :
    TypesEach sig (capturedSource src env path) (env.push [env.mint "acc", env.mint "item"])
      path (types ++ [acc, item]) T := by
  intro const
  obtain ⟨t, ht, hv⟩ := h const
  refine ⟨Term.weaken (env.names.length + 1) (Term.weaken env.names.length t), ?_, ?_⟩
  · simp only [capturedSource, ht]
    rfl
  · rw [← depth]
    have first := argTy_weaken sig types [] acc const t
    have second := argTy_weaken sig (types ++ [acc]) [] item const (Term.weaken types.length t)
    simp only [List.append_nil] at first second
    simp only [List.length_append, List.length_cons, List.length_nil] at second
    rw [List.append_assoc] at second
    simp only [List.cons_append, List.nil_append, Nat.zero_add] at second
    rw [second, first]
    exact hv

/-- The fold inputs type at their declared binder types and frozen outer types.
A helper of step-language-typed's fold arm. -/
theorem fold_inputs_types {Op : Type} {sig : Signature Op} {Γ : List Ty} {acc item : Ty}
    {src : {t : Ty} → Input Γ t → TermSrc} {env : Env} {path : List Nat} {types : List Ty}
    (depth : types.length = env.names.length)
    (hin : ∀ {t : Ty} (x : Input Γ t), TypesEach sig (src x) env path types t) :
    ∀ {t : Ty} (x : Input (acc :: item :: Γ) t),
      TypesEach sig (foldSources src env path x) (env.push [env.mint "acc", env.mint "item"])
        path (types ++ [acc, item]) t
  | _, .here _ _ => fun const =>
    ⟨_, rfl, (types_minted_acc (sig := sig) depth path acc item const).tree (minted_acc_tree env path)⟩
  | _, .there _ (.here _ _) => fun const =>
    ⟨_, rfl, (types_minted_item (sig := sig) depth path acc item const).tree (minted_item_tree env path)⟩
  | _, .there _ (.there _ x) => captured_types depth (hin x) acc item

/-! ## Reading -/

section Reading

variable (L : Leaves)

mutual
/-- **A step's term reads its value** (claim `step-language-sound`): at every scope, when the
caller's terms read the encodings of the inputs' values, a step that passes the reading check
has a term that reads the encoding of its value. -/
theorem sound_core : ∀ {Γ : List Ty} {vs : Inputs L Γ}
    {src : {t : Ty} → Input Γ t → TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (_hin : ∀ {t : Ty} (x : Input Γ t), Reads (src x) env path vals ((imageAt L t).toVal (x.get vs)))
    {s : Ty} (e : Step Γ s), e.canonical = true → (scope : e.ScopeFacts env vals.length) → (identity : e.IdentityFacts L) →
      Reads (e.term src) env path vals ((imageAt L s).toVal (e.eval L vs))
  | _, vs, src, env, path, vals, hin, _, .var x, _, _, _ => hin x
  | _, _, _, env, path, vals, _, _, .bool b, _, _, _ => reads_bool b env path vals
  | _, _, _, env, path, vals, _, _, .nat n, _, _, _ => reads_nat n env path vals
  | _, _, _, env, path, vals, _, _, .unit, _, _, _ => reads_unit
  | _, vs, src, env, path, vals, hin, _, .not a, h, hs, hi => reads_notT (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h)
  | _, vs, src, env, path, vals, hin, _, .and a b, h, hs, hi => reads_andT (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b (and_true h).2)
  | _, vs, src, env, path, vals, hin, _, .or a b, h, hs, hi => reads_orT (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b (and_true h).2)
  | _, vs, src, env, path, vals, hin, _, .ite c a b, h, hs, hi => by
    obtain ⟨hc, hab⟩ := and_true h
    exact (reads_ifT (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin c hc) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a (and_true hab).1)
      (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b (and_true hab).2)).to (toVal_ite _ _ _ _)
  | _, vs, src, env, path, vals, hin, _, .add a b, h, hs, hi => reads_add (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b (and_true h).2)
  | _, vs, src, env, path, vals, hin, _, .sub a b, h, hs, hi => reads_sub (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b (and_true h).2)
  | _, vs, src, env, path, vals, hin, _, .lt a b, h, hs, hi => reads_lt (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b (and_true h).2)
  | _, vs, src, env, path, vals, hin, _, .eq a b, h, hs, hi => reads_eq (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b (and_true h).2)
  | _, vs, src, env, path, vals, hin, _, .isZero a, h, hs, hi => reads_isZero (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h)
  | _, vs, src, env, path, vals, hin, _, .pair a b, h, hs, hi => reads_pair (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b (and_true h).2)
  | _, vs, src, env, path, vals, hin, _, .tuple2 a b, h, hs, hi => reads_tuple2 (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b (and_true h).2)
  | _, vs, src, env, path, vals, hin, _, .fst p, h, hs, hi => reads_app (.cons (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin p h) .nil) rfl
  | _, vs, src, env, path, vals, hin, _, .snd p, h, hs, hi => reads_app (.cons (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin p h) .nil) rfl
  | _, vs, src, env, path, vals, hin, _, .some a, h, hs, hi => reads_some (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h)
  | _, vs, src, env, path, vals, hin, _, .get r f, h, hs, hi =>
    reads_field (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin r (and_true h).2)
      (FieldRef.read_law (of_decide_eq_true (and_true h).1) f (r.eval L vs))
  | _, vs, src, env, path, vals, hin, _, .set r f v, h, hs, hi => by
    obtain ⟨hf, rest⟩ := and_true h
    exact reads_recordSet (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin r (and_true rest).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin v (and_true rest).2)
      (FieldRef.write_law (of_decide_eq_true hf) f (r.eval L vs) (v.eval L vs))
  | _, vs, src, env, path, vals, hin, _, .emptyLike xs, h, hs, hi => reads_noneOf (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h)
  | _, vs, src, env, path, vals, hin, _, .len xs, h, hs, hi => (reads_len (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h)).to (nat_length_map _ _)
  | _, vs, src, env, path, vals, hin, _, .snoc xs x, h, hs, hi =>
    (reads_snoc (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin x (and_true h).2)).to
      (list_snoc_map _ _ _)
  | _, vs, src, env, path, vals, hin, _, .append xs ys, h, hs, hi =>
    (reads_append (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin ys (and_true h).2)).to
      (list_append_map _ _ _)
  | _, vs, src, env, path, vals, hin, _, .take xs n, h, hs, hi =>
    (reads_take (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin n (and_true h).2)).to
      (list_take_map _ _ _)
  | _, vs, src, env, path, vals, hin, _, .drop xs n, h, hs, hi =>
    (reads_drop (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs (and_true h).1) (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin n (and_true h).2)).to
      (list_drop_map _ _ _)
  | _, vs, src, env, path, vals, hin, _, .head xs, h, hs, hi => (reads_head (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h)).to (toVal_head _ _)

  | Γ, vs, src, env, path, vals, hin, _, .fold (acc := acc) (item := item) xs init body, h, hs, hi => by
    have depth : vals.length = env.names.length := hs
    have scopeXs := scope_of_alignment xs depth
    have scopeInit := scope_of_alignment init depth
    have readsXs := sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) hin xs (and_true (and_true h).1).1 scopeXs
    have readsInit := sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) hin init (and_true (and_true h).1).2 scopeInit
    have resolved : ∀ {t : Ty} (x : Input Γ t), ∃ tree, src x env path = .ok tree := by
      intro t x
      obtain ⟨tree, ht, _⟩ := hin x
      exact ⟨tree, ht⟩
    have bodyInputs : ∀ {t : Ty} (x : Input (acc :: item :: Γ) t),
        ∃ tree, foldSources src env path x (env.push [env.mint "acc", env.mint "item"]) path =
          .ok tree := by
      intro t x
      cases x with
      | here => exact ⟨_, rfl⟩
      | there _ x =>
        cases x with
        | here => exact ⟨_, rfl⟩
        | there _ x =>
          obtain ⟨tree, ht⟩ := resolved x
          exact ⟨_, by simp only [foldSources, capturedSource, ht]; rfl⟩
    obtain ⟨bt, hbt⟩ := tree_exists body bodyInputs
    have evaluates : ∀ a i,
        evalTerm (vals ++ [(imageAt L acc).toVal a, (imageAt L item).toVal i]) bt =
          Option.some ((imageAt L acc).toVal (body.eval (Γ := acc :: item :: Γ) L ((a, (i, vs)) : Inputs L (acc :: item :: Γ)))) := by
      intro a i
      have extended : (vals ++ [(imageAt L acc).toVal a, (imageAt L item).toVal i]).length =
          (env.push [env.mint "acc", env.mint "item"]).names.length := by
        change (vals ++ [_, _]).length = (env.names ++ [_, _]).length
        simp only [List.length_append, List.length_cons, List.length_nil, depth]
      exact (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (fold_inputs_reads depth hin a i) body (and_true h).2
        (scope_of_alignment body extended)).eval hbt
    obtain ⟨lt, hlt, hle⟩ := readsXs
    obtain ⟨it, hit, hie⟩ := readsInit
    refine ⟨.fold Option.none lt it bt, ?_, ?_⟩
    · change (xs.term src env path >>= fun l => init.term src env path >>= fun i =>
        body.term (foldSources src env path) (env.push [env.mint "acc", env.mint "item"]) path >>=
          fun b => Except.ok (Term.fold Option.none l i b)) = _
      rw [hlt, hit, hbt]
      rfl
    · rw [evalTerm_fold, hle, Option.bind_some]
      change (Option.some ((xs.eval L vs).map (imageAt L item).toVal)).bind
        (fun items => (evalTerm vals it).bind fun start =>
          items.foldlM (fun a i => evalTerm (vals ++ [a, i]) bt) start) = _
      rw [Option.bind_some, hie, Option.bind_some]
      exact fold_eval_image (imageAt L item) (imageAt L acc)
        (fun a i => body.eval (Γ := acc :: item :: Γ) L ((a, (i, vs)) : Inputs L (acc :: item :: Γ))) vals bt evaluates (xs.eval L vs) (init.eval L vs)

  | _, vs, src, env, path, vals, hin, _, .tuple3 x y z, h, hs, hi =>
    reads_tuple3_image L _ _ _ _ _ _
      (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin x (and_true h).1)
      (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin y (and_true (and_true h).2).1)
      (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin z (and_true (and_true h).2).2)
  | _, vs, src, env, path, vals, hin, _, .record (fs := fs) fields, h, hs, hi =>
    reads_record_image L fs _ (of_decide_eq_true (and_true h).1)
      (fields_names fields src) (sound_fields hin fields (and_true (and_true h).2).2 hs hi)
  | _, _, _, env, path, vals, _, _, .nil (t := t), _, _, _ => reads_nil_ascribe t env path vals
  | _, _, _, env, path, vals, _, _, .none (t := t), _, _, _ => reads_none_ascribe t env path vals
  | _, vs, src, env, path, vals, hin, _, .cons x xs, h, hs, hi =>
    reads_app (.cons (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin x (and_true h).1)
      (.cons (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs (and_true h).2) .nil)) rfl
  | _, vs, src, env, path, vals, hin, _, .sameDeferred a b, h, hs, hi => by
    have capabilityExists := hi
    obtain ⟨capability⟩ := capabilityExists
    exact capability.reads_deferredEqual
      (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a (and_true h).1)
      (sound_core (identity := identity_mono hi (by intro hb; simp only [compares, cata, featureAlg] at hb ⊢; aesop)) (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b (and_true h).2)

/-- The required fields read their encoded carrier entries, in schema order. -/
theorem sound_fields : ∀ {Γ : List Ty} {vs : Inputs L Γ}
    {src : {t : Ty} → Input Γ t → TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (_hin : ∀ {t : Ty} (x : Input Γ t), Reads (src x) env path vals ((imageAt L t).toVal (x.get vs)))
    {fs : List (String × Bool × Ty)} (fields : StepFields Γ fs),
    (FieldResults.map (fun _ {_} value => value) fs
      (cataFields (checkAlg (fun fs => decide (Field.Ascending Field.bytesKey fs)) (fun _ => true)) fields)).all id = true →
    (Step.record fields).ScopeFacts env vals.length → (Step.record fields).IdentityFacts L →
    ReadsAll ((FieldResults.map (fun name {_} value => (name, value src)) fs
      (cataFields termAlg fields)).map Prod.snd) env path vals
      ((entriesAt L fs (FieldResults.values L vs fs (cataFields (evalAlg L) fields))).map Prod.snd)
  | _, _, _, _, _, _, _, _, .nil, _, _, _ => .nil
  | _, vs, src, env, path, vals, hin, _, .cons _ value rest, h, hs, hi =>
    .cons (sound_core
      (identity := identity_mono hi (by intro hb; simp only [compares, cata, cataFields, featureAlg, FieldResults.map, List.any_cons] at hb ⊢; aesop))
      (scope := scope_mono hs (by intro hb; simp only [binds, cata, cataFields, bindsAlg, featureAlg, FieldResults.map, List.any_cons] at hb ⊢; aesop))
      hin value (and_true h).1)
      (sound_fields hin rest (and_true h).2
        (scope_mono hs (by intro hb; simp only [binds, cata, cataFields, bindsAlg, featureAlg, FieldResults.map, List.any_cons] at hb ⊢; aesop))
        (identity_mono hi (by intro hb; simp only [compares, cata, cataFields, featureAlg, FieldResults.map, List.any_cons] at hb ⊢; aesop)))
end

/-- The reading law, with scope alignment only when a fold occurs. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem sound (vs : Inputs L Γ) {src : {t : Ty} → Input Γ t → TermSrc} {env : Env}
    {path : List Nat} {vals : List Val}
    (hin : ∀ {t : Ty} (x : Input Γ t), Reads (src x) env path vals ((imageAt L t).toVal (x.get vs)))
    {s : Ty} (e : Step Γ s) (h : e.canonical = true)
    (scope : e.ScopeFacts env vals.length := by trivial)
    (identity : e.IdentityFacts L := by trivial) :
    Reads (e.term src) env path vals ((imageAt L s).toVal (e.eval L vs)) :=
  sound_core L hin e h scope identity

end Reading

/-! ## Typing -/

section Typing

mutual
/-- **The typing check gives the typing facts**: each certified type is its own normal form
(`Ty.normalize_of_certNormal`), and a certified product's items are normal factors. -/
theorem facts_of_normal : ∀ {Γ : List Ty} {s : Ty} (e : Step Γ s), e.normal = true → e.Facts
  | _, _, .var _, _ => trivial
  | _, _, .bool _, _ => trivial
  | _, _, .nat _, _ => trivial
  | _, _, .unit, _ => trivial
  | _, _, .not a, h => facts_of_normal a h
  | _, _, .and a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, _, .or a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, _, .ite c a b, h => by
    obtain ⟨ht, rest⟩ := and_true h
    obtain ⟨hc, hab⟩ := and_true rest
    exact ⟨Ty.normalize_of_certNormal _ ht, facts_of_normal c hc,
      facts_of_normal a (and_true hab).1, facts_of_normal b (and_true hab).2⟩
  | _, _, .add a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, _, .sub a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, _, .lt a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, _, .eq a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, _, .isZero a, h => facts_of_normal a h
  | _, _, .pair a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩
  | _, _, .tuple2 a b, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact ⟨certNormal_prod_facts ht, facts_of_normal a (and_true rest).1,
      facts_of_normal b (and_true rest).2⟩
  | _, _, .fst p, h => facts_of_normal p h
  | _, _, .snd p, h => facts_of_normal p h
  | _, _, .some a, h => facts_of_normal a h
  | _, _, .get r _, h => ⟨Ty.normalize_of_certNormal _ (and_true h).1, facts_of_normal r (and_true h).2⟩
  | _, _, .set r _ v, h => by
    obtain ⟨hf, rest⟩ := and_true h
    exact ⟨Ty.normalize_of_certNormal _ hf, facts_of_normal r (and_true rest).1,
      facts_of_normal v (and_true rest).2⟩
  | _, _, .emptyLike xs, h => facts_of_normal xs h
  | _, _, .len xs, h => facts_of_normal xs h
  | _, _, .snoc xs x, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact ⟨Ty.normalize_of_certNormal _ ht, facts_of_normal xs (and_true rest).1,
      facts_of_normal x (and_true rest).2⟩
  | _, _, .append xs ys, h => by
    obtain ⟨ht, rest⟩ := and_true h
    exact ⟨Ty.normalize_of_certNormal _ ht, facts_of_normal xs (and_true rest).1,
      facts_of_normal ys (and_true rest).2⟩
  | _, _, .take xs n, h => ⟨facts_of_normal xs (and_true h).1, facts_of_normal n (and_true h).2⟩
  | _, _, .drop xs n, h => ⟨facts_of_normal xs (and_true h).1, facts_of_normal n (and_true h).2⟩
  | _, _, .head xs, h => facts_of_normal xs h
  | _, _, .fold xs init body, h =>
    ⟨facts_of_normal xs (and_true (and_true h).1).1,
      facts_of_normal init (and_true (and_true h).1).2, facts_of_normal body (and_true h).2⟩

  | _, _, .tuple3 x y z, h =>
    ⟨⟨Ty.normalize_of_certNormal _ (and_true (and_true h).1).1,
      Ty.normalize_of_certNormal _ (and_true (and_true (and_true h).1).2).1,
      Ty.normalize_of_certNormal _ (and_true (and_true (and_true h).1).2).2⟩,
      facts_of_normal x (and_true (and_true h).2).1,
      facts_of_normal y (and_true (and_true (and_true h).2).2).1,
      facts_of_normal z (and_true (and_true (and_true h).2).2).2⟩
  | _, _, .record fields, h =>
    ⟨Ty.normalize_of_certNormal _ (and_true h).1,
      Option.isNone_iff_eq_none.mp (and_true (and_true h).2).1,
      field_facts_of_normal fields (and_true (and_true h).2).2⟩
  | _, _, .nil, h => ⟨Ty.normalize_of_certNormal _ (and_true h).1,
    Option.isNone_iff_eq_none.mp (and_true (and_true h).2).1, (and_true (and_true h).2).2⟩
  | _, _, .none, h => ⟨Ty.normalize_of_certNormal _ (and_true h).1,
    Option.isNone_iff_eq_none.mp (and_true (and_true h).2).1, (and_true (and_true h).2).2⟩
  | _, _, .cons x xs, h => ⟨Ty.normalize_of_certNormal _ (and_true h).1,
    facts_of_normal x (and_true (and_true h).2).1, facts_of_normal xs (and_true (and_true h).2).2⟩
  | _, _, .sameDeferred a b, h => ⟨facts_of_normal a (and_true h).1, facts_of_normal b (and_true h).2⟩

/-- The required-field check supplies each child's typing facts. -/
theorem field_facts_of_normal : ∀ {Γ : List Ty} {fs : List (String × Bool × Ty)} (fields : StepFields Γ fs),
    (FieldResults.map (fun _ {_} value => value) fs
      (cataFields (checkAlg (fun fs => (Ty.record fs).certNormal) (fun t => t.certNormal)
        (fun t => (Formation.check (Formation.sites false [] t)).isNone)
        (fun a b => Ty.sub a.normalize b.normalize)) fields)).all id = true →
    FieldResults.All (fun {_} value => value) fs (cataFields factsAlg fields)
  | _, _, .nil, _ => trivial
  | _, _, .cons _ value rest, h =>
    ⟨facts_of_normal value (and_true h).1, field_facts_of_normal rest (and_true h).2⟩
end

variable {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
  {src : {t : Ty} → Input Γ t → TermSrc} {env : Env} {path : List Nat} {types : List Ty}

mutual
/-- **A step's term types at the step's type** (claim `step-language-typed`): at every scope,
when the caller's terms type at the inputs' types, a step whose typing facts hold has a term
that types at its type, under each literal flag. A caller proves the facts from premises where a
type is a parameter, or by the typing check (`typed_of_normal`). -/
theorem typed_core (atoms : sig.atomOf = nativeAtomTy) : ∀ {Γ : List Ty} {src : {t : Ty} → Input Γ t → TermSrc}
    {env : Env} {path : List Nat} {types : List Ty} (_hin : ∀ {t : Ty} (x : Input Γ t), TypesEach sig (src x) env path types t)
    {s : Ty} (e : Step Γ s), e.Facts → (scope : e.ScopeFacts env types.length) → TypesEach sig (e.term src) env path types s
  | _, src, env, path, types, hin, _, .var x, _, _ => hin x
  | _, _, _, _, _, _, _, .bool b, _, _ => types_bool b
  | _, _, _, _, _, _, _, .nat n, _, _ => types_nat n
  | _, _, _, _, _, _, _, .unit, _, _ => types_unit
  | _, src, env, path, types, hin, _, .not a, h, hs => types_notT atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h)
  | _, src, env, path, types, hin, _, .and a b, h, hs => types_andT atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b h.2)
  | _, src, env, path, types, hin, _, .or a b, h, hs => types_orT atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b h.2)
  | _, src, env, path, types, hin, _, .ite c a b, h, hs =>
    types_ifT atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin c h.2.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h.2.2.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b h.2.2.2) h.1
  | _, src, env, path, types, hin, _, .add a b, h, hs => types_add atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b h.2)
  | _, src, env, path, types, hin, _, .sub a b, h, hs => types_sub atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b h.2)
  | _, src, env, path, types, hin, _, .lt a b, h, hs => types_lt atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b h.2)
  | _, src, env, path, types, hin, _, .eq a b, h, hs => types_eq atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b h.2)
  | _, src, env, path, types, hin, _, .isZero a, h, hs => types_isZero atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h)
  | _, src, env, path, types, hin, _, .pair a b, h, hs => types_pair atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b h.2)
  | _, src, env, path, types, hin, _, .tuple2 a b, h, hs =>
    types_tuple2 atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h.2.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b h.2.2) h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2
  | _, src, env, path, types, hin, _, .fst p, h, hs => fun _ => types_app (.cons (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin p h _) .nil) (atomOf_native atoms rfl)
  | _, src, env, path, types, hin, _, .snd p, h, hs => fun _ => types_app (.cons (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin p h _) .nil) (atomOf_native atoms rfl)
  | _, src, env, path, types, hin, _, .some a, h, hs => types_some atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h)
  | _, src, env, path, types, hin, _, .get r f, h, hs => fun _ => types_field (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin r h.2 false) (fieldType_ref h.1 f)
  | _, src, env, path, types, hin, _, .set r f v, h, hs => fun _ =>
    types_recordSet (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin r h.2.1 false) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin v h.2.2 true) (setType_ref h.1 f)
  | _, src, env, path, types, hin, _, .emptyLike xs, h, hs => types_noneOf atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h)
  | _, src, env, path, types, hin, _, .len xs, h, hs => types_len atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h)
  | _, src, env, path, types, hin, _, .snoc xs x, h, hs => types_snoc atoms h.1 (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h.2.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin x h.2.2)
  | _, src, env, path, types, hin, _, .append xs ys, h, hs => types_append atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h.2.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin ys h.2.2) h.1
  | _, src, env, path, types, hin, _, .take xs n, h, hs => types_take atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin n h.2)
  | _, src, env, path, types, hin, _, .drop xs n, h, hs => types_drop atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin n h.2)
  | _, src, env, path, types, hin, _, .head xs, h, hs => types_head atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h)

  | Γ, src, env, path, types, hin, _, .fold (acc := acc) (item := item) xs init body, h, hs => by
    have depth : types.length = env.names.length := hs
    have typedXs := typed_core atoms hin xs h.1 (scope_of_alignment xs depth)
    have typedInit := typed_core atoms hin init h.2.1 (scope_of_alignment init depth)
    have extended : (types ++ [acc, item]).length =
        (env.push [env.mint "acc", env.mint "item"]).names.length := by
      change (types ++ [_, _]).length = (env.names ++ [_, _]).length
      simp only [List.length_append, List.length_cons, List.length_nil, depth]
    have typedBody := typed_core atoms (fold_inputs_types depth hin) body h.2.2
      (scope_of_alignment body extended)
    intro const
    obtain ⟨lt, hlt, hle⟩ := typedXs false
    obtain ⟨it, hit, hie⟩ := typedInit false
    obtain ⟨bt, hbt, hbe⟩ := typedBody false
    refine ⟨.fold Option.none lt it bt, ?_, ?_⟩
    · change (xs.term src env path >>= fun l => init.term src env path >>= fun i =>
        body.term (foldSources src env path) (env.push [env.mint "acc", env.mint "item"]) path >>=
          fun b => Except.ok (Term.fold Option.none l i b)) = _
      rw [hlt, hit, hbt]
      rfl
    · exact argTy_fold_intro const hle hie (Ty.subN_refl acc) hbe (Ty.subN_refl acc)

  | _, src, env, path, types, hin, _, .tuple3 x y z, h, hs =>
    types_tuple3 atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin x h.2.1)
      (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin y h.2.2.1)
      (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin z h.2.2.2) h.1.1 h.1.2.1 h.1.2.2
  | _, src, env, path, types, hin, _, .record (fs := fs) fields, h, hs =>
    types_record_declared sig fs (ascending_of_normal h.1) h.1 h.2.1
      (fields_names fields src) (typed_fields atoms hin fields h.2.2 hs)
  | _, _, _, _, _, _, _, .nil (t := t), h, _ => types_nil_ascribe sig atoms t h.1 h.2.1 h.2.2
  | _, _, _, _, _, _, _, .none (t := t), h, _ => types_none_ascribe sig atoms t h.1 h.2.1 h.2.2
  | _, src, env, path, types, hin, _, .cons x xs, h, hs =>
    types_cons atoms h.1 (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin x h.2.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin xs h.2.2)
  | _, src, env, path, types, hin, _, .sameDeferred a b, h, hs =>
    types_same atoms (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin a h.1) (typed_core atoms (scope := scope_mono hs (by intro hb; simp only [binds, cata, bindsAlg, featureAlg] at hb ⊢; aesop)) hin b h.2)

/-- The required fields type at the declared field types, in schema order. -/
theorem typed_fields (atoms : sig.atomOf = nativeAtomTy) : ∀ {Γ : List Ty} {src : {t : Ty} → Input Γ t → TermSrc}
    {env : Env} {path : List Nat} {types : List Ty}
    (_hin : ∀ {t : Ty} (x : Input Γ t), TypesEach sig (src x) env path types t)
    {fs : List (String × Bool × Ty)} (fields : StepFields Γ fs),
    FieldResults.All (fun {_} value => value) fs (cataFields factsAlg fields) →
    (Step.record fields).ScopeFacts env types.length →
    TypesAll sig ((FieldResults.map (fun name {_} value => (name, value src)) fs
      (cataFields termAlg fields)).map Prod.snd) env path types true (fs.map fun f => f.2.2)
  | _, _, _, _, _, _, _, .nil, _, _ => .nil
  | _, src, env, path, types, hin, _, .cons _ value rest, h, hs =>
    .cons (typed_core atoms
      (scope := scope_mono hs (by intro hb; simp only [binds, cata, cataFields, bindsAlg, featureAlg, FieldResults.map, List.any_cons] at hb ⊢; aesop))
      hin value h.1 true)
      (typed_fields atoms hin rest h.2
        (scope_mono hs (by intro hb; simp only [binds, cata, cataFields, bindsAlg, featureAlg, FieldResults.map, List.any_cons] at hb ⊢; aesop)))
end

include atoms

/-- The typing law, requiring scope alignment only when a fold occurs. -/
@[semantics "store-typing" (requirement := R4)]
theorem typed (hin : ∀ {t : Ty} (x : Input Γ t), TypesEach sig (src x) env path types t)
    {s : Ty} (e : Step Γ s) (facts : e.Facts)
    (scope : e.ScopeFacts env types.length := by trivial) : TypesEach sig (e.term src) env path types s :=
  typed_core sig atoms hin e facts scope

/-- The typing law by the typing check: it closes by `rfl` on a concrete step. -/
theorem typed_of_normal (hin : ∀ {t : Ty} (x : Input Γ t), TypesEach sig (src x) env path types t)
    {s : Ty} (e : Step Γ s) (h : e.normal = true)
    (scope : e.ScopeFacts env types.length := by trivial) : TypesEach sig (e.term src) env path types s :=
  typed sig atoms hin e (facts_of_normal e h) scope

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
    have spine : (if a.spine = b.spine then a.spine else Option.none) = Option.some x.index := hs
    by_cases equal : a.spine = b.spine
    · rw [if_pos equal] at spine
      have outside : g.name ∉ c.writes ++ a.writes ++ b.writes := hw
      rw [List.mem_append, List.mem_append, not_or, not_or] at outside
      have ha := frame x g a spine outside.1.2
      have hb := frame x g b (equal ▸ spine) outside.2
      have chosen : ∀ test : Bool,
          g.get ((evalAlg L).ite (t := .record fs) (fun _ => test) (fun _ => a.eval L vs) (fun _ => b.eval L vs) vs) =
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
  | .fold _ _ _, hs, _ => nomatch hs
  | .record _, hs, _ => nomatch hs

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
      (evalAlg L).ite (fun _ => test) (fun _ => a.eval L vs) (fun _ => b.eval L vs) vs = cond test (a.eval L vs) (b.eval L vs) := by
    intro test
    cases test <;> rfl
  exact chosen (c.eval L vs)

/-- The fold denotation uses the body at the accumulator, item and captured inputs.
A helper of step-language-sound for module value equations. -/
theorem eval_fold (L : Leaves) (vs : Inputs L Γ) {acc item : Ty}
    (xs : Step Γ (.list item)) (init : Step Γ acc) (body : Step (acc :: item :: Γ) acc) :
    (Step.fold xs init body).eval L vs =
      (xs.eval L vs).foldl
        (fun a i => body.eval (Γ := acc :: item :: Γ) L
          ((a, (i, vs)) : Inputs L (acc :: item :: Γ))) (init.eval L vs) := rfl

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
